{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# options_ghc -fno-strictness         #-}
{-# options_ghc -fno-specialise         #-}

module Swap.OnChain
    ( mkUniswapValidator
    , validateLiquidityMinting
    , validateReserveLiquidityMinting
    ) where

import qualified Data.Map                         as Map
import           Data.List                        (sortOn, group)
import qualified Data.Tuple                       as Tuple
import           Ledger
import           Ledger.Constraints.OnChain       as Constraints
import           Ledger.Constraints.TxConstraints as Constraints
import           Ledger.Value                     (AssetClass (..),
                                                   assetClassValue,
                                                   assetClassValueOf, geq,
                                                   symbols)
import qualified PlutusTx
import           PlutusTx.Prelude
import qualified PlutusTx.AssocMap                as TxMap
import qualified Prelude                          (div, zip)
import           Reserve.OnChain
import           Swap.Pool                        (calculateAdditionalLiquidity,
                                                   calculateInitialLiquidity,
                                                   calculateRemoval, checkSwap,
                                                   lpTicker)
import           Swap.Types
import           Wallet.Effects


{-# INLINABLE findOwnInput' #-}
findOwnInput' :: ScriptContext -> TxInInfo
findOwnInput' ctx = fromMaybe (error ()) (findOwnInput ctx)

{-# INLINABLE valueWithin #-}
valueWithin :: TxInInfo -> Value
valueWithin = txOutValue . txInInfoResolved


{-# INLINABLE validateSwap #-}
-- | We check the swap is valid through 'checkSwap', and otherwise just make
-- sure that the pool token is passed through.
validateSwap :: Coin ReserveState -> LiquidityPool -> Coin PoolState -> ScriptContext -> Bool
validateSwap r lp c ctx =
-- checkReserveConditions: everyone who created a reserve UTxO must get its share. The amounts are given by percentageForReserveOutputs mutiplied by totalValA and totalValB.. so roughly, the validator must make sure by observing the ctx that there are the appropriate amounts in utxos at all the pkh from the list..
    allClientsReceiveCoins                                                              &&
    traceIfFalse "reserve UTxOs in Output missing" allReserveOutputsPresent             &&
    traceIfFalse "reserve UTxOs in Input missing" allReserveInputsPresent               &&
    checkSwap oldA oldB newA newB                                                       &&
    traceIfFalse "expected pool state token to be present in input" (isUnity inVal c)   &&
    traceIfFalse "expected pool state token to be present in output" (isUnity outVal c) &&
    traceIfFalse "did not expect Uniswap minting" noUniswapMinting
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    outputsWithReserveToken :: [TxOut]
    outputsWithReserveToken = [ o | o <- txInfoOutputs info, isUnity (txOutValue o) r, lpLiquidity o == lp ]

    inputsWithReserveToken :: [TxOut]
    inputsWithReserveToken = [ o | o <- map txInInfoResolved (txInfoInputs info), isUnity (txOutValue o) r, lpLiquidity o == lp ]

    lpLiquidity :: TxOut -> LiquidityPool
    lpLiquidity o = case txOutDatumHash o of
        Nothing -> traceError "reserve datum missing"
        Just h  -> fst $ findReserveDatum info h

    nrReserveTokens :: TxOut -> Integer
    nrReserveTokens o = case txOutDatumHash o of 
        Nothing -> traceError "reserve datum missing"
        Just h  -> snd $ findReserveDatum info h

    oldNrReserveTokens :: Integer
    oldNrReserveTokens = nrReserveTokens $ head inputsWithReserveToken

    newNrReserveTokens :: Integer
    newNrReserveTokens
        | (((length usedReserveInputs) * 1000000) `divide` (length inputsWithReserveToken)) >= 700000 = oldNrReserveTokens + 1
        | (((length usedReserveInputs) * 1000000) `divide` (length inputsWithReserveToken)) <= 300000 = max 3 (oldNrReserveTokens - 1)
        | otherwise                                                                                   = oldNrReserveTokens 

    allReserveInputsPresent :: Bool
    allReserveInputsPresent = length inputsWithReserveToken == oldNrReserveTokens

    -- check that there are N (in this case 2) outputs with a ReserveToken and the correct liquidityPool
    allReserveOutputsPresent :: Bool
    allReserveOutputsPresent = length outputsWithReserveToken == newNrReserveTokens

    -- functions to determine the amount each reserve utxo brought to the swap
    -- filter out all the UTxOs containing a ReserveCoin, filter out the ones with datum Used
    usedReserveInputs :: [TxOut]
    usedReserveInputs = [ o | o <- inputsWithReserveToken, datumIsUsed o]
        where
        datumIsUsed :: TxOut -> Bool
        datumIsUsed o = case (reserveDatumValue o (`findDatum` info)) of
            Just (Used _ _ _) -> True
            _               -> False

-- filter out the ones where amountA is bigger then oldA/oldNrReserveTokens || amountB > oldB/oldNrReserveTokens
-- get list with and list without them.
-- list with them: create Used Reservations with that PubKey and that Value..

-- find the pkhs and the corresponding amounts of A and B
    completeReserveInputs :: [(PubKeyHash, (Amount A, Amount B))]
    completeReserveInputs = zip pkhs (zip as bs) 
        where
        pkhs :: [PubKeyHash]
        pkhs = map getPkh usedReserveInputs

        as :: [Amount A]
        as = map getValA usedReserveInputs

        bs :: [Amount B]
        bs = map getValB usedReserveInputs

        getPkh :: TxOut -> PubKeyHash
        getPkh o = case (reserveDatumValue o (`findDatum` info)) of
            Just (Used _ pkh _) -> pkh
            _                  -> traceError "expected datum with value used"

        getValA :: TxOut -> Amount A
        getValA o = Amount {unAmount = assetClassValueOf (txOutValue o) (unCoin (lpCoinA lp))}

        getValB :: TxOut -> Amount B
        getValB o = Amount {unAmount = assetClassValueOf (txOutValue o) (unCoin (lpCoinB lp))}

    filteredReserveInputs :: [(PubKeyHash, (Amount A, Amount B))]
    filteredReserveInputs = filter (\(_, (a,b)) -> ((unAmount a) <= (unAmount oldA) `divide` oldNrReserveTokens && (unAmount b) <= (unAmount oldB) `divide` oldNrReserveTokens)) completeReserveInputs
    
    totalValA :: Amount A
    totalValA = sum $ map fst $ map snd filteredReserveInputs

    totalValB :: Amount B
    totalValB = sum $ map snd $ map snd filteredReserveInputs

    percentageFromReserveInputs :: [(PubKeyHash, (Integer, Integer))]
    percentageFromReserveInputs = map getPercentage filteredReserveInputs
        where
        getPercentage :: (PubKeyHash, (Amount A, Amount B)) -> (PubKeyHash, (Integer, Integer))
        getPercentage (pkh, (a,b))
            | (unAmount totalValA) == 0 = (pkh, (0, roundedPercentage b totalValB))
            | (unAmount totalValB) == 0 = (pkh, (roundedPercentage a totalValA, 0))
            | otherwise                 = (pkh, (roundedPercentage a totalValA, roundedPercentage b totalValB))

        roundedPercentage :: Amount a -> Amount a -> Integer
        roundedPercentage n t = (((unAmount n) * 1000000) `divide` (unAmount t)) - modulo (((unAmount n) * 1000000) `divide` (unAmount t)) 10000 

-- swap the to integers for every user, so if someone puts x percent of A in, he gets x percent of B out.
    percentageForReserveOutputs' :: [(PubKeyHash, (Integer, Integer))]
    percentageForReserveOutputs' = Prelude.zip (map fst percentageFromReserveInputs) (map Tuple.swap $ map snd percentageFromReserveInputs) -- must be filtered for own pkh

-- own Reservations must be taken out, otherwise the valuesToPay == valuesPaid comparison doesnt work because tha swapping wallet also and gets fees
    percentageForReserveOutputs :: [(PubKeyHash, (Integer, Integer))]
    percentageForReserveOutputs = filter (\(pkh, _) -> not $ txSignedBy info pkh) percentageForReserveOutputs'

    ratio :: Integer
    ratio = ((unAmount oldB) * 1000000) `divide` (unAmount oldA) 

-- these amounts depend on wether newA - oldA is positive or negative, for details see docs
    totalValA' :: Amount A
    totalValA'
        | newA - oldA > 0 = Amount (((unAmount totalValB) * 1000000) `divide` ratio)               -- this means that Coin A was put into swap
        | otherwise       = (oldA - newA) + totalValA -- this means that Coin B was put in the swap and the output of that swap is added here. 

    totalValB' :: Amount B
    totalValB'
        | newA - oldA > 0 =  (oldB - newB) + totalValB
        | otherwise       = Amount (((unAmount totalValA) * ratio) `divide` 1000000) 

    valuesToPayOfCoinA' :: [Integer]
    valuesToPayOfCoinA' = map ((*) (unAmount totalValA')) $ map fst $ map snd percentageForReserveOutputs

    valuesToPayOfCoinB' :: [Integer]
    valuesToPayOfCoinB' = map ((*) (unAmount totalValB')) $ map snd $ map snd percentageForReserveOutputs
 
    roundedValuesToPayOfCoinA :: [Integer]
    roundedValuesToPayOfCoinA = map (\val -> val - (modulo val 1000000)) valuesToPayOfCoinA'

    roundedValuesToPayOfCoinB :: [Integer]
    roundedValuesToPayOfCoinB = map (\val -> val - (modulo val 1000000)) valuesToPayOfCoinB'

    valuesToPayOfCoinA :: [Value]
    valuesToPayOfCoinA = map (assetClassValue (unCoin (lpCoinA lp))) roundedValuesToPayOfCoinA

    valuesToPayOfCoinB :: [Value]
    valuesToPayOfCoinB = map (assetClassValue (unCoin (lpCoinB lp))) roundedValuesToPayOfCoinB

    valuesToPay :: [Value]
    valuesToPay = map (\(a, b)-> a <> b) (zip valuesToPayOfCoinA valuesToPayOfCoinB)

-- | There must be only one row for every PubKeyHash, otherwise valuesToPay == valuesPaid doesn't work
    valuesToPayWithoutDuplicates :: TxMap.Map PubKeyHash Value 
    valuesToPayWithoutDuplicates = foldr (\(k, v) acc -> TxMap.unionWith (<>) acc $ TxMap.singleton k v) TxMap.empty $ zip (map fst percentageForReserveOutputs) valuesToPay

-- | the amounts of A and B that were actually paid to the participants, multiplied by 1000000
    valuesPaid' :: [Value]
    valuesPaid' = map (valuePaidTo info) $ TxMap.keys valuesToPayWithoutDuplicates -- map fst percentageForReserveOutputs

    valuesPaidOfCoinA' :: [Integer]
    valuesPaidOfCoinA' = map (\val -> 1000000 * (assetClassValueOf val (unCoin (lpCoinA lp)))) valuesPaid' 

    valuesPaidOfCoinB' :: [Integer]
    valuesPaidOfCoinB' = map (\val -> 1000000 * (assetClassValueOf val (unCoin (lpCoinB lp)))) valuesPaid'

    valuesPaidOfCoinA :: [Value]
    valuesPaidOfCoinA = map (assetClassValue (unCoin (lpCoinA lp))) valuesPaidOfCoinA'

    valuesPaidOfCoinB :: [Value]
    valuesPaidOfCoinB = map (assetClassValue (unCoin (lpCoinB lp))) valuesPaidOfCoinB'

    valuesPaid :: [Value]
    valuesPaid = map (\(a, b)-> a <> b) (zip valuesPaidOfCoinA valuesPaidOfCoinB)

    allClientsReceiveCoins :: Bool
    allClientsReceiveCoins = traceIfFalse "wrong amount" (TxMap.elems valuesToPayWithoutDuplicates == valuesPaid)


    -- from here on, old logic of the validateSwap function

    ownInput :: TxInInfo
    ownInput = findOwnInput' ctx

    -- this is the exact output of the contract utxo beeing validated. In the case of the Reserve Contract, there are going to be multiple validations..
    ownOutput :: TxOut
    ownOutput = case [ o
                     | o <- getContinuingOutputs ctx
                     , txOutDatumHash o == Just (snd $ ownHashes ctx)
                     ] of
        [o] -> o
        _   -> traceError "expected exactly one output to the same liquidity pool"

    oldA = amountA inVal -- amountOf inVal lpCoinA
    oldB = amountB inVal
    newA = amountA outVal
    newB = amountB outVal

    amountA v = amountOf v (lpCoinA lp)
    amountB v = amountOf v (lpCoinB lp)

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue ownOutput

    noUniswapMinting :: Bool
    noUniswapMinting =
      let
        AssetClass (cs, _) = unCoin c
        minted             = txInfoMint info
      in
        all (/= cs) $ symbols minted

{-# INLINABLE validateCreate #-}
-- | Ths validates the creation of a liquidity pool to exchange coins. In order to be
-- valid,
--
--  1,2. We need to be dealing with the Uniswap coin,
--  3. We have to exchanging different coins,
--  4. The pool can't already exist,
--  5. The pool needs a single value as output,
--  6. The liquidity amount needs to be as-determined by 'calculateInitialLiquidity'
--      (i.e. the amount from the Uniswap V2 paper).
--  7,8. We need to be exchanging more than zero of each kind of coin.
--  9. It should output a pool with the determined properties
-- 10. also mint 2 ReserveCoins
validateCreate :: Uniswap
               -> Coin PoolState
               -> Coin ReserveState
               -> [LiquidityPool]
               -> LiquidityPool
               -> ScriptContext
               -> Bool
validateCreate Uniswap{..} c r lps lp@LiquidityPool{..} ctx =
    traceIfFalse "Uniswap coin not present" (isUnity (valueWithin $ findOwnInput' ctx) usCoin)          && -- 1.
    Constraints.checkOwnOutputConstraint ctx (OutputConstraint (Factory $ lp : lps) $ unitValue usCoin) && -- 2.
    (unCoin lpCoinA /= unCoin lpCoinB)                                                                  && -- 3.
    all (/= lp) lps                                                                                     && -- 4.
    isUnity minted c                                                                                    && -- 5.
    amountOf minted r == 3                                                                              && -- 10. New!!
    (amountOf minted liquidityCoin' == liquidity)                                                       && -- 6.
    (outA > 0)                                                                                          && -- 7.
    (outB > 0)                                                                                          && -- 8.
    Constraints.checkOwnOutputConstraint ctx (OutputConstraint (Pool lp liquidity) $                       -- 9.
        valueOf lpCoinA outA <> valueOf lpCoinB outB <> unitValue c)
  where
    poolOutput :: TxOut
    poolOutput = case [o | o <- getContinuingOutputs ctx, isUnity (txOutValue o) c] of
        [o] -> o
        _   -> traceError "expected exactly one pool output"

    outA      = amountOf (txOutValue poolOutput) lpCoinA
    outB      = amountOf (txOutValue poolOutput) lpCoinB
    liquidity = calculateInitialLiquidity outA outB

    minted :: Value
    minted = txInfoMint $ scriptContextTxInfo ctx

    liquidityCoin' :: Coin Liquidity
    liquidityCoin' = let AssetClass (cs,_) = unCoin c in mkCoin cs $ lpTicker lp

{-# INLINABLE validateCloseFactory #-}
-- | See 'Plutus.Contracts.Uniswap.OffChain.close'.
validateCloseFactory :: Uniswap -> Coin PoolState -> Coin ReserveState -> [LiquidityPool] -> ScriptContext -> Bool
validateCloseFactory Uniswap{..} c r lps ctx =
    traceIfFalse "Uniswap coin not present" (isUnity (valueWithin $ findOwnInput' ctx) usCoin)                          && -- 1.
    traceIfFalse "wrong mint value"        (txInfoMint info == negate (unitValue c <> valueOf lC (snd lpLiquidity) <> valueOf r (Amount tokensToBurn))) && -- 2. 
    traceIfFalse "factory output wrong"                                                                                    -- 3.
        (Constraints.checkOwnOutputConstraint ctx $ OutputConstraint (Factory $ filter (/= fst lpLiquidity) lps) $ unitValue usCoin)
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    poolInput :: TxInInfo
    poolInput = case [ i
                     | i <- txInfoInputs info
                     , isUnity (valueWithin i) c
                     ] of
        [i] -> i
        _   -> traceError "expected exactly one pool input"

    lpLiquidity :: (LiquidityPool, Amount Liquidity)
    lpLiquidity = case txOutDatumHash . txInInfoResolved $ poolInput of
        Nothing -> traceError "pool input witness missing"
        Just h  -> findPoolDatum info h

    lC :: Coin Liquidity
    lC  = let AssetClass (cs, _) = unCoin c in mkCoin cs (lpTicker $ fst lpLiquidity)

    inputsWithReserveToken :: [TxOut]
    inputsWithReserveToken = [ o | o <- map txInInfoResolved (txInfoInputs info), isUnity (txOutValue o) r ]

    nrReserveTokens :: TxOut -> Integer
    nrReserveTokens o = case txOutDatumHash o of 
        Nothing -> traceError "reserve datum missing"
        Just h  -> snd $ findReserveDatum info h

    tokensToBurn :: Integer
    tokensToBurn = nrReserveTokens $ head inputsWithReserveToken

{-# INLINABLE validateClosePool #-}
-- | See 'Plutus.Contracts.Uniswap.OffChain.close'.
validateClosePool :: Uniswap -> LiquidityPool -> Coin ReserveState -> ScriptContext -> Bool
validateClosePool us lp r ctx = 
    hasFactoryInput &&
    txInfoMint info == negate (valueOf r $ Amount nrReserveTokens)
   -- amountOf minted r == Amount nrReserveTokens
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    hasFactoryInput :: Bool
    hasFactoryInput =
        traceIfFalse "Uniswap factory input expected" $
        isUnity (valueSpent info) (usCoin us)

    inputsWithReserveToken :: [TxOut]
    inputsWithReserveToken = [ o | o <- map txInInfoResolved (txInfoInputs info), isUnity (txOutValue o) r, lpLiquidity o == lp ]

    lpLiquidity :: TxOut -> LiquidityPool
    lpLiquidity o = case txOutDatumHash o of
        Nothing -> traceError "reserve datum missing"
        Just h  -> fst $ findReserveDatum info h

    minted :: Value
    minted = txInfoMint $ scriptContextTxInfo ctx

    nrReserveTokens :: Integer
    nrReserveTokens = case txOutDatumHash (head inputsWithReserveToken) of 
        Nothing -> traceError "reserve datum missing"
        Just h  -> snd $ findReserveDatum info h

{-# INLINABLE validateRemove #-}
-- | See 'Plutus.Contracts.Uniswap.OffChain.remove'.
validateRemove :: Coin PoolState -> LiquidityPool -> Amount Liquidity -> ScriptContext -> Bool
validateRemove c lp liquidity ctx =
    traceIfFalse "zero removal"                        (diff > 0)                                     &&
    traceIfFalse "removal of too much liquidity"       (diff < liquidity)                             &&
    traceIfFalse "pool state coin missing"             (isUnity inVal c)                              &&
    traceIfFalse "wrong liquidity pool output"         (fst lpLiquidity == lp)                        &&
    traceIfFalse "pool state coin missing from output" (isUnity outVal c)                             &&
    traceIfFalse "liquidity tokens not burnt"          (txInfoMint info == negate (valueOf lC diff))  &&
    traceIfFalse "non-positive liquidity"              (outA > 0 && outB > 0)
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxInInfo
    ownInput = findOwnInput' ctx

    output :: TxOut
    output = case getContinuingOutputs ctx of
        [o] -> o
        _   -> traceError "expected exactly one Uniswap output"

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue output

    lpLiquidity :: (LiquidityPool, Amount Liquidity)
    lpLiquidity = case txOutDatumHash output of
        Nothing -> traceError "pool output witness missing"
        Just h  -> findPoolDatum info h

    lC :: Coin Liquidity
    lC = let AssetClass (cs, _) = unCoin c in mkCoin cs (lpTicker lp)

    diff         = liquidity - snd lpLiquidity
    inA          = amountOf inVal $ lpCoinA lp
    inB          = amountOf inVal $ lpCoinB lp
    (outA, outB) = calculateRemoval inA inB liquidity diff

{-# INLINABLE validateAdd #-}
-- | See 'Plutus.Contracts.Uniswap.OffChain.add'.
validateAdd :: Coin PoolState -> LiquidityPool -> Amount Liquidity -> ScriptContext -> Bool
validateAdd c lp liquidity ctx =
    traceIfFalse "pool stake token missing from input"          (isUnity inVal c)                                                    &&
    traceIfFalse "output pool for same liquidity pair expected" (lp == fst outDatum)                                                 &&
    traceIfFalse "must not remove tokens"                       (delA >= 0 && delB >= 0)                                             &&
    traceIfFalse "insufficient liquidity"                       (delL >= 0)                                                          &&
    traceIfFalse "wrong amount of liquidity tokens"             (delL == calculateAdditionalLiquidity oldA oldB liquidity delA delB) &&
    traceIfFalse "wrong amount of liquidity tokens minted"      (txInfoMint info == valueOf lC delL)
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxInInfo
    ownInput = findOwnInput' ctx

    ownOutput :: TxOut
    ownOutput = case [ o
                     | o <- getContinuingOutputs ctx
                     , isUnity (txOutValue o) c
                     ] of
        [o] -> o
        _   -> traceError "expected exactly on pool output"

    outDatum :: (LiquidityPool, Amount Liquidity)
    outDatum = case txOutDatum ownOutput of
        Nothing -> traceError "pool output datum hash not found"
        Just h  -> findPoolDatum info h

    inVal, outVal :: Value
    inVal  = valueWithin ownInput
    outVal = txOutValue ownOutput

    oldA = amountOf inVal aC
    oldB = amountOf inVal bC
    delA = amountOf outVal aC - oldA
    delB = amountOf outVal bC - oldB
    delL = snd outDatum - liquidity

    aC = lpCoinA lp
    bC = lpCoinB lp

    lC :: Coin Liquidity
    lC = let AssetClass (cs, _) = unCoin c in mkCoin cs $ lpTicker lp

{-# INLINABLE findPoolDatum #-}
findPoolDatum :: TxInfo -> DatumHash -> (LiquidityPool, Amount Liquidity)
findPoolDatum info h = case findDatum h info of
    Just (Datum d) -> case PlutusTx.unsafeFromBuiltinData d of
        (Pool lp a) -> (lp, a)
        _           -> traceError "error decoding data"
    _              -> traceError "pool input datum not found"

{-# INLINABLE findReserveDatum #-}
findReserveDatum :: TxInfo -> DatumHash -> (LiquidityPool, Integer)
findReserveDatum info h = case findDatum h info of
    Just (Datum d) -> case PlutusTx.unsafeFromBuiltinData d of
        (Used lp _ n) -> (lp, n)
        (Unused lp n) -> (lp, n) 
        _             -> traceError "error decoding data"
    _              -> traceError "reserve input datum not found"

{-# INLINABLE mkUniswapValidator #-}
mkUniswapValidator :: Uniswap
                   -> Coin PoolState
                   -> Coin ReserveState
                   -> UniswapDatum
                   -> UniswapAction
                   -> ScriptContext
                   -> Bool
mkUniswapValidator us c r (Factory lps) (Create lp) ctx = validateCreate us c r lps lp ctx
mkUniswapValidator _  c r (Pool lp _)   Swap        ctx = validateSwap r lp c ctx
mkUniswapValidator us c r (Factory lps) Close       ctx = validateCloseFactory us c r lps ctx
mkUniswapValidator us _ r (Pool lp _)   Close       ctx = validateClosePool us lp r ctx
mkUniswapValidator _  c _ (Pool lp a)   Remove      ctx = validateRemove c lp a ctx
mkUniswapValidator _  c _ (Pool lp a)   Add         ctx = validateAdd c lp a ctx
mkUniswapValidator _  _ _ _             _           _   = False

{-# INLINABLE validateLiquidityMinting #-}
validateLiquidityMinting :: Uniswap -> TokenName -> () -> ScriptContext -> Bool
validateLiquidityMinting Uniswap{..} tn _ ctx
  = case [ i
         | i <- txInfoInputs $ scriptContextTxInfo ctx
         , let v = valueWithin i
         , let c = mkCoin (ownCurrencySymbol ctx) tn
         , isUnity v usCoin || isUnity v lpC                                              -- maybe something like (amountOf v lpC) `geq` (Amount 1)??
         ] of
    [_]    -> True
    [_, _] -> True
    _      -> traceError "pool state minting without Uniswap input"
  where
    lpC :: Coin Liquidity
    lpC = mkCoin (ownCurrencySymbol ctx) tn

{-# INLINABLE validateReserveLiquidityMinting #-}
validateReserveLiquidityMinting :: Uniswap -> TokenName -> () -> ScriptContext -> Bool
validateReserveLiquidityMinting  Uniswap{..} tn _ ctx
  = case [ i
         | i <- txInfoInputs $ scriptContextTxInfo ctx
         , let v = valueWithin i
         , isUnity v usCoin || isUnity v rsC
         ] of
    [_]    -> True
    xs     -> length xs == nrReserveTokens || length xs == nrReserveTokens + 1 
  where
    rsC :: Coin ReserveState
    rsC = mkCoin (ownCurrencySymbol ctx) tn

    info :: TxInfo
    info = scriptContextTxInfo ctx

    inputWithReserveToken :: TxOut
    inputWithReserveToken = head [ o | o <- map txInInfoResolved (txInfoInputs info), isUnity (txOutValue o) rsC ]

    nrReserveTokens :: Integer
    nrReserveTokens = case txOutDatumHash inputWithReserveToken of 
        Nothing -> traceError "reserve datum missing"
        Just h  -> snd $ findReserveDatum info h
-- get the number from the datum and state that they have to be present..

{--    which :: Bool 
    which = case tn of 
        "Pool State" -> True 
        otherwise    -> False

    coinPresent :: Bool
    coinPresent = case which of 
        True -> isUnity v lpC
        False -> isUnity v rsC


--   if tn == "Reserve State" or tn == "Pool State" 
-- make case differentiation with tn if ReserveState:
    rsC :: Coin ReserveState
    rsC = mkCoin (ownCurrencySymbol ctx) tn  --}
