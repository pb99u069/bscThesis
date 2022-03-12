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

module Swap.OffChain
    ( poolStateCoinFromUniswapCurrency, reserveStateCoin, liquidityCoin
    , CreateParams (..)
    , SwapParams (..)
    , CloseParams (..)
    , RemoveParams (..)
    , AddParams (..)
    , ReserveParams (..)
    , RetrieveParams (..)
    , UniswapUserSchema, UserContractState (..)
    , UniswapOwnerSchema
    , start, create, add, remove, close, swap, pools, reserve, retrieve
    , ownerEndpoint, userEndpoints
    ) where

import           Ledger.Ada                (lovelaceValueOf)
import           Control.Monad             hiding (fmap)
import qualified Data.Map                  as Map
import           Data.Maybe                (fromJust)
import           Data.Monoid               (Last (..))
import           Data.Proxy                (Proxy (..))
import           Data.Text                 (Text, pack)
import qualified Data.Tuple                as Tuple
import           Data.Void                 (Void, absurd)
import           Ledger                    hiding (singleton)
import           Ledger.Constraints        as Constraints
import qualified Ledger.Typed.Scripts      as Scripts
import           Playground.Contract
import           Plutus.Contract
import qualified Plutus.Contracts.Currency as Currency
import qualified PlutusTx
import           PlutusTx.Prelude          hiding (Semigroup (..), dropWhile,
                                            flip, unless, sum)
import           Prelude                   as Haskell (mod, repeat, sum, Int, Semigroup (..),
                                                       String, div, dropWhile,
                                                       last, flip, show, (^))
import           Reserve.OnChain           (mkReserveValidator, ReserveDatum (..), ReserveRedeemer (..))
import           Swap.OnChain              (mkUniswapValidator, validateLiquidityMinting, validateReserveLiquidityMinting)
import           Swap.Pool
import           Swap.Types
import           Text.Printf               (printf)

data Uniswapping
instance Scripts.ValidatorTypes Uniswapping where
    type instance RedeemerType Uniswapping = UniswapAction
    type instance DatumType    Uniswapping = UniswapDatum

data ReserveContract
instance Scripts.ValidatorTypes ReserveContract where
    type instance RedeemerType ReserveContract = ReserveRedeemer
    type instance DatumType ReserveContract = ReserveDatum


type UniswapOwnerSchema = Endpoint "start" ()

-- | Schema for the endpoints for users of Uniswap.
type UniswapUserSchema =
        Endpoint "create"           CreateParams          -- here, in addition, N Reserve Coins have to be created and they must be paid to N UTxOs at the Reserve Address
        .\/ Endpoint "swap"         SwapParams        -- here, in addition, the N Reserve UTxOs must be consumed and recreated, and for all the UTxOs with Datum Used pkh, there must be a payment at the corresponding PubKey
        .\/ Endpoint "close"        CloseParams
        .\/ Endpoint "remove"       RemoveParams
        .\/ Endpoint "add"          AddParams
        .\/ Endpoint "pools"        ()
        .\/ Endpoint "funds"        ()
        .\/ Endpoint "reserveFunds" ()
        .\/ Endpoint "stop"         ()
        .\/ Endpoint "reserve"      ReserveParams 
        .\/ Endpoint "retrieve"     RetrieveParams

-- | Type of the Uniswap user contract state.
data UserContractState =
      Pools [((Coin A, Amount A), (Coin B, Amount B))]
    | Funds Value
    | ReserveFunds Value
    | Created
    | Swapped
    | Added
    | Removed
    | Closed
    | Stopped
    | Reserved
    | Retrieved
    deriving (Show, Generic, FromJSON, ToJSON)


uniswapTokenName, poolStateTokenName, reserveStateTokenName :: TokenName
uniswapTokenName = "Uniswap"
poolStateTokenName = "Pool State"
reserveStateTokenName = "Reserve State"

uniswapInstance :: Uniswap -> Scripts.TypedValidator Uniswapping
uniswapInstance us = Scripts.mkTypedValidator @Uniswapping
    ($$(PlutusTx.compile [|| mkUniswapValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode us
        `PlutusTx.applyCode` PlutusTx.liftCode c
        `PlutusTx.applyCode` PlutusTx.liftCode r)
     $$(PlutusTx.compile [|| wrap ||])
  where
    c :: Coin PoolState
    c = poolStateCoin us

    r :: Coin ReserveState
    r = reserveStateCoin us

    wrap = Scripts.wrapValidator @UniswapDatum @UniswapAction

uniswapScript :: Uniswap -> Validator
uniswapScript us = Scripts.validatorScript (uniswapInstance us)

uniswapAddress :: Uniswap -> Ledger.Address
uniswapAddress us = Ledger.scriptAddress (uniswapScript us)

typedReserveValidator :: Uniswap -> Scripts.TypedValidator ReserveContract
typedReserveValidator us = Scripts.mkTypedValidator @ReserveContract
    ($$(PlutusTx.compile [|| mkReserveValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode u
        `PlutusTx.applyCode` PlutusTx.liftCode r
        `PlutusTx.applyCode` PlutusTx.liftCode c)
    $$(PlutusTx.compile [|| wrap ||])
  where
    u :: Coin U
    u = usCoin us

    c :: Coin PoolState
    c = poolStateCoin us

    r :: Coin ReserveState
    r = reserveStateCoin us

    wrap = Scripts.wrapValidator @ReserveDatum @ReserveRedeemer

reserveValidator :: Uniswap -> Validator
reserveValidator us = Scripts.validatorScript (typedReserveValidator us)

reserveAddress :: Uniswap -> Ledger.Address
reserveAddress us = scriptAddress (reserveValidator us)

uniswap :: CurrencySymbol -> Uniswap
uniswap cs = Uniswap $ mkCoin cs uniswapTokenName

liquidityPolicy :: Uniswap -> MintingPolicy
liquidityPolicy us = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \u t -> Scripts.wrapMintingPolicy (validateLiquidityMinting u t) ||])
        `PlutusTx.applyCode` PlutusTx.liftCode us
        `PlutusTx.applyCode` PlutusTx.liftCode poolStateTokenName

liquidityCurrency :: Uniswap -> CurrencySymbol
liquidityCurrency = scriptCurrencySymbol . liquidityPolicy

poolStateCoin :: Uniswap -> Coin PoolState
poolStateCoin = flip mkCoin poolStateTokenName . liquidityCurrency

reserveLiquidityPolicy :: Uniswap -> MintingPolicy
reserveLiquidityPolicy us = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \u r -> Scripts.wrapMintingPolicy (validateReserveLiquidityMinting u r) ||])
        `PlutusTx.applyCode` PlutusTx.liftCode us
        `PlutusTx.applyCode` PlutusTx.liftCode reserveStateTokenName

reserveLiquidityCurrency :: Uniswap -> CurrencySymbol
reserveLiquidityCurrency = scriptCurrencySymbol . reserveLiquidityPolicy

reserveStateCoin :: Uniswap -> Coin ReserveState
reserveStateCoin = flip mkCoin reserveStateTokenName . reserveLiquidityCurrency

-- | Gets the 'Coin' used to identity liquidity pools.
poolStateCoinFromUniswapCurrency :: CurrencySymbol -- ^ The currency identifying the Uniswap instance.
                                 -> Coin PoolState
poolStateCoinFromUniswapCurrency = poolStateCoin . uniswap

-- | Gets the liquidity token for a given liquidity pool.
liquidityCoin :: CurrencySymbol -- ^ The currency identifying the Uniswap instance.
              -> Coin A         -- ^ One coin in the liquidity pair.
              -> Coin B         -- ^ The other coin in the liquidity pair.
              -> Coin Liquidity
liquidityCoin cs coinA coinB = mkCoin (liquidityCurrency $ uniswap cs) $ lpTicker $ LiquidityPool coinA coinB

-- | Parameters for the @create@-endpoint, which creates a new liquidity pool.
data CreateParams = CreateParams
    { cpCoinA   :: Coin A   -- ^ One 'Coin' of the liquidity pair.
    , cpCoinB   :: Coin B   -- ^ The other 'Coin'.
    , cpAmountA :: Amount A -- ^ Amount of liquidity for the first 'Coin'.
    , cpAmountB :: Amount B -- ^ Amount of liquidity for the second 'Coin'.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @swap@-endpoint, which allows swaps between the two different coins in a liquidity pool.
data SwapParams = SwapParams
    { spCoinA :: Coin A         -- ^ One 'Coin' of the liquidity pair.
    , spCoinB :: Coin B         -- ^ The other 'Coin'.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @close@-endpoint, which closes a liquidity pool.
data CloseParams = CloseParams
    { clpCoinA :: Coin A         -- ^ One 'Coin' of the liquidity pair.
    , clpCoinB :: Coin B         -- ^ The other 'Coin' of the liquidity pair.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @remove@-endpoint, which removes some liquidity from a liquidity pool.
data RemoveParams = RemoveParams
    { rpCoinA :: Coin A           -- ^ One 'Coin' of the liquidity pair.
    , rpCoinB :: Coin B           -- ^ The other 'Coin' of the liquidity pair.
    , rpDiff  :: Amount Liquidity -- ^ The amount of liquidity tokens to burn in exchange for liquidity from the pool.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @add@-endpoint, which adds liquidity to a liquidity pool in exchange for liquidity tokens.
data AddParams = AddParams
    { apCoinA   :: Coin A         -- ^ One 'Coin' of the liquidity pair.
    , apCoinB   :: Coin B         -- ^ The other 'Coin' of the liquidity pair.
    , apAmountA :: Amount A       -- ^ The amount of coins of the first kind to add to the pool.
    , apAmountB :: Amount B       -- ^ The amount of coins of the second kind to add to the pool.
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- | Parameters for the @reserve@-endpoint, both Amounts can be positive, if desired..
data ReserveParams = ReserveParams
    { rsCoinA   :: Coin A 
    , rsCoinB   :: Coin B 
    , rsAmountA :: Amount A       -- ^ The amount of coins of the first kind to reserve for a future Swap 
    , rsAmountB :: Amount B       -- ^ The amount of coins of the second kind to reserve for a future Swap
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)
--
-- | Parameters for the @retrieve@-endpoint 
data RetrieveParams = RetrieveParams
    { rtCoinA   :: Coin A 
    , rtCoinB   :: Coin B 
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)


-- | Creates a Uniswap "factory". This factory will keep track of the existing liquidity pools and enforce that there will be at most one liquidity pool
-- for any pair of tokens at any given time.
start :: forall w s. Contract w s Text Uniswap
start = do
    pkh <- pubKeyHash <$> ownPubKey
    cs  <- fmap Currency.currencySymbol $
           mapError (pack . show @Currency.CurrencyError) $
           Currency.mintContract pkh [(uniswapTokenName, 1)]
    let c    = mkCoin cs uniswapTokenName
        us   = uniswap cs
        inst = uniswapInstance us
        tx   = mustPayToTheScript (Factory []) $ unitValue c
    ledgerTx <- submitTxConstraints inst tx
    void $ awaitTxConfirmed $ txId ledgerTx
    void $ waitNSlots 1

    logInfo @String $ printf "started Uniswap %s at address %s" (show us) (show $ uniswapAddress us)
    return us

-- | Creates a liquidity pool for a pair of coins. The creator provides liquidity for both coins and gets liquidity tokens in return.
-- this function must also create N reserveState Coins and pay them to "otherScript" at the ReserveAddress, given by Reserve.OnChain..
create :: forall w s. Uniswap -> CreateParams -> Contract w s Text ()
create us CreateParams{..} = do
    when (unCoin cpCoinA == unCoin cpCoinB) $ throwError "coins must be different"
    when (cpAmountA <= 0 || cpAmountB <= 0) $ throwError "amounts must be positive"
    (oref, o, lps) <- findUniswapFactory us
    let liquidity = calculateInitialLiquidity cpAmountA cpAmountB
        lp        = LiquidityPool {lpCoinA = cpCoinA, lpCoinB = cpCoinB}
    let usInst   = uniswapInstance us
        usScript = uniswapScript us
        rsScript = reserveValidator us
        usDat1   = Factory $ lp : lps
        usDat2   = Pool lp liquidity
        rsDat    = Unused
        psC      = poolStateCoin us
        rsC      = reserveStateCoin us
        lC       = mkCoin (liquidityCurrency us) $ lpTicker lp
        usVal    = unitValue $ usCoin us
        lpVal    = valueOf cpCoinA cpAmountA <> valueOf cpCoinB cpAmountB <> unitValue psC
        rsVal    = valueOf rsC 3

        lookups  = Constraints.typedValidatorLookups usInst              <>
                   Constraints.otherScript usScript                      <>
                   Constraints.otherScript rsScript                      <>
                   Constraints.mintingPolicy (liquidityPolicy us)        <>
                   Constraints.mintingPolicy (reserveLiquidityPolicy us) <>
                   Constraints.unspentOutputs (Map.singleton oref o)

        tx       = Constraints.mustPayToOtherScript (validatorHash usScript) (Datum $ PlutusTx.toBuiltinData usDat1) usVal                <>
                   Constraints.mustPayToOtherScript (validatorHash usScript) (Datum $ PlutusTx.toBuiltinData usDat2) lpVal                <>
                   Constraints.mustPayToOtherScript (validatorHash rsScript) (Datum $ PlutusTx.toBuiltinData (Unused lp 3)) (unitValue rsC) <> -- MustPayToOtherScript ValidatorHash Datum Value
                   Constraints.mustPayToOtherScript (validatorHash rsScript) (Datum $ PlutusTx.toBuiltinData (Unused lp 3)) (unitValue rsC) <> -- MustPayToOtherScript ValidatorHash Datum Value
                   Constraints.mustPayToOtherScript (validatorHash rsScript) (Datum $ PlutusTx.toBuiltinData (Unused lp 3)) (unitValue rsC) <> -- MustPayToOtherScript ValidatorHash Datum Value
                   Constraints.mustMintValue (valueOf rsC 3 <> unitValue psC <> valueOf lC liquidity)                                     <>
                   Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData $ Create lp)

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "created liquidity pool: " ++ show lp ++ " and corresponding reserve utxos"

-- | Closes a liquidity pool by burning all remaining liquidity tokens in exchange for all liquidity remaining in the pool.
close :: forall w s. Uniswap -> CloseParams -> Contract w s Text ()
close us CloseParams{..} = do
    let rsC = reserveStateCoin us
    ((oref1, o1, lps), (oref2, o2, lp, liquidity)) <- findUniswapFactoryAndPool us clpCoinA clpCoinB
    reserveUtxos                                   <- findReserveUtxos us rsC                          -- TxOutRef, TxOutTx
    pkh                                            <- pubKeyHash <$> ownPubKey
    let usInst   = uniswapInstance us
        usScript = uniswapScript us
        rsScript = reserveValidator us
        usDat    = Factory $ filter (/= lp) lps
        usC      = usCoin us
        psC      = poolStateCoin us
        lC       = mkCoin (liquidityCurrency us) $ lpTicker lp
        usVal    = unitValue usC
        psVal    = unitValue psC
        lVal     = valueOf lC liquidity
        redeemer = Redeemer $ PlutusTx.toBuiltinData Close

        orefs                = map fst reserveUtxos
        os                   = map snd reserveUtxos
        orefsAndOs'          = zip orefs os
        dats                 = map (fromJust . getMaybeReserveDatum . txOutTxDatum) (map snd reserveUtxos)
        vals                 = map (txOutValue . txOutTxOut) (map snd reserveUtxos)
        datsAndVals          = zip dats vals
        allInputs            = zip orefsAndOs' datsAndVals                                               -- [(oref, o), (dat, val))]
        allUsedInputs        = filter (\(_, (dat, _)) -> outputStateUsedAndCorrectLp lp dat) allInputs                                                                                            -- [(Datum, Value)]
        orefsAndOsUsed       = map fst allUsedInputs
        allUnusedInputs      = filter (\(_, (dat, _)) -> outputStateUnusedAndCorrectLp lp dat) allInputs            -- [(Datum, Value)]
        orefsAndOsUnused     = map fst allUnusedInputs 
        orefsAndOs           = orefsAndOsUnused ++ orefsAndOsUsed
        rsVal                = valueOf rsC $ Amount (getNrReserveUtxos $ head dats)

        lookups  = Constraints.typedValidatorLookups usInst        <>
                   Constraints.otherScript usScript                <>
                   Constraints.mintingPolicy (liquidityPolicy us) <>
                   Constraints.ownPubKeyHash pkh                   <>
                   Constraints.unspentOutputs (Map.singleton oref1 o1 <> Map.singleton oref2 o2) <>
                   Constraints.mintingPolicy (reserveLiquidityPolicy us) <>
                   Constraints.otherScript rsScript         <>
                   Constraints.unspentOutputs (foldr (<>) Map.empty (unspentOutputsMaps orefsAndOs))

        tx       = Constraints.mustPayToTheScript usDat usVal          <>
                   Constraints.mustMintValue (negate $ psVal <> rsVal <> lVal) <>
                   Constraints.mustSpendScriptOutput oref1 redeemer    <>
                   Constraints.mustSpendScriptOutput oref2 redeemer    <>
                   Constraints.mustIncludeDatum (Datum $ PlutusTx.toBuiltinData $ Pool lp liquidity) <>
                   mconcat (scriptSpendingToClose $ map fst orefsAndOs) 

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "closed liquidity pool: " ++ show lp


scriptSpendingToClose :: forall i o. [TxOutRef] -> [TxConstraints i o]
scriptSpendingToClose [] = []
scriptSpendingToClose refs = map (\val -> Constraints.mustSpendScriptOutput val (Redeemer $ PlutusTx.toBuiltinData Destroy)) refs

-- | Removes some liquidity from a liquidity pool in exchange for liquidity tokens.
remove :: forall w s. Uniswap -> RemoveParams -> Contract w s Text ()
remove us RemoveParams{..} = do
    (_, (oref, o, lp, liquidity)) <- findUniswapFactoryAndPool us rpCoinA rpCoinB
    pkh                           <- pubKeyHash <$> ownPubKey
    when (rpDiff < 1 || rpDiff >= liquidity) $ throwError "removed liquidity must be positive and less than total liquidity"
    let usInst       = uniswapInstance us
        usScript     = uniswapScript us
        dat          = Pool lp $ liquidity - rpDiff
        psC          = poolStateCoin us
        lC           = mkCoin (liquidityCurrency us) $ lpTicker lp
        psVal        = unitValue psC
        lVal         = valueOf lC rpDiff
        inVal        = txOutValue $ txOutTxOut o
        inA          = amountOf inVal rpCoinA
        inB          = amountOf inVal rpCoinB
        (outA, outB) = calculateRemoval inA inB liquidity rpDiff
        val          = psVal <> valueOf rpCoinA outA <> valueOf rpCoinB outB
        redeemer     = Redeemer $ PlutusTx.toBuiltinData Remove

        lookups  = Constraints.typedValidatorLookups usInst          <>
                   Constraints.otherScript usScript                  <>
                   Constraints.mintingPolicy (liquidityPolicy us)   <>
                   Constraints.unspentOutputs (Map.singleton oref o) <>
                   Constraints.ownPubKeyHash pkh

        tx       = Constraints.mustPayToTheScript dat val          <>
                   Constraints.mustMintValue (negate lVal)        <>
                   Constraints.mustSpendScriptOutput oref redeemer

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "removed liquidity from pool: " ++ show lp

-- | Adds some liquidity to an existing liquidity pool in exchange for newly minted liquidity tokens.
add :: forall w s. Uniswap -> AddParams -> Contract w s Text ()
add us AddParams{..} = do
    pkh                           <- pubKeyHash <$> ownPubKey
    (_, (oref, o, lp, liquidity)) <- findUniswapFactoryAndPool us apCoinA apCoinB
    when (apAmountA < 0 || apAmountB < 0) $ throwError "amounts must not be negative"
    let outVal = txOutValue $ txOutTxOut o
        oldA   = amountOf outVal apCoinA
        oldB   = amountOf outVal apCoinB
        newA   = oldA + apAmountA
        newB   = oldB + apAmountB
        delL   = calculateAdditionalLiquidity oldA oldB liquidity apAmountA apAmountB
        inVal  = valueOf apCoinA apAmountA <> valueOf apCoinB apAmountB
    when (delL <= 0) $ throwError "insufficient liquidity"
    logInfo @String $ printf "oldA = %d, oldB = %d, newA = %d, newB = %d, delL = %d" oldA oldB newA newB delL

    let usInst       = uniswapInstance us
        usScript     = uniswapScript us
        dat          = Pool lp $ liquidity + delL
        psC          = poolStateCoin us
        lC           = mkCoin (liquidityCurrency us) $ lpTicker lp
        psVal        = unitValue psC
        lVal         = valueOf lC delL
        val          = psVal <> valueOf apCoinA newA <> valueOf apCoinB newB
        redeemer     = Redeemer $ PlutusTx.toBuiltinData Add

        lookups  = Constraints.typedValidatorLookups usInst             <>
                   Constraints.otherScript usScript                     <>
                   Constraints.mintingPolicy (liquidityPolicy us)       <>
                   Constraints.ownPubKeyHash pkh                        <>
                   Constraints.unspentOutputs (Map.singleton oref o)

        tx       = Constraints.mustPayToTheScript dat val          <>
                   Constraints.mustMintValue lVal                  <>
                   Constraints.mustSpendScriptOutput oref redeemer

    logInfo @String $ printf "val = %s, inVal = %s" (show val) (show inVal)
    logInfo $ show lookups
    logInfo $ show tx

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx

    logInfo $ "added liquidity to pool: " ++ show lp


fromUsedDatum :: ReserveDatum -> PubKeyHash
fromUsedDatum (Used lp pkh _) = pkh
fromUsedDatum _               = traceError "not Used"

getNrReserveUtxos :: ReserveDatum -> Integer
getNrReserveUtxos (Used _ _ n) = n
getNrReserveUtxos (Unused _ n) = n

getNewNrReserveUtxos :: Integer -> Integer -> Integer -> Integer
getNewNrReserveUtxos used all oldNr
    | (used * 1000000) `divide` all > 700000 = oldNr + 1
    | (used * 1000000) `divide` all < 300000 = max 3 (oldNr - 1)
    | otherwise                               = oldNr



getMaybeReserveDatum :: Maybe Datum -> Maybe ReserveDatum
getMaybeReserveDatum (Just (Datum d)) = PlutusTx.fromBuiltinData d
getMaybeReserveDatum _                = traceError "no Datum"

outputStateUsedAndCorrectLp :: LiquidityPool -> ReserveDatum -> Bool
outputStateUsedAndCorrectLp _ (Unused _ _) = False
outputStateUsedAndCorrectLp lp (Used lp' _ _) = lp == lp' && True

outputStateUnusedAndCorrectLp :: LiquidityPool -> ReserveDatum -> Bool
outputStateUnusedAndCorrectLp lp (Unused lp' _) = lp == lp' && True
outputStateUnusedAndCorrectLp _ (Used _ _ _) = False

getPercentage :: (Amount A, Amount B) -> (Amount A, Amount B) -> (Integer, Integer)
getPercentage (totA, totB) (a,b)
    | (unAmount totA) == 0 = (0, (unAmount b * 1000000) `divide` (unAmount totB))
    | (unAmount totB) == 0 = ((unAmount a * 1000000) `divide` (unAmount totA), 0)
    | otherwise            = ((unAmount a * 1000000) `divide` (unAmount totA), (unAmount b * 1000000) `divide` (unAmount totB))

amountForSwapInput :: Integer -> (Amount A, Amount B) -> (Amount A, Amount B)
amountForSwapInput r (a,b)
    | unAmount a * r > unAmount b * 1000000 = (Amount (unAmount a - (unAmount b * 1000000) `divide` r), Amount 0)
    | otherwise                             = (Amount 0, Amount (unAmount b - (unAmount a * r) `divide` 1000000))

amountOutWithoutSwapOfA :: Integer -> (Amount A, Amount B) -> Amount A
amountOutWithoutSwapOfA r (a,b)
    | unAmount a * r > unAmount b * 1000000 = Amount ((unAmount b * 1000000) `divide` r)
    | otherwise                             = a        -- plus result of the Swap of amountB'!!

amountOutWithoutSwapOfB :: Integer -> (Amount A, Amount B) -> Amount B
amountOutWithoutSwapOfB r (a,b)
    | unAmount a * r > unAmount b * 1000000 = b        -- plus the result of the Swap of amountA'!!
    | otherwise                             = Amount ((unAmount a * r) `divide` 1000000)

pubKeyConstraints :: forall i o. [(PubKeyHash, Value)] -> [TxConstraints i o]
pubKeyConstraints [] = [] 
pubKeyConstraints pkhs = map (\val -> Constraints.mustPayToPubKey (fst val) (snd val)) pkhs 

scriptSpending :: forall i o. [TxOutRef] -> [TxConstraints i o]
scriptSpending [] = []
scriptSpending refs = map (\val -> Constraints.mustSpendScriptOutput val (Redeemer $ PlutusTx.toBuiltinData Include)) refs

unspentOutputsMaps :: [(TxOutRef, TxOutTx)] -> [(Map.Map TxOutRef TxOutTx)]
unspentOutputsMaps [] = []
unspentOutputsMaps txs = map (\tx -> (Map.singleton (fst tx) (snd tx))) txs

-- | Uses a liquidity pool two swap one sort of coins in the pool against the other.
swap :: forall w s. Uniswap -> SwapParams -> Contract w s Text ()
swap us SwapParams{..} = do
    let rsC    = reserveStateCoin us
        lp     = LiquidityPool {lpCoinA = spCoinA, lpCoinB = spCoinB} 
    (_, (oref, o, lp, liquidity)) <- findUniswapFactoryAndPool us spCoinA spCoinB
    reserveUtxos                  <- findReserveUtxos us rsC                                            -- [(TxOutRef, TxOutTx)]
    logInfo @String $ printf "nr. ReserveUtxos: %d" (length reserveUtxos)
    let outVal = txOutValue $ txOutTxOut o
        oldA   = amountOf outVal spCoinA
        oldB   = amountOf outVal spCoinB
        
        orefs                = map fst reserveUtxos
        os                   = map snd reserveUtxos
        orefsAndOs'          = zip orefs os
        dats                 = map (fromJust . getMaybeReserveDatum . txOutTxDatum) (map snd reserveUtxos)
        vals                 = map (txOutValue . txOutTxOut) (map snd reserveUtxos)
        datsAndVals          = zip dats vals
        allInputs            = zip orefsAndOs' datsAndVals                                               -- [(oref, o), (dat, val))]
        allUsedInputs        = filter (\(_, (dat, _)) -> outputStateUsedAndCorrectLp lp dat) allInputs                                                                                            -- [(Datum, Value)]
    when (length allUsedInputs == 0) $ throwError "no reservations made"
    let orefsAndOsUsed       = map fst allUsedInputs
        allUnusedInputs      = filter (\(_, (dat, _)) -> outputStateUnusedAndCorrectLp lp dat) allInputs            -- [(Datum, Value)]
        orefsAndOsUnused     = map fst allUnusedInputs 
        orefsAndOs           = orefsAndOsUsed ++ orefsAndOsUnused

        amtsA                = map (\val' -> amountOf val' spCoinA) (map snd (map snd allUsedInputs))
        amtsB                = map (\val' -> amountOf val' spCoinB) (map snd (map snd allUsedInputs))

        valuesOfReservations = zip amtsA amtsB                                                          -- [(Value, Value)]
        pkhsOfReservations   = [pkh | pkh <- map (fromUsedDatum . fst) $ map snd allUsedInputs]         -- [(PubKeyHash)]
        completeReservations = zip pkhsOfReservations valuesOfReservations                              -- [(PubKeyHash, (Amount A, Amount B)]
        amountA              = Amount (sum (map unAmount (map fst valuesOfReservations)))
        amountB              = Amount (sum (map unAmount (map snd valuesOfReservations)))
        ratio                = ((unAmount oldB) * 1000000) `divide` (unAmount oldA)
        (amountA', amountB') = amountForSwapInput ratio (amountA, amountB) -- both spAmountA and spAmountB can be positive, so first the contract needs to exchange the two coins with the exchange rate r (oldB/oldA) without using the swap utxo so that afterwards either amountA' or amountB' is == 0. for the logic see docs..

        oldNrReserveUtxos    = getNrReserveUtxos $ fst $ snd (head allInputs)
        newNrReserveUtxos    = getNewNrReserveUtxos (length allUsedInputs) (length allInputs) oldNrReserveUtxos 

    logInfo @String $ printf "InputAmount A: %d, InputAmount B: %d" amountA amountB
    logInfo @String $ printf "The ratio B to A is %d" ratio
    logInfo @String $ printf "Amount put into Swap: Amount A = %d, Amount B = %d" amountA' amountB'

    let percentagefromInputValues = map (getPercentage (amountA, amountB)) valuesOfReservations
        percentageForOutputValues = map Tuple.swap percentagefromInputValues -- these are the pubkeys and the percentages to make the payments out of potA and potB (the finalOutputValues)

    (newA, newB) <- if amountA' > 0 then do
        let outB = Amount $ findSwapA oldA oldB amountA'
        when (outB == 0) $ throwError "no payout.."
        return (oldA + amountA', oldB - outB)
          else if amountB' > 0 then do
            let outA = Amount $ findSwapB oldA oldB amountB'
            when (outA == 0) $ throwError "no payout"
            return (oldA - outA, oldB + amountB')
              else do return (oldA, oldB) -- in case amountA == amountB, that means that there is no swap happening

    let (potA, potB) = if amountA' > 0
        then ((amountOutWithoutSwapOfA ratio (amountA, amountB)), (amountOutWithoutSwapOfB ratio (amountA, amountB) + (oldB - newB)))
        else ((amountOutWithoutSwapOfA ratio (amountA, amountB) + (oldA - newA)), (amountOutWithoutSwapOfB ratio (amountA, amountB)))

        finalOutput = zip (map (* (unAmount potA)) (map fst percentageForOutputValues)) (map (* (unAmount potB)) (map snd percentageForOutputValues)) -- [(Integer, Integer)]
        finalOutputRounded = map (\(val1, val2) -> ((val1 - mod val1 1000000), (val2 - mod val2 1000000))) finalOutput
        finalOutputVal  = map (\(int1, int2) -> (valueOf spCoinA (Amount (int1 `divide` 1000000)), valueOf spCoinB (Amount (int2 `divide` 1000000)))) finalOutputRounded 
        finalOutputVal' = map (\val -> ((fst val) <> (snd val))) finalOutputVal -- combined values of A and B
        clientAmounts   = zip pkhsOfReservations finalOutputVal'
        
    logInfo @String $ printf "money for the B-payers: %d, money for the A-payers: %d" potA potB    

    pkh <- pubKeyHash <$> ownPubKey

    logInfo @String $ printf "amount for the B-payers: %d, amount for the A-payers: %d" potA potB    
    logInfo @String $ printf "oldA = %d, oldB = %d, old product = %d, newA = %d, newB = %d, new product = %d" oldA oldB (unAmount oldA * unAmount oldB) newA newB (unAmount newA * unAmount newB)

    pkh <- pubKeyHash <$> ownPubKey
    let usInst   = uniswapInstance us
        rsInst   = typedReserveValidator us
        val      = valueOf spCoinA newA <> valueOf spCoinB newB <> unitValue (poolStateCoin us)
        usScript = uniswapScript us
        rsScript = reserveValidator us
        
        reservePayments = take newNrReserveUtxos (repeat $ Constraints.mustPayToOtherScript (validatorHash $ reserveValidator us) (Datum $ PlutusTx.toBuiltinData (Unused lp newNrReserveUtxos)) (unitValue rsC))

-- mustConsume: all the ReserveUtxos
-- mustPayToOtherScript: all the Coin ReserveState
-- mustPayToPubKey: all the finalOutputValues-List (transform the integers into values with lpCoinaA and lpCoinB)
        lookups = Constraints.typedValidatorLookups usInst              <>
                  Constraints.otherScript usScript                      <>
                  Constraints.otherScript rsScript                      <>
                  Constraints.mintingPolicy (reserveLiquidityPolicy us) <>
                  Constraints.unspentOutputs (foldr (<>) (Map.singleton oref o) (unspentOutputsMaps orefsAndOs))

        tx      = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData Swap)                                    <>
                  mconcat (scriptSpending $ map fst orefsAndOsUsed)                                                                  <>
                  mconcat (scriptSpending $ map fst orefsAndOsUnused)                                                                <>
                  Constraints.mustPayToOtherScript (validatorHash usScript) (Datum $ PlutusTx.toBuiltinData (Pool lp liquidity)) val <>
                  mconcat reservePayments                                                                                            <>
                  Constraints.mustMintValue (valueOf rsC (Amount $ newNrReserveUtxos - oldNrReserveUtxos))                                    <>
                  mconcat (pubKeyConstraints clientAmounts)

    logInfo $ show tx
    ledgerTx <- submitTxConstraintsWith lookups tx
    logInfo $ show ledgerTx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo $ "swapped with: " ++ show lp



-- | Finds all liquidity pools and their liquidity belonging to the Uniswap instance.
-- This merely inspects the blockchain and does not issue any transactions.
pools :: forall w s. Uniswap -> Contract w s Text [((Coin A, Amount A), (Coin B, Amount B))]
pools us = do
    utxos <- utxoAt (uniswapAddress us)
    go $ snd <$> Map.toList utxos
  where
    go :: [TxOutTx] -> Contract w s Text [((Coin A, Amount A), (Coin B, Amount B))]
    go []       = return []
    go (o : os) = do
        let v = txOutValue $ txOutTxOut o
        if isUnity v c
            then do
                d <- getUniswapDatum o
                case d of
                    Factory _ -> go os
                    Pool lp _ -> do
                        let coinA = lpCoinA lp
                            coinB = lpCoinB lp
                            amtA  = amountOf v coinA
                            amtB  = amountOf v coinB
                            s     = ((coinA, amtA), (coinB, amtB))
                        logInfo $ "found pool: " ++ show s
                        ss <- go os
                        return $ s : ss
            else go os
      where
        c :: Coin PoolState
        c = poolStateCoin us



-- | Gets the caller's funds.
funds :: forall w s. Contract w s Text Value
funds = do
    pkh <- pubKeyHash <$> ownPubKey
    os  <- map snd . Map.toList <$> utxoAt (pubKeyHashAddress pkh)
    return $ mconcat [txOutValue $ txOutTxOut o | o <- os]

-- | Gets the ReserveContracts Funds
reserveFunds :: forall w s. Uniswap -> Contract w s Text Value
reserveFunds us = do  
    let addr = reserveAddress us
    os  <- map snd . Map.toList <$> utxoAt addr 
    return $ mconcat [txOutValue $ txOutTxOut o | o <- os]

correctLiquidityPool :: LiquidityPool -> ReserveDatum -> Bool
correctLiquidityPool lp (Unused lp' _) = lp == lp'
correctLiquidityPool _  _            = False

-- | creates a UtxO at the Reserve Contract with the amount to swap. to do so, takes first unreserved utxo at reserveAddress
reserve :: forall w s. Uniswap -> ReserveParams -> Contract w s Text ()
reserve us ReserveParams{..} = do
    let lp = LiquidityPool {lpCoinA = rsCoinA, lpCoinB = rsCoinB}

    (_, (oref1, o1, _, _)) <- findUniswapFactoryAndPool us rsCoinA rsCoinB
    pkh                   <- pubKeyHash <$> ownPubKey
    (oref2, o2)            <- findUnusedReserveUtxo us (reserveStateCoin us) $ correctLiquidityPool lp 

    let poolAmtA = amountOf (txOutValue $ txOutTxOut o1) rsCoinA
        poolAmtB = amountOf (txOutValue $ txOutTxOut o1) rsCoinB
        nrReserveTokens      = getNrReserveUtxos $ (fromJust . getMaybeReserveDatum . txOutTxDatum) o2
    when (((unAmount rsAmountA) >= (unAmount poolAmtA) `divide` nrReserveTokens) || ((unAmount rsAmountB) >= (unAmount poolAmtB) `divide` nrReserveTokens)) $ throwError "pleas lower reservation amount"
    let rsC   = reserveStateCoin us
        instR = typedReserveValidator us
 
        -- pay to reserve address the following values: rsAmountA rsCoinA, rsAmountB rsCoinB, the fee (hardcoded in my case), rsC 
        val                  = unitValue rsC <> lovelaceValueOf 1000000 <> valueOf (rsCoinA) (rsAmountA) <> valueOf (rsCoinB) (rsAmountB)

        lookups = Constraints.otherScript (Scripts.validatorScript instR) <>
                  Constraints.unspentOutputs (Map.singleton oref2 o2)
        tx      = Constraints.mustSpendScriptOutput oref2 (Redeemer $ PlutusTx.toBuiltinData Reserve) <>
                  Constraints.mustPayToOtherScript (validatorHash $ reserveValidator us) (Datum $ PlutusTx.toBuiltinData (Used lp pkh nrReserveTokens)) val 
  
    ledgerTx <- submitTxConstraintsWith @ReserveContract lookups tx
    logInfo @String $ "reservation completed"
 

ownInput :: ReserveDatum -> PubKeyHash -> Bool
ownInput d pkh = getPkh d == pkh 
    where
    getPkh :: ReserveDatum -> PubKeyHash
    getPkh (Used _ pkh _) = pkh
    getPkh (Unused _ _)   = traceError "no PubKeyHash"

correctPubKeyAndPool :: LiquidityPool -> PubKeyHash -> ReserveDatum -> Maybe PubKeyHash
correctPubKeyAndPool lp pkh (Used lp' pkh' _) = if pkh == pkh' && lp == lp' then Just pkh' else Nothing 
correctPubKeyAndPool _  _   _               = Nothing

-- find reserve UTxOs with ownPubkey and consume them, make a new reserve UtxO with datum Unused
retrieve :: forall w s. Uniswap -> RetrieveParams -> Contract w s Text ()
retrieve us RetrieveParams{..} = do
    let lp = LiquidityPool {lpCoinA = rtCoinA, lpCoinB = rtCoinB}
    pkh <- pubKeyHash <$> ownPubKey
    (oref, o, a) <- findUsedReserveUtxo us (reserveStateCoin us) $ correctPubKeyAndPool lp pkh    

    let instU = uniswapInstance us
        instR = typedReserveValidator us
        rsC   = reserveStateCoin us
        nrReserveTokens = getNrReserveUtxos $ (fromJust . getMaybeReserveDatum . txOutTxDatum) o
        lookups = Constraints.otherScript (Scripts.validatorScript instR) <>
                  Constraints.unspentOutputs (Map.singleton oref o)
        tx      = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toBuiltinData Retrieve) <> 
                  Constraints.mustPayToOtherScript (validatorHash $ reserveValidator us) (Datum $ PlutusTx.toBuiltinData (Unused lp nrReserveTokens)) (unitValue rsC)

    ledgerTx <- submitTxConstraintsWith @ReserveContract lookups tx

    logInfo @String $ "retrieving.."

getUniswapDatum :: TxOutTx -> Contract w s Text UniswapDatum
getUniswapDatum o = case txOutDatumHash $ txOutTxOut o of
        Nothing -> throwError "datumHash not found"
        Just h -> case Map.lookup h $ txData $ txOutTxTx o of
            Nothing -> throwError "datum not found"
            Just (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> throwError "datum has wrong type"
                Just d  -> return d

getReserveDatum :: TxOutTx -> Contract w s Text ReserveDatum
getReserveDatum o = case txOutDatumHash $ txOutTxOut o of
        Nothing -> throwError "datumHash not found"
        Just h -> case Map.lookup h $ txData $ txOutTxTx o of 
            Nothing -> throwError "datum not found"
            Just (Datum e) -> case PlutusTx.fromBuiltinData e of 
                Nothing -> throwError "datum has wrong type"
                Just d  -> return d

-- finds the UTxOs sitting in the Reserve Contract
findReserveUtxos :: forall a b w s. Uniswap -> Coin b -> Contract w s Text [(TxOutRef, TxOutTx)]
findReserveUtxos us c = do
    let addr = reserveAddress us
    utxos <- utxoAt addr
    return [ x | x@(_, o) <- Map.toList utxos, isUnity (txOutValue $ txOutTxOut o) c]

findUsedReserveUtxo :: forall a b w s. Uniswap -> Coin b -> (ReserveDatum -> Maybe a) -> Contract w s Text (TxOutRef, TxOutTx, a)
findUsedReserveUtxo us c f = do
    let addr = reserveAddress us
    logInfo @String $ printf "looking for Reserve instance at address %s containing coin %s " (show addr) (show c)
    utxos <- utxoAt addr
    go  [x | x@(_, o) <- Map.toList utxos, isUnity (txOutValue $ txOutTxOut o) c]
  where
    go [] = throwError "Reserve instance not found"
    go ((oref, o) : xs) = do
        d <- getReserveDatum o
        case f d of
            Nothing -> go xs
            Just a  -> do
                logInfo @String $ printf "found Reserve instance with datum: %s" (show d)
                return (oref, o, a)

findUnusedReserveUtxo :: forall a b w s. Uniswap -> Coin b -> (ReserveDatum -> Bool) -> Contract w s Text (TxOutRef, TxOutTx)
findUnusedReserveUtxo us c f = do
    let addr = reserveAddress us
    logInfo @String $ printf "looking for Reserve instance at address %s containing coin %s " (show addr) (show c)
    utxos <- utxoAt addr
    go  [x | x@(_, o) <- Map.toList utxos, isUnity (txOutValue $ txOutTxOut o) c]
  where
    go [] = throwError "Reserve instance not found"
    go ((oref, o) : xs) = do
        d <- getReserveDatum o
        case f d of
            False -> go xs
            True  -> do
                logInfo @String $ printf "found unused Reserve instance"
                return (oref, o)

findUniswapInstance :: forall a b w s. Uniswap -> Coin b -> (UniswapDatum -> Maybe a) -> Contract w s Text (TxOutRef, TxOutTx, a)
findUniswapInstance us c f = do
    let addr = uniswapAddress us
    logInfo @String $ printf "looking for Uniswap instance at address %s containing coin %s " (show addr) (show c)
    utxos <- utxoAt addr
    go  [x | x@(_, o) <- Map.toList utxos, isUnity (txOutValue $ txOutTxOut o) c]
  where
    go [] = throwError "Uniswap instance not found"
    go ((oref, o) : xs) = do
        d <- getUniswapDatum o
        case f d of
            Nothing -> go xs
            Just a  -> do
                logInfo @String $ printf "found Uniswap instance with datum: %s" (show d)
                return (oref, o, a)

findUniswapFactory :: forall w s. Uniswap -> Contract w s Text (TxOutRef, TxOutTx, [LiquidityPool])
findUniswapFactory us@Uniswap{..} = findUniswapInstance us usCoin $ \case
    Factory lps -> Just lps
    Pool _ _    -> Nothing

findUniswapPool :: forall w s. Uniswap -> LiquidityPool -> Contract w s Text (TxOutRef, TxOutTx, Amount Liquidity)
findUniswapPool us lp = findUniswapInstance us (poolStateCoin us) $ \case
        Pool lp' l
            | lp == lp' -> Just l
        _               -> Nothing

findUniswapFactoryAndPool :: forall w s.
                             Uniswap
                          -> Coin A
                          -> Coin B
                          -> Contract w s Text ( (TxOutRef, TxOutTx, [LiquidityPool])
                                               , (TxOutRef, TxOutTx, LiquidityPool, Amount Liquidity)
                                               )
findUniswapFactoryAndPool us coinA coinB = do
    (oref1, o1, lps) <- findUniswapFactory us
    case [ lp'
         | lp' <- lps
         , lp' == LiquidityPool coinA coinB
         ] of
        [lp] -> do
            (oref2, o2, a) <- findUniswapPool us lp
            return ( (oref1, o1, lps)
                   , (oref2, o2, lp, a)
                   )
        _    -> throwError "liquidity pool not found"

findSwapA :: Amount A -> Amount B -> Amount A -> Integer
findSwapA oldA oldB inA
    | ub' <= 1   = 0
    | otherwise  = go 1 ub'
  where
    cs :: Integer -> Bool
    cs outB = checkSwap oldA oldB (oldA + inA) (oldB - Amount outB)

    ub' :: Integer
    ub' = head $ dropWhile cs [2 ^ i | i <- [0 :: Int ..]]

    go :: Integer -> Integer -> Integer
    go lb ub
        | ub == (lb + 1) = lb
        | otherwise      =
      let
        m = div (ub + lb) 2
      in
        if cs m then go m ub else go lb m

findSwapB :: Amount A -> Amount B -> Amount B -> Integer
findSwapB oldA oldB inB = findSwapA (switch oldB) (switch oldA) (switch inB)
  where
    switch = Amount . unAmount

ownerEndpoint :: Contract (Last (Either Text Uniswap)) EmptySchema ContractError ()
ownerEndpoint = do
    e <- mapError absurd $ runError start
    void $ waitNSlots 1
    tell $ Last $ Just e

-- | Provides the following endpoints for users of a Uniswap instance:
--
--      [@create@]: Creates a liquidity pool for a pair of coins. The creator provides liquidity for both coins and gets liquidity tokens in return.
--      [@swap@]: Uses a liquidity pool two swap one sort of coins in the pool against the other.
--      [@close@]: Closes a liquidity pool by burning all remaining liquidity tokens in exchange for all liquidity remaining in the pool.
--      [@remove@]: Removes some liquidity from a liquidity pool in exchange for liquidity tokens.
--      [@add@]: Adds some liquidity to an existing liquidity pool in exchange for newly minted liquidity tokens.
--      [@pools@]: Finds all liquidity pools and their liquidity belonging to the Uniswap instance. This merely inspects the blockchain and does not issue any transactions.
--      [@funds@]: Gets the caller's funds. This merely inspects the blockchain and does not issue any transactions.
--      [@stop@]: Stops the contract.
--      [@reserve@]: creates a Reservation UtxO 
userEndpoints :: Uniswap -> Promise (Last (Either Text UserContractState)) UniswapUserSchema Void ()
userEndpoints us =
    stop
        `select`
    (void (f (Proxy @"create")       (const Created)   create                   `select`
           f (Proxy @"swap")         (const Swapped)   swap                     `select`
           f (Proxy @"close")        (const Closed)    close                    `select`
           f (Proxy @"remove")       (const Removed)   remove                   `select`
           f (Proxy @"add")          (const Added)     add                      `select`
           f (Proxy @"pools")        Pools             (\us' () -> pools us')   `select`
           f (Proxy @"funds")        Funds             (\_us () -> funds)       `select`
           f (Proxy @"reserveFunds") ReserveFunds      (\us' () -> reserveFunds us') `select`
           f (Proxy @"reserve")      (const Reserved)  reserve                  `select`
           f (Proxy @"retrieve")     (const Retrieved) retrieve)
     <> userEndpoints us)
  where
    f :: forall l a p.
         (HasEndpoint l p UniswapUserSchema, FromJSON p)
      => Proxy l
      -> (a -> UserContractState)
      -> (Uniswap -> p -> Contract (Last (Either Text UserContractState)) UniswapUserSchema Text a)
      -> Promise (Last (Either Text UserContractState)) UniswapUserSchema Void ()
    f _ g c = handleEndpoint @l $ \p -> do
        e <- either (pure . Left) (runError . c us) p
        tell $ Last $ Just $ case e of
            Left err -> Left err
            Right a  -> Right $ g a

    stop :: Promise (Last (Either Text UserContractState)) UniswapUserSchema Void ()
    stop = handleEndpoint @"stop" $ \e -> do
        tell $ Last $ Just $ case e of
            Left err -> Left err
            Right () -> Right Stopped
