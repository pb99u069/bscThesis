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

module Reserve.OnChain
    ( ReserveDatum (..)
    , ReserveRedeemer (..)
    , mkReserveValidator
    , reserveDatumValue
    ) where

import           Control.Monad.Freer.Extras as Extras
import           Data.Aeson                 (FromJSON, ToJSON, encode)
import           Data.Functor               (void)
import qualified Data.Map                   as Map
import           Data.Monoid                (Last (..))
import           Data.Text                  (Text, pack)
import           Data.Void                  (Void)
import           GHC.Generics               (Generic)
import           Ledger
import           Ledger.Ada                 as Ada
import           Ledger.Constraints         as Constraints
import qualified Ledger.Contexts            as Validation
import qualified Ledger.Scripts             as Scripts
import qualified Ledger.Typed.Scripts       as Scripts
import           Ledger.Value               (AssetClass (..), symbols)
import           Plutus.Contract            as Contract
import           Plutus.Contracts.Currency  as Currency
import           Plutus.Trace.Emulator      as Emulator
import           Plutus.V1.Ledger.Value     as CS
import qualified PlutusTx
import           PlutusTx.Prelude           hiding (Semigroup (..), unless)
import           Prelude                    (IO, Semigroup (..), Show (..),
                                             String)
import qualified Prelude
import           Swap.Pool                  (calculateAdditionalLiquidity,
                                             calculateInitialLiquidity,
                                             calculateRemoval, checkSwap,
                                             lpTicker)
import           Swap.Types
import           Wallet.Emulator.Wallet


{-# INLINABLE reserveDatumValue #-}
reserveDatumValue :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe ReserveDatum
reserveDatumValue o f = do
    dh      <- txOutDatum o
    Datum d <- f dh
    PlutusTx.fromBuiltinData d

{-# INLINABLE mkReserveValidator #-}
mkReserveValidator :: Coin U -> Coin ReserveState -> Coin PoolState -> ReserveDatum -> ReserveRedeemer -> ScriptContext -> Bool
mkReserveValidator u rs ps reserveDatum reserveRedeemer ctx =
    case reserveDatum of
        (Unused lp n) -> case reserveRedeemer of
            Reserve ->
                outputContainsFee &&
                outputHasToken &&
                traceIfFalse "LiquidityPool and Number of Reservations in Datum must not change" (lp == getLiquidityPool outputDatum && n == getNumberOfReserveOutputs outputDatum)
            Include ->
                poolStateCoinIncluded
            Destroy -> 
                uniswapIncluded &&
                outputStateUnused outputDatum
        (Used lp pkh n) -> case reserveRedeemer of
            Retrieve ->
                (Validation.txSignedBy info pkh) &&
                outputHasToken                   &&
                outputStateUnused outputDatum    &&                                                              -- OwnOutput must have ReserveDatum Unused
                traceIfFalse "LiquidityPool and Number of Reservations in Datum must not change" (lp == getLiquidityPool outputDatum && n == getNumberOfReserveOutputs outputDatum)
            Include ->
                poolStateCoinIncluded
    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        ownInput :: TxOut
        ownInput = case findOwnInput ctx of
            Just i  -> txInInfoResolved i
            Nothing -> traceError "reserve utxo missing"

        ownOutput :: TxOut
        ownOutput = case [ o | o <- getContinuingOutputs ctx ] of
            [o] -> o
            _   -> traceError "expected only one Reserve output"

        outputHasToken :: Bool
        outputHasToken = isUnity (txOutValue ownOutput) rs

        outputContainsFee :: Bool
        outputContainsFee =
            let
                inVal  = txOutValue ownInput
                outVal = txOutValue ownOutput
            in
                outVal `geq` (inVal <> Ada.lovelaceValueOf 2000)

        getLiquidityPool :: ReserveDatum -> LiquidityPool
        getLiquidityPool (Used lp _ _) = lp
        getLiquidityPool (Unused lp _)   = lp

        getNumberOfReserveOutputs :: ReserveDatum -> Integer
        getNumberOfReserveOutputs (Used _ _ n) = n
        getNumberOfReserveOutputs (Unused _ n) = n

        outputDatum :: ReserveDatum
        outputDatum = case (reserveDatumValue ownOutput (`findDatum` info)) of
            Just s  -> s
            Nothing -> traceError "expected a datum value"

        outputStateUnused :: ReserveDatum -> Bool
        outputStateUnused (Unused _ _) = True
        outputStateUnused (Used _ _ _) = False

        poolStateCoinIncluded :: Bool
        poolStateCoinIncluded = valueSpent info `geq` unitValue ps
        
        uniswapIncluded :: Bool
        uniswapIncluded = valueSpent info `geq` unitValue u
