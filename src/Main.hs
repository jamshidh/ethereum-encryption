{-# LANGUAGE OverloadedStrings #-}

module Main (
  main
  ) where

import Control.Monad.IO.Class
import Crypto.PubKey.ECC.DH
import Crypto.Types.PubKey.ECC
import Crypto.Random
import qualified Data.ByteString as B
--import qualified Data.ByteString.Base16 as B16
--import qualified Data.ByteString.Char8 as BC
import Data.Maybe
import qualified Network.Haskoin.Internals as H
--import Numeric

import Blockchain.Format
import Blockchain.Data.RLP
import Blockchain.Data.Wire
import Blockchain.SHA (SHA(..))

import Frame
import UDP
import RLPx

--import Debug.Trace

theCurve::Curve
theCurve = getCurveByName SEC_p256k1

sendMsg::Message->EthCryptM ()
sendMsg msg = do
  let (pType, pData) = wireMessage2Obj msg
  encryptAndPutFrame $
    B.cons pType $ rlpSerialize pData

recvMsg::EthCryptM Message
recvMsg = do
  frameData <- getAndDecryptFrame

  let packetType = fromInteger $ rlpDecode $ rlpDeserialize $ B.take 1 frameData
      packetData = rlpDeserialize $ B.drop 1 frameData

  return $ obj2WireMessage packetType packetData

--I need to use two definitions of PubKey (internally they represent the same thing)
--The one in the Haskoin package allows me to recover signatures.
--The one in the crypto packages let me do AES encryption.
--At some point I have to convert from one PubKey to the other, this function
--lets me to that.
hPubKeyToPubKey::H.PubKey->Point
hPubKeyToPubKey (H.PubKey hPoint) =
  Point (fromIntegral x) (fromIntegral y)
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX hPoint
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY hPoint
hPubKeyToPubKey (H.PubKeyU _) = error "PubKeyU not supported in hPubKeyToPUbKey yet"


  
main::IO ()    
main = do
  entropyPool <- createEntropyPool
  let g = cprgCreate entropyPool :: SystemRNG
      (myPriv, _) = generatePrivate g theCurve

  otherPubKey <- fmap hPubKeyToPubKey $ getServerPubKey "127.0.0.1" 30303

  runEthCryptM myPriv otherPubKey $ do

    liftIO $ putStrLn "Connected"

    sendMsg Hello {
      version=3,
      clientId="dummyClient",
      capability=[ETH 60],
      port=30303,
      nodeId=0x1
      }
    liftIO . putStrLn . format =<< recvMsg
    sendMsg Ping
    liftIO . putStrLn . format =<< recvMsg
    sendMsg Pong
    liftIO . putStrLn . format =<< recvMsg
    sendMsg Status{
      protocolVersion=60,
      networkID="",
      totalDifficulty=131072,
      latestHash=SHA 0,
      genesisHash=SHA 0xfd4af92a79c7fc2fd8bf0d342f2e832e1d4f485c85b9152d2039e03bc604fdca
      }
    liftIO . putStrLn . format =<< recvMsg
    liftIO . putStrLn . format =<< recvMsg
    liftIO . putStrLn . format =<< recvMsg


  return ()
