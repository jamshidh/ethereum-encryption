{-# LANGUAGE OverloadedStrings #-}

module RLPx (
  runEthCryptM
  ) where

import Control.Monad.Trans.State
import Crypto.Cipher.AES
import qualified Crypto.Hash.SHA3 as SHA3
import Crypto.PubKey.ECC.DH
import Crypto.Types.PubKey.ECC
import Data.Binary
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Network

import Blockchain.ExtWord

import qualified AESCTR as AES
import Frame
import Handshake

--import Debug.Trace

theCurve::Curve
theCurve = getCurveByName SEC_p256k1

intToBytes::Integer->[Word8]
intToBytes x = map (fromIntegral . (x `shiftR`)) [256-8, 256-16..0]

{-
showPoint::Point->String
showPoint (Point x y) =
  "Point " ++ showHex x "" ++ " " ++ showHex y ""
showPoint PointO = error "showPoint got value PointO, I don't know what to do here"

hShowPoint::H.Point->String
hShowPoint point =
  "Point " ++ showHex x "" ++ " " ++ showHex y ""
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
-}


bXor::B.ByteString->B.ByteString->B.ByteString
bXor x y | B.length x == B.length y = B.pack $ B.zipWith xor x y
bXor _ _ = error "bXor called with two ByteStrings of different length"

runEthCryptM::PrivateNumber->PublicPoint->EthCryptM a->IO a
runEthCryptM myPriv otherPubKey f = do
  h <- connectTo "127.0.0.1" $ PortNumber 30303


  let myNonce = B.pack $ word256ToBytes 20 --TODO- Important!  Don't hardcode this
  handshakeInitBytes <- getHandshakeBytes myPriv otherPubKey myNonce
      

  B.hPut h handshakeInitBytes

  handshakeReplyBytes <- B.hGet h 210
  let replyECEISMsg = decode $ BL.fromStrict handshakeReplyBytes

  let ackMsg = bytesToAckMsg $ B.unpack $ decryptECEIS myPriv replyECEISMsg

------------------------------

  let m_originated=False -- hardcoded for now, I can only connect as client
      add::B.ByteString->B.ByteString->B.ByteString
      add acc val | B.length acc ==32 && B.length val == 32 = SHA3.hash 256 $ val `B.append` acc
      add _ _ = error "add called with ByteString of length not 32"

      otherNonce=B.pack $ word256ToBytes $ ackNonce ackMsg

      SharedKey shared' = getShared theCurve myPriv (ackEphemeralPubKey ackMsg)
      shared = B.pack $ intToBytes shared'

      frameDecKey = myNonce `add` otherNonce `add` shared `add` shared
      macEncKey = frameDecKey `add` shared

      ingressCipher = if m_originated then handshakeInitBytes else handshakeReplyBytes
      egressCipher = if m_originated then handshakeReplyBytes else handshakeInitBytes
  let cState =
        EthCryptState {
          handle = h,
          encryptState = AES.AESCTRState (initAES frameDecKey) (aesIV_ $ B.replicate 16 0) 0,
          decryptState = AES.AESCTRState (initAES frameDecKey) (aesIV_ $ B.replicate 16 0) 0,
          egressMAC=SHA3.update (SHA3.init 256) $
                    (macEncKey `bXor` otherNonce) `B.append` egressCipher,
          egressKey=macEncKey,
          ingressMAC=SHA3.update (SHA3.init 256) $ 
                     (macEncKey `bXor` myNonce) `B.append` ingressCipher,
          ingressKey=macEncKey
          }

  (ret, _) <- flip runStateT cState f

  return ret
  
