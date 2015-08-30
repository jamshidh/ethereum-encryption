
module Blockchain.UDP (
  getServerPubKey,
  processDataStream,
  ndPacketToRLP,
  rlpToNDPacket,
  NodeDiscoveryPacket(..),
  Endpoint(..),
  Neighbor(..),
  NodeID(..)
  ) where

import Network.Socket

import Control.Exception
import Control.Monad.IO.Class
import qualified Crypto.Hash.SHA3 as SHA3
import Crypto.Types.PubKey.ECC
import Data.Binary
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BL
import Data.Maybe
import GHC.IO.IOMode
import qualified Network.Haskoin.Internals as H
import System.IO
--import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Blockchain.Data.RLP
import Blockchain.ExtendedECDSA
import Blockchain.ExtWord
import Blockchain.Format
import Blockchain.SHA

--import Debug.Trace

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

encrypt::H.PrvKey->Word256->H.SecretT IO ExtendedSignature
encrypt prvKey' theHash = do
  extSignMsg theHash prvKey'

data RawNodeDiscoveryPacket =
  RawNDPacket SHA ExtendedSignature Integer RLPObject deriving (Show)

data NodeDiscoveryPacket =
  Ping Integer Endpoint Endpoint Integer |
  Pong Endpoint Integer Integer |
  FindNode NodeID Integer |
  Neighbors [Neighbor] Integer deriving (Show,Read,Eq)

data Endpoint = Endpoint String Word16 Word16 deriving (Show,Read,Eq)
data Neighbor = Neighbor Endpoint NodeID deriving (Show,Read,Eq)



rlpToNDPacket::Word8->RLPObject->NodeDiscoveryPacket
rlpToNDPacket 0x1 (RLPArray [protocolVersion, RLPArray [ ipFrom, udpPortFrom, tcpPortFrom], RLPArray [ipTo, udpPortTo, tcpPortTo], expiration]) =
    Ping (rlpDecode protocolVersion) (Endpoint (rlpDecode ipFrom) (fromInteger $ rlpDecode udpPortFrom) (fromInteger $ rlpDecode tcpPortFrom))
                                     (Endpoint (rlpDecode ipTo) (fromInteger $ rlpDecode udpPortTo) (fromInteger $ rlpDecode tcpPortTo))
                                     (rlpDecode expiration)
rlpToNDPacket 0x2 (RLPArray [ RLPArray [ ipFrom, udpPortFrom, tcpPortFrom ], replyToken, expiration]) = Pong (Endpoint (rlpDecode ipFrom)
                                                                       (fromInteger $ rlpDecode udpPortFrom)
                                                                       (fromInteger $ rlpDecode tcpPortFrom))
                                                                       (rlpDecode replyToken)
                                                                       (rlpDecode expiration)
--rlpToNDPacket 0x3 (RLPArray [target, expiration]) = FindNode (rlpDecode target) (fromInteger $ rlpDecode expiration)
--rlpToNDPacket 0x4 (RLPArray [ip, port, id', expiration]) = Neighbors (rlpDecode ip) (fromInteger $ rlpDecode port) (rlpDecode id') (rlpDecode expiration)
rlpToNDPacket v x = error $ "Missing case in rlpToNDPacket: " ++ show v ++ ", " ++ show x

ndPacketToRLP::NodeDiscoveryPacket->(Word8, RLPObject)
ndPacketToRLP (Ping ver (Endpoint ipFrom udpPortFrom tcpPortFrom) (Endpoint ipTo udpPortTo tcpPortTo) expiration) =
  (1, RLPArray [rlpEncode ver,
                RLPArray [
                rlpEncode ipFrom,
                rlpEncode $ toInteger udpPortFrom,
                rlpEncode $ toInteger tcpPortFrom],
                RLPArray [
                rlpEncode ipTo,
                rlpEncode $ toInteger udpPortTo,
                rlpEncode $ toInteger tcpPortTo],
                rlpEncode expiration])
ndPacketToRLP (Pong (Endpoint ipFrom udpPortFrom tcpPortFrom) tok expiration) = (2, RLPArray [RLPArray [ rlpEncode ipFrom,
                                                                                                         rlpEncode $ toInteger udpPortFrom,
                                                                                                         rlpEncode $ toInteger tcpPortFrom],
                                                                                                         rlpEncode tok,
                                                                                                         rlpEncode expiration])
--ndPacketToRLP (FindNode target expiration) = (3, RLPArray [rlpEncode target, rlpEncode expiration])
--ndPacketToRLP (Neighbors ip port id' expiration) = (4, RLPArray [rlpEncode ip, rlpEncode $ toInteger port, rlpEncode id', rlpEncode expiration])

--showPoint::H.Point->String
--showPoint (H.Point x y) = "Point 0x" ++ showHex x "" ++ " 0x" ++ showHex y ""

{-
showPubKey::H.PubKey->String
showPubKey (H.PubKey point) =
  "Point 0x" ++ showHex x "" ++ " 0x" ++ showHex y ""
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
  
showPubKey (H.PubKeyU _) = error "Missing case in showPubKey: PubKeyU"
-}  

ndPacketToRLP _ = error "Unsupported case in call to ndPacketToRLP"


processDataStream'::[Word8]->IO H.PubKey
processDataStream'
  (_:_:_:_:_:_:_:_:_:_:_:_:_:_:_:_:
   _:_:_:_:_:_:_:_:_:_:_:_:_:_:_:_:
--   h1:h2:h3:h4:h5:h6:h7:h8:h9:h10:h11:h12:h13:h14:h15:h16:
--   h17:h18:h19:h20:h21:h22:h23:h24:h25:h26:h27:h28:h29:h30:h31:h32:
   r1:r2:r3:r4:r5:r6:r7:r8:r9:r10:r11:r12:r13:r14:r15:r16:
   r17:r18:r19:r20:r21:r22:r23:r24:r25:r26:r27:r28:r29:r30:r31:r32:
   s1:s2:s3:s4:s5:s6:s7:s8:s9:s10:s11:s12:s13:s14:s15:s16:
   s17:s18:s19:s20:s21:s22:s23:s24:s25:s26:s27:s28:s29:s30:s31:s32:
   v:
   theType:rest) = do
  let --theHash = bytesToWord256 [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
      --                          h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32]
      r = bytesToWord256 [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,
                          r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32]
      s = bytesToWord256 [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,
                          s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32]
      yIsOdd = v == 1 -- 0x1c
      signature = ExtendedSignature (H.Signature (fromIntegral r) (fromIntegral s)) yIsOdd
    
--  putStrLn $ show (pretty theHash) ++ ", " ++ show theType

  
  
  let (rlp, _) = rlpSplit rest

  let SHA messageHash = hash $ B.pack $ [theType] ++ B.unpack (rlpSerialize rlp)
      publicKey = getPubKeyFromSignature signature messageHash  

  return $ fromMaybe (error "malformed signature in call to processDataStream") $ publicKey

processDataStream' _ = error "processDataStream' called with too few bytes"


processDataStream::BL.ByteString->IO H.PubKey
{-processDataStream x = do
  putStrLn "got some data"
  let result = runGet get x
  print (result::RawNodeDiscoveryPacket) -}
processDataStream x = processDataStream' . BL.unpack $ x


newtype NodeID = NodeID B.ByteString deriving (Show, Read, Eq)

instance Format NodeID where
  format (NodeID x) = BC.unpack $ B16.encode x

{-
pubKeyToNodeID::H.PubKey->NodeID
pubKeyToNodeID (H.PubKey point) =
  NodeID $ BL.toStrict $ encode x `BL.append` encode y
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
pubKeyToNodeID (H.PubKeyU _) = error "Missing case in pubKeyToNodeId: PubKeyU"
-}

getServerPubKey::H.PrvKey->String->PortNumber->IO Point
getServerPubKey myPriv domain port = do

  --let theCurve = getCurveByName Crypto.Types.PubKey.ECC.SEC_p256k1

  --ep <- createEntropyPool

  --let g = cprgCreate ep::SystemRNG

  --let (prvKey', g') = generatePrivate g theCurve

  --let pubKey = calculatePublic theCurve prvKey

  --    Point x y = pubKey

  --print $ pointToBytes pubKey

  withSocketsDo $ bracket getSocket hClose (talk myPriv)
        where getSocket = do
                (serveraddr:_) <- getAddrInfo Nothing (Just domain) (Just $ show port)
                s <- socket (addrFamily serveraddr) Datagram defaultProtocol
                _ <- connect s (addrAddress serveraddr) >> return s
                socketToHandle s ReadWriteMode

              talk::H.PrvKey->Handle->IO Point
              talk prvKey' h = do
                let (theType, theRLP) = ndPacketToRLP $
                              Ping 4 (Endpoint "127.0.0.1" (fromIntegral $ port) 30303) (Endpoint "127.0.0.1" (fromIntegral $ port) 30303) 1451606400
--                              FindNode "qq" 1451606400
                    theData = B.unpack $ rlpSerialize theRLP
                    SHA theMsgHash = hash $ B.pack $ (theType:theData)

                ExtendedSignature signature yIsOdd <-
                  liftIO $ H.withSource H.devURandom $ encrypt prvKey' theMsgHash

                let v = if yIsOdd then 1 else 0 -- 0x1c else 0x1b
                    r = H.sigR signature
                    s = H.sigS signature
                    theSignature = word256ToBytes (fromIntegral r) ++ word256ToBytes (fromIntegral s) ++ [v]
                    theHash = B.unpack $ SHA3.hash 256 $ B.pack $ theSignature ++ [theType] ++ theData
                --putStrLn $ "my address is " ++ show (pretty $ prvKey2Address prvKey')
                --let nodeId = pubKeyToNodeID $ H.derivePubKey prvKey

--                putStrLn $ "r:       " ++ (show r)
  --              putStrLn $ "s:       " ++ (show s)
    --            putStrLn $ "v:       " ++ (show v)
      --          putStrLn $ "theHash: " ++ (show theHash)

                    
                B.hPut h $ B.pack $ theHash ++ theSignature ++ [theType] ++ theData
                --send s $ map w2c $ theHash ++ theSignature ++ theType ++ theData
                --recv s 1024 >>= \msg -> putStrLn $ "Received " ++ msg
                --B.hGet h 4 >>= \msg -> putStrLn $ "Received " ++ show msg
                pubKey <- BL.hGetContents h >>= processDataStream

                return $ hPubKeyToPubKey pubKey
