import Network.Socket

import Control.Exception
import Control.Monad.IO.Class
import qualified Crypto.Hash.SHA3 as SHA3
import Crypto.PubKey.ECC.DH
import Crypto.Types.PubKey.ECC
import Crypto.Random
import Data.Binary
import Data.Binary.Get
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BLC
import Data.ByteString.Internal
import Data.Maybe
import Data.Word
import GHC.IO.IOMode
import qualified Network.Haskoin.Internals as H
import Numeric
import System.IO
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Blockchain.Data.Address
import Blockchain.Data.RLP
import Blockchain.ExtendedECDSA
import Blockchain.ExtWord
import Blockchain.Format
import Blockchain.SHA

import Debug.Trace

port = "30303"

integerToBytes::Integer->[Word8]
integerToBytes x = map (fromIntegral . (x `shiftR`)) [256-8, 256-16..0]

pointToBytes::Point->[Word8]
pointToBytes (Point x y) = integerToBytes x ++ integerToBytes y

--encrypt::PrvKey->Word256->ExtendedSignature
encrypt prvKey theHash = do
  extSignMsg theHash prvKey


prvKey::H.PrvKey
Just prvKey = H.makePrvKey 0xac3e8ce2ef31c3f45d5da860bcd9aee4b37a05c5a3ddee40dd061620c3dab380

data RawNodeDiscoveryPacket =
  RawNDPacket SHA ExtendedSignature Integer RLPObject deriving (Show)


{-
instance Binary ExtendedSignature where
  get = do
{-    v <- getWord8
    r <- getWord64be
    s <- getWord64be-}
    let r = 0; s = 0; v = 27
    return $ ExtendedSignature (Signature (fromIntegral r) (fromIntegral s)) (case v of 27 -> True; 28 -> False)
  put = error "undefined put ExtendedSignature"
  
instance Binary RLPObject where
  get = do
  put = error "undefined put RLPObject"
  
instance Binary RawNodeDiscoveryPacket where
  get = do
    theHash <- get
    theSignature <- get
    theType <- getWord64be
    theData <- get
    return $ RawNDPacket (trace "qq1" theHash) (trace "qq2" theSignature) (trace "qq3" (fromIntegral theType)) (trace "qq4" theData)
  put = error "undefined put RawNodeDiscoveryPacket"

-}


data NodeDiscoveryPacket =
  Ping Integer String Word16 Integer |
  Pong String Integer |
  FindNode String Integer |
  Neighbors String Word16 String Integer deriving (Show)


rlpToNDPacket::Word8->RLPObject->NodeDiscoveryPacket
rlpToNDPacket 0x1 (RLPArray [protocolVersion, ip, port, expiration]) =
    Ping (rlpDecode protocolVersion) (rlpDecode ip) (fromInteger $ rlpDecode port) (rlpDecode expiration)
rlpToNDPacket 0x2 (RLPArray [replyToken, expiration]) = Pong (rlpDecode replyToken) (rlpDecode expiration)
rlpToNDPacket 0x3 (RLPArray [target, expiration]) = FindNode (rlpDecode target) (fromInteger $ rlpDecode expiration)
rlpToNDPacket 0x4 (RLPArray [ip, port, id, expiration]) = Neighbors (rlpDecode ip) (fromInteger $ rlpDecode port) (rlpDecode id) (rlpDecode expiration)
rlpToNDPacket v x = error $ "Missing case in rlpToNDPacket: " ++ show v ++ ", " ++ show x

ndPacketToRLP::NodeDiscoveryPacket->(Word8, RLPObject)
ndPacketToRLP (Ping ver ip port exp) = (1, RLPArray [rlpEncode ver, rlpEncode ip, rlpEncode $ toInteger port, rlpEncode exp])
ndPacketToRLP (Pong tok exp) = (2, RLPArray [rlpEncode tok, rlpEncode exp])
ndPacketToRLP (FindNode target exp) = (3, RLPArray [rlpEncode target, rlpEncode exp])
ndPacketToRLP (Neighbors ip port id exp) = (4, RLPArray [rlpEncode ip, rlpEncode $ toInteger port, rlpEncode id, rlpEncode exp])

--showPoint::H.Point->String
--showPoint (H.Point x y) = "Point 0x" ++ showHex x "" ++ " 0x" ++ showHex y ""

showPubKey::H.PubKey->String
showPubKey (H.PubKey point) =
  "Point 0x" ++ showHex x "" ++ " 0x" ++ showHex y ""
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
    
showPubKey (H.PubKeyU _) = error "Missing case in showPubKey: PubKeyU"

processDataStream'::[Word8]->IO ()
processDataStream'
  (h1:h2:h3:h4:h5:h6:h7:h8:h9:h10:h11:h12:h13:h14:h15:h16:
   h17:h18:h19:h20:h21:h22:h23:h24:h25:h26:h27:h28:h29:h30:h31:h32:
   r1:r2:r3:r4:r5:r6:r7:r8:r9:r10:r11:r12:r13:r14:r15:r16:
   r17:r18:r19:r20:r21:r22:r23:r24:r25:r26:r27:r28:r29:r30:r31:r32:
   s1:s2:s3:s4:s5:s6:s7:s8:s9:s10:s11:s12:s13:s14:s15:s16:
   s17:s18:s19:s20:s21:s22:s23:s24:s25:s26:s27:s28:s29:s30:s31:s32:
   v:
   theType:rest) = do
  let theHash = bytesToWord256 [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
                                h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32]
      r = bytesToWord256 [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,
                          r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32]
      s = bytesToWord256 [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,
                          s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32]
      yIsOdd = v == 1 -- 0x1c
      signature = ExtendedSignature (H.Signature (fromIntegral r) (fromIntegral s)) yIsOdd
  
--  putStrLn $ show (pretty theHash) ++ ", " ++ show theType

  let (rlp, rest') = rlpSplit rest

  let SHA messageHash = hash $ B.pack $ [theType] ++ B.unpack (rlpSerialize rlp)
      publicKey = getPubKeyFromSignature signature messageHash  

  putStrLn $ showPubKey publicKey

--  print rlp

  print $ rlpToNDPacket theType rlp

--  processDataStream' rest'


processDataStream::BL.ByteString->IO ()
{-processDataStream x = do
  putStrLn "got some data"
  let result = runGet get x
  print (result::RawNodeDiscoveryPacket) -}
processDataStream x = processDataStream' . BL.unpack $ x


newtype NodeID = NodeID B.ByteString deriving (Show)

instance Format NodeID where
  format (NodeID x) = BC.unpack $ B16.encode x

pubKeyToNodeID::H.PubKey->NodeID
pubKeyToNodeID (H.PubKey point) =
  NodeID $ BL.toStrict $ encode x `BL.append` encode y
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
pubKeyToNodeID (H.PubKeyU _) = error "Missing case in pubKeyToNodeId: PubKeyU"


main::IO ()
main = do

  let theCurve = getCurveByName Crypto.Types.PubKey.ECC.SEC_p256k1

  ep <- createEntropyPool

  let g = cprgCreate ep::SystemRNG

  let (prvKey', g') = generatePrivate g theCurve

  --let pubKey = calculatePublic theCurve prvKey

  --    Point x y = pubKey

  --print $ pointToBytes pubKey

  withSocketsDo $ bracket getSocket hClose (talk prvKey)
        where getSocket = do
                (serveraddr:_) <- getAddrInfo Nothing (Just "127.0.0.1") (Just port)
                s <- socket (addrFamily serveraddr) Datagram defaultProtocol
                connect s (addrAddress serveraddr) >> return s
                socketToHandle s ReadWriteMode

              talk prvKey h = do
                let (theType, theRLP) = ndPacketToRLP $
                              Ping 3 "127.0.0.1" 4000 1451606400
--                              FindNode "qq" 1451606400
                    theData = B.unpack $ rlpSerialize theRLP
                    SHA theMsgHash = hash $ B.pack $ (theType:theData)

                ExtendedSignature signature yIsOdd <-
                  liftIO $ H.withSource H.devURandom $ encrypt prvKey theMsgHash

                let v = if yIsOdd then 1 else 0 -- 0x1c else 0x1b
                    r = H.sigR signature
                    s = H.sigS signature
                    theSignature = word256ToBytes (fromIntegral r) ++ word256ToBytes (fromIntegral s) ++ [v]
                    theHash = B.unpack $ SHA3.hash 256 $ B.pack $ theSignature ++ [theType] ++ theData
                putStrLn $ "my address is " ++ show (pretty $ prvKey2Address prvKey)
                let nodeId = pubKeyToNodeID $ H.derivePubKey prvKey
                B.hPut h $ B.pack $ theHash ++ theSignature ++ [theType] ++ theData
                --send s $ map w2c $ theHash ++ theSignature ++ theType ++ theData
                --recv s 1024 >>= \msg -> putStrLn $ "Received " ++ msg
                --B.hGet h 4 >>= \msg -> putStrLn $ "Received " ++ show msg
                BL.hGetContents h >>= processDataStream
