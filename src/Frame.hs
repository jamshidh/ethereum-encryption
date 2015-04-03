
module Frame (
  FrameHeader(..),
  bytesToFrameHeader,
  frameHeaderToBytes
  ) where

import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BC

import qualified AESCTR as AES

data FrameHeader =
  FrameHeader {
    frameSize::Int,
    headerHmac::B.ByteString
    } deriving (Show)

bytesToFrameHeader::AES.AESCTRState->B.ByteString->(AES.AESCTRState, FrameHeader)
bytesToFrameHeader state bytes | B.length bytes == 32 =
  if B.unpack (B.drop 3 first) == [0xc2, 0x80, 0x80, 0,0,0,0,0,0,0,0,0,0]
  then
    (state',
     FrameHeader {
        frameSize = 
           (fromIntegral $ first `B.index` 0 `shiftL` 16) +
           (fromIntegral $ first `B.index` 1 `shiftL` 8) +
           (fromIntegral $ first `B.index` 2),
        headerHmac = hmac'
        })
  else error $ "frame header in wrong format: " ++ BC.unpack (B16.encode bytes)
  where
    (encryptedFirst, hmac') = B.splitAt 16 bytes
    (state', first) = AES.decrypt state encryptedFirst
    
bytesToFrameHeader _ x = error $ "Missing case for bytesToFrameHeader: " ++ BC.unpack (B16.encode x)

frameHeaderToBytes::FrameHeader->B.ByteString
frameHeaderToBytes fh =
  B.pack [fromIntegral $ frameSize fh `shiftR` 16,
          fromIntegral $ frameSize fh `shiftR` 8,
          fromIntegral $ frameSize fh,
          0xc2,
          0x80,
          0x80,
          0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  `B.append` headerHmac fh
  
  
  
