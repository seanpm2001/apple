{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE TupleSections  #-}

module Asm.Aarch64.Byte ( assembleCtx, dbgFp ) where

import           Asm.Aarch64
import           Asm.M
import           Data.Bifunctor  (second)
import           Data.Bits       (Bits (..))
import qualified Data.ByteString as BS
import qualified Data.Map        as M
import           Data.Word       (Word8)
import           Foreign.Ptr     (FunPtr)
import           Hs.FFI
import           Sys.DL

hasMa :: [AArch64 reg freg a] -> Bool
hasMa = any g where g Bl{}=True; g _=False

prepAddrs :: [AArch64 reg freg a] -> IO (Maybe (Int, Int))
prepAddrs ss = if hasMa ss then Just <$> mem' else pure Nothing

assembleCtx :: (Int, Int) -> [AArch64 AReg FAReg a] -> IO (BS.ByteString, FunPtr b)
assembleCtx ctx isns = do
    let (sz, lbls) = mkIx 0 isns
    p <- if hasMa isns then allocNear (fst ctx) (fromIntegral sz) else allocExec (fromIntegral sz)
    let b = BS.pack.concat$asm 0 (pI p, Just ctx, lbls) isns
    (b,)<$>finish b p

dbgFp = fmap fst . allFp
allFp :: [AArch64 AReg FAReg a] -> IO ([BS.ByteString], FunPtr b)
allFp instrs = do
    let (sz, lbls) = mkIx 0 instrs
    (fn, p) <- do
        res <- prepAddrs instrs
        case res of
            Just (m, _) -> (res,) <$> allocNear m (fromIntegral sz)
            _           -> (res,) <$> allocExec (fromIntegral sz)
    let is = asm 0 (pI p, fn, lbls) instrs; b = BS.pack.concat$is; bs = BS.pack<$>is
    (bs,)<$>finish b p

mkIx :: Int -> [AArch64 AReg FAReg a] -> (Int, M.Map Label Int)
mkIx ix (Label _ l:asms) = second (M.insert l ix) $ mkIx ix asms
mkIx ix (_:asms)         = mkIx (ix+4) asms
mkIx ix []               = (ix, M.empty)

be :: Enum a => a -> Word8
be = fromIntegral.fromEnum

asm :: Int -> (Int, Maybe (Int, Int), M.Map Label Int) -> [AArch64 AReg FAReg a] -> [[Word8]]
asm _ _ [] = []
asm ix st (MovRC _ r i:asms) = [0b11010010, 0b100 `shiftL` 5 .|. fromIntegral (0b11111 .&. (i `shiftL` 11)), fromIntegral (0xf .&. (i `shiftL` 3)), ((fromIntegral (0x7 .&. i)) `shiftL` 5) .|. be r] : asm (ix+4) st asms
asm ix st (MovK _ r i s:asms) = [0b11110010, 0b1 `shiftL` 7 .|. (fromIntegral (s `div` 16)) `shiftL` 5 .|. fromIntegral (0b11111 .&. (i `shiftL` 11)), fromIntegral (0x7 .&. (i `shiftL` 3)), ((fromIntegral (0x7 .&. i)) `shiftL` 5) .|. be r] : asm (ix+4) st asms
asm ix st (FMovDR _ d r:asms) = [0b10011110, 0b11100110, be r `shiftR` 3, ((0x7 .&. be r) `shiftL` 5) .|. be d] : asm (ix+4) st asms
asm ix st (Fadd _ d0 d1 d2:asms) = [0b00011110, 0x1 `shiftL` 6 .|. 0x1 `shiftL` 5 .|. be d2, 0b001010 `shiftL` 2 .|. (be d1 `shiftR` 3), ((0x7 .&. be d1) `shiftL` 5) .|. be d0] : asm (ix+4) st asms
asm ix st (Ret{}:asms) = [0b11010110, 0b01011111, 0x0, 0x0] : asm (ix+4) st asms
