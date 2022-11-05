-- https://defuse.ca/online-x86-assembler.htm
-- https://disasm.pro/
--
-- https://wiki.osdev.org/X86-64_Instruction_Encoding

{-# LANGUAGE TupleSections #-}

module Asm.X86.Byte ( aFp, assemble, assembleCtx, dbgFp ) where

import           Asm.X86
import           Data.Bifunctor   (first, second)
import           Data.Bits        (Bits, rotateR, shiftL, (.&.), (.|.))
import qualified Data.ByteString  as BS
import           Data.Int         (Int32, Int64, Int8)
import qualified Data.Map.Strict  as M
import           Data.Word
import           Foreign.Ptr      (FunPtr, IntPtr (..), Ptr, castFunPtrToPtr, ptrToIntPtr)
import           Foreign.Storable (Storable, sizeOf)
import           Hs.FFI
import           Sys.DL

pI :: Ptr a -> Int
pI = (\(IntPtr i) -> i) . ptrToIntPtr

hasMa :: [X86 reg freg a] -> Bool
hasMa = any g where
    g Call{} = True
    g _      = False

prepAddrs :: [X86 reg freg a] -> IO (Maybe (Int, Int))
prepAddrs ss = if hasMa ss then Just <$> mem' else pure Nothing

aFp = fmap (first BS.length) . allFp
dbgFp = fmap fst . allFp

assembleCtx :: (Int, Int) -> [X86 X86Reg FX86Reg a] -> IO (BS.ByteString, FunPtr b)
assembleCtx ctx isns = do
    let (sz, lbls) = mkIx 0 isns
    p <- if hasMa isns then allocNear (fst ctx) (fromIntegral sz) else allocExec (fromIntegral sz)
    let b = BS.pack$asm 0 (pI p, Just ctx, lbls) isns
    (b,)<$>finish b p

allFp :: [X86 X86Reg FX86Reg a] -> IO (BS.ByteString, FunPtr b)
allFp instrs = do
    let (sz, lbls) = mkIx 0 instrs
    (fn, p) <- do
        res <- prepAddrs instrs
        case res of
            Just (m, _) -> (res,) <$> allocNear m (fromIntegral sz)
            _           -> (res,) <$> allocExec (fromIntegral sz)
    let b = BS.pack$asm 0 (pI p, fn, lbls) instrs
    (b,)<$>finish b p

assemble :: [X86 X86Reg FX86Reg a] -> BS.ByteString
assemble instrs =
    let (_, lbls) = mkIx 0 instrs in
    BS.pack $ asm 0 (error "Internal error: no self", Nothing, lbls) instrs

data VEXM = F | F38 | F3A

data PP = S6 | F3 | F2

rrNoPre :: RMB reg
        => [Word8]
        -> reg -- ^ r/m
        -> reg -- ^ reg
        -> [Word8] -> [Word8]
rrNoPre opc r0 r1 =
    let (_, b0) = modRM r0
        (_, b1) = modRM r1
        modRMB = (0x3 `shiftL` 6) .|. (b1 `shiftL` 3) .|. b0
        in (\x -> opc++modRMB:x)

mkRR opc = mkAR opc 3

mkAR :: (RMB reg0, RMB reg1)
     => [Word8]
     -> Word8 -- ^ mod
     -> reg0 -- ^ r/m
     -> reg1 -- ^ reg
     -> [Word8] -> [Word8]
mkAR opc m r0 r1 =
    let (e0, b0) = modRM r0
        (e1, b1) = modRM r1
        prefix = 0x48 .|. (e1 `shiftL` 2) .|. e0
        modRMB = (m `shiftL` 6) .|. (b1 `shiftL` 3) .|. b0
        in (\x -> prefix:opc++modRMB:x)

-- movapd xmm9, xmm5 -> 66 44 0f 28 cd
-- movapd xmm1, xmm5 -> 66 0f 28 cd
--
-- addsd xmm8,xmm10 -> f2 45 0f 58 c2
extSse :: Word8 -> Word8 -> FX86Reg -> FX86Reg -> [Word8] -> [Word8]
extSse pre opc r0 r1 =
    let (e0, b0) = modRM r0
        (e1, b1) = modRM r1
        b = 0x40 .|. (e1 `shiftL` 2) .|. e0
        modRMB = (0x3 `shiftL` 6) .|. (b1 `shiftL` 3) .|. b0
        in (\x -> pre:b:0xf:opc:modRMB:x)

vexV4 :: FX86Reg -> Word8
vexV4 XMM0  = 0xf
vexV4 XMM1  = 0xe
vexV4 XMM2  = 0xd
vexV4 XMM3  = 0xc
vexV4 XMM4  = 0xb
vexV4 XMM5  = 0xa
vexV4 XMM6  = 0x9
vexV4 XMM7  = 0x8
vexV4 XMM8  = 0x7
vexV4 XMM9  = 0x6
vexV4 XMM10 = 0x5
vexV4 XMM11 = 0x4
vexV4 XMM12 = 0x3
vexV4 XMM13 = 0x2
vexV4 XMM14 = 0x1
vexV4 XMM15 = 0x0

bitC :: Word8 -> Word8
bitC 0x0 = 0x1
bitC 0x1 = 0x0

bitsm :: VEXM -> Word8
bitsm F   = 0x1
bitsm F38 = 0x2
bitsm F3A = 0x3

ppbits :: PP -> Word8
ppbits S6 = 0x1
ppbits F3 = 0x2
ppbits F2 = 0x3

mkVex :: Word8 -> PP -> FX86Reg -> FX86Reg -> FX86Reg -> ([Word8] -> [Word8])
mkVex opc pp r0 r1 r2 =
    \x -> 0xc5:b:opc:modRMB:x
    where b = (bitC e0 `shiftL` 7) .|. (vexV4 r1 `shiftL` 3) .|. ppbits pp
          (e0, b0) = modRM r0
          (_, b2) = modRM r2
          modRMB = (0x3 `shiftL` 6) .|. b0 `shiftL` 3 .|. b2

mkVex3 :: Word8 -> PP -> VEXM -> FX86Reg -> FX86Reg -> FX86Reg -> ([Word8] -> [Word8])
mkVex3 opc pp mm r0 r1 r2 =
    \x -> 0xc4:by0:by1:opc:modRMB:x
    where by0 = (bitC e0 `shiftL` 7) .|. (0x1 `shiftL` 6) .|. (bitC e2 `shiftL` 5) .|. bitsm mm
          by1 = 1 `shiftL` 7 .|. (vexV4 r1 `shiftL` 3) .|. ppbits pp
          (e0, b0) = modRM r0
          (e2, b2) = modRM r2
          modRMB = (0x3 `shiftL` 6) .|. b0 `shiftL` 3 .|. b2

mkIx :: Int -> [X86 X86Reg FX86Reg a] -> (Int, M.Map Label Int)
mkIx ix (Pop _ r:asms) | fits r               = mkIx (ix+1) asms
                       | otherwise            = mkIx (ix+2) asms
mkIx ix (Push _ r:asms) | fits r              = mkIx (ix+1) asms
                        | otherwise           = mkIx (ix+2) asms
mkIx ix (Label _ l:asms)                      = second (M.insert l ix) $ mkIx ix asms
mkIx ix (MovRR{}:asms)                        = mkIx (ix+3) asms
mkIx ix (Movapd _ r0 r1:asms) | fits r0 && fits r1 = mkIx (ix+4) asms
                              | otherwise = mkIx (ix+5) asms
mkIx ix (IAddRR{}:asms)                       = mkIx (ix+3) asms
mkIx ix (And{}:asms)                          = mkIx (ix+3) asms
mkIx ix (ISubRR{}:asms)                       = mkIx (ix+3) asms
mkIx ix (Addsd _ r0 r1:asms) | fits r0 && fits r1 = mkIx (ix+4) asms
                             | otherwise = mkIx (ix+5) asms
mkIx ix (Mulsd _ r0 r1:asms) | fits r0 && fits r1 = mkIx (ix+4) asms
                             | otherwise = mkIx (ix+5) asms
mkIx ix (Divsd _ r0 r1:asms) | fits r0 && fits r1 = mkIx (ix+4) asms
                             | otherwise = mkIx (ix+5) asms
mkIx ix (Vsubsd _ _ _ r:asms) | fits r        = mkIx (ix+4) asms
                              | otherwise     = mkIx (ix+5) asms
mkIx ix (Vaddsd _ _ _ r:asms) | fits r        = mkIx (ix+4) asms
                              | otherwise     = mkIx (ix+5) asms
mkIx ix (Vdivsd _ _ _ r:asms) | fits r        = mkIx (ix+4) asms
                              | otherwise     = mkIx (ix+5) asms
mkIx ix (Vmulsd _ _ _ r:asms) | fits r        = mkIx (ix+4) asms
                              | otherwise     = mkIx (ix+5) asms
mkIx ix (Vfmadd231sd{}:asms)                  = mkIx (ix+5) asms
mkIx ix (CmpRR{}:asms)                        = mkIx (ix+3) asms
mkIx ix (IMulRR{}:asms)                       = mkIx (ix+4) asms
mkIx ix (MovqXR{}:asms)                       = mkIx (ix+5) asms
mkIx ix ((CmpRI _ _ i):asms) | Just{} <- mi64i8 (fromIntegral i) = mkIx (ix+4) asms
mkIx ix ((IAddRI _ _ i):asms) | Just{} <- mi64i8 i = mkIx (ix+4) asms
mkIx ix ((ISubRI _ _ i):asms) | Just{} <- mi64i8 i = mkIx (ix+4) asms
                              | otherwise     = mkIx (ix+7) asms
mkIx ix (MovRI _ r i:asms) | Just{} <- mi64i32 i, i >= 0 && (r < R8 || r == Rax) = mkIx (ix+5) asms
mkIx ix (MovRI{}:asms)                        = mkIx (ix+10) asms
mkIx ix (Roundsd _ r0 r1 _:asms) | fits r0 && fits r1 = mkIx (ix+6) asms
mkIx ix (Roundsd{}:asms)                      = mkIx (ix+7) asms
mkIx ix (Cvttsd2si{}:asms)                    = mkIx (ix+5) asms
mkIx ix (Cvtsi2sd{}:asms)                     = mkIx (ix+5) asms
mkIx ix (Ret{}:asms)                          = mkIx (ix+1) asms
mkIx ix (Je{}:asms)                           = mkIx (ix+6) asms
mkIx ix (Jg{}:asms)                           = mkIx (ix+6) asms
mkIx ix (Jge{}:asms)                          = mkIx (ix+6) asms
mkIx ix (Jl{}:asms)                           = mkIx (ix+6) asms
mkIx ix (Jle{}:asms)                          = mkIx (ix+6) asms
mkIx ix (J{}:asms)                            = mkIx (ix+5) asms
mkIx ix (MovRA _ _ RC{}:asms)                 = mkIx (ix+4) asms
mkIx ix (MovqXA _ _ (R R13):asms)             = mkIx (ix+6) asms
mkIx ix (MovqXA _ r0 (R r1):asms) | fits r0 && fits r1 = mkIx (ix+4) asms
                                  | otherwise = mkIx (ix+5) asms
mkIx ix (MovqAX _ (RC Rsp _) r1:asms) | fits r1 = mkIx (ix+6) asms
mkIx ix (MovqAX _ (RC rb _) r:asms) | fits rb && fits r = mkIx (ix+5) asms
mkIx ix (MovqAX _ (RSD b _ i _) r:asms) | fits r && fits b && fits i = mkIx (ix+6) asms
mkIx ix (MovqAX _ RSD{} _:asms)               = mkIx (ix+7) asms
mkIx ix (MovqXA _ _ (RS R13 _ _):asms)        = mkIx (ix+7) asms
mkIx ix (MovqXA _ _ RSD{}:asms)               = mkIx (ix+7) asms
mkIx ix (MovqXA _ _ RS{}:asms)                = mkIx (ix+6) asms
mkIx ix (MovqXA _ r0 (RC Rsp _):asms) | fits r0 = mkIx (ix+6) asms
mkIx ix (MovqXA _ _ RC{}:asms)                = mkIx (ix+6) asms
mkIx ix (Fldl2e{}:asms)                       = mkIx (ix+2) asms
mkIx ix (Fldln2{}:asms)                       = mkIx (ix+2) asms
mkIx ix (Fld1{}:asms)                         = mkIx (ix+2) asms
mkIx ix (FldS{}:asms)                         = mkIx (ix+2) asms
mkIx ix (Fld _ (RC Rsp _):asms)               = mkIx (ix+4) asms
mkIx ix (Fyl2x{}:asms)                        = mkIx (ix+2) asms
mkIx ix (Fmulp{}:asms)                        = mkIx (ix+2) asms
mkIx ix (F2xm1{}:asms)                        = mkIx (ix+2) asms
mkIx ix (Fprem{}:asms)                        = mkIx (ix+2) asms
mkIx ix (Faddp{}:asms)                        = mkIx (ix+2) asms
mkIx ix (Fscale{}:asms)                       = mkIx (ix+2) asms
mkIx ix (Fxch{}:asms)                         = mkIx (ix+2) asms
mkIx ix (Fstp _ (RC Rsp _):asms)              = mkIx (ix+4) asms
mkIx ix (Sal{}:asms)                          = mkIx (ix+4) asms
mkIx ix (Sar{}:asms)                          = mkIx (ix+4) asms
mkIx ix (Call{}:asms)                         = mkIx (ix+5) asms
mkIx ix (MovAI32 _ (R Rsp)_:asms)             = mkIx (ix+8) asms
mkIx ix (MovAI32 _ R{} _:asms)                = mkIx (ix+7) asms
mkIx ix (MovAR _ (RC Rsp _) _:asms)           = mkIx (ix+5) asms
mkIx ix (MovAR _ RC{} _:asms)                 = mkIx (ix+4) asms
mkIx ix (MovRA _ _ RS{}:asms)                 = mkIx (ix+4) asms
mkIx ix (MovRA _ _ RSD{}:asms)                = mkIx (ix+5) asms
mkIx ix (MovAR _ RSD{} _:asms)                = mkIx (ix+5) asms
mkIx ix (MovAR _ RS{} _:asms)                 = mkIx (ix+4) asms
mkIx ix (MovAR _ R{} _:asms)                  = mkIx (ix+3) asms
mkIx ix (MovRA _ _ R{}:asms)                  = mkIx (ix+3) asms
mkIx ix (Sqrtsd{}:asms)                       = mkIx (ix+4) asms
mkIx ix (Not{}:asms)                          = mkIx (ix+3) asms
mkIx ix (Cmovnle{}:asms)                      = mkIx (ix+4) asms
mkIx ix []                                    = (ix, M.empty)
mkIx _ (instr:_) = error (show instr)

fits :: RMB reg => reg -> Bool
fits r = let (e, _) = modRM r in e == 0

asm :: Int -> (Int, Maybe (Int, Int), M.Map Label Int) -> [X86 X86Reg FX86Reg a] -> [Word8]
asm _ _ [] = []
asm ix st (Push _ r:asms) | fits r =
    let (_, b0) = modRM r
        isn = 0x50 .|. b0
    in isn:asm (ix+1) st asms
                          | otherwise =
    let (_, b0) = modRM r
        instr = [0x41, 0x50 .|. b0]
    in instr ++ asm (ix+2) st asms
asm ix st (Pop _ r:asms) | fits r =
    let (_, b0) = modRM r
        isn = 0x58 .|. b0
    in isn:asm (ix+1) st asms
                         | otherwise =
    let (_, b0) = modRM r
        instr = [0x41, 0x58 .|. b0]
    in instr ++ asm (ix+2) st asms
asm ix st (Label{}:asms) =
    asm ix st asms
asm ix st (MovRR _ r0 r1:asms) =
    mkRR [0x89] r0 r1 $ asm (ix+3) st asms
asm ix st (MovRA _ r0 (RC r1 i8):asms) =
    let (e0, b0) = modRM r0
        (e1, b1) = modRM r1
        pref = 0x48 .|. (e0 `shiftL` 2) .|. e1
        modB = 0x1 `shiftL` 6 .|. (b0 `shiftL` 3) .|. b1
        opc=0x8b
        instr = pref:opc:modB:le i8
    in (instr++) $ asm (ix+4) st asms
asm ix st (MovqXA _ r0 (RC r1@Rsp i8):asms) | fits r0 =
    let (_, b0) = modRM r0
        (_, b1) = modRM r1
        modB = 0x1 `shiftL` 6 .|. b0 `shiftL` 3 .|. 0x4
        sib = b1 `shiftL` 3 .|. b1
        instr = 0xf3:0xf:0x7e:modB:sib:le i8
    in (instr++) $ asm (ix+6) st asms
asm ix st (MovqXA _ r0 (R r1):asms) | fits r0 && fits r1 =
    let (_, b0) = modRM r0
        (_, b1) = modRM r1
        modB = b0 `shiftL` 3 .|. b1
        instr = [0xf3, 0x0f, 0x7e, modB]
    in instr ++ asm (ix+4) st asms
-- https://stackoverflow.com/questions/52522544/rbp-not-allowed-as-sib-base
asm ix st (MovqXA l r0 (R R13):asms) = asm ix st (MovqXA l r0 (RC R13 0):asms)
asm ix st (MovqXA _ r0 (RC r1 i8):asms) =
      let (e0, b0) = modRM r0
          (e1, b1) = modRM r1
          modB = 0x1 `shiftL` 6 .|. b0 `shiftL` 3 .|. b1
          pre = 0x48 .|. e0 `shiftL` 2 .|. e1
          instr = 0x66:pre:0xf:0x6e:modB:le i8
      in instr ++ asm (ix+6) st asms
asm ix st (MovqXA _ r0 (R r1):asms) =
      let (e0, b0) = modRM r0
          (e1, b1) = modRM r1
          modB = b0 `shiftL` 3 .|. b1
          pre = 0x48 .|. e0 `shiftL` 2 .|. e1
          instr = [0x66, pre, 0xf, 0x6e, modB]
      in instr ++ asm (ix+5) st asms
-- https://stackoverflow.com/questions/52522544/rbp-not-allowed-as-sib-base
asm ix st (MovqAX _ (RC r0@Rsp i8) r1:asms) | fits r1 =
    let (0, b0) = modRM r0
        (_, b1) = modRM r1
        modB = 0x1 `shiftL` 6 .|. b1 `shiftL` 3 .|. 0x4
        sib = b0 `shiftL` 3 .|. b0
        instr = 0x66:0x0f:0xd6:modB:sib:le i8
    in instr++asm (ix+6) st asms
asm ix st (MovqAX _ (RC rb i8) r:asms) | fits rb && fits r =
    let (_, bb) = modRM rb
        (_, b) = modRM r
        modB = 0x1 `shiftL` 6 .|. b `shiftL` 3 .|. bb
        isn = 0x66:0x0f:0xd6:modB:le i8
    in isn ++ asm (ix+5) st asms
asm ix st (MovqAX _ (RSD rb s ri d) r:asms) | fits r && fits rb && fits ri =
    let (_, b) = modRM r; (_, bi) = modRM ri; (_, bb) = modRM rb
        modB = 0x1 `shiftL` 6 .|. b `shiftL` 3 .|. 0x4
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        instr = 0x66:0x0f:0xd6:modB:sib:le d
    in instr++asm (ix+6) st asms
asm ix st (MovqAX _ (RSD rb s ri d) r:asms) =
    let (e, b) = modRM r; (eb, bb) = modRM rb; (ei, bi) = modRM ri
        modB = 0x1 `shiftL` 6 .|. b `shiftL` 3 .|. 0x4
        rex = 0x48 .|. e `shiftL` 2 .|. ei `shiftL` 1 .|. eb
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        instr = 0x66:rex:0x0f:0x7e:modB:sib:le d
    in instr++asm (ix+7) st asms
asm ix st (MovqXA l r (RS R13 s ri):asms) = asm ix st (MovqXA l r (RSD R13 s ri 0):asms)
asm ix st (MovqXA _ r (RS rb s ri):asms) =
    let (e, b) = modRM r; (eb, bb) = modRM rb; (ei, bi) = modRM ri
        modB = b `shiftL` 3 .|. 4
        rex = 0x48 .|. e `shiftL` 2 .|. ei `shiftL` 1 .|. eb
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        instr = [0x66,rex,0x0f,0x6e,modB,sib]
    in instr++asm (ix+6) st asms
asm ix st (MovqXA _ r (RSD rb s ri d):asms) =
    let (e, b) = modRM r; (eb, bb) = modRM rb; (ei, bi) = modRM ri
        modB = 1 `shiftL` 6 .|. b `shiftL` 3 .|. 4
        rex = 0x48 .|. e `shiftL` 2 .|. ei `shiftL` 1 .|. eb
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        instr = 0x66:rex:0x0f:0x6e:modB:sib:le d
    in instr ++ asm (ix+7) st asms
asm ix st (Movapd _ r0 r1:asms) | fits r0 && fits r1 =
    rrNoPre [0x66,0x0f,0x28] r1 r0 $ asm (ix+4) st asms
                                | otherwise =
    extSse 0x66 0x28 r1 r0 $ asm (ix+5) st asms
asm ix st (IAddRR _ r0 r1:asms) =
    mkRR [0x01] r0 r1 $ asm (ix+3) st asms
asm ix st (And _ r0 r1:asms) =
    mkRR [0x21] r0 r1 $ asm (ix+3) st asms
asm ix st (ISubRR _ r0 r1:asms) =
    mkRR [0x29] r0 r1 $ asm (ix+3) st asms
asm ix st (Addsd _ r0 r1:asms) | fits r0 && fits r1 =
    rrNoPre [0xf2,0x0f,0x58] r1 r0 $ asm (ix+4) st asms -- idk why swapped for mulsd &c.
                               | otherwise =
    extSse 0xf2 0x58 r1 r0 $ asm (ix+5) st asms
asm ix st (Mulsd _ r0 r1:asms) | fits r0 && fits r1 =
    rrNoPre [0xf2,0x0f,0x59] r1 r0 $ asm (ix+4) st asms
                               | otherwise =
    extSse 0xf2 0x59 r1 r0 $ asm (ix+5) st asms
asm ix st (Divsd _ r0 r1:asms) | fits r0 && fits r1 =
    rrNoPre [0xf2,0x0f,0x5e] r1 r0 $ asm (ix+4) st asms
                               | otherwise =
    extSse 0xf2 0x5e r1 r0 $ asm (ix+5) st asms
asm ix st (Vsubsd _ r0 r1 r2:asms) | fits r2 =
    mkVex 0x5c F2 r0 r1 r2 $ asm (ix+4) st asms
                                   | otherwise =
    mkVex3 0x5c F2 F r0 r1 r2 $ asm (ix+5) st asms
asm ix st (Vaddsd _ r0 r1 r2:asms) | fits r2 =
    mkVex 0x58 F2 r0 r1 r2 $ asm (ix+4) st asms
                                   | otherwise =
    mkVex3 0x58 F2 F r0 r1 r2 $ asm (ix+5) st asms
asm ix st (Vdivsd _ r0 r1 r2:asms) | fits r2 =
    mkVex 0x5e F2 r0 r1 r2 $ asm (ix+4) st asms
                                   | otherwise =
    mkVex3 0x5e F2 F r0 r1 r2 $ asm (ix+5) st asms
asm ix st (Vmulsd _ r0 r1 r2:asms) | fits r2 =
    mkVex 0x59 F2 r0 r1 r2 $ asm (ix+4) st asms
                                   | otherwise =
    mkVex3 0x59 F2 F r0 r1 r2 $ asm (ix+5) st asms
asm ix st (Vfmadd231sd _ r0 r1 r2:asms) =
    mkVex3 0xb9 S6 F38 r0 r1 r2 $ asm (ix+5) st asms
asm ix st (Roundsd _ r0 r1 i:asms) | fits r0 && fits r1 =
    rrNoPre [0x66,0x0f,0x3a,0x0b] r1 r0 . (le (roundMode i) ++) $ asm (ix+6) st asms
asm ix st (Roundsd _ r0 r1 i:asms) =
    (0x66:) . mkAR [0xf,0x3a,0xb] 0 r1 r0 . (le (roundMode i) ++) $ asm (ix+7) st asms
asm ix st (Cvttsd2si _ r0 r1:asms) =
    (0xf2:) . mkRR [0x0f,0x2c] r1 r0 $ asm (ix+5) st asms
asm ix st (Cvtsi2sd _ fr r:asms) =
    (0xf2:) . mkRR [0x0f,0x2a] r fr $ asm (ix+5) st asms
asm ix st (Sqrtsd _ r0 r1:asms) =
    rrNoPre [0xf2,0x0f,0x51] r1 r0 $ asm (ix+4) st asms
asm ix st (CmpRR _ r0 r1:asms) =
    mkRR [0x39] r0 r1 $ asm (ix+3) st asms
asm ix st (MovqXR _ fr r:asms) =
    (0x66:) . mkRR [0x0f,0x6e] r fr $ asm (ix+5) st asms
asm ix st (IMulRR _ r0 r1:asms) =
    -- flip r0,r1 as instr. uses them differently from sub, etc.
    mkRR [0x0f, 0xaf] r1 r0 $ asm (ix+4) st asms
asm ix st (CmpRI _ r i:asms) | Just i8 <- mi64i8 (fromIntegral i) =
    let (e, b) = modRM r
        prefix = 0x48 .|. e
        modRMB = (0x3 `shiftL` 6) .|. (0o7 `shiftL` 3) .|. b
    in (prefix:0x83:modRMB:le i8) ++ asm (ix+4) st asms
asm ix st (IAddRI _ r i:asms) | Just i8 <- mi64i8 i =
    let (e, b) = modRM r
        prefix = 0x48 .|. e
        modRMB = (0x3 `shiftL` 6) .|. b -- /0
    in (prefix:0x83:modRMB:le i8) ++ asm (ix+4) st asms
asm ix st (ISubRI _ r i:asms) | Just i8 <- mi64i8 i =
    let (e, b) = modRM r
        prefix = 0x48 .|. e
        modRMB = (0x3 `shiftL` 6) .|. (0x5 `shiftL` 3) .|. b
    in (prefix:0x83:modRMB:le i8) ++ asm (ix+4) st asms
asm ix st (ISubRI _ r i:asms) | Just i32 <- mi64i32 i =
    let (e, b) = modRM r
        prefix = 0x48 .|. e
        modRMB = (0x3 `shiftL` 6) .|. (0x5 `shiftL` 3) .|. b
    in (prefix:0x81:modRMB:le i32) ++ asm (ix+7) st asms
                           | otherwise = error "Not implemented yet: handling 64-bit immediates"
-- TODO: r32<-i32 like nasm does (note r32<-i32 (zero-extended) vs.
-- sign-extended
-- https://stackoverflow.com/questions/40315803/difference-between-movq-and-movabsq-in-x86-64
asm ix st (MovRI _ r i:asms) | Just i32 <- mi64i32 i, i >= 0 && fits r =
    let (_, b) = modRM r
        opc = 0xb8 .|. b
    in (opc:cd i32) ++ asm (ix+5) st asms
    -- TODO: 0xc7 for case i<0
asm ix st (MovRI _ r i:asms) =
    let (e, b) = modRM r
        pre = (0x48 .|. e:) . (0xB8 .|. b:)
    in pre (le i) ++ asm (ix+10) st asms
asm ix st (Ret{}:asms) =
    0xc3:asm (ix+1) st asms
asm ix st (Je _ l:asms) =
    let lIx = get l st
        instr = let offs = lIx-ix-6 in 0x0f:0x84:cd (fromIntegral offs :: Int32)
    in (instr ++) $ asm (ix+6) st asms
asm ix st (Jg _ l:asms) =
    let lIx = get l st
        instr = let offs = lIx-ix-6 in 0x0f:0x8f:cd (fromIntegral offs :: Int32)
    in (instr ++) $ asm (ix+6) st asms
asm ix st (Jge _ l:asms) =
    let lIx = get l st
        instr = let offs = lIx-ix-6 in 0x0f:0x8d:cd (fromIntegral offs :: Int32)
    in (instr ++) $ asm (ix+6) st asms
asm ix st (Jl _ l:asms) =
    let lIx = get l st
        instr = let offs = lIx-ix-6 in 0x0f:0x8c:cd (fromIntegral offs :: Int32)
    in (instr ++) $ asm (ix+6) st asms
asm ix st (Jle _ l:asms) =
    let lIx = get l st
        instr = let offs = lIx-ix-6 in 0x0f:0x8e:cd (fromIntegral offs :: Int32)
    in (instr ++) $ asm (ix+6) st asms
asm ix st (J _ l:asms) =
    let lIx = get l st
        instr = let offs = lIx-ix-5 in 0xe9:cd (fromIntegral offs :: Int32)
    in (instr ++) $ asm (ix+5) st asms
asm ix st (Fmulp{}:asms) =
    (0xde:) . (0xc9:) $ asm (ix+2) st asms
asm ix st (F2xm1{}:asms) =
    (0xd9:) . (0xf0:) $ asm (ix+2) st asms
asm ix st (Fldl2e{}:asms) =
    (0xd9:) . (0xea:) $ asm (ix+2) st asms
asm ix st (Fldln2{}:asms) =
    (0xd9:) . (0xed:) $ asm (ix+2) st asms
asm ix st (Fld1{}:asms) =
    (0xd9:) . (0xe8:) $ asm (ix+2) st asms
asm ix st (FldS _ (ST i):asms) =
    let isn = [0xd9, 0xc0+fromIntegral i] in isn ++ asm (ix+2) st asms
asm ix st (Fprem{}:asms) =
    (0xd9:) . (0xf8:) $ asm (ix+2) st asms
asm ix st (Faddp{}:asms) =
    (0xde:) . (0xc1:) $ asm (ix+2) st asms
asm ix st (Fscale{}:asms) =
    (0xd9:) . (0xfd:) $ asm (ix+2) st asms
asm ix st (Fxch _ (ST i):asms) =
    let isn = [0xd9, 0xc9+fromIntegral i] in isn ++ asm (ix+2) st asms
asm ix st (Fyl2x{}:asms) =
    (0xd9:) . (0xf1:) $ asm (ix+2) st asms
asm ix st (Fld _ (RC r@Rsp i8):asms) =
    let (_, b) = modRM r
        modB = 0x1 `shiftL` 6 .|. 0x4
        sib = b `shiftL` 3 .|. b
        instr = 0xdd:modB:sib:le i8
    in instr ++ asm (ix+4) st asms
asm ix st (Fstp _ (RC r@Rsp i8):asms) =
    let (_, b) = modRM r
        modB = 0x1 `shiftL` 6 .|. 0x3 `shiftL` 3 .|. 0x4
        sib = b `shiftL` 3 .|. b
        instr = 0xdd:modB:sib:le i8
    in instr ++ asm (ix+4) st asms
asm ix st (Sal _ r i:asms) =
    let (e, b) = modRM r
        modRMB = (0x3 `shiftL` 6) .|. (0x4 `shiftL` 3) .|. b
        pre = 0x48 .|. e
        instr = pre:0xc1:modRMB:le i
    in instr ++ asm (ix+4) st asms
asm ix st (Sar _ r i:asms) =
    let (e, b) = modRM r
        modRMB = (0x3 `shiftL` 6) .|. (0x7 `shiftL` 3) .|. b
        pre = 0x48 .|. e
        instr = pre:0xc1:modRMB:le i
    in instr ++ asm (ix+4) st asms
asm ix st (MovAI32 _ (R Rsp) i32:asms) =
    let (0, b) = modRM Rsp
        modB = 0x4
        sib = b `shiftL` 3 .|. b
        instr = 0x48:0xc7:modB:sib:le i32
    in instr ++ asm (ix+8) st asms
asm ix st (MovAI32 _ (R r) i32:asms) =
    let (e, b) = modRM r
        modRMB = b
        pre = 0x48 .|. e
        instr = pre:0xc7:modRMB:le i32
    in instr ++ asm (ix+7) st asms
asm ix st (MovAR _ (RC Rsp i8) r:asms) =
    let (e, b) = modRM r
        (0, bi) = modRM Rsp
        pre = 0x48 .|. e `shiftL` 3
        modB = 0x1 `shiftL` 6 .|. b `shiftL` 3 .|. 0x4
        sib = bi `shiftL` 3 .|. bi
        instr = pre:0x89:modB:sib:le i8
    in instr ++ asm (ix+5) st asms
asm ix st (MovAR _ (RC ar i8) r:asms) =
    mkAR [0x89] 1 ar r $ le i8 ++ asm (ix+4) st asms
asm ix st (MovRA _ r (RS b s i):asms) =
    let (e0, b0) = modRM r
        (eb, bb) = modRM b
        (ei, bi) = modRM i
        pre = 0x48 .|. e0 `shiftL` 2 .|. ei `shiftL` 1 .|. eb
        modB = b0 `shiftL` 3 .|. 4
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        instr = [pre,0x8b,modB,sib]
    in instr ++ asm (ix+4) st asms
asm ix st (MovAR _ (RSD b s i i8) r:asms) =
    let (eb, bb) = modRM b
        (ei, bi) = modRM i
        (e0, b0) = modRM r
        pre = 0x48 .|. e0 `shiftL` 2 .|. ei `shiftL` 1 .|. eb
        modRMB = 1 `shiftL` 6 .|. b0 `shiftL` 3 .|. 4
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        instr = pre:0x89:modRMB:sib:le i8
    in instr ++ asm (ix+5) st asms
asm ix st (MovRA _ r (RSD b s i i8):asms) =
    let (eb, bb) = modRM b
        (ei, bi) = modRM i
        (e0, b0) = modRM r
        pre = 0x48 .|. e0 `shiftL` 2 .|. ei `shiftL` 1 .|. eb
        modRMB = 1 `shiftL` 6 .|. b0 `shiftL` 3 .|. 4
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        instr = pre:0x8b:modRMB:sib:le i8
    in instr ++ asm (ix+5) st asms
asm ix st (MovAR _ (R ar) r:asms) =
    mkAR [0x89] 0 ar r $ asm (ix+3) st asms
asm ix st (MovRA _ r (R ar):asms) =
    mkAR [0x8b] 0 ar r $ asm (ix+3) st asms
asm ix st (Cmovnle _ r0 r1:asms) =
    mkRR [0xf,0x4f] r1 r0 $ asm (ix+4) st asms
asm ix st (MovAR _ (RS rb s ri) r:asms) =
    let (eb, bb) = modRM rb
        (ei, bi) = modRM ri
        (e, b) = modRM r
        modRMB = b `shiftL` 3 .|. 4
        sib = encS s `shiftL` 6 .|. bi `shiftL` 3 .|. bb
        pre = 0x48 .|. e `shiftL` 2 .|. ei `shiftL` 1 .|. eb
    in pre:0x89:modRMB:sib:asm (ix+4) st asms
asm ix st (Not _ r:asms) =
    let (e, b) = modRM r
        pre = 0x48 .|. e
        opc = 0xf7
        modB = 3 `shiftL` 6 .|. 2 `shiftL` 3 .|. b
    in (pre:).(opc:).(modB:) $ asm(ix+3) st asms
asm ix st@(self, Just (m, _), _) (Call _ Malloc:asms) | Just i32 <- mi32 (m-(self+ix+5)) =
    let instr = 0xe8:le i32
    in instr ++ asm (ix+5) st asms
asm ix st@(self, Just (_, f), _) (Call _ Free:asms) | Just i32 <- mi32 (f-(self+ix+5)) =
    let instr = 0xe8:le i32
    in instr ++ asm (ix+5) st asms
asm _ (_, Nothing, _) (Call{}:_) = error "Internal error? no dynlibs"
asm _ _ (instr:_) = error (show instr)

encS :: Scale -> Word8
encS One   = 0
encS Two   = 1
encS Four  = 2
encS Eight = 3

get :: Label -> (Int, Maybe (Int, Int), M.Map Label Int) -> Int
get l =
    M.findWithDefault (error "Internal error: label not found") l . thd where thd (_, _, z) = z

mi64i8 :: Int64 -> Maybe Int8
mi64i8 i | i > fromIntegral (maxBound :: Int8) || i < fromIntegral (minBound :: Int8) = Nothing
         | otherwise = Just $ fromIntegral i

mi32 :: Int -> Maybe Int32
mi32 i | i > fromIntegral (maxBound :: Int32) || i < fromIntegral (minBound :: Int32) = Nothing
       | otherwise = Just $ fromIntegral i

mi64i32 :: Int64 -> Maybe Int32
mi64i32 i | i > fromIntegral (maxBound :: Int32) || i < fromIntegral (minBound :: Int32) = Nothing
          | otherwise = Just $ fromIntegral i

class RMB a where
    -- extra is 1 bit, ModR/M is 3 bits; I store them as bytes for ease of
    -- manipulation
    modRM :: a -> (Word8, Word8)

instance RMB X86Reg where
    modRM Rax = (0, 0o0)
    modRM Rcx = (0, 0o1)
    modRM Rdx = (0, 0o2)
    modRM Rbx = (0, 0o3)
    modRM Rsp = (0, 0o4)
    modRM Rsi = (0, 0o6)
    modRM Rdi = (0, 0o7)
    modRM R8  = (1, 0o0)
    modRM R9  = (1, 0o1)
    modRM R10 = (1, 0o2)
    modRM R11 = (1, 0o3)
    modRM R12 = (1, 0o4)
    modRM R13 = (1, 0o5)
    modRM R14 = (1, 0o6)
    modRM R15 = (1, 0o7)

instance RMB FX86Reg where
    modRM XMM0  = (0, 0o0)
    modRM XMM1  = (0, 0o1)
    modRM XMM2  = (0, 0o2)
    modRM XMM3  = (0, 0o3)
    modRM XMM4  = (0, 0o4)
    modRM XMM5  = (0, 0o5)
    modRM XMM6  = (0, 0o6)
    modRM XMM7  = (0, 0o7)
    modRM XMM8  = (1, 0o0)
    modRM XMM9  = (1, 0o1)
    modRM XMM10 = (1, 0o2)
    modRM XMM11 = (1, 0o3)
    modRM XMM12 = (1, 0o4)
    modRM XMM13 = (1, 0o5)
    modRM XMM14 = (1, 0o6)
    modRM XMM15 = (1, 0o7)

cb :: (Integral a) => a -> [Word8]
cb x = le (fromIntegral x :: Int8)

cd :: (Integral a) => a -> [Word8]
cd x = le (fromIntegral x :: Word32)

dlB :: FunPtr a -> IntPtr
dlB = ptrToIntPtr . castFunPtrToPtr

-- little endian
le :: (Storable a, Integral a, Bits a) => a -> [Word8]
le x = fromIntegral <$> zipWith (\m e -> (x .&. m) `rotateR` e) masks ee
    where ee = [0,8..(8*(sizeOf x-1))]
          masks = iterate (*0x100) 0xff
