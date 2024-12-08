module IR.Hoist ( loop, graphParts, hoist ) where

import           CF
import           Control.Arrow                  ((&&&))
import           Control.Composition            (thread)
import           Control.Monad.Trans.State.Lazy (State, gets, modify, runState, state)
import qualified Data.Array                     as A
import           Data.Bifunctor                 (bimap, first, second)
import           Data.Foldable                  (toList)
import           Data.Function                  (on)
import           Data.Functor                   (($>))
import           Data.Graph                     (Tree (Node))
import           Data.Graph.Dom                 (Graph, Node, domTree)
import qualified Data.IntMap                    as IM
import qualified Data.IntSet                    as IS
import qualified Data.Map.Strict                as M
import           Data.Maybe                     (catMaybes, fromJust, mapMaybe)
import           Data.Tuple.Extra               (first3, snd3)
import           Data.Void                      (Void, absurd)
import           IR
import           IR.CF
import           LR
import           Q

type N=Int
type LTbl = A.Array Int Liveness; type CfTbl=A.Array Int (Stmt, ControlAnn); type StmtTbl=A.Array Int Stmt

mapFA :: (FTemp -> FTemp) -> AE -> AE
mapFA f (AP t e l) = AP t (mapFE f<$>e) l

mapFE :: (FTemp -> FTemp) -> Exp -> Exp
mapFE f (IRFloor x)      = IRFloor (mapFF f x)
mapFE f (EAt a)          = EAt (mapFA f a)
mapFE f (BAt a)          = BAt (mapFA f a)
mapFE _ e@ConstI{}       = e
mapFE _ e@Reg{}          = e
mapFE _ e@Is{}           = e
mapFE f (FRel rel x0 x1) = FRel rel (mapFF f x0) (mapFF f x1)
mapFE f (IB op e0 e1)    = IB op (mapFE f e0) (mapFE f e1)
mapFE f (IU op e)        = IU op (mapFE f e)
mapFE f (BU op e)        = BU op (mapFE f e)
mapFE f (IRel rel e0 e1) = IRel rel (mapFE f e0) (mapFE f e1)
mapFE _ e@LA{}           = e

mapFF2 :: (FTemp -> FTemp) -> FExp F2 c Void -> FExp F2 c Void
mapFF2 _ x@KF{}        = x
mapFF2 f (FAt a)       = FAt (mapFA f a)
mapFF2 f (FReg r)      = FReg (view f r)
mapFF2 f (FB op e0 e1) = FB op (mapFF2 f e0) (mapFF2 f e1)
mapFF2 f (FU op e)     = FU op (mapFF2 f e)
mapFF2 _ (FConv x)     = absurd x

mapFF :: (FTemp -> FTemp) -> FExp FTemp c Exp -> FExp FTemp c Exp
mapFF _ x@KF{}        = x
mapFF f (FAt a)       = FAt (mapFA f a)
mapFF f (FB op e0 e1) = FB op (mapFF f e0) (mapFF f e1)
mapFF f (FU op e)     = FU op (mapFF f e)
mapFF f (FReg r)      = FReg (f r)
mapFF f (FConv e)     = FConv (mapFE f e)

view :: (FTemp -> FTemp) -> F2 -> F2
view f (F2Temp i) = case f (FTemp i) of (FTemp j) -> F2Temp j

vv :: F2 -> FTemp
vv (F2Temp i) = FTemp i

mapF :: (FTemp -> FTemp) -> Stmt -> Stmt
mapF f (MX t e)       = MX (f t) (mapFF f e)
mapF f (MX2 t e)      = MX2 (view f t) (mapFF2 f e)
mapF f (S2 o t r)     = S2 o (f t) (view f r)
mapF f (Fill2 r t)    = Fill2 (view f r) (f t)
mapF f (Ins r t)      = Ins (view f r) (f t)
mapF _ s@L{}          = s
mapF _ s@C{}          = s
mapF _ s@R{}          = s
mapF _ s@J{}          = s
mapF _ s@IRnd{}       = s
mapF _ s@RA{}         = s
mapF f (FRnd t)       = FRnd (f t)
mapF _ s@Free{}       = s
mapF f (MT t e)       = MT t (mapFE f e)
mapF f (Wr a e)       = Wr (mapFA f a) (mapFE f e)
mapF f (WrF a x)      = WrF (mapFA f a) (mapFF f x)
mapF f (WrF2 a v)     = WrF2 (mapFA f a) (mapFF2 f v)
mapF f (WrB a e)      = WrB (mapFA f a) (mapFE f e)
mapF f (Fcmov e t x)  = Fcmov (mapFE f e) (f t) (mapFF f x)
mapF f (MJ e l)       = MJ (mapFE f e) l
mapF f (Ma l t e)     = Ma l t (mapFE f e)
mapF f (Sa t e)       = Sa t (mapFE f e)
mapF f (Pop e)        = Pop (mapFE f e)
mapF f (Sa8 t e)      = Sa8 t (mapFE f e)
mapF f (Pop8 e)       = Pop8 (mapFE f e)
mapF f (Cpy a0 a1 e)  = Cpy (mapFA f a0) (mapFA f a1) (mapFE f e)
mapF f (Cpy1 a0 a1 e) = Cpy1 (mapFA f a0) (mapFA f a1) (mapFE f e)
mapF f (Mv a0 a1 n)   = Mv (mapFA f a0) (mapFA f a1) n
mapF f (Cmov p t e)   = Cmov (mapFE f p) t (mapFE f e)
mapF f (Cset t p)     = Cset t (mapFE f p)

type Loop = (N, IS.IntSet)
type LLoop = M.Map Label (Label, IS.IntSet)

lm :: [(Stmt, NLiveness)] -> LTbl
lm cs = A.array (0, maximum ns) (zip ns (liveness<$>ls))
  where ls=map snd cs; ns = map nx ls

data CM = LL !Label | FM !FTemp !Double | F2M !F2 !(Double, Double)

nh :: LM Label
nh = state (\u -> (u, u+1))

hl :: (Loop, CfTbl, LTbl) -> LM (LLoop, [(N, Maybe N, CM)])
hl ((n,ns), info, linfo) =
    let ss'=go ss
    in if null ss'
        then pure (M.empty, [])
        else do {fl <- nh; pure (M.singleton lh (fl,ns), (n,Nothing,LL fl):ss')}
  where
    fliveInH=fins (linfo A.! n)
    go ((MX x (KF i), a):ssϵ) | fToInt x `IS.notMember` fliveInH && notFDef (fToInt x) (node a) = (n, Just$node a, FM x i):go ssϵ
    go ((MX2 x (KF i), a):ssϵ) | f2ToInt x `IS.notMember` fliveInH && notFDef (f2ToInt x) (node a) = (n, Just$node a, F2M x i):go ssϵ
    go (_:ssϵ)                      = go ssϵ
    go []                           = []
    otherDefFs nL = defsFNode.ud.snd.getCf<$>IS.toList(IS.delete nL ns)
    notFDef r nL = not $ any (r `IS.member`) (otherDefFs nL)
    ss = getCf<$>IS.toList ns; (L lh,_) = getCf n
    getCf = (info A.!)

data S = S { f1s :: !(M.Map Double FTemp), f2s :: !(M.Map (Double, Double) F2)
           , su :: !(M.Map FTemp FTemp)
           }

emptyS = S M.empty M.empty M.empty

type LM=State Label

i1 x t = modify (\(S f1 f2 s) -> S (M.insert x t f1) f2 s); i2 x t = modify (\(S f1 f2 s) -> S f1 (M.insert x t f2) s)
br t r (S f1 f2 s) = S f1 f2 (M.insert t r s)

rwL :: LLoop -> (Stmt, NLiveness) -> (Stmt, N)
rwL s (MJ e l, a) = let n=nx a in (case M.lookup l s of {Just (lϵ,m) | n `IS.notMember` m -> MJ e lϵ; _ -> MJ e l}, n)
rwL _ (ss, a)     = (ss, nx a)

hoist :: Label -> [Stmt] -> ([Stmt], Label)
hoist u ss = flip runState u $ do
    (cf, m, is, dels) <- indels ss
    let go ((_,n):ssϵ) | n `IS.member` dels = go ssϵ
        go ((s,n):ssϵ) | Just cs <- IM.lookup n is = let (css, S _ _ subst) = {-# SCC "consolidate" #-} consolidate cs in bimap (subst<>) ((css++[s])++) (go ssϵ)
        go ((s,_):ssϵ) = second (s:)$go ssϵ
        go [] = (M.empty, [])

        (ts, ss') = go (rwL m<$>cf)
    pure ({-# SCC "applySubst" #-} map (ts@>) ss')
  where
    (@>) s = mapF (\t -> M.findWithDefault t t s)
    consolidate = first concat . flip runState emptyS . traverse c

    c (LL l) = pure [L l]
    c (FM t x) = do
        seen <- gets f1s
        case M.lookup x seen of
            Nothing -> i1 x t$>[MX t (KF x)]
            Just r  -> modify (br t r) $> []
    c (F2M t x) = do
        seen <- gets f2s
        case M.lookup x seen of
            Nothing -> i2 x t$>[MX2 t (KF x)]
            Just r  -> modify ((br `on` vv) t r) $> []

indels :: [Stmt] -> LM ([(Stmt, NLiveness)], LLoop, IM.IntMap [CM], IS.IntSet)
indels ss = do
    (c,ls,h) <- gatherLoops ss
    let ds = IS.fromList (mapMaybe snd3 h)
        is = thread ((\(n,_,s) -> n!:s)<$>h)
    pure (c, ls, is IM.empty, ds)

gatherLoops :: [Stmt] -> LM ([(Stmt, NLiveness)], LLoop, [(N, Maybe N, CM)])
gatherLoops ss = let (ls, cf, dm) = loop ss
                     mm = lm cf
                 in fmap ((\(x,y) -> (cf,x,y)) . bimerge) (traverse (\l -> hl (l,dm,mm)) (outers ls))
  where
    bimerge xys = let (xs,ys)=unzip xys in (mconcat xs, concat ys)

loop :: [Stmt] -> ([Loop], [(Stmt, NLiveness)], CfTbl)
loop = first3 (fmap mkL).(\(w,x,y,z) -> (et w (fmap fst z) [] x,y,z)).graphParts
  where
    mkL (n, ns) = (n, IS.fromList ns)

graphParts :: [Stmt] -> (Graph, Tree N, [(Stmt, NLiveness)], CfTbl)
graphParts ss = (\ssϵ -> (\(x,y,z) -> (x,y,reconstructFlat$fst ssϵ,z))$mkG ssϵ) (mkControlFlow ss)

dead :: (ControlAnn, NLiveness) -> Bool
dead (l, cl) = not (missingo (defsNode u) (out lv)) && not (missingo (defsFNode u) (fout lv))
  where u=ud l
        lv=liveness cl
        missingo x y | IS.null x = False
                     | otherwise = x `IS.disjoint` y

{-# SCC outers #-}
outers :: [Loop] -> [Loop]
outers ls = filter (\(_,ns) -> not $ any (\(_,ns') -> ns `IS.isProperSubsetOf` ns') ls) ls

-- expand tree
et :: Graph -> StmtTbl -> [N] -> Tree N -> [(N, [N])]
et g ss seen t = expandLoop t <$> loopHeads g ss seen t

-- everything the start node dominates
expandLoop :: Tree N -> N -> (N,[N])
--- wir müssen wissen, wir werden wissen
expandLoop t s = (s, fromJust (go t))
  where
    go (Node n tϵ) | n==s = Just$concatMap toList tϵ
    go (Node _ ns) = mh (go<$>ns) where mh xs=case catMaybes xs of {[] -> Nothing; (nϵ:_) -> Just nϵ}

loopHeads :: Graph -> StmtTbl -> [N] -> Tree N -> [N]
loopHeads g ss seen (Node n cs) =
    let bes=hasEdge g n #. seen
    in (if isMJ n then (bes++) else id) $ concatMap (loopHeads g ss (n:seen)) cs
  where
    isMJ nϵ = p (ss A.! nϵ)
    p MJ{}=True; p _=False

hasEdge :: Graph -> Node -> Node -> Bool
hasEdge g n0 n1 = case IM.lookup n0 g of {Nothing -> False; Just ns -> n1 `IS.member` ns}

mkG :: ([(Stmt, ControlAnn)], Int) -> (Graph, Tree N, CfTbl)
mkG (ns,m) = (domG, domTree (node (snd (head ns)), domG), sa)
  where
    domG = IM.fromList [ (node ann, IS.fromList (conn ann)) | (_, ann) <- ns ]
    sa = A.array (0,m-1) ((node.snd &&& id)<$>ns)
