{-# LANGUAGE OverloadedStrings #-}

module A.Opt ( optA
             ) where

import           A
import           Data.Bits ((.<<.), (.>>.))
import           R
import           R.R

-- TODO zip-of-map->zip

fop op e0 = EApp F (EApp (F ~> F) (Builtin (F ~> F ~> F) op) e0)
eMinus = fop Minus; eDiv = fop Div

mShLit (Id _ (AShLit is es)) = Just (is, es)
mShLit (ALit _ es)           = Just ([length es], es)
mShLit _                     = Nothing

mSz :: Sh a -> Maybe Int
mSz (Ix _ i `Cons` sh) = (i*)<$>mSz sh
mSz Nil                = Just 1
mSz _                  = Nothing

optA :: E (T ()) -> RM (E (T ()))
optA (ILit F x)            = pure (FLit F (realToFrac x))
optA e@ILit{}              = pure e
optA e@FLit{}              = pure e
optA e@BLit{}              = pure e
optA e@Var{}               = pure e
optA (Builtin t (Rank rs)) = pure (Builtin t (Rank (g<$>rs))) where g r@(_,Just{})=r; g (cr,Nothing)=(cr, Just [1..cr])
optA (Builtin ty C)        | Arrow fTy (Arrow gTy (Arrow tC tD)) <- ty = do
    f <- nextU "f" fTy; g <- nextU "g" gTy; x <- nextU "x" tC
    pure $ Lam undefined f (Lam undefined g (Lam undefined x (EApp tD (Var fTy f) (EApp undefined (Var gTy g) (Var tC x)))))
optA e@Builtin{}           = pure e
optA (EApp _ (Builtin _ Size) xs) | Arr sh _ <- eAnn xs, Just sz <- mSz sh = pure $ ILit I (toInteger sz)
optA (EApp _ (Builtin _ Dim) xs) | Arr (Ix _ i `Cons` _) _ <- eAnn xs = pure $ ILit I (toInteger i)
optA (EApp l0 (EApp l1 op@(Builtin _ Exp) e0) e1) = do
    e0' <- optA e0
    e1' <- optA e1
    pure $ case (e0', e1') of
        (FLit _ x, FLit _ y) -> FLit l0 (x**y)
        _                    -> EApp l0 (EApp l1 op e0') e1'
optA (EApp l0 (EApp l1 op@(Builtin l2 Div) e0) e1) = do
    e0' <- optA e0
    e1' <- optA e1
    pure $ case (e0', e1') of
        (FLit _ x, FLit _ y) -> FLit l0 (x/y)
        (x, FLit t y)        -> EApp l0 (EApp l1 (Builtin l2 Times) x) (FLit t (1/y))
        _                    -> EApp l0 (EApp l1 op e0') e1'
optA (EApp l0 op@(Builtin _ N) e0) = do
    e0' <- optA e0
    pure $ case e0' of
        (BLit _ b) -> BLit B (not b)
        _          -> EApp l0 op e0'
optA (EApp l0 (EApp l1 op@(Builtin _ Sr) e0) e1) = do
    e0' <- optA e0
    e1' <- optA e1
    pure $ case (e0', e1') of
        (ILit _ m, ILit _ n) -> ILit I (m .>>. fromIntegral n)
        _                    -> EApp l0 (EApp l1 op e0') e1'
optA (EApp l0 (EApp l1 op@(Builtin _ Sl) e0) e1) = do
    e0' <- optA e0
    e1' <- optA e1
    pure $ case (e0', e1') of
        (ILit _ m, ILit _ n) -> ILit I (m .<<. fromIntegral n)
        _                    -> EApp l0 (EApp l1 op e0') e1'
optA (Lam l n e) = Lam l n <$> optA e
optA (EApp l0 (EApp l1 op@(Builtin _ Times) x) y) = do
    xO <- optA x
    yO <- optA y
    pure $ case (xO, yO) of
        (FLit _ x', FLit _ y') -> FLit F (x'*y')
        (FLit _ x', ILit _ y') -> FLit F (x'*realToFrac y')
        (ILit _ x', FLit _ y') -> FLit F (realToFrac x'*y')
        _                      -> EApp l0 (EApp l1 op xO) yO
optA (EApp l0 f@(Builtin _ ItoF) x) = do
    x' <- optA x
    pure $ case x' of
        ILit _ n -> FLit F (realToFrac n)
        _        -> EApp l0 f x'
optA (EApp l0 (EApp l1 op@(Builtin _ Minus) x) y) = do
    xO <- optA x
    yO <- optA y
    pure $ case (xO, yO) of
        (FLit _ x', FLit _ y') -> FLit F (x'-y')
        (FLit _ x', ILit _ y') -> FLit F (x'-realToFrac y')
        (ILit _ x', FLit _ y') -> FLit F (realToFrac x'-y')
        _                      -> EApp l0 (EApp l1 op xO) yO
optA (EApp l op@(Builtin _ Sqrt) x) = do
    xO <- optA x
    pure $ case xO of
        FLit _ z -> FLit F (sqrt z)
        _        -> EApp l op xO
optA (EApp _ (Builtin _ Floor) (EApp _ (Builtin _ ItoF) x)) = optA x
optA (EApp ty (EApp _ (Builtin _ IntExp) x) (ILit _ 2)) = pure $ EApp ty (EApp (ty ~> ty) (Builtin (ty ~> ty ~> ty) Times) x) x
optA (EApp l0 (EApp _ (Builtin _ Fold) op) (EApp _ (EApp _ (EApp _ (Builtin _ FRange) start) end) nSteps)) = do
    start' <- optA start
    incrN <- optA $ (end `eMinus` start) `eDiv` (EApp F (Builtin (Arrow I F) ItoF) nSteps `eMinus` FLit F 1)
    fF <- optA op
    n <- nextU "n" F
    pure $ Id l0 $ FoldGen start' (Lam (F ~> F) n (EApp F (EApp (F ~> F) (Builtin (F ~> F ~> F) Plus) incrN) (Var F n))) fF nSteps
optA (EApp l0 (EApp _ (Builtin _ Fold) op) (EApp _ (EApp _ (EApp _ (Builtin _ Gen) seed) f) n)) =
    Id l0 <$> (FoldGen <$> optA seed <*> optA f <*> optA op <*> optA n)
optA (EApp l0 (EApp _ (EApp _ (Builtin _ ho0@FoldS) op) seed) (EApp _ (EApp _ (Builtin _ Map) f) x))
    | Arrow dom fCod <- eAnn f
    , Arrow _ (Arrow _ cod) <- eAnn op = do
        x' <- optA x
        x0 <- nextU "x" cod; x1 <- nextU "y" dom
        opA <- optA op
        let vx0 = Var cod x0; vx1 = Var dom x1
            opTy = cod ~> dom ~> cod
            op' = Lam opTy x0 (Lam (dom ~> cod) x1 (EApp cod (EApp undefined opA vx0) (EApp fCod f vx1)))
            arrTy = eAnn x'
        optA (EApp l0 (EApp undefined (EApp (arrTy ~> l0) (Builtin (opTy ~> arrTy ~> l0) ho0) op') seed) x')
optA (EApp l0 (EApp _ (Builtin _ Succ) f) (EApp _ (EApp _ (Builtin _ Map) g) xs))
    | (Arrow _ (Arrow _ fCod)) <- eAnn f
    , (Arrow gDom _) <- eAnn g = do
        f' <- optA f; g' <- optA g; g'' <- rE g
        xs' <- optA xs
        x <- nextU "w" gDom; y <- nextU "v" gDom
        let vx=Var gDom x; vy=Var gDom y
            f2g=Lam (gDom ~> gDom ~> fCod) x (Lam (gDom ~> fCod) y (EApp undefined (EApp undefined f' (EApp undefined g' vx)) (EApp undefined g'' vy)))
        pure (EApp l0 (EApp undefined (Builtin undefined Succ) f2g) xs')
optA (EApp l0 (EApp _ (Builtin _ Map) f) (EApp _ (EApp _ (Builtin _ Map) g) xs))
    | (Arrow _ fCod) <- eAnn f
    , (Arrow gDom _) <- eAnn g = do
        f' <- optA f; g' <- optA g
        xs' <- optA xs
        x <- nextU "x" gDom
        let vx=Var gDom x
            fog=Lam (gDom ~> fCod) x (EApp undefined f' (EApp undefined g' vx))
        pure (EApp l0 (EApp undefined (Builtin undefined Map) fog) xs')
optA (EApp l0 (EApp _ (Builtin _ Fold) op) (EApp _ (EApp _ (Builtin _ Map) f) x))
    | fTy@(Arrow dom fCod) <- eAnn f
    , Arrow _ (Arrow _ cod) <- eAnn op = do
        f' <- optA f; f'' <- rE f'
        x' <- optA x
        x0 <- nextU "x" cod; x1 <- nextU "y" dom
        x0' <- nextU "x" dom
        opA <- optA op
        let vx0 = Var cod x0; vx1 = Var dom x1
            vx0' = Var dom x0'
            opT = cod ~> dom ~> cod
            op' = Lam opT x0 (Lam (dom ~> cod) x1 (EApp cod (EApp undefined opA vx0) (EApp fCod f' vx1)))
            f''' = Lam fTy x0' (EApp fCod f'' vx0')
        pure $ Id l0 $ FoldOfZip f''' op' [x']
optA (EApp l0 (EApp _ (Builtin _ (Rank [(0,_)])) f) (EApp _ (EApp _ (EApp _ ho@(Builtin _ (Rank [(0,_),(0,_)])) op) xs) ys))
    | Arrow _ cod <- eAnn f
    , Arrow dom0 (Arrow dom1 _) <- eAnn op = do
        f' <- optA f; opA <- optA op; ho' <- optA ho
        xs' <- optA xs; ys' <- optA ys
        x <- nextU "x" dom0; y <- nextU "y" dom1
        let vx=Var dom0 x; vy=Var dom1 y
            opTy = dom0 ~> dom1 ~> cod
            op' = Lam opTy x (Lam undefined y (EApp undefined f' (EApp undefined (EApp undefined opA vx) vy)))
        pure (EApp l0 (EApp undefined (EApp undefined (ho' { eAnn = undefined }) op') xs') ys')
optA (EApp l0 (EApp _ (EApp _ ho@(Builtin _ (Rank [(0,_),(0,_)])) op) (EApp _ (EApp _ (Builtin _ (Rank [(0,_)])) f) xs)) (EApp _ (EApp _ (Builtin _ (Rank [(0,_)])) g) ys))
    | Arrow dom0 _ <- eAnn f
    , Arrow dom1 _ <- eAnn g
    , Arrow _ (Arrow _ cod) <- eAnn op = do
        f' <- optA f; g' <- optA g
        opA <- optA op; ho' <- optA ho
        xs' <- optA xs; ys' <- optA ys
        x <- nextU "x" dom0; y <- nextU "y" dom1
        let vx = Var dom0 x; vy = Var dom1 y
            opTy = dom0 ~> dom1 ~> cod
            op' = Lam opTy x (Lam undefined y (EApp undefined (EApp undefined opA (EApp undefined f' vx)) (EApp undefined g' vy)))
        pure (EApp l0 (EApp undefined (EApp undefined (ho' { eAnn = undefined }) op') xs') ys')
optA (EApp l0 (EApp _ (EApp _ ho@(Builtin _ (Rank [(0,_),(0,_)])) op) xs) (EApp _ (EApp _ (Builtin _ (Rank [(0,_)])) g) ys))
    | Arrow dom _ <- eAnn g
    , Arrow xT (Arrow _ cod) <- eAnn op = do
        g' <- optA g
        opA <- optA op; ho' <- optA ho
        xs' <- optA xs; ys' <- optA ys
        x <- nextU "x" xT; y <- nextU "y" dom
        let vx = Var xT x; vy = Var dom y
            opTy = xT ~> dom ~> cod
            op' = Lam opTy x (Lam undefined y (EApp undefined (EApp undefined opA vx) (EApp undefined g' vy)))
        pure (EApp l0 (EApp undefined (EApp undefined (ho' { eAnn = undefined }) op') xs') ys')
optA (EApp l0 (EApp _ (EApp _ ho@(Builtin _ (Rank [(0,_),(0,_)])) op) (EApp _ (EApp _ (Builtin _ (Rank [(0,_)])) f) xs)) ys)
    | Arrow dom _ <- eAnn f
    , Arrow _ (Arrow yT cod) <- eAnn op = do
        f' <- optA f
        opA <- optA op; ho' <- optA ho
        xs' <- optA xs; ys' <- optA ys
        x <- nextU "x" dom; y <- nextU "y" yT
        let vx = Var dom x; vy = Var yT y
            opTy = dom ~> yT ~> cod
            op' = Lam opTy x (Lam undefined y (EApp undefined (EApp undefined opA (EApp undefined f' vx)) vy))
        pure (EApp l0 (EApp undefined (EApp undefined (ho' { eAnn = undefined }) op') xs') ys')
optA (EApp _ (EApp _ (EApp _ (Builtin _ Zip) op) (EApp _ (EApp _ (Builtin _ Map) f) xs)) (EApp _ (EApp _ (Builtin _ Map) g) ys))
    | Arrow dom0 _ <- eAnn f
    , Arrow dom1 _ <- eAnn g
    , Arrow _ (Arrow _ cod) <- eAnn op = do
        f' <- optA f; g' <- optA g
        opA <- optA op
        xs' <- optA xs; ys' <- optA ys
        x0 <- nextU "x" dom0; x1 <- nextU "y" dom1
        let vx0 = Var dom0 x0; vx1 = Var dom1 x1
            opTy = dom0 ~> dom1 ~> cod
            op' = Lam opTy x0 (Lam undefined x1 (EApp undefined (EApp undefined opA (EApp undefined f' vx0)) (EApp undefined g' vx1)))
        pure (EApp undefined (EApp undefined (EApp undefined (Builtin undefined Zip) op') xs') ys')
optA (EApp l (EApp _ (EApp _ (Builtin _ Zip) op) (EApp _ (EApp _ (Builtin _ Map) f) xs)) ys)
    | Arrow dom0 _ <- eAnn f
    , Arrow _ (Arrow dom1 cod) <- eAnn op = do
        f' <- optA f
        opA <- optA op
        xs' <- optA xs; ys' <- optA ys
        x0 <- nextU "x" dom0; x1 <- nextU "y" dom1
        let vx0 = Var dom0 x0; vx1 = Var dom1 x1
            opTy = dom0 ~> dom1 ~> cod
            op' = Lam opTy x0 (Lam undefined x1 (EApp undefined (EApp undefined opA (EApp undefined f' vx0)) vx1))
        pure (EApp l (EApp undefined (EApp undefined (Builtin undefined Zip) op') xs') ys')
optA (EApp l (EApp _ (EApp _ (Builtin _ Zip) op) xs) (EApp _ (EApp _ (Builtin _ Map) g) ys))
    | Arrow dom1 _ <- eAnn g
    , Arrow dom0 (Arrow _ cod) <- eAnn op = do
        g' <- optA g
        opA <- optA op
        xs' <- optA xs; ys' <- optA ys
        x0 <- nextU "x" dom0; x1 <- nextU "y" dom1
        let vx0 = Var dom0 x0; vx1 = Var dom1 x1
            opTy = dom0 ~> dom1 ~> cod
            op' = Lam opTy x0 (Lam undefined x1 (EApp undefined (EApp undefined opA vx0) (EApp undefined g' vx1)))
        pure (EApp l (EApp undefined (EApp undefined (Builtin undefined Zip) op') xs') ys')
optA (EApp l (EApp t0 (EApp t1 (Builtin bt b@FoldS) op) seed) arr) = do
    arr' <- optA arr
    seed' <- optA seed
    opA <- optA op
    case arr' of
        (EApp _ (EApp _ (EApp _ (Builtin _ Zip) f) xs) ys)
            | Arrow dom0 (Arrow dom1 dom2) <- eAnn f
            , Arrow _ (Arrow _ cod) <- eAnn op -> do
                f' <- optA f
                xs' <- optA xs
                ys' <- optA ys
                x0 <- nextU "x" cod; x1 <- nextU "y" dom0; x2 <- nextU "z" dom1
                let vx0 = Var cod x0; vx1 = Var dom0 x1; vx2 = Var dom1 x2
                    opTy = cod ~> dom0 ~> dom1 ~> cod
                    op' = Lam opTy x0 (Lam undefined x1 (Lam (dom1 ~> cod) x2 (EApp cod (EApp undefined opA vx0) (EApp dom2 (EApp undefined f' vx1) vx2))))
                pure $ Id l $ FoldSOfZip seed' op' [xs',ys']
        _ -> pure (EApp l (EApp t0 (EApp t1 (Builtin bt b) opA) seed') arr')
optA (EApp t0 (EApp t1 (Builtin bt Fold) op) arr) = do
    arr' <- optA arr
    opA <- optA op
    case arr' of
        (EApp _ (EApp _ (EApp _ (Builtin _ Zip) f) xs) ys)
            | fTy@(Arrow dom0 (Arrow dom1 dom2)) <- eAnn f
            , Arrow _ (Arrow _ cod) <- eAnn op -> do
                f' <- optA f; f'' <- rE f'
                xs' <- optA xs; ys' <- optA ys
                x0 <- nextU "x" cod; x1 <- nextU "y" dom0; x2 <- nextU "z" dom1
                x0' <- nextU "x" dom0; x1' <- nextU "y" dom1
                let vx0 = Var cod x0; vx1 = Var dom0 x1; vx2 = Var dom1 x2
                    vx0' = Var dom0 x0'; vx1' = Var dom1 x1'
                    opT = cod ~> dom0 ~> dom1 ~> cod
                    op' = Lam opT x0 (Lam undefined x1 (Lam (dom1 ~> cod) x2 (EApp cod (EApp undefined opA vx0) (EApp dom2 (EApp undefined f' vx1) vx2))))
                    f''' = Lam fTy x0' (Lam undefined x1' (EApp dom2 (EApp undefined f'' vx0') vx1'))
                pure $ Id t0 $ FoldOfZip f''' op' [xs',ys']
        _ -> pure (EApp t0 (EApp t1 (Builtin bt Fold) opA) arr')
optA (EApp l e0 e1) = EApp l <$> optA e0 <*> optA e1
optA (ALit l es) = do
    es' <- traverse optA es
    pure $ case unzip <$> traverse mShLit es' of
        Nothing        -> Id l $ AShLit [length es] es'
        Just (ds, esϵ) -> Id l $ AShLit (length ds : head ds) (concat esϵ)
optA (Tup l es) = Tup l <$> traverse optA es
optA (Let l (n, e') e) = do
    e'Opt <- optA e'
    eOpt <- optA e
    pure $ Let l (n, e'Opt) eOpt
optA (LLet l (n, e') e) = do
    e'Opt <- optA e'
    eOpt <- optA e
    pure $ LLet l (n, e'Opt) eOpt
optA (Id l idm) = Id l <$> optI idm
optA (Cond l p e0 e1) = Cond l <$> optA p <*> optA e0 <*> optA e1

optI (FoldSOfZip seed op es) = FoldSOfZip <$> optA seed <*> optA op <*> traverse optA es
optI (FoldOfZip zop op es)   = FoldOfZip <$> optA zop <*> optA op <*> traverse optA es
optI (FoldGen seed f g n)    = FoldGen <$> optA seed <*> optA f <*> optA g <*> optA n
optI (AShLit ds es)          = AShLit ds <$> traverse optA es
