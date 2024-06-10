module Parser.Rw ( rewrite
                 ) where

import           A

rewrite = rw

isBinOp :: Builtin -> Bool
isBinOp FRange = False
isBinOp IRange = False
isBinOp T      = False
isBinOp Zip    = False
isBinOp Rank{} = False
isBinOp Fib    = False
isBinOp Log    = False
isBinOp Size   = False
isBinOp Sqrt   = False
isBinOp Scan{} = False
isBinOp ItoF   = False
isBinOp Last   = False
isBinOp LastM  = False
isBinOp Head   = False
isBinOp HeadM  = False
isBinOp Gen    = False
isBinOp TAt{}  = False
isBinOp Outer  = False
isBinOp R      = False
isBinOp Tail   = False
isBinOp Init   = False
isBinOp Even   = False
isBinOp Odd    = False
isBinOp Abs    = False
isBinOp _      = True

fi :: Builtin -> Int
fi Succ = 9; fi Fold = 9
fi IntExp = 8; fi Exp = 8
fi Times = 7; fi Div = 7; fi Mod = 7
fi Plus = 6; fi Minus = 6
fi Map{} = 5
fi ConsE = 4; fi Snoc = 4
fi Eq = 4; fi Neq = 4; fi Gt = 4
fi Lt = 4; fi Lte = 4; fi Gte = 4
fi CatE   = 5

lassoc :: Builtin -> Bool
lassoc IntExp = False
lassoc Exp    = False
lassoc Div    = True
lassoc Mod    = True
lassoc Times  = True
lassoc Mul    = True
lassoc Plus   = True
lassoc Minus  = True
lassoc ConsE  = False
lassoc Map{}  = False
lassoc CatE   = False

shuntl :: Builtin -> Builtin -> Bool
shuntl op0 op1 = fi op0 > fi op1 || lassoc op0 && lassoc op1 && fi op0 == fi op1

rw :: E a -> E a
-- TODO: guard against rewriting unary ops (transpose, reverse, floor?)
rw (EApp l0 (EApp l1 e0@(Builtin _ op0) e1) e2) | isBinOp op0 =
    case rw e2 of
        (EApp l2 (EApp l3 e3@(Builtin _ op1) e4) e5) | isBinOp op1 && shuntl op0 op1 -> EApp l0 (EApp l1 e3 (rw (EApp l2 (EApp l3 e0 e1) e4))) e5
        e2'                                                                          -> EApp l0 (EApp l1 e0 (rw e1)) e2'
rw (EApp l e0 e') =
    case rw e' of
        (EApp lϵ e1@(EApp lϵϵ e3@(Builtin _ op) e4) e2) | not (isBinOp op) -> EApp l (rw $ EApp lϵ e0 e1) e2
                                                        | otherwise -> EApp l (EApp lϵϵ e3 (rw $ EApp lϵ e0 e4)) e2
        (EApp lϵ e1@EApp{} e2) -> EApp l (rw $ EApp lϵ e0 e1) e2
        (EApp lϵ e1 e2)        -> EApp l (EApp lϵ (rw e0) e1) e2
        eRw                    -> EApp l (rw e0) eRw
rw (Let l (n, e') e) = Let l (n, rw e') (rw e)
rw (Def l (n, e') e) = Def l (n, rw e') (rw e)
rw (LLet l (n, e') e) = LLet l (n, rw e') (rw e)
rw (Tup l es) = Tup l (rw<$>es)
rw (ALit l es) = ALit l (rw<$>es)
rw (Lam l n e) = Lam l n (rw e)
rw (Dfn l e) = Dfn l (rw e)
rw (Parens l e) = Parens l (rw e)
rw (Ann l e t) = Ann l (rw e) (rt t)
rw (Cond l p e e') = Cond l (rw p) (rw e) (rw e')
rw e = e

rt :: T a -> T a
rt (Arr sh (Arrow t t')) = Arrow (Arr sh (rt t)) (rt t')
rt t                     = t
