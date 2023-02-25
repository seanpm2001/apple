{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Main (main) where

import           A
import           Control.Monad.IO.Class    (liftIO)
import           Control.Monad.State       (StateT, evalStateT, gets, modify)
import           Control.Monad.Trans.Class (lift)
import           Criterion                 (benchmark, nfIO)
import qualified Data.ByteString.Lazy      as BSL
import           Data.Foldable             (traverse_)
import           Data.Int                  (Int64)
import           Data.List
import qualified Data.Text                 as T
import qualified Data.Text.IO              as TIO
import qualified Data.Text.Lazy            as TL
import           Data.Text.Lazy.Encoding   (encodeUtf8)
import           Data.Tuple.Extra          (first3)
import           Dbg
import           Foreign.LibFFI            (callFFI, retCDouble, retInt64, retPtr, retWord8)
import           Foreign.Marshal.Alloc     (free)
import           Foreign.Ptr               (Ptr, castPtr)
import           Foreign.Storable          (peek)
import           Hs.A
import           Hs.FFI
import           L
import           Nm
import           Prettyprinter             (hardline, pretty, tupled, (<+>))
import           Prettyprinter.Render.Text (putDoc)
import           Sys.DL
import           System.Console.Haskeline  (Completion, CompletionFunc, InputT, completeFilename, defaultSettings, fallbackCompletion, getInputLine, historyFile, runInputT,
                                            setComplete, simpleCompletion)
import           System.Directory          (getHomeDirectory)
import           System.FilePath           ((</>))
import           System.Info               (arch)
import           Ty

main :: IO ()
main = runRepl loop

namesStr :: StateT Env IO [String]
namesStr = gets (fmap (T.unpack.name.fst) . ee)

data Arch = X64 | AArch64 !MCtx

data Env = Env { _lex :: !AlexUserState, ee :: [(Nm AlexPosn, E AlexPosn)], mf :: CCtx, _arch :: Arch }

aEe :: Nm AlexPosn -> E AlexPosn -> Env -> Env
aEe n e (Env l ees mm a) = Env l ((n,e):ees) mm a

setL :: AlexUserState -> Env -> Env
setL lSt (Env _ ees mm a) = Env lSt ees mm a

type Repl a = InputT (StateT Env IO)

cyclicSimple :: [String] -> [Completion]
cyclicSimple = fmap simpleCompletion

runRepl :: Repl a x -> IO x
runRepl x = do
    histDir <- (</> ".apple_history") <$> getHomeDirectory
    mfϵ <- mem'
    initSt <- Env alexInitUserState [] mfϵ <$> case arch of {"x86_64" -> pure X64; "aarch64" -> AArch64<$>math'; _ -> error "Unsupported architecture!"}
    let myCompleter = appleCompletions `fallbackCompletion` completeFilename
    let settings = setComplete myCompleter $ defaultSettings { historyFile = Just histDir }
    flip evalStateT initSt $ runInputT settings x

appleCompletions :: CompletionFunc (StateT Env IO)
appleCompletions (":","")         = pure (":", cyclicSimple ["help", "h", "ty", "quit", "q", "list", "ann", "bench", "y", "yank"])
appleCompletions ("i:", "")       = pure ("i:", cyclicSimple ["r", "nspect", ""])
appleCompletions ("ri:", "")      = pure ("ri:", cyclicSimple [""])
appleCompletions ("c:", "")       = pure ("c:", cyclicSimple ["mm"])
appleCompletions ("mc:", "")      = pure ("mc:", cyclicSimple ["m"])
appleCompletions ("mmc:", "")     = pure ("mmc:", cyclicSimple [""])
appleCompletions ("ni:", "")      = pure ("ni:", [simpleCompletion "spect"])
appleCompletions ("sni:", "")     = pure ("sni:", [simpleCompletion "pect"])
appleCompletions ("psni:", "")    = pure ("psni:", [simpleCompletion "ect"])
appleCompletions ("epsni:", "")   = pure ("epsni:", [simpleCompletion "ct"])
appleCompletions ("cepsni:", "")  = pure ("cepsni:", [simpleCompletion "t"])
appleCompletions ("tcepsni:", "") = pure ("tcepsni:", [simpleCompletion ""])
appleCompletions ("t:", "")       = pure ("t:", cyclicSimple ["y"])
appleCompletions ("b:", "")       = pure ("b:", cyclicSimple ["ench", ""])
appleCompletions ("eb:", "")      = pure ("eb:", [simpleCompletion "nch"])
appleCompletions ("neb:", "")     = pure ("neb:", [simpleCompletion "ch"])
appleCompletions ("cneb:", "")    = pure ("cneb:", [simpleCompletion "h"])
appleCompletions ("hcneb:", "")   = pure ("hcneb:", [simpleCompletion ""])
appleCompletions ("c:", "")       = pure ("c:", cyclicSimple ["ompile", ""])
appleCompletions ("oc:", "")      = pure ("oc:", cyclicSimple ["mpile", ""])
appleCompletions ("moc:", "")     = pure ("moc:", cyclicSimple ["pile", ""])
appleCompletions ("pmoc:", "")    = pure ("pmoc:", cyclicSimple ["ile", ""])
appleCompletions ("ipmoc:", "")   = pure ("ipmoc:", cyclicSimple ["le", ""])
appleCompletions ("lipmoc:", "")  = pure ("lipmoc:", cyclicSimple ["e", ""])
appleCompletions ("elipmoc:", "") = pure ("elipmoc:", cyclicSimple [""])
appleCompletions ("yt:", "")      = pure ("yt:", cyclicSimple [""])
appleCompletions ("y:", "")       = pure ("y:", cyclicSimple ["ank", ""])
appleCompletions ("ay:", "")      = pure ("ay:", cyclicSimple ["nk"])
appleCompletions ("nay:", "")     = pure ("nay:", cyclicSimple ["k"])
appleCompletions ("knay:", "")    = pure ("knay:", cyclicSimple [""])
appleCompletions ("d:", "")       = pure ("d:", [simpleCompletion "isasm"])
appleCompletions ("id:", "")      = pure ("id:", [simpleCompletion "sasm"])
appleCompletions ("sid:", "")     = pure ("sid:", [simpleCompletion "asm"])
appleCompletions ("asid:", "")    = pure ("asid:", [simpleCompletion "sm"])
appleCompletions ("sasid:", "")   = pure ("sasid:", [simpleCompletion "m"])
appleCompletions ("msasid:", "")  = pure ("msasid:", [simpleCompletion ""])
appleCompletions ("a:", "")       = pure ("a:", [simpleCompletion "sm", simpleCompletion "nn"])
appleCompletions ("sa:", "")      = pure ("sa:", [simpleCompletion "m"])
appleCompletions ("msa:", "")     = pure ("msa:", [simpleCompletion ""])
appleCompletions ("na:", "")      = pure ("na:", [simpleCompletion "n"])
appleCompletions ("nna:", "")     = pure ("nna:", [simpleCompletion ""])
appleCompletions ("q:", "")       = pure ("q:", cyclicSimple ["uit", ""])
appleCompletions ("uq:", "")      = pure ("uq:", [simpleCompletion "it"])
appleCompletions ("iuq:", "")     = pure ("iuq:", [simpleCompletion "t"])
appleCompletions ("tiuq:", "")    = pure ("tiuq:", [simpleCompletion ""])
appleCompletions ("h:", "")       = pure ("h:", cyclicSimple ["elp", ""])
appleCompletions ("eh:", "")      = pure ("eh:", [simpleCompletion "lp"])
appleCompletions ("leh:", "")     = pure ("leh:", [simpleCompletion "p"])
appleCompletions ("pleh:", "")    = pure ("pleh:", [simpleCompletion ""])
appleCompletions (" yt:", "")     = do { ns <- namesStr ; pure (" yt:", cyclicSimple ns) }
appleCompletions (" t:", "")      = do { ns <- namesStr ; pure (" t:", cyclicSimple ns) }
appleCompletions ("", "")         = ("",) . cyclicSimple <$> namesStr
appleCompletions (rp, "")         = do { ns <- namesStr ; pure (unwords ("" : tail (words rp)), cyclicSimple (namePrefix ns rp)) }
appleCompletions _                = pure (undefined, [])

namePrefix :: [String] -> String -> [String]
namePrefix names prevRev = filter (last (words (reverse prevRev)) `isPrefixOf`) names

loop :: Repl AlexPosn ()
loop = do
    inp <- getInputLine " > "
    case words <$> inp of
        Just []               -> loop
        Just (":h":_)         -> showHelp *> loop
        Just (":help":_)      -> showHelp *> loop
        Just ("\\l":_)        -> langHelp *> loop
        Just (":ty":e)        -> tyExprR (unwords e) *> loop
        Just [":q"]           -> pure ()
        Just [":quit"]        -> pure ()
        Just (":asm":e)       -> dumpAsm (unwords e) *> loop
        Just (":ann":e)       -> annR (unwords e) *> loop
        Just (":b":e)         -> benchE (unwords e) *> loop
        Just (":bench":e)     -> benchE (unwords e) *> loop
        Just (":ir":e)        -> irR (unwords e) *> loop
        Just (":c":e)         -> cR (unwords e) *> loop
        Just (":cmm":e)       -> cR (unwords e) *> loop
        Just (":disasm":e)    -> disasm (unwords e) *> loop
        Just (":inspect":e)   -> inspect (unwords e) *> loop
        Just (":compile":e)   -> benchC (unwords e) *> loop
        Just (":yank":f:[fp]) -> iCtx f fp *> loop
        Just (":y":f:[fp])    -> iCtx f fp *> loop
        Just (":graph":e)     -> graph (unwords e) *> loop
        Just e                -> printExpr (unwords e) *> loop
        Nothing               -> pure ()

graph :: String -> Repl AlexPosn ()
graph s = liftIO $ case dumpX86Ass (ubs s) of
    Left err -> putDoc (pretty err <> hardline)
    Right d  -> putDoc (d <> hardline)

showHelp :: Repl AlexPosn ()
showHelp = liftIO $ putStr $ concat
    [ helpOption ":help, :h" "" "Show this help"
    , helpOption ":ty" "<expression>" "Display the type of an expression"
    , helpOption ":ann" "<expression>" "Annotate with types"
    , helpOption ":bench, :b" "<expression>" "Benchmark an expression"
    , helpOption ":list" "" "List all names that are in scope"
    , helpOption ":quit, :q" "" "Quit REPL"
    , helpOption ":yank, :y" "<fn> <file>" "Read file"
    , helpOption "\\l" "" "Reference card"
    -- TODO: dump debug state
    ]

langHelp :: Repl AlexPosn ()
langHelp = liftIO $ putStr $ concat
    [ lOption "Λ" "scan" "√" "sqrt"
    , lOption "⋉"  "max" "⋊"  "min"
    , lOption "⍳" "integer range" "⌊" "floor"
    , lOption "ℯ" "exp" "⨳ {m,n}" "convolve"
    , lOption "\\~" "successive application" "\\`n" "dyadic infix"
    , lOption "_." "log" "'n" "map"
    , lOption "`" "zip" "`{i,j∘[k,l]}" "rank"
    , lOption "𝒻" "range (real)" "𝜋" "pi"
    , lOption "_" "negate" ":" "size"
    , lOption "𝓉" "dimension" "}.?" "last"
    , lOption "->n" "select" "**" "power"
    , lOption "gen." "generate" "𝓕" "fibonacci"
    , lOption "re:" "repeat" "}." "typesafe last"
    , lOption "⊲" "cons" "⊳" "snoc"
    , lOption "^:" "iterate" "%." "matmul"
    , lOption "⊗" "outer product" "|:" "transpose"
    , lOption "{.?" "head" "{." "typesafe head"
    , lOption "}.?" "last" "}:" "typesafe init"
    , lOption "⟨z,w⟩" "array literal" "?p,.e1,.e2" "conditional"
    , lOption "/*" "fold all" "ℝ" "i->f conversion"
    , lOption "⧺" "cat" "{:" "typesafe tail"
    , lOption "⊖" "rotate" "sin." "sine"
    , lOption "𝔯" "rand" "⍳" "range (int)"
    , lOption "/ₒ" "fold with seed" "Λₒ" "scan with seed"
    , lOption "{x←y;z}" "let...in" "⊙" "cycle"
    , lOption "˙" "at" "|" "rem"
    , lOption "@." "index of" "di." "diagonal"
    , lOption "%:" "vector mul" "odd." "parity"
    , lOption "~" "reverse" "" ""
    ]

lOption op0 desc0 op1 desc1 =
    rightPad 14 op0 ++ rightPad 25 desc0 ++ rightPad 14 op1 ++ desc1 ++ "\n"

rightPad :: Int -> String -> String
rightPad n str = take n $ str ++ repeat ' '

helpOption :: String -> String -> String -> String
helpOption cmd args desc =
    rightPad 15 cmd ++ rightPad 14 args ++ desc ++ "\n"

ubs :: String -> BSL.ByteString
ubs = encodeUtf8 . TL.pack

disasm :: String -> Repl AlexPosn ()
disasm s = do
    st <- lift $ gets _lex
    a <- lift $ gets _arch
    let d=case a of {X64 -> eDtxt; AArch64{} -> edAtxt}
    case rwP st (ubs s) of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            res <- liftIO $ d i eC
            liftIO $ case res of
                Left err -> putDoc (pretty err <> hardline)
                Right b  -> TIO.putStr b

cR :: String -> Repl AlexPosn ()
cR s = do
    st <- lift $ gets _lex
    case rwP st (ubs s) of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            liftIO $ case eDumpC i eC of
                Left err -> putDoc (pretty err <> hardline)
                Right d  -> putDoc (d <> hardline)

irR :: String -> Repl AlexPosn ()
irR s = do
    st <- lift $ gets _lex
    case rwP st (ubs s) of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            liftIO $ case eDumpIR i eC of
                Left err -> putDoc (pretty err <> hardline)
                Right d  -> putDoc (d <> hardline)

dumpAsm :: String -> Repl AlexPosn ()
dumpAsm s = do
    st <- lift $ gets _lex; a <- lift $ gets _arch
    let dump = case a of {X64 -> eDumpX86; AArch64{} -> eDumpAarch64}
    case rwP st (ubs s) of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            liftIO $ case dump i eC of
                Left err -> putDoc (pretty err <> hardline)
                Right d  -> putDoc (d <> hardline)

tyExprR :: String -> Repl AlexPosn ()
tyExprR s = do
    st <- lift $ gets _lex
    case rwP st (ubs s) of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            liftIO $ case tyClosed i eC of
                Left err      -> putDoc (pretty err <> hardline)
                Right (e,c,_) -> putDoc (prettyC (eAnn e, c) <> hardline)

annR :: String -> Repl AlexPosn ()
annR s = do
    st <- lift $ gets _lex
    case rwP st (ubs s) of
        Left err    -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            liftIO $ case tyClosed i eC of
                Left err      -> putDoc (pretty err <> hardline)
                Right (e,_,_) -> putDoc (prettyTyped e <> hardline)

freeAsm (sz, fp, mp) = freeFunPtr sz fp -- *> traverse_ free mp

inspect :: String -> Repl AlexPosn ()
inspect s = do
    st <- lift $ gets _lex
    a <- lift $ gets _arch
    case rwP st bs of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            case tyClosed i eC of
                Left err -> liftIO $ putDoc (pretty err <> hardline)
                Right (e, _, i') -> do
                    let dbgPrint =
                            case eAnn e of
                                (Arr _ (P [F,F])) -> \p -> (dbgAB :: Ptr (Apple (P2 Double Double)) -> IO T.Text) (castPtr p)
                                (Arr _ F)         -> \p -> (dbgAB :: Ptr (Apple Double) -> IO T.Text) (castPtr p)
                                (Arr _ I)         -> \p -> (dbgAB :: Ptr (Apple Int64) -> IO T.Text) (castPtr p)
                    c <- lift $ gets mf
                    let efp=case a of {X64 -> eFunP i' c; AArch64 m -> eAFunP i' (c,m)}
                    liftIO $ do
                        asm@(_, fp, _) <- efp eC
                        p <- callFFI fp (retPtr undefined) []
                        TIO.putStrLn =<< dbgPrint p
                        free p *> freeAsm asm
        where bs = ubs s

iCtx :: String -> String -> Repl AlexPosn ()
iCtx f fp = do
    st <- lift $ gets _lex
    bs <- liftIO $ BSL.readFile fp
    case tyParseCtx st bs of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (_,i) ->
            let (st', n) = newIdent (AlexPn 0 0 0) (T.pack f) (setM i st)
                x' = parseE st' bs
            in lift $ do {modify (aEe n x'); modify (setL st')}
    where setM i' (_, mm, im) = (i', mm, im)

benchC :: String -> Repl AlexPosn ()
benchC s = case tyParse bs of
    Left err -> liftIO $ putDoc (pretty err <> hardline)
    Right _ -> do
        m <- lift $ gets mf
        liftIO $ benchmark (nfIO (do{(sz,fp) <- ctxFunP m bs; freeFunPtr sz fp}))
    where bs = ubs s

benchE :: String -> Repl AlexPosn ()
benchE s = do
    st <- lift $ gets _lex
    case rwP st bs of   
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            case tyClosed i eC of
                Left err -> liftIO $ putDoc (pretty err <> hardline)
                Right (e, _, i') -> do
                    m <- lift $ gets mf
                    case eAnn e of
                        (Arr _ F) -> do
                            liftIO $ do
                                (sz, fp) <- eFunP i' m eC
                                benchmark (nfIO (do{p<- callFFI fp (retPtr undefined) []; free p}))
                                freeFunPtr sz fp
                        (Arr _ I) -> do
                            liftIO $ do
                                (sz, fp) <- eFunP i' m eC
                                benchmark (nfIO (do{p<- callFFI fp (retPtr undefined) []; free p}))
                                freeFunPtr sz fp
                        I -> do
                            liftIO $ do
                                (sz, fp) <- eFunP i' m eC
                                benchmark (nfIO $ callFFI fp retInt64 [])
                                freeFunPtr sz fp
                        F -> do
                            liftIO $ do
                                (sz, fp) <- eFunP i' m eC
                                benchmark (nfIO $ callFFI fp retCDouble [])
                                freeFunPtr sz fp
    where bs = ubs s

printExpr :: String -> Repl AlexPosn ()
printExpr s = do
    st <- lift $ gets _lex
    a <- lift $ gets _arch
    case rwP st bs of
        Left err -> liftIO $ putDoc (pretty err <> hardline)
        Right (eP, i) -> do
            eC <- eRepl eP
            case first3 (fmap rLi) <$> tyClosed i eC of
                Left err -> liftIO $ putDoc (pretty err <> hardline)
                Right (e, _, i') -> do
                    c <- lift $ gets mf
                    let efp=case a of {X64 -> eFunP i' c; AArch64 ma -> eAFunP i' (c,ma)}
                    case eAnn e of
                        I ->
                          liftIO $ do
                              asm@(_, fp, _) <- efp eC -- TODO: i after tyClosed gets discarded?
                              print =<< callFFI fp retInt64 []
                              freeAsm asm
                        F ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                print =<< callFFI fp retCDouble []
                                freeAsm asm
                        (Arr _ F) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                putDoc.(<>hardline).pretty =<< (peek :: Ptr AF -> IO AF) p
                                free p *> freeAsm asm
                        (Arr _ I) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                putDoc.(<>hardline).pretty =<< (peek :: Ptr AI -> IO AI) p
                                free p *> freeAsm asm
                        A.B ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                cb <- callFFI fp retWord8 []
                                putStrLn (sB cb)
                                freeAsm asm
                            where sB 1 = "#t"; sB 0 = "#f"
                        (P [Arr _ F, Arr _ F]) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                (P2 pa0 pa1) <- (peek :: Ptr (P2 (U Double) (U Double)) -> IO (P2 (U Double) (U Double))) p
                                a0 <- peek pa0; a1 <- peek pa1
                                putDoc$(<>hardline)$pretty (a0, a1)
                                free p *> free pa0 *> free pa1 *> freeAsm asm
                        (P [Arr _ F, Arr _ F, Arr _ F, F]) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                (P4 pa0 pa1 pa2 f) <- (peek :: Ptr (P4 (U Double) (U Double) (U Double) Double) -> IO (P4 (U Double) (U Double) (U Double) Double)) p
                                a0 <- peek pa0; a1 <- peek pa1; a2 <- peek pa2
                                putDoc$(<>hardline)$tupled [pretty a0, pretty a1, pretty a2, pretty f]
                                free p *> free pa0 *> free pa1 *> free pa2 *> freeAsm asm
                        (P [Arr _ F, Arr _ F, F]) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                (P3 pa0 pa1 f) <- (peek :: Ptr (P3 (U Double) (U Double) Double) -> IO (P3 (U Double) (U Double) Double)) p
                                a0 <- peek pa0; a1 <- peek pa1
                                putDoc$(<>hardline)$tupled [pretty a0, pretty a1, pretty f]
                                free p *> free pa0 *> free pa1 *> freeAsm asm
                        (P [F,F,F,F]) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                (P4 x0 x1 x2 x3) <- (peek :: Ptr (P4 Double Double Double Double) -> IO (P4 Double Double Double Double)) p
                                putDoc$(<>hardline)$tupled [pretty x0, pretty x1, pretty x2, pretty x3]
                                freeAsm asm
                        (P [Arr _ (P [F,F,F,F]), F, F]) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                (P3 pa x0 x1) <- (peek :: Ptr (P3 (U (P4 Double Double Double Double)) Double Double) -> IO (P3 (U (P4 Double Double Double Double)) Double Double)) p
                                aϵ <- peek pa
                                putDoc$(<>hardline)$tupled [pretty aϵ, pretty x0, pretty x1]
                                free p *> free pa *> freeAsm asm
                        (P [Arr _ I, Arr _ I]) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                (P2 pa0 pa1) <- (peek :: Ptr (P2 (U Int64) (U Int64)) -> IO (P2 (U Int64) (U Int64))) p
                                a0 <- peek pa0; a1 <- peek pa1
                                putDoc$(<>hardline)$pretty (a0, a1)
                                free p *> free pa0 *> free pa1 *> freeAsm asm
                        (Arr _ (P [F,F])) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                putDoc.(<>hardline).pretty =<< (peek :: U (P2 Double Double) -> IO (Apple (P2 Double Double))) p
                                free p *> freeAsm asm
                        (Arr _ (P [F,F,F])) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                putDoc.(<>hardline).pretty =<< (peek :: U (P3 Double Double Double) -> IO (Apple (P3 Double Double Double))) p
                                free p *> freeAsm asm
                        (Arr _ (P [F,F,F,F])) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                putDoc.(<>hardline).pretty =<< (peek :: U (P4 Double Double Double Double) -> IO (Apple (P4 Double Double Double Double))) p
                                free p *> freeAsm asm
                        (Arr _ (P [I,I])) ->
                            liftIO $ do
                                asm@(_, fp, _) <- efp eC
                                p <- callFFI fp (retPtr undefined) []
                                putDoc.(<>hardline).pretty =<< (peek :: U (P2 Int64 Int64) -> IO (Apple (P2 Int64 Int64))) p
                                free p *> freeAsm asm
                        t -> liftIO $ putDoc (pretty e <+> ":" <+> pretty t <> hardline)
    where bs = ubs s

parseE st bs = fst . either (error "Internal error?") id $ rwP st bs

eRepl :: E AlexPosn -> Repl AlexPosn (E AlexPosn)
eRepl e = do { ees <- lift $ gets ee; pure $ foldLet ees e }
    where foldLet = thread . fmap (\b@(_,eϵ) -> Let (eAnn eϵ) b) where thread = foldr (.) id
