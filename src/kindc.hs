-- Kind2-Core
-- ==========
--
-- This is a Haskell implementation of Kind2's proof kernel. It is based on the
-- Calculus of Constructions, extended with Self-Types and U48 operations. This
-- allows us to express arbitrary inductive types and proofs with a simple core.

import Control.Monad (forM_)
import Data.Char (chr, ord)
import Debug.Trace
import Prelude hiding (LT, GT, EQ)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Parsec ((<|>))
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Text.Parsec as P

-- Kind2 Types
-- -----------

-- Kind Core's AST
data Term

  -- Product: `∀(x: A) B`
  = All String Term (Term -> Term) 

  -- Lambda: `λx f`
  | Lam String (Term -> Term)

  -- Application: 
  | App Term Term

  -- Annotation: `{x: T}`
  | Ann Bool Term Term

  -- Self-Type: `$(x: A) B`
  | Slf String Term (Term -> Term)

  -- Self-Inst: `~x`
  | Ins Term

  -- Top-Level Reference
  | Ref String

  -- Local let-definition
  | Let String Term (Term -> Term)

  -- Local use-definition
  | Use String Term (Term -> Term)

  -- Type : Type
  | Set

  -- U48 Type
  | U48

  -- U48 Value
  | Num Int

  -- U48 Binary Operation
  | Op2 Oper Term Term

  -- U48 Elimination
  | Swi String Term Term (Term -> Term) (Term -> Term)

  -- Inspection Hole
  | Hol String [Term]

  -- Unification Metavar
  | Met Int [Term]

  -- Variable
  | Var String Int

  -- Source Location
  | Src Int Term

  -- Text Literal (sugar)
  | Txt String

  -- Nat Literal (sugar)
  | Nat Integer

-- Numeric Operators
data Oper
  = ADD | SUB | MUL | DIV
  | MOD | EQ  | NE  | LT
  | GT  | LTE | GTE | AND
  | OR  | XOR | LSH | RSH

-- Book of Definitions
type Book = M.Map String Term

-- Type-Checker Outputs
data Info
  = Found String Term [Term] Int
  | Solve Int Term Int
  | Error Int Term Term Term Int
  | Vague String
  | Print Term Int

-- Unification Solutions
type Fill = IM.IntMap Term

-- Checker State
data Check = Check Int Term Term Int -- postponed check
data State = State Book Fill [Check] [Info] -- state type
data Res a = Done State a | Fail State -- result type
data Env a = Env (State -> Res a) -- monadic checker

-- Environment
-- -----------

infoIsSolve :: Info -> Bool
infoIsSolve (Solve _ _ _) = True
infoIsSolve _             = False

envBind :: Env a -> (a -> Env b) -> Env b
envBind (Env a) b = Env $ \state -> case a state of
  Done state' value -> let Env b' = b value in b' state'
  Fail state'       -> Fail state'

envPure :: a -> Env a
envPure a = Env $ \state -> Done state a

envFail :: Env a
envFail = Env $ \state -> Fail state

envRun :: Env a -> Book -> Res a
envRun (Env chk) book = chk (State book IM.empty [] [])

envLog :: Info -> Env Int
envLog log = Env $ \(State book fill susp logs) -> Done (State book fill susp (log : logs)) 1

envSnapshot :: Env State
envSnapshot = Env $ \state -> Done state state

envRewind :: State -> Env Int
envRewind state = Env $ \_ -> Done state 0

envSusp :: Check -> Env ()
envSusp chk = Env $ \(State book fill susp logs) -> Done (State book fill (susp ++ [chk]) logs) ()

envFill :: Int -> Term -> Env ()
envFill k v = Env $ \(State book fill susp logs) -> Done (State book (IM.insert k v fill) susp logs) ()

envGetFill :: Env Fill
envGetFill = Env $ \(State book fill susp logs) -> Done (State book fill susp logs) fill

envGetBook :: Env Book
envGetBook = Env $ \(State book fill susp logs) -> Done (State book fill susp logs) book

envTakeSusp :: Env [Check]
envTakeSusp = Env $ \(State book fill susp logs) -> Done (State book fill [] logs) susp

instance Functor Env where
  fmap f (Env chk) = Env $ \logs -> case chk logs of
    Done logs' a -> Done logs' (f a)
    Fail logs' -> Fail logs'

instance Applicative Env where
  pure = envPure
  (Env chkF) <*> (Env chkA) = Env $ \logs -> case chkF logs of
    Done logs' f -> case chkA logs' of
      Done logs'' a -> Done logs'' (f a)
      Fail logs'' -> Fail logs''
    Fail logs' -> Fail logs'

instance Monad Env where
  (Env a) >>= b = envBind (Env a) b

-- Binding
-- -------

bind :: Term -> Term
bind term = go term [] where
  go (All nam inp bod) ctx = All nam (go inp ctx) (\x -> go (bod (Var nam 0)) ((nam, x) : ctx))
  go (Lam nam bod)     ctx = Lam nam (\x -> go (bod (Var nam 0)) ((nam, x) : ctx))
  go (App fun arg)     ctx = App (go fun ctx) (go arg ctx)
  go (Ann chk val typ) ctx = Ann chk (go val ctx) (go typ ctx)
  go (Slf nam typ bod) ctx = Slf nam (go typ ctx) (\x -> go (bod (Var nam 0)) ((nam, x) : ctx))
  go (Ins val)         ctx = Ins (go val ctx)
  go (Ref nam)         ctx = case lookup nam ctx of { Just x -> x; Nothing -> Ref nam }
  go (Let nam val bod) ctx = Let nam (go val ctx) (\x -> go (bod (Var nam 0)) ((nam, x) : ctx))
  go (Use nam val bod) ctx = Use nam (go val ctx) (\x -> go (bod (Var nam 0)) ((nam, x) : ctx))
  go Set               ctx = Set
  go U48               ctx = U48
  go (Num val)         ctx = Num val
  go (Op2 opr fst snd) ctx = Op2 opr (go fst ctx) (go snd ctx)
  go (Swi nam x z s p) ctx = Swi nam (go x ctx) (go z ctx) (\k -> go (s (Var (nam ++ "-1") 0)) ((nam ++ "-1", k) : ctx)) (\k -> go (p (Var nam 0)) ((nam, k) : ctx))
  go (Txt txt)         ctx = Txt txt
  go (Nat val)         ctx = Nat val
  go (Hol nam ctxs)    ctx = Hol nam (map (\t -> go t ctx) ctxs)
  go (Met uid spn)     ctx = Met uid (map (\t -> go t ctx) spn)
  go (Var nam idx)     ctx = Var nam idx
  go (Src src val)     ctx = Src src (go val ctx)

-- Evaluation
-- ----------

-- Evaluation levels:
-- - 0: reduces refs: never
-- - 1: reduces refs: redexes
-- - 2: reduces refs: always

reduce :: Book -> Fill -> Int -> Term -> Term
reduce book fill lv (App fun arg)     = reduceApp book fill lv (reduce book fill lv fun) arg
reduce book fill lv (Ann chk val typ) = reduce book fill lv val
reduce book fill lv (Ins val)         = reduce book fill lv val
reduce book fill lv (Ref nam)         = reduceRef book fill lv nam
reduce book fill lv (Let nam val bod) = reduce book fill lv (bod val)
reduce book fill lv (Use nam val bod) = reduce book fill lv (bod val)
reduce book fill lv (Op2 opr fst snd) = reduceOp2 book fill lv opr (reduce book fill lv fst) (reduce book fill lv snd)
reduce book fill lv (Swi nam x z s p) = reduceSwi book fill lv nam (reduce book fill lv x) z s p
reduce book fill lv (Txt txt)         = reduceTxt book fill lv txt
reduce book fill lv (Nat val)         = reduceNat book fill lv val
reduce book fill lv (Src src val)     = reduce book fill lv val
reduce book fill lv (Met uid spn)     = reduceMet book fill lv uid spn
reduce book fill lv val               = val

reduceApp :: Book -> Fill -> Int -> Term -> Term -> Term
reduceApp book fill 2  (Ref nam)     arg = reduceApp book fill 2 (reduceRef book fill 2 nam) arg
reduceApp book fill 1  (Ref nam)     arg = reduceApp book fill 1 (reduceRef book fill 1 nam) arg
reduceApp book fill lv (Met uid spn) arg = reduce book fill lv (Met uid (spn ++ [arg]))
reduceApp book fill lv (Lam nam bod) arg = reduce book fill lv (bod (reduce book fill 0 arg))
reduceApp book fill lv fun arg           = App fun arg

reduceMet :: Book -> Fill -> Int -> Int -> [Term] -> Term
reduceMet book fill lv uid spn = case IM.lookup uid fill of
  Just val -> reduce book fill lv (reduceMetSpine val spn)
  Nothing  -> Met uid spn

reduceMetSpine :: Term -> [Term] -> Term
reduceMetSpine val []       = val
reduceMetSpine val (x : xs) = reduceMetSpine (App val x) xs

reduceOp2 :: Book -> Fill -> Int -> Oper -> Term -> Term -> Term
reduceOp2 book fill 1  op  (Ref nam) (Num snd) = reduceOp2 book fill 1 op (reduceRef book fill 1 nam) (Num snd)
reduceOp2 book fill 2  op  (Ref nam) (Num snd) = reduceOp2 book fill 2 op (reduceRef book fill 2 nam) (Num snd)
reduceOp2 book fill 1  op  (Num fst) (Ref nam) = reduceOp2 book fill 1 op (Num fst) (reduceRef book fill 1 nam)
reduceOp2 book fill 2  op  (Num fst) (Ref nam) = reduceOp2 book fill 2 op (Num fst) (reduceRef book fill 2 nam)
reduceOp2 book fill lv ADD (Num fst) (Num snd) = Num (fst + snd)
reduceOp2 book fill lv SUB (Num fst) (Num snd) = Num (fst - snd)
reduceOp2 book fill lv MUL (Num fst) (Num snd) = Num (fst * snd)
reduceOp2 book fill lv DIV (Num fst) (Num snd) = Num (div fst snd)
reduceOp2 book fill lv MOD (Num fst) (Num snd) = Num (mod fst snd)
reduceOp2 book fill lv EQ  (Num fst) (Num snd) = if fst == snd then Num 1 else Num 0
reduceOp2 book fill lv NE  (Num fst) (Num snd) = if fst /= snd then Num 1 else Num 0
reduceOp2 book fill lv LT  (Num fst) (Num snd) = if fst < snd then Num 1 else Num 0
reduceOp2 book fill lv GT  (Num fst) (Num snd) = if fst > snd then Num 1 else Num 0
reduceOp2 book fill lv LTE (Num fst) (Num snd) = if fst <= snd then Num 1 else Num 0
reduceOp2 book fill lv GTE (Num fst) (Num snd) = if fst >= snd then Num 1 else Num 0
reduceOp2 book fill lv opr fst snd             = Op2 opr fst snd

reduceSwi :: Book -> Fill -> Int -> String -> Term -> Term -> (Term -> Term) -> (Term -> Term) -> Term
reduceSwi book fill 2  nam (Ref x)             z s p = reduceSwi book fill 2 nam (reduceRef book fill 2 x) z s p
reduceSwi book fill 1  nam (Ref x)             z s p = reduceSwi book fill 1 nam (reduceRef book fill 1 x) z s p
reduceSwi book fill lv nam (Num 0)             z s p = reduce book fill lv z
reduceSwi book fill lv nam (Num n)             z s p = reduce book fill lv (s (Num (n - 1)))
reduceSwi book fill lv nam (Op2 ADD (Num 1) k) z s p = reduce book fill lv (s k)
reduceSwi book fill lv nam val                 z s p = Swi nam val z s p

reduceRef :: Book -> Fill -> Int -> String -> Term
reduceRef book fill 2  nam = case M.lookup nam book of
  Just val -> reduce book fill 2 val
  Nothing  -> error $ "Undefined reference: " ++ nam
reduceRef book fill 1  nam = Ref nam
reduceRef book fill lv nam = Ref nam

reduceTxt :: Book -> Fill -> Int -> String -> Term
reduceTxt book fill lv []     = reduce book fill lv (Ref "String/cons")
reduceTxt book fill lv (x:xs) = reduce book fill lv (App (App (Ref "String/nil") (Num (ord x))) (Txt xs))

reduceNat :: Book -> Fill -> Int -> Integer -> Term
reduceNat book fill lv 0 = Ref "Nat/zero"
reduceNat book fill lv n = App (Ref "Nat/succ") (reduceNat book fill lv (n - 1))

-- Normalization
-- -------------

normal :: Book -> Fill -> Int -> Term -> Int -> Term
normal book fill lv term dep = normalGo book fill lv (reduce book fill lv term) dep where
  normalGo book fill lv (All nam inp bod) dep = All nam (normal book fill lv inp dep) (\x -> normal book fill lv (bod (Var nam dep)) (dep + 1))
  normalGo book fill lv (Lam nam bod)     dep = Lam nam (\x -> normal book fill lv (bod (Var nam dep)) (dep + 1))
  normalGo book fill lv (App fun arg)     dep = App (normal book fill lv fun dep) (normal book fill lv arg dep)
  normalGo book fill lv (Ann chk val typ) dep = Ann chk (normal book fill lv val dep) (normal book fill lv typ dep)
  normalGo book fill lv (Slf nam typ bod) dep = Slf nam typ (\x -> normal book fill lv (bod (Var nam dep)) (dep + 1))
  normalGo book fill lv (Ins val)         dep = Ins (normal book fill lv val dep)
  normalGo book fill lv (Ref nam)         dep = Ref nam
  normalGo book fill lv (Let nam val bod) dep = Let nam (normal book fill lv val dep) (\x -> normal book fill lv (bod (Var nam dep)) (dep + 1))
  normalGo book fill lv (Use nam val bod) dep = Use nam (normal book fill lv val dep) (\x -> normal book fill lv (bod (Var nam dep)) (dep + 1))
  normalGo book fill lv (Hol nam ctx)     dep = Hol nam ctx
  normalGo book fill lv Set               dep = Set
  normalGo book fill lv U48               dep = U48
  normalGo book fill lv (Num val)         dep = Num val
  normalGo book fill lv (Op2 opr fst snd) dep = Op2 opr (normal book fill lv fst dep) (normal book fill lv snd dep)
  normalGo book fill lv (Swi nam x z s p) dep = Swi nam (normal book fill lv x dep) (normal book fill lv z dep) (\k -> normal book fill lv (s (Var (nam ++ "-1") dep)) dep) (\k -> normal book fill lv (p (Var nam dep)) dep)
  normalGo book fill lv (Txt val)         dep = Txt val
  normalGo book fill lv (Nat val)         dep = Nat val
  normalGo book fill lv (Var nam idx)     dep = Var nam idx
  normalGo book fill lv (Src src val)     dep = Src src (normal book fill lv val dep)
  normalGo book fill lv (Met uid spn)     dep = Met uid spn -- TODO: normalize spine

-- Equality
-- --------

-- Conversion checking works as follows:
-- 1. Two terms are equal if their wnf's are structurally identical
-- 2. Otherwise, they're equal if they're similar (component-wise equal)
-- This allows us to always identify two terms that have the same normal form,
-- while also allowing us to return earlier, if they become identical at any
-- point in the reduction. Note that, for Self types, the similarity checker
-- will "un-reduce" from `$(x: (T a b)) body` to `(T a b)`, avoiding loops.

equal :: Term -> Term -> Int -> Env Bool
equal a b dep = do
  -- trace ("== " ++ termStr a dep ++ "\n.. " ++ termStr b dep) $ do
    book <- envGetBook
    fill <- envGetFill
    let a' = reduce book fill 2 a
    let b' = reduce book fill 2 b
    same <- tryIdentical a' b' dep
    if same then do
      return True
    else do
      similar a' b' dep

tryIdentical :: Term -> Term -> Int -> Env Bool
tryIdentical a b dep = do
  state <- envSnapshot
  equal <- identical a b dep
  if equal
    then envPure True
    else envRewind state >> envPure False

similar :: Term -> Term -> Int -> Env Bool
similar a b dep =
  -- trace ("~~ " ++ termStr a dep ++ "\n.. " ++ termStr b dep) $ do
  go a b dep
  where
  go (All aNam aInp aBod) (All bNam bInp bBod) dep = do
    eInp <- equal aInp bInp dep
    eBod <- equal (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
    envPure (eInp && eBod)
  go (Lam aNam aBod) (Lam bNam bBod) dep =
    equal (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
  go (App aFun aArg) (App bFun bArg) dep = do
    eFun <- similar aFun bFun dep
    eArg <- equal aArg bArg dep
    envPure (eFun && eArg)
  go (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep = do
    book <- envGetBook
    similar (reduce book IM.empty 0 aTyp) (reduce book IM.empty 0 bTyp) dep
  go (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep = do
    eFst <- equal aFst bFst dep
    eSnd <- equal aSnd bSnd dep
    envPure (eFst && eSnd)
  go (Swi aNam aX aZ aS aP) (Swi bNam bX bZ bS bP) dep = do
    eX <- equal aX bX dep
    eZ <- equal aZ bZ dep
    eS <- equal (aS (Var (aNam ++ "-1") dep)) (bS (Var (bNam ++ "-1") dep)) dep
    eP <- equal (aP (Var aNam dep)) (bP (Var bNam dep)) dep
    envPure (eX && eZ && eS && eP)
  go a b dep = identical a b dep

identical :: Term -> Term -> Int -> Env Bool
identical a b dep = go a b dep where
  go (All aNam aInp aBod) (All bNam bInp bBod) dep = do
    iInp <- identical aInp bInp dep
    iBod <- identical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
    return (iInp && iBod)
  go (Lam aNam aBod) (Lam bNam bBod) dep =
    identical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
  go (App aFun aArg) (App bFun bArg) dep = do
    iFun <- identical aFun bFun dep
    iArg <- identical aArg bArg dep
    return (iFun && iArg)
  go (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
    identical aTyp bTyp dep
  go (Ins aVal) b dep =
    identical aVal b dep
  go a (Ins bVal) dep =
    identical a bVal dep
  go (Let aNam aVal aBod) b dep =
    identical (aBod aVal) b dep
  go a (Let bNam bVal bBod) dep =
    identical a (bBod bVal) dep
  go (Use aNam aVal aBod) b dep =
    identical (aBod aVal) b dep
  go a (Use bNam bVal bBod) dep =
    identical a (bBod bVal) dep
  go Set Set dep =
    return True
  go (Ann chk aVal aTyp) b dep =
    identical aVal b dep
  go a (Ann chk bVal bTyp) dep =
    identical a bVal dep
  go a (Met bUid bSpn) dep =
    unify bUid bSpn a dep
  go (Met aUid aSpn) b dep =
    unify aUid aSpn b dep
  go (Hol aNam aCtx) b dep =
    return True
  go a (Hol bNam bCtx) dep =
    return True
  go U48 U48 dep =
    return True
  go (Num aVal) (Num bVal) dep =
    return (aVal == bVal)
  go (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep = do
    iFst <- identical aFst bFst dep
    iSnd <- identical aSnd bSnd dep
    return (iFst && iSnd)
  go (Swi aNam aX aZ aS aP) (Swi bNam bX bZ bS bP) dep = do
    iX <- identical aX bX dep
    iZ <- identical aZ bZ dep
    iS <- identical (aS (Var (aNam ++ "-1") dep)) (bS (Var (bNam ++ "-1") dep)) dep
    iP <- identical (aP (Var aNam dep)) (bP (Var bNam dep)) dep
    return (iX && iZ && iS && iP)
  go (Txt aTxt) (Txt bTxt) dep =
    return (aTxt == bTxt)
  go (Nat aVal) (Nat bVal) dep =
    return (aVal == bVal)
  go (Src aSrc aVal) b dep =
    identical aVal b dep
  go a (Src bSrc bVal) dep =
    identical a bVal dep
  go (Ref aNam) (Ref bNam) dep =
    return (aNam == bNam)
  go (Var aNam aIdx) (Var bNam bIdx) dep =
    return (aIdx == bIdx)
  go a b dep =
    return False

-- Unification
-- -----------

-- The unification algorithm is a simple pattern unifier, based on smalltt:
-- > https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/Main.hs
-- The pattern unification problem provides a solution to the following problem:
--   (?X x y z ...) = K
-- When:
--   1. The LHS spine, `x y z ...`, consists of distinct variables.
--   2. Every free var of the RHS, `K`, occurs in the spine.
--   3. The LHS hole, `?A`, doesn't occur in the RHS, `K`.
-- If these conditions are met, ?X is solved as:
--   ?X = λx λy λz ... K
-- In this implementation, checking condition `2` is not necessary, because we
-- subst holes directly where they occur (rather than on top-level definitions),
-- so, it is impossible for unbound variables to appear.

-- If possible, solves a `(?X x y z ...) = K` problem, generating a subst.
unify :: Int -> [Term] -> Term -> Int -> Env Bool
unify uid spn b dep = do
  book <- envGetBook
  fill <- envGetFill
  let unsolved = not (IM.member uid fill) -- is this hole not already solved?
  let solvable = unifyValid fill spn [] -- does the spine satisfies conditions?
  let no_loops = not $ unifyIsRec book fill uid b dep -- is the solution not recursive?
  -- trace ("unify: " ++ show uid ++ " " ++ termStr b dep ++ " | " ++ show unsolved ++ " " ++ show solvable ++ " " ++ show no_loops) $ do
  do
    -- If all is ok, generate the solution and return true
    if unsolved && solvable && no_loops then do
      let solution = unifySolve book fill uid spn b
      envFill uid solution
      return True
    -- Otherwise, return true iff both are identical metavars
    else case b of
      (Met bUid bSpn) -> return $ uid == bUid
      other           -> return False

-- Checks if a problem is solveable by pattern unification.
unifyValid :: Fill -> [Term] -> [Int] -> Bool
unifyValid fill []        vars = True
unifyValid fill (x : spn) vars = case reduce M.empty fill 0 x of
  (Var nam idx) -> not (elem idx vars) && unifyValid fill spn (idx : vars)
  otherwise     -> False
  
-- Generates the solution, adding binders and renaming variables.
unifySolve :: Book -> Fill -> Int -> [Term] -> Term -> Term
unifySolve book fill uid []        b = b
unifySolve book fill uid (x : spn) b = case reduce book fill 0 x of
  (Var nam idx) -> Lam nam $ \x -> unifySubst idx x (unifySolve book fill uid spn b)
  otherwise     -> error "unreachable"         

-- Checks if a hole uid occurs recursively inside a term
unifyIsRec :: Book -> Fill -> Int -> Term -> Int -> Bool
unifyIsRec book fill uid (All nam inp bod) dep = unifyIsRec book fill uid inp dep || unifyIsRec book fill uid (bod (Var nam dep)) (dep + 1)
unifyIsRec book fill uid (Lam nam bod)     dep = unifyIsRec book fill uid (bod (Var nam dep)) (dep + 1)
unifyIsRec book fill uid (App fun arg)     dep = unifyIsRec book fill uid fun dep || unifyIsRec book fill uid arg dep
unifyIsRec book fill uid (Ann chk val typ) dep = unifyIsRec book fill uid val dep || unifyIsRec book fill uid typ dep
unifyIsRec book fill uid (Slf nam typ bod) dep = unifyIsRec book fill uid typ dep || unifyIsRec book fill uid (bod (Var nam dep)) (dep + 1)
unifyIsRec book fill uid (Ins val)         dep = unifyIsRec book fill uid val dep
unifyIsRec book fill uid (Let nam val bod) dep = unifyIsRec book fill uid val dep || unifyIsRec book fill uid (bod (Var nam dep)) (dep + 1)
unifyIsRec book fill uid (Use nam val bod) dep = unifyIsRec book fill uid val dep || unifyIsRec book fill uid (bod (Var nam dep)) (dep + 1)
unifyIsRec book fill uid (Hol nam ctx)     dep = False
unifyIsRec book fill uid (Op2 opr fst snd) dep = unifyIsRec book fill uid fst dep || unifyIsRec book fill uid snd dep
unifyIsRec book fill uid (Swi nam x z s p) dep = unifyIsRec book fill uid x dep || unifyIsRec book fill uid z dep || unifyIsRec book fill uid (s (Var (nam ++ "-1") dep)) (dep + 1) || unifyIsRec book fill uid (p (Var nam dep)) dep
unifyIsRec book fill uid (Src src val)     dep = unifyIsRec book fill uid val dep
unifyIsRec book fill uid (Met bUid bSpn)   dep = case reduceMet book fill 2 bUid bSpn of
  (Met bUid bSpn) -> uid == bUid
  term            -> unifyIsRec book fill uid term dep
unifyIsRec book fill uid _                 dep = False

-- Substitutes a Bruijn level variable by a `neo` value in `term`.
unifySubst :: Int -> Term -> Term -> Term
unifySubst lvl neo (All nam inp bod) = All nam (unifySubst lvl neo inp) (\x -> unifySubst lvl neo (bod x))
unifySubst lvl neo (Lam nam bod)     = Lam nam (\x -> unifySubst lvl neo (bod x))
unifySubst lvl neo (App fun arg)     = App (unifySubst lvl neo fun) (unifySubst lvl neo arg)
unifySubst lvl neo (Ann chk val typ) = Ann chk (unifySubst lvl neo val) (unifySubst lvl neo typ)
unifySubst lvl neo (Slf nam typ bod) = Slf nam (unifySubst lvl neo typ) (\x -> unifySubst lvl neo (bod x))
unifySubst lvl neo (Ins val)         = Ins (unifySubst lvl neo val)
unifySubst lvl neo (Ref nam)         = Ref nam
unifySubst lvl neo (Let nam val bod) = Let nam (unifySubst lvl neo val) (\x -> unifySubst lvl neo (bod x))
unifySubst lvl neo (Use nam val bod) = Use nam (unifySubst lvl neo val) (\x -> unifySubst lvl neo (bod x))
unifySubst lvl neo (Met uid spn)     = Met uid (map (unifySubst lvl neo) spn)
unifySubst lvl neo (Hol nam ctx)     = Hol nam (map (unifySubst lvl neo) ctx)
unifySubst lvl neo Set               = Set
unifySubst lvl neo U48               = U48
unifySubst lvl neo (Num n)           = Num n
unifySubst lvl neo (Op2 opr fst snd) = Op2 opr (unifySubst lvl neo fst) (unifySubst lvl neo snd)
unifySubst lvl neo (Swi nam x z s p) = Swi nam (unifySubst lvl neo x) (unifySubst lvl neo z) (\k -> unifySubst lvl neo (s k)) (\k -> unifySubst lvl neo (p k))
unifySubst lvl neo (Txt txt)         = Txt txt
unifySubst lvl neo (Nat val)         = Nat val
unifySubst lvl neo (Var nam idx)     = if lvl == idx then neo else Var nam idx
unifySubst lvl neo (Src src val)     = Src src (unifySubst lvl neo val)

-- Type-Checking
-- -------------

-- Note that, for type-checking, instead of passing down contexts (as usual), we
-- just annotate variables (with a `{x: T}` type hint) and check. This has the
-- same effect, while being slightly more efficient. Type derivations comments
-- are written in this style too.

-- ### Inference

infer :: Term -> Int -> Env Term
infer term dep =
  -- trace ("infer: " ++ termStr term dep) $
  inferGo term dep

inferGo :: Term -> Int -> Env Term

-- inp : Set
-- (bod {nam: inp}) : Set
-- ----------------------- function
-- (∀(nam: inp) bod) : Set
inferGo (All nam inp bod) dep = do
  envSusp (Check 0 inp Set dep)
  envSusp (Check 0 (bod (Ann False (Var nam dep) inp)) Set (dep + 1))
  return Set

-- fun : ∀(ftyp_nam: ftyp_inp) ftyp_bod
-- arg : ftyp_inp
-- ------------------------------------ application
-- (fun arg) : (ftyp_bod arg)
inferGo (App fun arg) dep = do
  ftyp <- infer fun dep
  book <- envGetBook
  fill <- envGetFill
  case reduce book fill 2 ftyp of
    (All ftyp_nam ftyp_inp ftyp_bod) -> do
      envSusp (Check 0 arg ftyp_inp dep)
      return $ ftyp_bod arg
    otherwise -> do
      envLog (Error 0 (Hol "function" []) ftyp (App fun arg) dep)
      envFail

-- 
-- ---------------- annotation (infer)
-- {val: typ} : typ
inferGo (Ann chk val typ) dep = do
  if chk then do
    check 0 val typ dep
  else do
    return ()
  return typ

-- (bod {nam: typ}) : Set
-- ----------------------- self-type
-- ($(nam: typ) bod) : Set
inferGo (Slf nam typ bod) dep = do
  envSusp (Check 0 (bod (Ann False (Var nam dep) typ)) Set (dep + 1))
  return Set

-- val : $(vtyp_nam: vtyp_typ) vtyp_bod
-- ------------------------------------ self-inst (infer)
-- ~val : (vtyp_bod (~val))
inferGo (Ins val) dep = do
  vtyp <- infer val dep
  book <- envGetBook
  fill <- envGetFill
  case reduce book fill 2 vtyp of
    (Slf vtyp_nam vtyp_typ vtyp_bod) -> do
      return $ vtyp_bod (Ins val)
    otherwise -> do
      envLog (Error 0 (Hol "self-type" []) vtyp (Ins val) dep)
      envFail

-- val : T
-- ----------------- reference
-- (Ref nam) : T
inferGo (Ref nam) dep = do
  book <- envGetBook
  case M.lookup nam book of
    Just val -> infer val dep
    Nothing  -> do
      envLog (Error 0 (Hol "undefined_reference" []) (Hol "unknown_type" []) (Ref nam) dep)
      envFail

-- ...
-- --------- type-in-type
-- Set : Set
inferGo Set dep = do
  return Set

-- ...
-- --------- U48-type
-- U48 : Set
inferGo U48 dep = do
  return Set

-- ...
-- ----------- U48-value
-- <num> : U48
inferGo (Num num) dep = do
  return U48

-- ...
-- -------------- String-literal
-- "txt" : String
inferGo (Txt txt) dep = do
  return (Ref "String")

-- ...
-- --------- Nat-literal
-- 123 : Nat
inferGo (Nat val) dep = do
  return (Ref "Nat")

-- fst : U48
-- snd : U48
-- ----------------- U48-operator
-- (+ fst snd) : U48
inferGo (Op2 opr fst snd) dep = do
  envSusp (Check 0 fst U48 dep)
  envSusp (Check 0 snd U48 dep)
  return U48

-- x : U48
-- p : U48 -> Set
-- z : (p 0)
-- s : (n: U48) -> (p (+ 1 n))
-- ------------------------------------- U48-elim
-- (switch x { 0: z ; _: s }: p) : (p x)
inferGo (Swi nam x z s p) dep = do
  envSusp (Check 0 x U48 dep)
  envSusp (Check 0 (p (Ann False (Var nam dep) U48)) Set dep)
  envSusp (Check 0 z (p (Num 0)) dep)
  envSusp (Check 0 (s (Ann False (Var (nam ++ "-1") dep) U48)) (p (Op2 ADD (Num 1) (Var (nam ++ "-1") dep))) (dep + 1))
  return (p x)

-- val : typ
-- (bod {nam: typ}) : T
-- ------------------------ let-binder (infer)
-- (let nam = val; bod) : T
inferGo (Let nam val bod) dep = do
  typ <- infer val dep
  infer (bod (Ann False (Var nam dep) typ)) dep

-- (bod val) : T
-- ------------------------ use-binder (infer)
-- (use nam = val; bod) : T
inferGo (Use nam val bod) dep = do
  infer (bod val) dep

-- Can't Infer λ
inferGo (Lam nam bod) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_lambda" []) (Lam nam bod) dep)
  envFail

-- Can't Infer ?A
inferGo (Hol nam ctx) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_hole" []) (Hol nam ctx) dep)
  envFail

-- Can't Infer _
inferGo (Met uid spn) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_meta" []) (Met uid spn) dep)
  envFail

-- Can't Infer Var
inferGo (Var nam idx) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_variable" []) (Var nam idx) dep)
  envFail

-- Src-passthrough
inferGo (Src src val) dep = do
  infer val dep

check :: Int -> Term -> Term -> Int -> Env ()
check src val typ dep =
  -- trace ("check: " ++ termStr val dep ++ "\n    :: " ++ termStr typ dep) $
  checkGo src val typ dep

-- ### Checking

checkGo :: Int -> Term -> Term -> Int -> Env ()

-- (bod {typ_nam: typ_inp}) : (typ_bod {nam: typ_inp})
-- --------------------------------------------------- lambda
-- (λnam bod) : (∀(typ_nam: typ_inp) typ_bod)
checkGo src (Lam nam bod) typx dep = do
  book <- envGetBook
  fill <- envGetFill
  case reduce book fill 2 typx of
    (All typ_nam typ_inp typ_bod) -> do
      let ann  = Ann False (Var nam dep) typ_inp
      let term = bod ann
      let typx = typ_bod ann
      check 0 term typx (dep + 1)
    otherwise -> do
      infer (Lam nam bod) dep
      return ()

-- val : (typ_bod ~val)
-- ---------------------------------- self-inst (check)
-- ~val : $(typ_nam: typ_typ) typ_bod
checkGo src (Ins val) typx dep = do
  book <- envGetBook
  fill <- envGetFill
  case reduce book fill 2 typx of
    Slf typ_nam typ_typ typ_bod -> do
      check 0 val (typ_bod (Ins val)) dep
    _ -> do
      infer (Ins val) dep
      return ()

-- val : typ
-- (bod {nam: typ}) : T
-- ------------------------ let-binder (check)
-- (let nam = val; bod) : T
checkGo src (Let nam val bod) typx dep = do
  typ <- infer val dep
  check 0 (bod (Ann False (Var nam dep) typ)) typx dep

-- (bod val) : T
-- ------------------------ use-binder (check)
-- (use nam = val; bod) : T
checkGo src (Use nam val bod) typx dep = do
  check 0 (bod val) typx dep

-- ...
-- ------ inspection
-- ?A : T
checkGo src (Hol nam ctx) typx dep = do
  envLog (Found nam typx ctx dep)
  return ()

-- ...
-- ----- metavar
-- _ : T
checkGo src (Met uid spn) typx dep = do
  return ()

-- ...
-- ---------------- annotation (check)
-- {val: typ} : typ
checkGo src (Ann chk val typ) typx dep = do
  checkCompare src val typ typx dep
  if chk then do
    check src val typ dep
  else do
    return ()

-- val : T
-- ------- source (just skipped)
-- val : T
checkGo _ (Src src val) typx dep = do
  check src val typx dep

-- A == B
-- val : A
-- -------
-- val : B
checkGo src term typx dep = do
  infer <- infer term dep
  checkCompare src term typx infer dep

-- Checks types equality and reports
checkCompare src term expected detected dep = do
  equal <- equal expected detected dep
  if equal then do
    susp <- envTakeSusp
    forM_ susp $ \(Check src val typ dep) -> do
      checkGo src val typ dep
    return ()
  else do
    envLog (Error src expected detected term dep)
    envFail

checkDef :: Term -> Env ()
checkDef (Ref nam) = do
  book <- envGetBook
  case M.lookup nam book of
    Just val -> case val of
      Ann chk val typ -> check 0 val typ 0 >> return ()
      Ref nm2         -> checkDef (Ref nm2)
      _               -> infer val 0 >> return ()
    Nothing  -> do
      envLog (Error 0 (Hol "undefined_reference" []) (Hol "unknown_type" []) (Ref nam) 0)
      envFail
checkDef other = error "invalid top-level definition"

-- Stringification
-- ---------------

termStr :: Term -> Int -> String
termStr (All nam inp bod) dep =
  let nam' = nam
      inp' = termStr inp dep
      bod' = termStr (bod (Var nam dep)) (dep + 1)
  in concat ["∀(" , nam' , ": " , inp' , ") " , bod']
termStr (Lam nam bod) dep =
  let nam' = nam
      bod' = termStr (bod (Var nam dep)) (dep + 1)
  in concat ["λ" , nam' , " " , bod']
termStr (App fun arg) dep =
  let fun' = termStr fun dep
      arg' = termStr arg dep
  in concat ["(" , fun' , " " , arg' , ")"]
termStr (Ann chk val typ) dep =
  let val' = termStr val dep
      typ' = termStr typ dep
  in concat ["{" , val' , ": " , typ' , "}"]
termStr (Slf nam typ bod) dep =
  termStr typ dep
termStr (Ins val) dep =
  let val' = termStr val dep
  in concat ["~" , val']
termStr (Ref nam) dep = nam
termStr (Let nam val bod) dep =
  let nam' = nam
      val' = termStr val dep
      bod' = termStr (bod (Var nam dep)) (dep + 1)
  in concat ["let " , nam' , " = " , val' , "; " , bod']
termStr (Use nam val bod) dep =
  let nam' = nam
      val' = termStr val dep
      bod' = termStr (bod (Var nam dep)) (dep + 1)
  in concat ["use " , nam' , " = " , val' , "; " , bod']
termStr Set dep = "*"
termStr U48 dep = "U48"
termStr (Num val) dep =
  let val' = show val
  in concat [val']
termStr (Op2 opr fst snd) dep =
  let opr' = operStr opr
      fst' = termStr fst dep
      snd' = termStr snd dep
  in concat ["(" , opr' , " " , fst' , " " , snd' , ")"]
termStr (Swi nam x z s p) dep =
  let nam' = nam
      x'   = termStr x dep
      z'   = termStr z dep
      s'   = termStr (s (Var (nam ++ "-1") dep)) (dep + 1)
      p'   = termStr (p (Var nam dep)) dep
  in concat ["switch " , nam' , " = " , x' , " { 0: " , z' , " _: " , s' , " }: " , p']
termStr (Txt txt) dep = concat ["\"" , txt , "\""]
termStr (Nat val) dep = show val
termStr (Hol nam ctx) dep = concat ["?" , nam]
termStr (Met uid spn) dep = concat ["(_", strSpn (reverse spn) dep, ")"]
termStr (Var nam idx) dep = nam
termStr (Src src val) dep = termStr val dep

strSpn :: [Term] -> Int -> String
strSpn []       dep = ""
strSpn (x : xs) dep = concat [" ", termStr x dep, strSpn xs dep]

operStr :: Oper -> String
operStr ADD = "+"
operStr SUB = "-"
operStr MUL = "*"
operStr DIV = "/"
operStr MOD = "%"
operStr EQ  = "=="
operStr NE  = "!="
operStr LT  = "<"
operStr GT  = ">"
operStr LTE = "<="
operStr GTE = ">="
operStr AND = "&"
operStr OR  = "|"
operStr XOR = "^"
operStr LSH = "<<"
operStr RSH = ">>"

contextStr :: Book -> Fill -> [Term] -> Int -> String
contextStr book fill []     dep = ""
contextStr book fill (x:xs) dep = concat [" " , contextStrAnn book fill x dep , contextStr book fill xs dep]

contextStrAnn :: Book -> Fill -> Term -> Int -> String
contextStrAnn book fill (Ann chk val typ) dep = concat ["{" , termStr (normal book fill 0 val dep) dep , ": " , termStr (normal book fill 0 typ dep) dep , "}"]
contextStrAnn book fill term              dep = termStr (normal book fill 0 term dep) dep

infoStr :: Book -> Fill -> Info -> String
infoStr book fill (Found name typ ctx dep) =
  let typ' = termStr (normal book fill 0 typ dep) dep
      ctx' = drop 1 (contextStr book fill ctx dep)
  in concat ["#found{", name, " ", typ', " [", ctx', "]}"]
infoStr book fill (Error src expected detected value dep) =
  let exp = termStr (normal book fill 0 expected dep) dep
      det = termStr (normal book fill 0 detected dep) dep
      val = termStr (normal book fill 0 value dep) dep
  in concat ["#error{", exp, " ", det, " ", val, " ", show src, "}"]
infoStr book fill (Solve name term dep) =
  let term' = termStr (normal book fill 0 term dep) dep
  in concat ["#solve{", show name, " ",  term', "}"]
infoStr book fill (Vague name) =
  concat ["#vague{", name, "}"]
infoStr book fill (Print value dep) =
  let val = termStr (normal book fill 0 value dep) dep
  in concat ["#print{", val, "}"]

-- Parsing
-- -------

doParseTerm :: String -> Term
doParseTerm input = case P.parse parseTerm "" input of
  Left  err  -> error $ "Parse error: " ++ show err
  Right term -> bind term

parseTerm :: P.Parsec String () Term
parseTerm = do
  P.spaces
  P.choice
    [ parseAll
    , parseLam
    , parseOp2
    , parseApp
    , parseAnn
    , parseSlf
    , parseIns
    , parseUse
    , parseLet
    , parseSet
    , parseNum
    , parseSwi
    , parseTxt
    , parseNat
    , parseHol
    , parseMet
    , parseSrc
    , parseRef
    ]

parseAll = do
  P.string "∀"
  P.char '('
  nam <- parseName
  P.char ':'
  inp <- parseTerm
  P.char ')'
  bod <- parseTerm
  return $ All nam inp (\x -> bod)

parseLam = do
  P.string "λ"
  nam <- parseName
  bod <- parseTerm
  return $ Lam nam (\x -> bod)

parseApp = do
  P.char '('
  fun <- parseTerm
  arg <- parseTerm
  P.char ')'
  return $ App fun arg

parseAnn = do
  P.char '{'
  val <- parseTerm
  P.spaces
  P.char ':'
  chk <- P.option False (P.char ':' >> return True)
  typ <- parseTerm
  P.spaces
  P.char '}'
  return $ Ann chk val typ

parseSlf = do
  P.string "$("
  nam <- parseName
  P.char ':'
  typ <- parseTerm
  P.char ')'
  bod <- parseTerm
  return $ Slf nam typ (\x -> bod)

parseIns = do
  P.char '~'
  val <- parseTerm
  return $ Ins val

parseRef = do
  name <- parseName
  return $ case name of
    "U48" -> U48
    _     -> Ref name

parseUse = do
  P.try (P.string "use ")
  nam <- parseName
  P.spaces
  P.char '='
  val <- parseTerm
  P.char ';'
  bod <- parseTerm
  return $ Use nam val (\x -> bod)

parseLet = do
  P.try (P.string "let ")
  nam <- parseName
  P.spaces
  P.char '='
  val <- parseTerm
  P.char ';'
  bod <- parseTerm
  return $ Let nam val (\x -> bod)

parseSet = P.char '*' >> return Set

parseNum = Num . read <$> P.many1 P.digit

parseOp2 = do
  opr <- P.try $ do
    P.string "("
    opr <- parseOper
    return opr
  fst <- parseTerm
  snd <- parseTerm
  P.char ')'
  return $ Op2 opr fst snd

parseSwi = do
  P.try (P.string "switch ")
  nam <- parseName
  P.spaces
  P.char '='
  x <- parseTerm
  P.spaces
  P.char '{'
  P.spaces
  P.string "0:"
  z <- parseTerm
  P.spaces
  P.string "_:"
  s <- parseTerm
  P.spaces
  P.char '}'
  P.char ':'
  p <- parseTerm
  return $ Swi nam x z (\k -> s) (\k -> p)

parseTxt = do
  P.char '"'
  txt <- P.many (P.noneOf "\"")
  P.char '"'
  return $ Txt txt

parseNat = do
  P.char '#'
  val <- read <$> P.many1 P.digit
  return $ Nat val

parseHol = do
  P.char '?'
  nam <- parseName
  ctx <- P.option [] $ do
    P.char '['
    terms <- P.sepBy parseTerm (P.char ',')
    P.char ']'
    return terms
  return $ Hol nam ctx

parseMet = do
  P.char '_'
  uid <- read <$> P.many1 P.digit
  return $ Met uid []

parseSrc = do
  P.char '!'
  src <- read <$> P.many1 P.digit
  val <- parseTerm
  return $ Src src val

parseName :: P.Parsec String () String
parseName = do
  P.spaces
  head <- P.letter
  tail <- P.many (P.alphaNum <|> P.char '/' <|> P.char '.' <|> P.char '_' <|> P.char '-')
  return (head : tail)

parseOper = P.choice
  [ P.try (P.string "+") >> return ADD
  , P.try (P.string "-") >> return SUB
  , P.try (P.string "*") >> return MUL
  , P.try (P.string "/") >> return DIV
  , P.try (P.string "%") >> return MOD
  , P.try (P.string "<=") >> return LTE
  , P.try (P.string ">=") >> return GTE
  , P.try (P.string "<") >> return LT
  , P.try (P.string ">") >> return GT
  , P.try (P.string "==") >> return EQ
  , P.try (P.string "!=") >> return NE
  , P.try (P.string "&") >> return AND
  , P.try (P.string "|") >> return OR
  , P.try (P.string "^") >> return XOR
  , P.try (P.string "<<") >> return LSH
  , P.try (P.string ">>") >> return RSH
  ]

parseBook :: P.Parsec String () Book
parseBook = do
  defs <- P.many parseDef
  return $ M.fromList defs

parseDef :: P.Parsec String () (String, Term)
parseDef = do
  name <- parseName
  P.spaces
  (typ, hasType) <- P.option (undefined, False) $ do
    P.char ':'
    typ <- parseTerm
    P.spaces
    return (typ, True)
  P.char '='
  value <- parseTerm
  P.char ';'
  P.spaces
  return (name, if hasType then Ann True value typ else value)

doParseBook :: String -> Book
doParseBook input = case P.parse parseBook "" input of
  Left  err  -> error $ "Parse error: " ++ show err
  Right book -> M.map bind book

-- API
-- ---

-- Normalizes a term
apiNormal :: Book -> Term -> IO ()
apiNormal book term = putStrLn $ infoStr book IM.empty (Print (normal book IM.empty 2 term 0) 0)

-- Type-checks a term
apiCheck :: Book -> Term -> IO ()
apiCheck book term = case envRun (checkDef term) book of
  Done state value -> apiPrintLogs state
  Fail state       -> apiPrintLogs state

apiPrintLogs :: State -> IO ()
apiPrintLogs (State book fill susp (log : logs)) = do
  putStrLn $ infoStr book fill log
  apiPrintLogs (State book fill susp logs)
apiPrintLogs (State book fill susp []) = do
  return ()

-- Main
-- ----

book :: Book
book = M.fromList []

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["check", file] -> do
      content <- readFile file
      let book = doParseBook content
      case M.lookup "main" book of
        Just term -> apiCheck book (Ref "main")
        Nothing -> putStrLn "Error: No 'main' definition found in the file."
    ["run", file] -> do
      content <- readFile file
      let book = doParseBook content
      case M.lookup "main" book of
        Just term -> apiNormal book term
        Nothing -> putStrLn "Error: No 'main' definition found in the file."
    ["show", file] -> do
      content <- readFile file
      let book = doParseBook content
      case M.lookup "main" book of
        Just term -> putStrLn $ termStr term 0
        Nothing -> putStrLn "Error: No 'main' definition found in the file."
    ["help"] -> printHelp
    [] -> printHelp
    _ -> do
      putStrLn "Invalid command. Use 'kindc help' for usage information."
      exitFailure

printHelp :: IO ()
printHelp = do
  putStrLn "Kind2 Core Checker (kindc) usage:"
  putStrLn "  kindc check file.kindc # Type-checks the main definition"
  putStrLn "  kindc run   file.kindc # Normalizes the main definition"
  putStrLn "  kindc show  file.kindc # Stringifies the main definition"
  putStrLn "  kindc help             # Shows this help message"
