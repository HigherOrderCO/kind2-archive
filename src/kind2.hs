-- This is a Haskell implementation of Kind2's type checker. Since Kind2 isn't
-- bootstrapped, we can't use Kind2 itself to type-check it, and developing a
-- complex checker in an untyped language (like HVM) is hard. As such, this
-- Haskell view helps me develop and debug the checker, and it is done in a way
-- that makes it easy to manually compile it to HVM, keeping an HVM view. It can
-- also be useful to let us benchmark all versions (GHC/HVM1/HVM2), giving us a
-- good idea on how these compare in performance.

import Data.Char (chr, ord)
import Prelude hiding (LT, GT, EQ)
import Debug.Trace
import Control.Monad (forM_)

-- Kind2 Types
-- -----------

data Oper
  = ADD | SUB | MUL | DIV
  | MOD | EQ  | NE  | LT
  | GT  | LTE | GTE | AND
  | OR  | XOR | LSH | RSH

data Term
  = All String Term (Term -> Term)
  | Lam String (Term -> Term)
  | App Term Term
  | Ann Bool Term Term
  | Slf String Term (Term -> Term)
  | Ins Term
  | Ref String Term
  | Let String Term (Term -> Term)
  | Use String Term (Term -> Term)
  | Set
  | U60
  | Num Int
  | Op2 Oper Term Term
  | Mat String Term Term (Term -> Term) (Term -> Term)
  | Hol String [Term]
  | Met Int [Term]
  | Var String Int
  | Src Int Term
  | Txt String
  | Nat Integer

data Info
  = Found String Term [Term] Int
  | Solve Int Term Int
  | Error Int Term Term Term Int
  | Vague String
  | Print Term Int

data Check = Check Int Term Term Int
data State = State (Map Term) [Check] [Info] -- state type
data Res a = Done State a | Fail State -- result type
data Env a = Env (State -> Res a) -- environment computation

data Bits = O Bits | I Bits | E deriving Show
data Map a = Leaf | Node (Maybe a) (Map a) (Map a) deriving Show

-- Prelude
-- -------
-- Note: many of these functions are present in Haskell, but we re-implement
-- them here in order to have identical equivalents on HVM's view.
-- FIXME: replace Int by proper U60

u60Show :: Int -> String
u60Show n = u60ShowGo n "" where
  u60ShowGo n res            = u60ShowGoMatch (n < 10) n res
  u60ShowGoMatch False n res = u60ShowGo (div n 10) (chr (ord '0' + mod n 10) : res)
  u60ShowGoMatch True  n res = chr (ord '0' + n) : res

u60Name :: Int -> String
u60Name n = u60NameGo (n + 1) where
  u60NameGo 0 = ""
  u60NameGo n = chr (ord 'a' + mod (n - 1) 26) : u60NameGo (div (n - 1) 26)

listFind :: Eq a => a -> [(a, b)] -> Maybe b
listFind _    []                = Nothing
listFind name ((nam, val):tail) = if name == nam then Just val else listFind name tail

listMap :: (a -> b) -> [a] -> [b]
listMap f []     = []
listMap f (x:xs) = f x : listMap f xs

listPush :: a -> [a] -> [a]
listPush x []     = [x]
listPush x (y:ys) = y : listPush x ys

newLine :: String
newLine = [chr 10]

quote :: String
quote = [chr 34]

stringEqual :: String -> String -> Bool
stringEqual []     []     = True
stringEqual []     _      = False
stringEqual _      []     = False
stringEqual (x:xs) (y:ys) = x == y && stringEqual xs ys

stringConcat :: String -> String -> String
stringConcat []     ys = ys
stringConcat (x:xs) ys = x : stringConcat xs ys

stringJoin :: [String] -> String
stringJoin [] = ""
stringJoin (x:xs) = stringConcat x (stringJoin xs)

stringTail :: String -> String
stringTail [] = []
stringTail (_:xs) = xs

pairFst :: (a, b) -> a
pairFst (fst, _) = fst

pairSnd :: (a, b) -> b
pairSnd (_, snd) = snd

pairGet :: (a, b) -> (a -> b -> c) -> c
pairGet (fst, snd) fun = fun fst snd

maybeMatch :: Maybe a -> (a -> b) -> b -> b
maybeMatch (Just value) some _    = some value
maybeMatch Nothing      _    none = none

maybePure :: a -> Maybe a
maybePure x = Just x

maybeBind :: Maybe a -> (a -> Maybe b) -> Maybe b
maybeBind a b = maybeMatch a b Nothing

key :: Int -> Bits
key 0 = E
key 1 = I E
key n = if even n
  then O (key (div n 2))
  else I (key (div n 2))

mapNew :: Map a
mapNew = Leaf

mapHas :: Bits -> Map a -> Bool
mapHas E        (Node (Just _) _ _) = True
mapHas (O bits) (Node _ lft _)      = mapHas bits lft
mapHas (I bits) (Node _ _ rgt)      = mapHas bits rgt
mapHas _        _                   = False

mapGet :: Bits -> Map a -> Maybe a
mapGet E        (Node val _ _) = val
mapGet (O bits) (Node _ lft _) = mapGet bits lft
mapGet (I bits) (Node _ _ rgt) = mapGet bits rgt
mapGet _        Leaf           = Nothing

mapSet :: Bits -> a -> Map a -> Map a
mapSet E        val Leaf             = Node (Just val) Leaf Leaf
mapSet E        val (Node _ lft rgt) = Node (Just val) lft rgt
mapSet (O bits) val Leaf             = Node Nothing (mapSet bits val Leaf) Leaf
mapSet (O bits) val (Node v lft rgt) = Node v (mapSet bits val lft) rgt
mapSet (I bits) val Leaf             = Node Nothing Leaf (mapSet bits val Leaf)
mapSet (I bits) val (Node v lft rgt) = Node v lft (mapSet bits val rgt)

-- Environment
-- -----------

infoIsSolve :: Info -> Bool
infoIsSolve (Solve _ _ _) = True
infoIsSolve _             = False

-- Pattern matches on a computation result
-- resMatch :: Res a -> (State -> a -> b) -> (State -> Info -> b) -> b
-- resMatch (Done state value) done _    = done state value
-- resMatch (Fail state)       _    fail = fail state error

-- Monadic bind function
envBind :: Env a -> (a -> Env b) -> Env b
envBind (Env a) b = Env $ \state -> case a state of
  Done state' value -> let Env b' = b value in b' state'
  Fail state'       -> Fail state'

envPure :: a -> Env a
envPure a = Env $ \state -> Done state a

envFail :: Env a
envFail = Env $ \state -> Fail state

envRun :: Env a -> Res a
envRun (Env chk) = chk (State mapNew [] [])

envLog :: Info -> Env Int
envLog log = Env $ \(State fill susp logs) -> Done (State fill susp (log : logs)) 1

envSnapshot :: Env State
envSnapshot = Env $ \state -> Done state state

envRewind :: State -> Env Int
envRewind state = Env $ \_ -> Done state 0

envSusp :: Check -> Env ()
envSusp chk = Env $ \(State fill susp logs) -> Done (State fill (listPush chk susp) logs) ()

envFill :: Int -> Term -> Env ()
envFill k v = Env $ \(State fill susp logs) -> Done (State (mapSet (key k) v fill) susp logs) ()

envGetFill :: Env (Map Term)
envGetFill = Env $ \(State fill susp logs) -> Done (State fill susp logs) fill

envTakeSusp :: Env [Check]
envTakeSusp = Env $ \(State fill susp logs) -> Done (State fill [] logs) susp

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

-- Evaluation
-- ----------

-- Evaluation levels:
-- - 0: reduces refs never
-- - 1: reduces refs on redexes
-- - 2: reduces refs always

termReduce :: Map Term -> Int -> Term -> Term
termReduce fill lv (App fun arg)     = termReduceApp fill lv (termReduce fill lv fun) arg
termReduce fill lv (Ann chk val typ) = termReduce fill lv val
termReduce fill lv (Ins val)         = termReduce fill lv val
termReduce fill lv (Ref nam val)     = termReduceRef fill lv nam (termReduce fill lv val)
termReduce fill lv (Let nam val bod) = termReduce fill lv (bod val)
termReduce fill lv (Use nam val bod) = termReduce fill lv (bod val)
termReduce fill lv (Op2 opr fst snd) = termReduceOp2 fill lv opr (termReduce fill lv fst) (termReduce fill lv snd)
termReduce fill lv (Mat nam x z s p) = termReduceMat fill lv nam (termReduce fill lv x) z s p
termReduce fill lv (Txt txt)         = termReduceTxt fill lv txt
termReduce fill lv (Nat val)         = termReduceNat fill lv val
termReduce fill lv (Src src val)     = termReduce fill lv val
termReduce fill lv (Met uid spn)     = termReduceMet fill lv uid spn
termReduce fill lv val               = val

termReduceApp :: Map Term -> Int -> Term -> Term -> Term
termReduceApp fill 2  (Ref nam val) arg = termReduceApp fill 2 val arg
termReduceApp fill 1  (Ref nam val) arg = termReduceApp fill 1 val arg
termReduceApp fill lv (Met uid spn) arg = termReduce fill lv (Met uid (listPush arg spn))
termReduceApp fill lv (Lam nam bod) arg = termReduce fill lv (bod (termReduce fill 0 arg))
termReduceApp fill lv fun arg           = App fun arg

termReduceMet :: Map Term -> Int -> Int -> [Term] -> Term
termReduceMet fill lv uid spn = case mapGet (key uid) fill of
  Just val -> termReduce fill lv (termReduceMetSpine val spn)
  Nothing  -> Met uid spn

termReduceMetSpine :: Term -> [Term] -> Term
termReduceMetSpine val []       = val
termReduceMetSpine val (x : xs) = termReduceMetSpine (App val x) xs

termReduceOp2 :: Map Term -> Int -> Oper -> Term -> Term -> Term
termReduceOp2 fill 1  op  (Ref _ x) (Num snd) = termReduceOp2 fill 1 op x (Num snd)
termReduceOp2 fill 2  op  (Ref _ x) (Num snd) = termReduceOp2 fill 2 op x (Num snd)
termReduceOp2 fill 1  op  (Num fst) (Ref _ x) = termReduceOp2 fill 1 op (Num fst) x
termReduceOp2 fill 2  op  (Num fst) (Ref _ x) = termReduceOp2 fill 2 op (Num fst) x
termReduceOp2 fill lv ADD (Num fst) (Num snd) = Num (fst + snd)
termReduceOp2 fill lv SUB (Num fst) (Num snd) = Num (fst - snd)
termReduceOp2 fill lv MUL (Num fst) (Num snd) = Num (fst * snd)
termReduceOp2 fill lv DIV (Num fst) (Num snd) = Num (div fst snd)
termReduceOp2 fill lv MOD (Num fst) (Num snd) = Num (mod fst snd)
termReduceOp2 fill lv EQ  (Num fst) (Num snd) = if fst == snd then Num 1 else Num 0
termReduceOp2 fill lv NE  (Num fst) (Num snd) = if fst /= snd then Num 1 else Num 0
termReduceOp2 fill lv LT  (Num fst) (Num snd) = if fst < snd then Num 1 else Num 0
termReduceOp2 fill lv GT  (Num fst) (Num snd) = if fst > snd then Num 1 else Num 0
termReduceOp2 fill lv LTE (Num fst) (Num snd) = if fst <= snd then Num 1 else Num 0
termReduceOp2 fill lv GTE (Num fst) (Num snd) = if fst >= snd then Num 1 else Num 0
termReduceOp2 fill lv opr fst snd             = Op2 opr fst snd

termReduceMat :: Map Term -> Int -> String -> Term -> Term -> (Term -> Term) -> (Term -> Term) -> Term
termReduceMat fill 2  nam (Ref _ x)           z s p = termReduceMat fill 2 nam x z s p
termReduceMat fill 1  nam (Ref _ x)           z s p = termReduceMat fill 1 nam x z s p
termReduceMat fill lv nam (Num 0)             z s p = termReduce fill lv z
termReduceMat fill lv nam (Num n)             z s p = termReduce fill lv (s (Num (n - 1)))
termReduceMat fill lv nam (Op2 ADD (Num 1) k) z s p = termReduce fill lv (s k)
termReduceMat fill lv nam val                 z s p = Mat nam val z s p

termReduceRef :: Map Term -> Int -> String -> Term -> Term
termReduceRef fill 2  nam val = termReduce fill 2 val
termReduceRef fill 1  nam val = Ref nam val
termReduceRef fill lv nam val = Ref nam val

termReduceTxt :: Map Term -> Int -> String -> Term
termReduceTxt fill lv []     = termReduce fill lv xString_nil
termReduceTxt fill lv (x:xs) = termReduce fill lv (App (App xString_cons (Num (ord x))) (Txt xs))

termReduceNat :: Map Term -> Int -> Integer -> Term
termReduceNat fill lv 0 = xNat_zero
termReduceNat fill lv n = App xNat_succ (termReduceNat fill lv (n - 1))

-- Normalization
-- -------------

termNormal :: Map Term -> Int -> Term -> Int -> Term
-- termNormal fill lv term dep = termNormalGo fill lv (termNormalPrefer fill (termReduce fill 0 term) (termReduce fill lv term)) dep where
termNormal fill lv term dep = termNormalGo fill lv (termReduce fill lv term) dep where

  -- termNormalPrefer fill soft (Lam _ _)   = soft
  -- termNormalPrefer fill soft (Slf _ _ _) = soft
  -- termNormalPrefer fill soft (All _ _ _) = soft
  -- termNormalPrefer fill soft hard        = hard

  termNormalGo fill lv (All nam inp bod) dep = All nam (termNormal fill lv inp dep) (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (Lam nam bod)     dep = Lam nam (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (App fun arg)     dep = App (termNormal fill lv fun dep) (termNormal fill lv arg dep)
  termNormalGo fill lv (Ann chk val typ) dep = Ann chk (termNormal fill lv val dep) (termNormal fill lv typ dep)
  termNormalGo fill lv (Slf nam typ bod) dep = Slf nam typ (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (Ins val)         dep = Ins (termNormal fill lv val dep)
  termNormalGo fill lv (Ref nam val)     dep = Ref nam (termNormal fill lv val dep)
  termNormalGo fill lv (Let nam val bod) dep = Let nam (termNormal fill lv val dep) (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (Use nam val bod) dep = Use nam (termNormal fill lv val dep) (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (Hol nam ctx)     dep = Hol nam ctx
  termNormalGo fill lv Set               dep = Set
  termNormalGo fill lv U60               dep = U60
  termNormalGo fill lv (Num val)         dep = Num val
  termNormalGo fill lv (Op2 opr fst snd) dep = Op2 opr (termNormal fill lv fst dep) (termNormal fill lv snd dep)
  termNormalGo fill lv (Mat nam x z s p) dep = Mat nam (termNormal fill lv x dep) (termNormal fill lv z dep) (\k -> termNormal fill lv (s (Var (stringConcat nam "-1") dep)) dep) (\k -> termNormal fill lv (p (Var nam dep)) dep)
  termNormalGo fill lv (Txt val)         dep = Txt val
  termNormalGo fill lv (Nat val)         dep = Nat val
  termNormalGo fill lv (Var nam idx)     dep = Var nam idx
  termNormalGo fill lv (Src src val)     dep = Src src (termNormal fill lv val dep)
  termNormalGo fill lv (Met uid spn)     dep = Met uid spn -- TODO: normalize spine

-- Equality
-- --------

-- trace ("equal:\n- " ++ termShow a dep ++ "\n- " ++ termShow b dep) $ do
termEqual :: Term -> Term -> Int -> Env Bool
termEqual a b dep = do
    fill <- envGetFill
    let a' = termReduce fill 2 a
    let b' = termReduce fill 2 b
    termTryIdentical a' b' dep $ do
      termSimilar a' b' dep

termTryIdentical :: Term -> Term -> Int -> Env Bool -> Env Bool
termTryIdentical a b dep cont = do
  state <- envSnapshot
  equal <- termIdentical a b dep
  if equal
    then envPure True
    else envRewind state >> cont

termSimilar :: Term -> Term -> Int -> Env Bool
termSimilar (All aNam aInp aBod) (All bNam bInp bBod) dep = do
  eInp <- termEqual aInp bInp dep
  eBod <- termEqual (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
  envPure (eInp && eBod)
termSimilar (Lam aNam aBod) (Lam bNam bBod) dep =
  termEqual (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
termSimilar (App aFun aArg) (App bFun bArg) dep = do
  eFun <- termSimilar aFun bFun dep
  eArg <- termEqual aArg bArg dep
  envPure (eFun && eArg)
termSimilar (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
  termSimilar (termReduce mapNew 0 aTyp) (termReduce mapNew 0 bTyp) dep
-- termSimilar (Hol aNam aCtx) (Hol bNam bCtx) dep =
  -- envPure (aNam == bNam)
-- termSimilar (Met aUid aSpn) (Met bUid bSpn) dep =
  -- envPure (aUid == bUid)
termSimilar (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep = do
  eFst <- termEqual aFst bFst dep
  eSnd <- termEqual aSnd bSnd dep
  envPure (eFst && eSnd)
termSimilar (Mat aNam aX aZ aS aP) (Mat bNam bX bZ bS bP) dep = do
  eX <- termEqual aX bX dep
  eZ <- termEqual aZ bZ dep
  eS <- termEqual (aS (Var (stringConcat aNam "-1") dep)) (bS (Var (stringConcat bNam "-1") dep)) dep
  eP <- termEqual (aP (Var aNam dep)) (bP (Var bNam dep)) dep
  envPure (eX && eZ && eS && eP)
termSimilar a b dep = termIdentical a b dep

termIdentical :: Term -> Term -> Int -> Env Bool
termIdentical a b dep = termIdenticalGo a b dep

termIdenticalGo :: Term -> Term -> Int -> Env Bool
termIdenticalGo (All aNam aInp aBod) (All bNam bInp bBod) dep =
  envBind (termIdentical aInp bInp dep) $ \iInp ->
  envBind (termIdentical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)) $ \iBod ->
  envPure (iInp && iBod)
termIdenticalGo (Lam aNam aBod) (Lam bNam bBod) dep =
  termIdentical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
termIdenticalGo (App aFun aArg) (App bFun bArg) dep =
  envBind (termIdentical aFun bFun dep) $ \iFun ->
  envBind (termIdentical aArg bArg dep) $ \iArg ->
  envPure (iFun && iArg)
termIdenticalGo (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
  termIdentical aTyp bTyp dep
termIdenticalGo (Ins aVal) b dep =
  termIdentical aVal b dep
termIdenticalGo a (Ins bVal) dep =
  termIdentical a bVal dep
termIdenticalGo (Let aNam aVal aBod) b dep =
  termIdentical (aBod aVal) b dep
termIdenticalGo a (Let bNam bVal bBod) dep =
  termIdentical a (bBod bVal) dep
termIdenticalGo (Use aNam aVal aBod) b dep =
  termIdentical (aBod aVal) b dep
termIdenticalGo a (Use bNam bVal bBod) dep =
  termIdentical a (bBod bVal) dep
termIdenticalGo Set Set dep =
  envPure True
termIdenticalGo (Ann chk aVal aTyp) b dep =
  termIdentical aVal b dep
termIdenticalGo a (Ann chk bVal bTyp) dep =
  termIdentical a bVal dep
-- termIdenticalGo (Met aUid aSpn) (Met bUid bSpn) dep =
  -- envPure (aUid == bUid)
termIdenticalGo (Met aUid aSpn) b dep =
  -- traceShow ("unify: " ++ show aUid ++ " x=" ++ termShow (Met aUid aSpn) dep ++ " t=" ++ termShow b dep) $
  termUnify aUid aSpn b dep
termIdenticalGo a (Met bUid bSpn) dep =
  -- traceShow ("unify: " ++ show bUid ++ " x=" ++ termShow (Met bUid bSpn) dep ++ " t=" ++ termShow a dep) $
  termUnify bUid bSpn a dep
termIdenticalGo (Hol aNam aCtx) b dep =
  envPure True
termIdenticalGo a (Hol bNam bCtx) dep =
  envPure True
termIdenticalGo U60 U60 dep =
  envPure True
termIdenticalGo (Num aVal) (Num bVal) dep =
  envPure (aVal == bVal)
termIdenticalGo (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep =
  envBind (termIdentical aFst bFst dep) $ \iFst ->
  envBind (termIdentical aSnd bSnd dep) $ \iSnd ->
  envPure (iFst && iSnd)
termIdenticalGo (Mat aNam aX aZ aS aP) (Mat bNam bX bZ bS bP) dep =
  envBind (termIdentical aX bX dep) $ \iX ->
  envBind (termIdentical aZ bZ dep) $ \iZ ->
  envBind (termIdentical (aS (Var (stringConcat aNam "-1") dep)) (bS (Var (stringConcat bNam "-1") dep)) dep) $ \iS ->
  envBind (termIdentical (aP (Var aNam dep)) (bP (Var bNam dep)) dep) $ \iP ->
  envPure (iX && iZ && iS && iP)
termIdenticalGo (Txt aTxt) (Txt bTxt) dep =
  envPure (aTxt == bTxt)
termIdenticalGo (Nat aVal) (Nat bVal) dep =
  envPure (aVal == bVal)
termIdenticalGo (Src aSrc aVal) b dep =
  termIdentical aVal b dep
termIdenticalGo a (Src bSrc bVal) dep =
  termIdentical a bVal dep
termIdenticalGo (Ref aNam aVal) (Ref bNam bVal) dep =
  envPure (aNam == bNam)
termIdenticalGo (Var aNam aIdx) (Var bNam bIdx) dep =
  envPure (aIdx == bIdx)
termIdenticalGo a b dep =
  envPure False

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
-- so, it is impossible for unbound variables to appear. We also don't check for
-- condition 3, and just allow recursive solutions.

-- If possible, solves a `(?X x y z ...) = K` problem, generating a subst.
termUnify :: Int -> [Term] -> Term -> Int -> Env Bool
termUnify uid spn b dep = do
  fill <- envGetFill
  let unsolved = not (mapHas (key uid) fill)
  let solvable = termUnifyValid fill spn []
  if unsolved && solvable then do
    let solution = termUnifySolve fill uid spn b
    -- trace ("solve: " ++ show uid ++ " " ++ termShow solution dep) $ do
    envFill uid solution
    return True
  else
    return False

-- Checks if an problem is solveable by pattern unification.
termUnifyValid :: Map Term -> [Term] -> [Int] -> Bool
termUnifyValid fill []        vars = True
termUnifyValid fill (x : spn) vars = case termReduce fill 0 x of
  (Var nam idx) -> not (elem idx vars) && termUnifyValid fill spn (idx : vars)
  otherwise     -> False
  
-- Generates the solution, adding binders and renaming variables.
termUnifySolve :: Map Term -> Int -> [Term] -> Term -> Term
termUnifySolve fill uid []        b = b
termUnifySolve fill uid (x : spn) b = case termReduce fill 0 x of
  (Var nam idx) -> Lam nam $ \x -> termUnifySubst idx x (termUnifySolve fill uid spn b)
  otherwise     -> error "unreachable"         

-- Substitutes a Bruijn level variable by a `neo` value in `term`.
termUnifySubst :: Int -> Term -> Term -> Term
-- termUnifySubst lvl neo term = term
termUnifySubst lvl neo (All nam inp bod) = All nam (termUnifySubst lvl neo inp) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Lam nam bod)     = Lam nam (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (App fun arg)     = App (termUnifySubst lvl neo fun) (termUnifySubst lvl neo arg)
termUnifySubst lvl neo (Ann chk val typ) = Ann chk (termUnifySubst lvl neo val) (termUnifySubst lvl neo typ)
termUnifySubst lvl neo (Slf nam typ bod) = Slf nam (termUnifySubst lvl neo typ) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Ins val)         = Ins (termUnifySubst lvl neo val)
termUnifySubst lvl neo (Ref nam val)     = Ref nam (termUnifySubst lvl neo val)
termUnifySubst lvl neo (Let nam val bod) = Let nam (termUnifySubst lvl neo val) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Use nam val bod) = Use nam (termUnifySubst lvl neo val) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Met uid spn)     = Met uid (map (termUnifySubst lvl neo) spn)
termUnifySubst lvl neo (Hol nam ctx)     = Hol nam (map (termUnifySubst lvl neo) ctx)
termUnifySubst lvl neo Set               = Set
termUnifySubst lvl neo U60               = U60
termUnifySubst lvl neo (Num n)           = Num n
termUnifySubst lvl neo (Op2 opr fst snd) = Op2 opr (termUnifySubst lvl neo fst) (termUnifySubst lvl neo snd)
termUnifySubst lvl neo (Mat nam x z s p) = Mat nam (termUnifySubst lvl neo x) (termUnifySubst lvl neo z) (\k -> termUnifySubst lvl neo (s k)) (\k -> termUnifySubst lvl neo (p k))
termUnifySubst lvl neo (Txt txt)         = Txt txt
termUnifySubst lvl neo (Nat val)         = Nat val
termUnifySubst lvl neo (Var nam idx)     = if lvl == idx then neo else Var nam idx
termUnifySubst lvl neo (Src src val)     = Src src (termUnifySubst lvl neo val)

-- Type-Checking
-- -------------

termIfAll :: Term -> (String -> Term -> (Term -> Term) -> a) -> a -> a
termIfAll (All nam inp bod) yep _   = yep nam inp bod
termIfAll _                 _   nop = nop

termIfSlf :: Term -> (String -> Term -> (Term -> Term) -> a) -> a -> a
termIfSlf (Slf nam typ bod) yep _   = yep nam typ bod
termIfSlf _                 _   nop = nop

termInfer :: Term -> Int -> Env Term
termInfer term dep =
  -- trace ("infer: " ++ termShow term dep) $
  termInferGo term dep

termInferGo :: Term -> Int -> Env Term
termInferGo (All nam inp bod) dep = do
  envSusp (Check 0 inp Set dep)
  envSusp (Check 0 (bod (Ann False (Var nam dep) inp)) Set (dep + 1))
  return Set
termInferGo (App fun arg) dep = do
  ftyp <- termInfer fun dep
  fill <- envGetFill
  case termReduce fill 2 ftyp of
    (All ftyp_nam ftyp_inp ftyp_bod) -> do
      envSusp (Check 0 arg ftyp_inp dep)
      return $ ftyp_bod arg
    otherwise -> do
      envLog (Error 0 (Hol "function" []) ftyp (App fun arg) dep)
      envFail
termInferGo (Ann chk val typ) dep = do
  if chk then do
    termCheck 0 val typ dep
  else do
    return ()
  return typ
termInferGo (Slf nam typ bod) dep = do
  envSusp (Check 0 (bod (Ann False (Var nam dep) typ)) Set (dep + 1))
  return Set
termInferGo (Ins val) dep = do
  vtyp <- termInfer val dep
  fill <- envGetFill
  case termReduce fill 2 vtyp of
    (Slf vtyp_nam vtyp_typ vtyp_bod) -> do
      return $ vtyp_bod (Ins val)
    otherwise -> do
      envLog (Error 0 (Hol "self-type" []) vtyp (Ins val) dep)
      envFail
termInferGo (Ref nam val) dep = do
  termInfer val dep
termInferGo Set dep = do
  return Set
termInferGo U60 dep = do
  return Set
termInferGo (Num num) dep = do
  return U60
termInferGo (Txt txt) dep = do
  return xString
termInferGo (Nat val) dep = do
  return xNat
termInferGo (Op2 opr fst snd) dep = do
  envSusp (Check 0 fst U60 dep)
  envSusp (Check 0 snd U60 dep)
  return U60
termInferGo (Mat nam x z s p) dep = do
  envSusp (Check 0 x U60 dep)
  envSusp (Check 0 (p (Ann False (Var nam dep) U60)) Set dep)
  envSusp (Check 0 z (p (Num 0)) dep)
  envSusp (Check 0 (s (Ann False (Var (stringConcat nam "-1") dep) U60)) (p (Op2 ADD (Num 1) (Var (stringConcat nam "-1") dep))) (dep + 1))
  return (p x)
termInferGo (Let nam val bod) dep = do
  typ <- termInfer val dep
  termInfer (bod (Ann False (Var nam dep) typ)) dep
termInferGo (Use nam val bod) dep = do
  termInfer (bod val) dep
termInferGo (Lam nam bod) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_lambda" []) (Lam nam bod) dep)
  envFail
termInferGo (Hol nam ctx) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_hole" []) (Hol nam ctx) dep)
  envFail
termInferGo (Met uid spn) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_meta" []) (Met uid spn) dep)
  envFail
termInferGo (Var nam idx) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_variable" []) (Var nam idx) dep)
  envFail
termInferGo (Src src val) dep = do
  termInfer val dep

termCheck :: Int -> Term -> Term -> Int -> Env ()
termCheck src val typ dep =
  -- trace ("check: " ++ termShow val dep ++ "\n    :: " ++ termShow typ dep) $
  termCheckGo src val typ dep

termCheckGo :: Int -> Term -> Term -> Int -> Env ()
termCheckGo src (Lam termNam termBod) typx dep = do
  fill <- envGetFill
  case termReduce fill 2 typx of
    (All typeNam typeInp typeBod) -> do
      let ann  = Ann False (Var termNam dep) typeInp
      let term = termBod ann
      let typx = typeBod ann
      termCheck 0 term typx (dep + 1)
    otherwise -> do
      termInfer (Lam termNam termBod) dep
      return ()
termCheckGo src (Ins termVal) typx dep = do
  fill <- envGetFill
  case termReduce fill 2 typx of
    Slf typeNam typeTyp typeBod -> do
      termCheck 0 termVal (typeBod (Ins termVal)) dep
    _ -> do
      termInfer (Ins termVal) dep
      return ()
termCheckGo src (Let termNam termVal termBod) typx dep = do
  termTyp <- termInfer termVal dep
  termCheck 0 (termBod (Ann False (Var termNam dep) termTyp)) typx dep
termCheckGo src (Use termNam termVal termBod) typx dep = do
  termCheck 0 (termBod termVal) typx dep
termCheckGo src (Hol termNam termCtx) typx dep = do
  envLog (Found termNam typx termCtx dep)
  return ()
termCheckGo src (Met uid spn) typx dep = do
  return ()
termCheckGo src (Ann chk val typ) typx dep = do
  termCheckCompare src val typ typx dep
  if chk then do
    termCheck src val typ dep
  else do
    return ()
-- termCheckGo src (Ref termNam (Ann termVal termTyp)) typx dep = do
  -- equal <- termEqual typx termTyp dep
  -- termCheckReport src equal termTyp typx termVal dep
termCheckGo src (Src termSrc termVal) typx dep = do
  termCheck termSrc termVal typx dep
termCheckGo src term typx dep = do
  infer <- termInfer term dep
  termCheckCompare src term typx infer dep

termCheckCompare src term expected detected dep = do
  equal <- termEqual expected detected dep
  if equal then do
    susp <- envTakeSusp
    forM_ susp $ \(Check src val typ dep) -> do
      termCheckGo src val typ dep
    return ()
  else do
    envLog (Error src expected detected term dep)
    envFail
    
-- termCheckReport :: Int -> Bool -> Term -> Term -> Term -> Int -> Env ()
-- termCheckReport src False detected expected value dep = do
  -- envLog (Error src detected expected value dep)
  -- envFail
-- termCheckReport src True detected expected value dep =
  -- envPure ()

termCheckDef :: Term -> Env ()
termCheckDef (Ref nam (Ann chk val typ)) = termCheck 0 val typ 0 >> return ()
termCheckDef (Ref nam val)               = termInfer val 0 >> return ()
termCheckDef other                       = error "invalid top-level definition"

-- Stringification
-- ---------------

termShow :: Term -> Int -> String
termShow (All nam inp bod) dep =
  let nam' = nam
      inp' = termShow inp dep
      bod' = termShow (bod (Var nam dep)) (dep + 1)
  in stringJoin ["∀(" , nam' , ": " , inp' , ") " , bod']
termShow (Lam nam bod) dep =
  let nam' = nam
      bod' = termShow (bod (Var nam dep)) (dep + 1)
  in stringJoin ["λ" , nam' , " " , bod']
termShow (App fun arg) dep =
  let fun' = termShow fun dep
      arg' = termShow arg dep
  in stringJoin ["(" , fun' , " " , arg' , ")"]
termShow (Ann chk val typ) dep =
  let val' = termShow val dep
      typ' = termShow typ dep
  in stringJoin ["{" , val' , ": " , typ' , "}"]
termShow (Slf nam typ bod) dep =
  termShow typ dep
termShow (Ins val) dep =
  let val' = termShow val dep
  in stringJoin ["~" , val']
termShow (Ref nam val) dep = nam
termShow (Let nam val bod) dep =
  let nam' = nam
      val' = termShow val dep
      bod' = termShow (bod (Var nam dep)) (dep + 1)
  in stringJoin ["let " , nam' , " = " , val' , "; " , bod']
termShow (Use nam val bod) dep =
  let nam' = nam
      val' = termShow val dep
      bod' = termShow (bod (Var nam dep)) (dep + 1)
  in stringJoin ["use " , nam' , " = " , val' , "; " , bod']
termShow Set dep = "*"
termShow U60 dep = "#U60"
termShow (Num val) dep =
  let val' = u60Show val
  in stringJoin ["#" , val']
termShow (Op2 opr fst snd) dep =
  let opr' = operShow opr
      fst' = termShow fst dep
      snd' = termShow snd dep
  in stringJoin ["#(" , opr' , " " , fst' , " " , snd' , ")"]
termShow (Mat nam x z s p) dep =
  let nam' = nam
      x'   = termShow x dep
      z'   = termShow z dep
      s'   = termShow (s (Var (stringConcat nam "-1") dep)) (dep + 1)
      p'   = termShow (p (Var nam dep)) dep
  in stringJoin ["#match " , nam' , " = " , x' , " { #0: " , z' , " #+: " , s' , " }: " , p']
termShow (Txt txt) dep = stringJoin [quote , txt , quote]
termShow (Nat val) dep = show val
termShow (Hol nam ctx) dep = stringJoin ["?" , nam]
termShow (Met uid spn) dep = stringJoin ["(_", termShowSpn (reverse spn) dep, ")"]
termShow (Var nam idx) dep = nam
-- termShow (Var nam idx) dep = stringJoin [nam, "^", show idx]
termShow (Src src val) dep = termShow val dep
-- termShow (Src src val) dep = stringJoin ["!", (termShow val dep)]

termShowSpn :: [Term] -> Int -> String
termShowSpn []       dep = ""
termShowSpn (x : xs) dep = stringJoin [" ", termShow x dep, termShowSpn xs dep]

operShow :: Oper -> String
operShow ADD = "+"
operShow SUB = "-"
operShow MUL = "*"
operShow DIV = "/"
operShow MOD = "%"
operShow EQ  = "=="
operShow NE  = "!="
operShow LT  = "<"
operShow GT  = ">"
operShow LTE = "<="
operShow GTE = ">="
operShow AND = "&"
operShow OR  = "|"
operShow XOR = "^"
operShow LSH = "<<"
operShow RSH = ">>"

contextShow :: Map Term -> [Term] -> Int -> String
contextShow fill []     dep = ""
contextShow fill (x:xs) dep = stringJoin [" " , contextShowAnn fill x dep , contextShow fill xs dep]

contextShowAnn :: Map Term -> Term -> Int -> String
contextShowAnn fill (Ann chk val typ) dep = stringJoin ["{" , termShow (termNormal fill 0 val dep) dep , ": " , termShow (termNormal fill 0 typ dep) dep , "}"]
contextShowAnn fill term              dep = termShow (termNormal fill 0 term dep) dep

infoShow :: Map Term -> Info -> String
infoShow fill (Found name typ ctx dep) =
  let typ' = termShow (termNormal fill 1 typ dep) dep
      ctx' = stringTail (contextShow fill ctx dep)
  in stringJoin ["#found{", name, " ", typ', " [", ctx', "]}"]
infoShow fill (Error src expected detected value dep) =
  let exp = termShow (termNormal fill 1 expected dep) dep
      det = termShow (termNormal fill 1 detected dep) dep
      val = termShow (termNormal fill 0 value dep) dep
  in stringJoin ["#error{", exp, " ", det, " ", val, " ", u60Show src, "}"]
infoShow fill (Solve name term dep) =
  let term' = termShow (termNormal fill 1 term dep) dep
  in stringJoin ["#solve{", show name, " ",  term', "}"]
infoShow fill (Vague name) =
  stringJoin ["#vague{", name, "}"]
infoShow fill (Print value dep) =
  let val = termShow (termNormal fill 0 value dep) dep
  in stringJoin ["#print{", val, "}"]

-- API
-- ---

-- Normalizes a term
apiNormal :: Term -> IO ()
apiNormal term = putStrLn $ infoShow mapNew (Print (termNormal mapNew 2 term 0) 0)

-- Type-checks a term
apiCheck :: Term -> IO ()
apiCheck term = case envRun $ termCheckDef term of
  Done state value -> apiPrintLogs state
  Fail state       -> apiPrintLogs state

apiPrintLogs :: State -> IO ()
apiPrintLogs (State fill susp (log : logs)) = do
  putStrLn $ infoShow fill log
  apiPrintLogs (State fill susp logs)
apiPrintLogs (State fill susp []) = do
  return ()

-- Main
-- ----

hvmPrint :: String -> a -> a
hvmPrint = undefined

-- main :: IO ()
-- main = apiCheck book_main

-- Book
-- ----

xtest :: Term
xtest = Ref "test" $ Ann True val typ where
  typ = (All "P" Set $ \p -> (All "f" (All "x" p $ \x -> p) $ \f -> (All "x" p $ \x -> p)))
  val = (Lam "P" $ \p -> (Lam "f" $ \f -> (Lam "x" $ \x -> f)))

xString = undefined; xString_cons = undefined; xString_nil = undefined; xNat = undefined; xNat_succ = undefined; xNat_zero = undefined
