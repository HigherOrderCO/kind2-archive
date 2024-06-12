-- Kind2-Core
-- ==========
--
-- This is a Haskell implementation of Kind2's proof kernel. It is based on the
-- Calculus of Constructions, extended with Self-Types and U60 operations. This
-- allows us to express arbitrary inductive types and proofs with a simple core.
-- 
-- HVM1 and HVM2 versions are provided. To make all versions similar, this file
-- will reimplement Prelude functions, and will use a primitive coding style.

import Data.Char (chr, ord)
import Prelude hiding (LT, GT, EQ, map, even, reverse, elem)
import Debug.Trace

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
  | Ref String Term

  -- Local let-definition
  | Let String Term (Term -> Term)

  -- Local use-definition
  | Use String Term (Term -> Term)

  -- Type : Type
  | Set

  -- U60 Type
  | U60

  -- U60 Value
  | Num Int

  -- U60 Binary Operation
  | Op2 Oper Term Term

  -- U60 Elimination
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

-- Type-Checker Outputs
data Info
  = Found String Term [Term] Int
  | Solve Int Term Int
  | Error Int Term Term Term Int
  | Vague String
  | Print Term Int

-- Checker State
data Check = Check Int Term Term Int -- posponed check
data State = State (Map Term) [Check] [Info] -- state type
data Res a = Done State a | Fail State -- result type
data Env a = Env (State -> Res a) -- monadic checker

-- Maps
data Bits = O Bits | I Bits | E deriving Show
data Map a = Leaf | Node (Maybe a) (Map a) (Map a) deriving Show

-- Prelude
-- -------

even :: Int -> Bool
even n = mod n 2 == 0

reverse :: [a] -> [a] 
reverse l =  reverseGo l [] where
  reverseGo []     a = a
  reverseGo (x:xs) a = reverseGo xs (x:a)

elem :: Eq a => a -> [a] -> Bool
elem a []     = False
elem a (x:xs) = if a == x then True else elem a xs

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
termReduce fill lv (Swi nam x z s p) = termReduceSwi fill lv nam (termReduce fill lv x) z s p
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

termReduceSwi :: Map Term -> Int -> String -> Term -> Term -> (Term -> Term) -> (Term -> Term) -> Term
termReduceSwi fill 2  nam (Ref _ x)           z s p = termReduceSwi fill 2 nam x z s p
termReduceSwi fill 1  nam (Ref _ x)           z s p = termReduceSwi fill 1 nam x z s p
termReduceSwi fill lv nam (Num 0)             z s p = termReduce fill lv z
termReduceSwi fill lv nam (Num n)             z s p = termReduce fill lv (s (Num (n - 1)))
termReduceSwi fill lv nam (Op2 ADD (Num 1) k) z s p = termReduce fill lv (s k)
termReduceSwi fill lv nam val                 z s p = Swi nam val z s p

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
  termNormalGo fill lv (Swi nam x z s p) dep = Swi nam (termNormal fill lv x dep) (termNormal fill lv z dep) (\k -> termNormal fill lv (s (Var (stringConcat nam "-1") dep)) dep) (\k -> termNormal fill lv (p (Var nam dep)) dep)
  termNormalGo fill lv (Txt val)         dep = Txt val
  termNormalGo fill lv (Nat val)         dep = Nat val
  termNormalGo fill lv (Var nam idx)     dep = Var nam idx
  termNormalGo fill lv (Src src val)     dep = Src src (termNormal fill lv val dep)
  termNormalGo fill lv (Met uid spn)     dep = Met uid spn -- TODO: normalize spine

-- Equality
-- --------

-- Conversion checking works as follows:
-- 1. Two terms are equal if their wnf's are structurally identical
-- 2. Otherwise, they're equal if they're similar (component-wise equal)
-- This allows us to always identify two terms that have the same normal form,
-- while also allowing us to return earlier, if they become identical at any
-- point in the reduction. Note that, for Self types, the similarity checker
-- will "un-reduce" from `$(x: (T a b)) body` to `(T a b)`, avoiding loops.

-- trace ("equal:\n- " ++ termShow a dep ++ "\n- " ++ termShow b dep) $ do
termEqual :: Term -> Term -> Int -> Env Bool
termEqual a b dep = do
  fill <- envGetFill
  let a' = termReduce fill 2 a
  let b' = termReduce fill 2 b
  same <- termTryIdentical a' b' dep
  if same then do
    return True
  else do
    termSimilar a' b' dep

termTryIdentical :: Term -> Term -> Int -> Env Bool
termTryIdentical a b dep = do
  state <- envSnapshot
  equal <- termIdentical a b dep
  if equal
    then envPure True
    else envRewind state >> envPure False

termSimilar :: Term -> Term -> Int -> Env Bool
termSimilar a b dep = go a b dep where
  go (All aNam aInp aBod) (All bNam bInp bBod) dep = do
    eInp <- termEqual aInp bInp dep
    eBod <- termEqual (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
    envPure (eInp && eBod)
  go (Lam aNam aBod) (Lam bNam bBod) dep =
    termEqual (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
  go (App aFun aArg) (App bFun bArg) dep = do
    eFun <- termSimilar aFun bFun dep
    eArg <- termEqual aArg bArg dep
    envPure (eFun && eArg)
  go (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
    termSimilar (termReduce mapNew 0 aTyp) (termReduce mapNew 0 bTyp) dep
  go (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep = do
    eFst <- termEqual aFst bFst dep
    eSnd <- termEqual aSnd bSnd dep
    envPure (eFst && eSnd)
  go (Swi aNam aX aZ aS aP) (Swi bNam bX bZ bS bP) dep = do
    eX <- termEqual aX bX dep
    eZ <- termEqual aZ bZ dep
    eS <- termEqual (aS (Var (stringConcat aNam "-1") dep)) (bS (Var (stringConcat bNam "-1") dep)) dep
    eP <- termEqual (aP (Var aNam dep)) (bP (Var bNam dep)) dep
    envPure (eX && eZ && eS && eP)
  go a b dep = termIdentical a b dep

termIdentical :: Term -> Term -> Int -> Env Bool
termIdentical a b dep = go a b dep where
  go (All aNam aInp aBod) (All bNam bInp bBod) dep = do
    iInp <- termIdentical aInp bInp dep
    iBod <- termIdentical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
    return (iInp && iBod)
  go (Lam aNam aBod) (Lam bNam bBod) dep =
    termIdentical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
  go (App aFun aArg) (App bFun bArg) dep = do
    iFun <- termIdentical aFun bFun dep
    iArg <- termIdentical aArg bArg dep
    return (iFun && iArg)
  go (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
    termIdentical aTyp bTyp dep
  go (Ins aVal) b dep =
    termIdentical aVal b dep
  go a (Ins bVal) dep =
    termIdentical a bVal dep
  go (Let aNam aVal aBod) b dep =
    termIdentical (aBod aVal) b dep
  go a (Let bNam bVal bBod) dep =
    termIdentical a (bBod bVal) dep
  go (Use aNam aVal aBod) b dep =
    termIdentical (aBod aVal) b dep
  go a (Use bNam bVal bBod) dep =
    termIdentical a (bBod bVal) dep
  go Set Set dep =
    return True
  go (Ann chk aVal aTyp) b dep =
    termIdentical aVal b dep
  go a (Ann chk bVal bTyp) dep =
    termIdentical a bVal dep
  go a (Met bUid bSpn) dep =
    termUnify bUid bSpn a dep
  go (Met aUid aSpn) b dep =
    termUnify aUid aSpn b dep
  go (Hol aNam aCtx) b dep =
    return True
  go a (Hol bNam bCtx) dep =
    return True
  go U60 U60 dep =
    return True
  go (Num aVal) (Num bVal) dep =
    return (aVal == bVal)
  go (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep = do
    iFst <- termIdentical aFst bFst dep
    iSnd <- termIdentical aSnd bSnd dep
    return (iFst && iSnd)
  go (Swi aNam aX aZ aS aP) (Swi bNam bX bZ bS bP) dep = do
    iX <- termIdentical aX bX dep
    iZ <- termIdentical aZ bZ dep
    iS <- termIdentical (aS (Var (stringConcat aNam "-1") dep)) (bS (Var (stringConcat bNam "-1") dep)) dep
    iP <- termIdentical (aP (Var aNam dep)) (bP (Var bNam dep)) dep
    return (iX && iZ && iS && iP)
  go (Txt aTxt) (Txt bTxt) dep =
    return (aTxt == bTxt)
  go (Nat aVal) (Nat bVal) dep =
    return (aVal == bVal)
  go (Src aSrc aVal) b dep =
    termIdentical aVal b dep
  go a (Src bSrc bVal) dep =
    termIdentical a bVal dep
  go (Ref aNam aVal) (Ref bNam bVal) dep =
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
termUnify :: Int -> [Term] -> Term -> Int -> Env Bool
termUnify uid spn b dep = do
  fill <- envGetFill
  let unsolved = not (mapHas (key uid) fill) -- is this hole not already solved?
  let solvable = termUnifyValid fill spn [] -- does the spine satisfies conditions?
  let no_loops = not $ termUnifyIsRec fill uid b dep -- is the solution not recursive?
  -- If all is ok, generate the solution and return true
  if unsolved && solvable && no_loops then do
    let solution = termUnifySolve fill uid spn b
    -- trace ("solve: " ++ show uid ++ " " ++ termShow solution dep) $ do
    envFill uid solution
    return True
  -- Otherwise, return true iff both are identical metavars
  else case b of
    (Met bUid bSpn) -> return $ uid == bUid
    other           -> return $ False

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

-- Checks if a hole uid occurs recursively inside a term
termUnifyIsRec :: Map Term -> Int -> Term -> Int -> Bool
termUnifyIsRec fill uid (All nam inp bod) dep = termUnifyIsRec fill uid inp dep || termUnifyIsRec fill uid (bod (Var nam dep)) (dep + 1)
termUnifyIsRec fill uid (Lam nam bod)     dep = termUnifyIsRec fill uid (bod (Var nam dep)) (dep + 1)
termUnifyIsRec fill uid (App fun arg)     dep = termUnifyIsRec fill uid fun dep || termUnifyIsRec fill uid arg dep
termUnifyIsRec fill uid (Ann chk val typ) dep = termUnifyIsRec fill uid val dep || termUnifyIsRec fill uid typ dep
termUnifyIsRec fill uid (Slf nam typ bod) dep = termUnifyIsRec fill uid typ dep || termUnifyIsRec fill uid (bod (Var nam dep)) (dep + 1)
termUnifyIsRec fill uid (Ins val)         dep = termUnifyIsRec fill uid val dep
termUnifyIsRec fill uid (Let nam val bod) dep = termUnifyIsRec fill uid val dep || termUnifyIsRec fill uid (bod (Var nam dep)) (dep + 1)
termUnifyIsRec fill uid (Use nam val bod) dep = termUnifyIsRec fill uid val dep || termUnifyIsRec fill uid (bod (Var nam dep)) (dep + 1)
termUnifyIsRec fill uid (Hol nam ctx)     dep = False
termUnifyIsRec fill uid (Op2 opr fst snd) dep = termUnifyIsRec fill uid fst dep || termUnifyIsRec fill uid snd dep
termUnifyIsRec fill uid (Swi nam x z s p) dep = termUnifyIsRec fill uid x dep || termUnifyIsRec fill uid z dep || termUnifyIsRec fill uid (s (Var (stringConcat nam "-1") dep)) (dep + 1) || termUnifyIsRec fill uid (p (Var nam dep)) dep
termUnifyIsRec fill uid (Src src val)     dep = termUnifyIsRec fill uid val dep
termUnifyIsRec fill uid (Met bUid bSpn)   dep = case termReduceMet fill 2 bUid bSpn of
  (Met bUid bSpn) -> uid == bUid
  term            -> termUnifyIsRec fill uid term dep
termUnifyIsRec fill uid _                 dep = False

-- Substitutes a Bruijn level variable by a `neo` value in `term`.
termUnifySubst :: Int -> Term -> Term -> Term
termUnifySubst lvl neo (All nam inp bod) = All nam (termUnifySubst lvl neo inp) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Lam nam bod)     = Lam nam (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (App fun arg)     = App (termUnifySubst lvl neo fun) (termUnifySubst lvl neo arg)
termUnifySubst lvl neo (Ann chk val typ) = Ann chk (termUnifySubst lvl neo val) (termUnifySubst lvl neo typ)
termUnifySubst lvl neo (Slf nam typ bod) = Slf nam (termUnifySubst lvl neo typ) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Ins val)         = Ins (termUnifySubst lvl neo val)
termUnifySubst lvl neo (Ref nam val)     = Ref nam (termUnifySubst lvl neo val)
termUnifySubst lvl neo (Let nam val bod) = Let nam (termUnifySubst lvl neo val) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Use nam val bod) = Use nam (termUnifySubst lvl neo val) (\x -> termUnifySubst lvl neo (bod x))
termUnifySubst lvl neo (Met uid spn)     = Met uid (listMap (termUnifySubst lvl neo) spn)
termUnifySubst lvl neo (Hol nam ctx)     = Hol nam (listMap (termUnifySubst lvl neo) ctx)
termUnifySubst lvl neo Set               = Set
termUnifySubst lvl neo U60               = U60
termUnifySubst lvl neo (Num n)           = Num n
termUnifySubst lvl neo (Op2 opr fst snd) = Op2 opr (termUnifySubst lvl neo fst) (termUnifySubst lvl neo snd)
termUnifySubst lvl neo (Swi nam x z s p) = Swi nam (termUnifySubst lvl neo x) (termUnifySubst lvl neo z) (\k -> termUnifySubst lvl neo (s k)) (\k -> termUnifySubst lvl neo (p k))
termUnifySubst lvl neo (Txt txt)         = Txt txt
termUnifySubst lvl neo (Nat val)         = Nat val
termUnifySubst lvl neo (Var nam idx)     = if lvl == idx then neo else Var nam idx
termUnifySubst lvl neo (Src src val)     = Src src (termUnifySubst lvl neo val)

-- Type-Checking
-- -------------

-- Note that, for type-checking, instead of passing down contexts (as usual), we
-- just annotate variables (with a `{x: T}` type hint) and check. This has the
-- same effect, while being slightly more efficient. Type derivations comments
-- are written in this style too.

-- ### Inference

termInfer :: Term -> Int -> Env Term
termInfer term dep =
  -- trace ("infer: " ++ termShow term dep) $
    termInferGo term dep

termInferGo :: Term -> Int -> Env Term

-- inp : Set
-- (bod {nam: inp}) : Set
-- ----------------------- function
-- (∀(nam: inp) bod) : Set
termInferGo (All nam inp bod) dep = do
  envSusp (Check 0 inp Set dep)
  envSusp (Check 0 (bod (Ann False (Var nam dep) inp)) Set (dep + 1))
  return Set

-- fun : ∀(ftyp_nam: ftyp_inp) ftyp_bod
-- arg : ftyp_inp
-- ------------------------------------ application
-- (fun arg) : (ftyp_bod arg)
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

-- 
-- ---------------- annotation (infer)
-- {val: typ} : typ
termInferGo (Ann chk val typ) dep = do
  if chk then do
    termCheck 0 val typ dep
  else do
    return ()
  return typ

-- (bod {nam: typ}) : Set
-- ----------------------- self-type
-- ($(nam: typ) bod) : Set
termInferGo (Slf nam typ bod) dep = do
  envSusp (Check 0 (bod (Ann False (Var nam dep) typ)) Set (dep + 1))
  return Set

-- val : $(vtyp_nam: vtyp_typ) vtyp_bod
-- ------------------------------------ self-inst (infer)
-- ~val : (vtyp_bod (~val))
termInferGo (Ins val) dep = do
  vtyp <- termInfer val dep
  fill <- envGetFill
  case termReduce fill 2 vtyp of
    (Slf vtyp_nam vtyp_typ vtyp_bod) -> do
      return $ vtyp_bod (Ins val)
    otherwise -> do
      envLog (Error 0 (Hol "self-type" []) vtyp (Ins val) dep)
      envFail

-- val : T
-- ----------------- reference
-- (Ref nam val) : T
termInferGo (Ref nam val) dep = do
  termInfer val dep

-- ...
-- --------- type-in-type
-- Set : Set
termInferGo Set dep = do
  return Set

-- ...
-- --------- U60-type
-- U60 : Set
termInferGo U60 dep = do
  return Set

-- ...
-- ----------- U60-value
-- <num> : U60
termInferGo (Num num) dep = do
  return U60

-- ...
-- -------------- String-literal
-- "txt" : String
termInferGo (Txt txt) dep = do
  return xString

-- ...
-- --------- Nat-literal
-- 123 : Nat
termInferGo (Nat val) dep = do
  return xNat

-- fst : U60
-- snd : U60
-- ----------------- U60-operator
-- (+ fst snd) : U60
termInferGo (Op2 opr fst snd) dep = do
  envSusp (Check 0 fst U60 dep)
  envSusp (Check 0 snd U60 dep)
  return U60

-- x : U60
-- p : U60 -> Set
-- z : (p 0)
-- s : (n: U60) -> (p (+ 1 n))
-- ------------------------------------- U60-elim
-- (switch x { 0: z ; _: s }: p) : (p x)
termInferGo (Swi nam x z s p) dep = do
  envSusp (Check 0 x U60 dep)
  envSusp (Check 0 (p (Ann False (Var nam dep) U60)) Set dep)
  envSusp (Check 0 z (p (Num 0)) dep)
  envSusp (Check 0 (s (Ann False (Var (stringConcat nam "-1") dep) U60)) (p (Op2 ADD (Num 1) (Var (stringConcat nam "-1") dep))) (dep + 1))
  return (p x)

-- val : typ
-- (bod {nam: typ}) : T
-- ------------------------ let-binder (infer)
-- (let nam = val; bod) : T
termInferGo (Let nam val bod) dep = do
  typ <- termInfer val dep
  termInfer (bod (Ann False (Var nam dep) typ)) dep

-- (bod val) : T
-- ------------------------ use-binder (infer)
-- (use nam = val; bod) : T
termInferGo (Use nam val bod) dep = do
  termInfer (bod val) dep

-- Can't Infer λ
termInferGo (Lam nam bod) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_lambda" []) (Lam nam bod) dep)
  envFail

-- Can't Infer ?A
termInferGo (Hol nam ctx) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_hole" []) (Hol nam ctx) dep)
  envFail

-- Can't Infer _
termInferGo (Met uid spn) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_meta" []) (Met uid spn) dep)
  envFail

-- Can't Infer Var
termInferGo (Var nam idx) dep = do
  envLog (Error 0  (Hol "type_annotation" []) (Hol "untyped_variable" []) (Var nam idx) dep)
  envFail

-- Src-passthrough
termInferGo (Src src val) dep = do
  termInfer val dep

termCheck :: Int -> Term -> Term -> Int -> Env ()
termCheck src val typ dep =
  -- trace ("check: " ++ termShow val dep ++ "\n    :: " ++ termShow typ dep) $
  termCheckGo src val typ dep

-- ### Checking

termCheckGo :: Int -> Term -> Term -> Int -> Env ()

-- (bod {typ_nam: typ_inp}) : (typ_bod {nam: typ_inp})
-- --------------------------------------------------- lambda
-- (λnam bod) : (∀(typ_nam: typ_inp) typ_bod)
termCheckGo src (Lam nam bod) typx dep = do
  fill <- envGetFill
  case termReduce fill 2 typx of
    (All typ_nam typ_inp typ_bod) -> do
      let ann  = Ann False (Var nam dep) typ_inp
      let term = bod ann
      let typx = typ_bod ann
      termCheck 0 term typx (dep + 1)
    otherwise -> do
      termInfer (Lam nam bod) dep
      return ()

-- val : (typ_bod ~val)
-- ---------------------------------- self-inst (check)
-- ~val : $(typ_nam: typ_typ) typ_bod
termCheckGo src (Ins val) typx dep = do
  fill <- envGetFill
  case termReduce fill 2 typx of
    Slf typ_nam typ_typ typ_bod -> do
      termCheck 0 val (typ_bod (Ins val)) dep
    _ -> do
      termInfer (Ins val) dep
      return ()

-- val : typ
-- (bod {nam: typ}) : T
-- ------------------------ let-binder (check)
-- (let nam = val; bod) : T
termCheckGo src (Let nam val bod) typx dep = do
  typ <- termInfer val dep
  termCheck 0 (bod (Ann False (Var nam dep) typ)) typx dep

-- (bod val) : T
-- ------------------------ use-binder (check)
-- (use nam = val; bod) : T
termCheckGo src (Use nam val bod) typx dep = do
  termCheck 0 (bod val) typx dep

-- ...
-- ------ inspection
-- ?A : T
termCheckGo src (Hol nam ctx) typx dep = do
  envLog (Found nam typx ctx dep)
  return ()

-- ...
-- ----- metavar
-- _ : T
termCheckGo src (Met uid spn) typx dep = do
  return ()

-- ...
-- ---------------- annotation (check)
-- {val: typ} : typ
termCheckGo src (Ann chk val typ) typx dep = do
  termCheckCompare src val typ typx dep
  if chk then do
    termCheck src val typ dep
  else do
    return ()

-- val : T
-- ------- source (just skipped)
-- val : T
termCheckGo _ (Src src val) typx dep = do
  termCheck src val typx dep

-- A == B
-- val : A
-- -------
-- val : B
termCheckGo src term typx dep = do
  infer <- termInfer term dep
  termCheckCompare src term typx infer dep

-- Checks types equality and reports
termCheckCompare src term expected detected dep = do
  equal <- termEqual expected detected dep
  if equal then do
    susp <- envTakeSusp
    listCheck susp 
    return ()
  else do
    envLog (Error src expected detected term dep)
    envFail

listCheck :: [Check] -> Env ()
listCheck []     = do
  return ()
listCheck (x:xs) = do
  let (Check src val typ dep) = x;
  termCheck src val typ dep
  listCheck xs

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
termShow U60 dep = "U60"
termShow (Num val) dep =
  let val' = u60Show val
  in stringJoin [val']
termShow (Op2 opr fst snd) dep =
  let opr' = operShow opr
      fst' = termShow fst dep
      snd' = termShow snd dep
  in stringJoin ["(" , opr' , " " , fst' , " " , snd' , ")"]
termShow (Swi nam x z s p) dep =
  let nam' = nam
      x'   = termShow x dep
      z'   = termShow z dep
      s'   = termShow (s (Var (stringConcat nam "-1") dep)) (dep + 1)
      p'   = termShow (p (Var nam dep)) dep
  in stringJoin ["switch " , nam' , " = " , x' , " { 0: " , z' , " _: " , s' , " }: " , p']
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
