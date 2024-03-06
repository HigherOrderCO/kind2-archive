-- This is a Haskell implementation of Kind2's type checker. Since Kind2 isn't
--
-- bootstrapped, we can't use Kind2 itself to type-check it, and developing a
-- complex checker in an untyped language (like HVM) is hard. As such, this
-- Haskell view helps me develop and debug the checker, and it is done in a way
-- that makes it easy to manually compile it to HVM, keeping an HVM view. It can
-- also be useful to let us benchmark all versions (GHC/HVM1/HVM2), giving us a
-- good idea on how these compare in performance.

import Data.Char (chr, ord)
import Prelude hiding (LT, GT, EQ)
import Debug.Trace

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
  | Ann Term Term
  | Slf String Term (Term -> Term)
  | Ins Term
  | Ref String Term
  | Let String Term (Term -> Term)
  | Set
  | U60
  | Num Int
  | Op2 Oper Term Term
  | Mat String Term Term (Term -> Term) (Term -> Term)
  | Txt String
  | Hol String [Term]
  | Met Int
  | Var String Int
  | Src Int Term

data Info
  = Found String Term [Term] Int
  | Solve Int Term Int
  | Error Int Term Term Term Int
  | Vague String

data State = State [Info] (Map Term) -- state type
data Res a = Done State a | Fail State Info -- result type
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

-- Pattern matches on a computation result
resMatch :: Res a -> (State -> a -> b) -> (State -> Info -> b) -> b
resMatch (Done state value) done _    = done state value
resMatch (Fail state error) _    fail = fail state error

-- Monadic bind function
envBind :: Env a -> (a -> Env b) -> Env b
envBind (Env a) b = Env $ \state -> case a state of
  Done state' value -> let Env b' = b value in b' state'
  Fail state' error -> Fail state' error

envPure :: a -> Env a
envPure a = Env $ \state -> Done state a

envFail :: Info -> Env a
envFail i = Env $ \state -> Fail state i

envRun :: Env a -> Res a
envRun (Env chk) = chk (State [] mapNew)

envLog :: Info -> Env Int
envLog log = Env $ \(State logs fill) -> Done (State (log : logs) fill) 1

envSnapshot :: Env State
envSnapshot = Env $ \state -> Done state state

envRewind :: State -> Env Int
envRewind state = Env $ \_ -> Done state 0

envGetFill :: Env (Map Term)
envGetFill = Env $ \(State logs fill) -> Done (State logs fill) fill

instance Functor Env where
  fmap f (Env chk) = Env $ \logs -> case chk logs of
    Done logs' a -> Done logs' (f a)
    Fail logs' e -> Fail logs' e

instance Applicative Env where
  pure = envPure
  (Env chkF) <*> (Env chkA) = Env $ \logs -> case chkF logs of
    Done logs' f -> case chkA logs' of
      Done logs'' a -> Done logs'' (f a)
      Fail logs'' e -> Fail logs'' e
    Fail logs' e -> Fail logs' e

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
termReduce fill lv (Ann val typ)     = termReduce fill lv val
termReduce fill lv (Ins val)         = termReduce fill lv val
termReduce fill lv (Ref nam val)     = termReduceRef fill lv nam (termReduce fill lv val)
termReduce fill lv (Let nam val bod) = termReduce fill lv (bod val)
termReduce fill lv (Op2 opr fst snd) = termReduceOp2 fill lv opr (termReduce fill lv fst) (termReduce fill lv snd)
termReduce fill lv (Mat nam x z s p) = termReduceMat fill lv nam (termReduce fill lv x) z s p
termReduce fill lv (Txt txt)         = termReduceTxt fill lv txt
termReduce fill lv (Src src val)     = termReduce fill lv val
termReduce fill lv (Met uid)         = termReduceMet fill lv uid
termReduce fill lv val               = val

termReduceApp :: Map Term -> Int -> Term -> Term -> Term
termReduceApp fill 2  (Ref nam val) arg = termReduceApp fill 2 val arg
termReduceApp fill 1  (Ref nam val) arg = termReduceApp fill 1 val arg
termReduceApp fill lv (Lam nam bod) arg = termReduce fill lv (bod (termReduce fill 0 arg))
termReduceApp fill lv fun arg           = App fun arg

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

termReduceMet :: Map Term -> Int -> Int -> Term
termReduceMet fill lv uid = case mapGet (key uid) fill of
  Just val -> termReduce fill lv val
  Nothing  -> Met uid

termReduceTxt :: Map Term -> Int -> String -> Term
termReduceTxt fill lv txt = Txt txt

-- Normalization
-- -------------

termNormal :: Map Term -> Int -> Term -> Int -> Term
termNormal fill lv term dep = termNormalGo fill lv (termNormalPrefer fill (termReduce fill 0 term) (termReduce fill lv term)) dep where

  termNormalPrefer fill soft (Lam _ _)   = soft
  termNormalPrefer fill soft (Slf _ _ _) = soft
  termNormalPrefer fill soft (All _ _ _) = soft
  termNormalPrefer fill soft hard        = hard

  termNormalGo fill lv (All nam inp bod) dep = All nam (termNormal fill lv inp dep) (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (Lam nam bod)     dep = Lam nam (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (App fun arg)     dep = App (termNormal fill lv fun dep) (termNormal fill lv arg dep)
  termNormalGo fill lv (Ann val typ)     dep = Ann (termNormal fill lv val dep) (termNormal fill lv typ dep)
  termNormalGo fill lv (Slf nam typ bod) dep = Slf nam typ (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (Ins val)         dep = Ins (termNormal fill lv val dep)
  termNormalGo fill lv (Ref nam val)     dep = Ref nam (termNormal fill lv val dep)
  termNormalGo fill lv (Let nam val bod) dep = Let nam (termNormal fill lv val dep) (\x -> termNormal fill lv (bod (Var nam dep)) (dep + 1))
  termNormalGo fill lv (Hol nam ctx)     dep = Hol nam ctx
  termNormalGo fill lv Set               dep = Set
  termNormalGo fill lv U60               dep = U60
  termNormalGo fill lv (Num val)         dep = Num val
  termNormalGo fill lv (Op2 opr fst snd) dep = Op2 opr (termNormal fill lv fst dep) (termNormal fill lv snd dep)
  termNormalGo fill lv (Mat nam x z s p) dep = Mat nam (termNormal fill lv x dep) (termNormal fill lv z dep) (\k -> termNormal fill lv (s (Var (stringConcat nam "-1") dep)) dep) (\k -> termNormal fill lv (p (Var nam dep)) dep)
  termNormalGo fill lv (Txt val)         dep = Txt val
  termNormalGo fill lv (Var nam idx)     dep = Var nam idx
  termNormalGo fill lv (Src src val)     dep = Src src (termNormal fill lv val dep)
  termNormalGo fill lv (Met uid)         dep = Met uid

-- Equality
-- --------

termEqual :: Term -> Term -> Int -> Env Bool
termEqual a b dep =
  -- trace ("equal: " ++ termShow a dep ++ "\n    == " ++ termShow b dep) $
  termTryIdentical a b dep $ do
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
  eFun <- termEqual aFun bFun dep
  eArg <- termEqual aArg bArg dep
  envPure (eFun && eArg)
termSimilar (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
  termSimilar (termReduce mapNew 0 aTyp) (termReduce mapNew 0 bTyp) dep
termSimilar (Hol aNam aCtx) (Hol bNam bCtx) dep =
  envPure (aNam == bNam)
termSimilar (Met aUid) (Met bUid) dep =
  envPure (aUid == bUid)
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
termSimilar a b dep = envPure False

termIdentical :: Term -> Term -> Int -> Env Bool
termIdentical a b dep = 
  -- termUnifyTry a b dep $
  -- termUnifyTry b a dep $
  termIdenticalGo a b dep

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
termIdenticalGo Set Set dep =
  envPure True
termIdenticalGo (Ann aVal aTyp) b dep =
  termIdentical aVal b dep
termIdenticalGo a (Ann bVal bTyp) dep =
  termIdentical a bVal dep
termIdenticalGo (Met aUid) (Met bUid) dep =
  envPure (aUid == bUid)
termIdenticalGo (Hol aNam aCtx) (Hol bNam bCtx) dep =
  envPure (aNam == bNam)
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

-- TODO: the code below has been implemented in HVM, an untyped Haskell-like
-- functional language. We're porting it to Haskell.

-- // The unification algorithm is a simple pattern unifier, based on smalltt:
-- // > https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/Main.hs
-- // The 'Unify.try' fn will attempt to match the following pattern:
-- //   (?A x y z ...) = B
-- // Where:
-- //   1. The LHS spine, `x y z ...`, consists of distinct variables.
-- //   2. Every free var of the RHS, `B`, occurs in the spine.
-- //   3. The LHS hole, `?A`, doesn't occur in the RHS, `B`.
-- // If it is successful, it outputs the following substitution:
-- //   ?A = λx λy λz ... B
-- // In this checker, we don't allow holes to occur in solutions at all.

termUnifyTry :: Term -> Term -> Int -> Env Bool -> Env Bool
termUnifyTry a b dep cont = do
  (maybeMatch (termUnifyMatch a b dep mapNew)
    (\(key, val) ->
      envBind (envLog (Solve key val dep)) $ \_ ->
      envPure True)
    (if termUnifySkip a
      then envPure True
      else cont))

termUnifyMatch :: Term -> Term -> Int -> Map Term -> Maybe (Int, Term)
termUnifyMatch (App fun (Var nam idx)) b dep ctx | mapHas (key idx) ctx = Nothing
termUnifyMatch (App fun (Var nam idx)) b dep ctx | otherwise =
  let ctx' = mapSet (key idx) (Var nam dep) ctx in
  maybeBind (termUnifyMatch fun b (dep + 1) ctx') $ \(key,val) ->
  maybePure (key, Lam nam $ \x -> val) -- TODO: subst [var dep <- x]
termUnifyMatch (Met uid) b dep ctx =
  maybeBind (termUnifySolution b dep uid ctx) $ \neo ->
  maybePure (uid, neo)
termUnifyMatch (App fun (Ann val _)) b dep ctx = termUnifyMatch (App fun val) b dep ctx
termUnifyMatch (App fun (Ins val))   b dep ctx = termUnifyMatch (App fun val) b dep ctx
termUnifyMatch (App fun (Src _ val)) b dep ctx = termUnifyMatch (App fun val) b dep ctx
termUnifyMatch (Ann val typ)         b dep ctx = termUnifyMatch val b dep ctx
termUnifyMatch (Ins val)             b dep ctx = termUnifyMatch val b dep ctx
termUnifyMatch (Src src val)         b dep ctx = termUnifyMatch val b dep ctx
termUnifyMatch other                 b dep ctx = Nothing

termUnifySkip :: Term -> Bool
termUnifySkip (App fun arg)  = termUnifySkip fun
termUnifySkip (Ann val typ)  = termUnifySkip val
termUnifySkip (Ins val)      = termUnifySkip val
termUnifySkip (Src src val)  = termUnifySkip val
termUnifySkip (Met uid)      = True
termUnifySkip (Hol nam ctx)  = True
termUnifySkip other          = False

termUnifySolution :: Term -> Int -> Int -> Map Term -> Maybe Term
termUnifySolution (All nam inp bod) dep uid ctx =
  maybeBind (termUnifySolution inp dep uid ctx) $ \inp' ->
  maybeBind (termUnifySolution (bod (Var nam dep)) (dep + 1) uid ctx) $ \bod' ->
  maybePure (All nam inp' (\_ -> bod'))
termUnifySolution (Lam nam bod) dep uid ctx =
  maybeBind (termUnifySolution (bod (Var nam dep)) (dep + 1) uid ctx) $ \bod' ->
  maybePure (Lam nam (\_ -> bod'))
termUnifySolution (App fun arg) dep uid ctx =
  maybeBind (termUnifySolution fun dep uid ctx) $ \fun' ->
  maybeBind (termUnifySolution arg dep uid ctx) $ \arg' ->
  maybePure (App fun' arg')
termUnifySolution (Ann val typ) dep uid ctx =
  maybeBind (termUnifySolution val dep uid ctx) $ \val' ->
  maybeBind (termUnifySolution typ dep uid ctx) $ \typ' ->
  maybePure (Ann val' typ')
termUnifySolution (Slf nam typ bod) dep uid ctx =
  termUnifySolution typ dep uid ctx
termUnifySolution (Ins val) dep uid ctx =
  maybeBind (termUnifySolution val dep uid ctx) $ \val' ->
  maybePure (Ins val')
termUnifySolution (Ref nam val) dep uid ctx =
  maybePure (Ref nam val)
termUnifySolution (Let nam val bod) dep uid ctx =
  maybeBind (termUnifySolution val dep uid ctx) $ \val' ->
  maybeBind (termUnifySolution (bod (Var nam dep)) (dep + 1) uid ctx) $ \bod' ->
  maybePure (Let nam val' (\_ -> bod'))
termUnifySolution (Met uid') dep uid ctx =
  Nothing
termUnifySolution (Hol nam _) dep hol ctx =
  maybePure (Hol nam [])
termUnifySolution Set dep uid ctx =
  maybePure Set
termUnifySolution U60 dep uid ctx =
  maybePure U60
termUnifySolution (Num val) dep uid ctx =
  maybePure (Num val)
termUnifySolution (Op2 opr fst snd) dep uid ctx =
  maybeBind (termUnifySolution fst dep uid ctx) $ \fst' ->
  maybeBind (termUnifySolution snd dep uid ctx) $ \snd' ->
  maybePure (Op2 opr fst' snd')
termUnifySolution (Mat nam x z s p) dep uid ctx =
  maybeBind (termUnifySolution x dep uid ctx) $ \x' ->
  maybeBind (termUnifySolution z dep uid ctx) $ \z' ->
  maybeBind (termUnifySolution (s (Var (stringConcat nam "-1") dep)) dep uid ctx) $ \s' ->
  maybeBind (termUnifySolution (p (Var nam dep)) dep uid ctx) $ \p' ->
  maybePure (Mat nam x' z' (\_ -> s') (\_ -> p'))
termUnifySolution (Txt val) dep uid ctx =
  maybePure (Txt val)
termUnifySolution (Var nam idx) dep uid ctx =
  maybeBind (mapGet (key idx) ctx) $ \val ->
  maybePure val
termUnifySolution (Src src val) dep uid ctx =
  maybeBind (termUnifySolution val dep uid ctx) $ \val' ->
  maybePure (Src src val')

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
termInferGo (All nam inp bod) dep =
  envBind (termCheck 0 inp Set dep) $ \_ ->
  envBind (termCheck 0 (bod (Ann (Var nam dep) inp)) Set (dep + 1)) $ \_ ->
  envPure Set
termInferGo (App fun arg) dep =
  envBind (termInfer fun dep) $ \fun_typ ->
  envBind envGetFill $ \fill ->
  (termIfAll (termReduce fill 2 fun_typ)
    (\fun_nam fun_typ_inp fun_typ_bod fun arg ->
      envBind (termCheck 0 arg fun_typ_inp dep) $ \_ ->
      envPure (fun_typ_bod arg))
    (\fun arg ->
      envFail (Error 0 fun_typ (Hol "function" []) (App fun arg) dep))
    fun arg)
termInferGo (Ann val typ) dep =
  envPure typ
termInferGo (Slf nam typ bod) dep =
  envBind (termCheck 0 (bod (Ann (Var nam dep) typ)) Set (dep + 1)) $ \_ ->
  envPure Set
termInferGo (Ins val) dep =
  envBind (termInfer val dep) $ \vty ->
  envBind envGetFill $ \fill ->
  (termIfSlf (termReduce fill 2 vty)
    (\vty_nam vty_typ vty_bod val ->
      envPure (vty_bod (Ins val)))
    (\val ->
      envFail (Error 0 vty (Hol "self-type" []) (Ins val) dep))
    val)
termInferGo (Ref nam val) dep = 
  termInfer val dep
termInferGo Set dep =
  envPure Set
termInferGo U60 dep =
  envPure Set
termInferGo (Num num) dep =
  envPure U60
termInferGo (Txt txt) dep =
  envPure xString
termInferGo (Op2 opr fst snd) dep =
  envBind (termCheck 0 fst U60 dep) $ \_ ->
  envBind (termCheck 0 snd U60 dep) $ \_ ->
  envPure U60
termInferGo (Mat nam x z s p) dep =
  envBind (termCheck 0 x U60 dep) $ \_ ->
  envBind (termCheck 0 (p (Ann (Var nam dep) U60)) Set dep) $ \_ ->
  envBind (termCheck 0 z (p (Num 0)) dep) $ \_ ->
  envBind (termCheck 0 (s (Ann (Var (stringConcat nam "-1") dep) U60)) (p (Op2 ADD (Num 1) (Var (stringConcat nam "-1") dep))) (dep + 1)) $ \_ ->
  envPure (p x)
termInferGo (Lam nam bod) dep =
  envFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Lam nam bod) dep)
termInferGo (Let nam val bod) dep =
  envFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Let nam val bod) dep)
termInferGo (Hol nam ctx) dep =
  envFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Hol nam ctx) dep)
termInferGo (Met uid) dep =
  envFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Met uid) dep)
termInferGo (Var nam idx) dep =
  envFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Var nam idx) dep)
termInferGo (Src src val) dep =
  termInfer val dep

termCheck :: Int -> Term -> Term -> Int -> Env Int
termCheck src val typ dep =
  -- trace ("check: " ++ termShow val dep ++ "\n    :: " ++ termShow typ dep) $
  termCheckGo src val typ dep

termCheckGo :: Int -> Term -> Term -> Int -> Env Int
termCheckGo src (Lam termNam termBod) typx dep =
  envBind envGetFill $ \fill ->
  (termIfAll (termReduce fill 2 typx)
    (\typeNam typeInp typeBod termBod ->
      let ann  = Ann (Var termNam dep) typeInp
          term = termBod ann
          typx = typeBod ann
      in termCheck 0 term typx (dep + 1))
    (\termBod ->
      envBind (termInfer (Lam termNam termBod) dep) $ \x ->
      envPure 0)
    termBod)
termCheckGo src (Ins termVal) typx dep =
  envBind envGetFill $ \fill ->
  (termIfSlf (termReduce fill 2 typx)
    (\typeNam typeTyp typeBod termVal ->
      termCheck 0 termVal (typeBod (Ins termVal)) dep)
    (\termVal ->
      envBind (termInfer (Ins termVal) dep) $ \x ->
      envPure 0)
    termVal)
termCheckGo src (Let termNam termVal termBod) typx dep =
  termCheck 0 (termBod termVal) typx (dep + 1)
termCheckGo src (Hol termNam termCtx) typx dep =
  envBind (envLog (Found termNam typx termCtx dep)) $ \x ->
  envPure 0
termCheckGo src (Met uid) typx dep =
  envPure 0
termCheckGo src (Ref termNam (Ann termVal termTyp)) typx dep =
  envBind (termEqual typx termTyp dep) $ \equal ->
  termCheckReport src equal termTyp typx termVal dep
termCheckGo src (Src termSrc termVal) typx dep =
  termCheck termSrc termVal typx dep
termCheckGo src term typx dep =
  termCheckVerify src term typx dep

termCheckVerify :: Int -> Term -> Term -> Int -> Env Int
termCheckVerify src term typx dep =
  envBind (termInfer term dep) $ \infer ->
  envBind (termEqual typx infer dep) $ \equal ->
  termCheckReport src equal infer typx term dep

termCheckReport :: Int -> Bool -> Term -> Term -> Term -> Int -> Env Int
termCheckReport src False detected expected value dep =
  envFail (Error src detected expected value dep)
termCheckReport src True detected expected value dep =
  envPure 0

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
termShow (Ann val typ) dep =
  let val' = termShow val dep
      typ' = termShow typ dep
  in stringJoin ["{" , val' , ": " , typ' , "}"]
termShow (Slf nam typ bod) dep =
  let nam' = nam
      typ' = termShow typ dep
      bod' = termShow (bod (Var nam dep)) (dep + 1)
  in stringJoin ["$(" , nam' , ": " , typ' , ") " , bod']
termShow (Ins val) dep =
  let val' = termShow val dep
  in stringJoin ["~" , val']
termShow (Ref nam val) dep = nam
termShow (Let nam val bod) dep =
  let nam' = nam
      val' = termShow val dep
      bod' = termShow (bod (Var nam dep)) (dep + 1)
  in stringJoin ["let " , nam' , " = " , val' , "; " , bod']
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
termShow (Hol nam ctx) dep = stringJoin ["? " , nam]
termShow (Met uid) dep = "_"
termShow (Var nam idx) dep = nam
termShow (Src src val) dep = stringJoin ["!", (termShow val dep)]

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
contextShowAnn fill (Ann val typ) dep = stringJoin ["{" , termShow (termNormal fill 0 val dep) dep , ": " , termShow (termNormal fill 0 typ dep) dep , "}"]
contextShowAnn fill term          dep = termShow (termNormal fill 0 term dep) dep

infoShow :: Map Term -> Info -> String
infoShow fill (Found name typ ctx dep) =
  let typ' = termShow (termNormal fill 1 typ dep) dep
      ctx' = stringTail (contextShow fill ctx dep)
  in stringJoin ["#found{", name, " ", typ', " [", ctx', "]}"]
infoShow fill (Error src detected expected value dep) =
  let det = termShow (termNormal fill 1 detected dep) dep
      exp = termShow (termNormal fill 1 expected dep) dep
      val = termShow (termNormal fill 0 value dep) dep
  in stringJoin ["#error{", exp, " ", det, " ", val, " ", u60Show src, "}"]
infoShow fill (Solve name term dep) =
  let term' = termShow (termNormal fill 1 term dep) dep
  in stringJoin ["#solve{", show name, " ",  term', "}"]
infoShow fill (Vague name) =
  stringJoin ["#vague{", name, "}"]

-- API
-- ---

apiCheck :: Term -> IO ()
apiCheck (Ref nam def) =
  (resMatch (envRun (apiCheckDo def))
    -- done
    (\(State logs fill) value -> do
      print "ok")
    -- fail
    (\(State logs fill) error -> do
      putStrLn $ infoShow fill error))

apiCheckDo :: Term -> Env Int
apiCheckDo (Ann val typ) = do
  termCheck 0 val typ 0
  return 0
apiCheckDo val = do
  termInfer val 0
  return 0

-- Main
-- ----

hvmPrint :: String -> a -> a
hvmPrint = undefined

-- main :: IO ()
-- main = apiCheck book_main

-- Book
-- ----

xtest :: Term
xtest = Ref "test" $ Ann val typ where
  typ = (All "P" Set $ \p -> (All "f" (All "x" p $ \x -> p) $ \f -> (All "x" p $ \x -> p)))
  val = (Lam "P" $ \p -> (Lam "f" $ \f -> (Lam "x" $ \x -> f)))

xString = undefined
