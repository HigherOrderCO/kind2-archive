import Data.Char (chr, ord)
import Prelude hiding (LT, GT, EQ)

newLine = [chr 10]
quote   = [chr 34]

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

data Bits = E | O Bits | I Bits deriving Show

u60ToBits :: Int -> Bits
u60ToBits 0 = E
u60ToBits 1 = I E
u60ToBits n = if even n then O (u60ToBits (div n 2)) else I (u60ToBits (div n 2))

type BitsMap k v = [(k, v)]

mapNew :: BitsMap k v
mapNew = []

mapHas :: Eq k => (k -> k -> Bool) -> k -> BitsMap k v -> Bool
mapHas eq k []               = False
mapHas eq k ((key, val):map) = if eq key k then True else mapHas eq k map

mapIns :: Eq k => (k -> k -> Bool) -> k -> v -> BitsMap k v -> Maybe (BitsMap k v)
mapIns eq k v []               = Just [(k, v)]
mapIns eq k v ((key, val):map) = if eq key k then Nothing else maybeBind (mapIns eq k v map) (\map' -> Just ((key, val):map'))

mapSet :: Eq k => (k -> k -> Bool) -> k -> v -> BitsMap k v -> BitsMap k v
mapSet eq k v []               = [(k, v)]
mapSet eq k v ((key, val):map) = if eq key k then (k, v) : map else (key, val) : mapSet eq k v map

mapGet :: Eq k => (k -> k -> Bool) -> k -> BitsMap k v -> Maybe v
mapGet eq k []               = Nothing
mapGet eq k ((key, val):map) = if eq key k then Just val else mapGet eq k map

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
  | Ref String [(String,Term)] Term
  | Let String Term (Term -> Term)
  | Set
  | U60
  | Num Int
  | Op2 Oper Term Term
  | Mat String Term Term (Term -> Term) (Term -> Term)
  | Txt String
  | Hol String [Term]
  | Met String (Maybe Term)
  | Var String Int
  | Src Int Term

termFill :: [(String, Maybe Term)] -> (Maybe Term -> Term) -> Term
termFill []                    val = val Nothing
termFill ((nam, Nothing):subs) val = termFill subs val
termFill ((nam, Just x):subs)  val = termFill subs (\_ -> val (Just x))

termReduce :: Int -> Term -> Term
termReduce lv (App fun arg)     = termReduceApp lv (termReduce lv fun) arg
termReduce lv (Ann val typ)     = termReduce lv val
termReduce lv (Ins val)         = termReduce lv val
termReduce lv (Ref nam sub val) = termReduceRef lv nam sub (termReduce lv val)
termReduce lv (Let nam val bod) = termReduce lv (bod val)
termReduce lv (Op2 opr fst snd) = termReduceOp2 lv opr (termReduce lv fst) (termReduce lv snd)
termReduce lv (Mat nam x z s p) = termReduceMat lv nam (termReduce lv x) z s p
termReduce lv (Met nam val)     = termReduceMet lv nam val
termReduce lv (Txt txt)         = termReduceTxt lv txt
termReduce lv (Src src val)     = termReduce lv val
termReduce lv val               = val

termReduceApp :: Int -> Term -> Term -> Term
termReduceApp lv (Lam nam bod) arg = termReduce lv (bod (termReduce 0 arg))
termReduceApp lv fun arg           = App fun arg

termReduceOp2 :: Int -> Oper -> Term -> Term -> Term
termReduceOp2 lv ADD (Num fst) (Num snd) = Num (fst + snd)
termReduceOp2 lv SUB (Num fst) (Num snd) = Num (fst - snd)
termReduceOp2 lv MUL (Num fst) (Num snd) = Num (fst * snd)
termReduceOp2 lv DIV (Num fst) (Num snd) = Num (div fst snd)
termReduceOp2 lv MOD (Num fst) (Num snd) = Num (mod fst snd)
termReduceOp2 lv EQ  (Num fst) (Num snd) = if fst == snd then Num 1 else Num 0
termReduceOp2 lv NE  (Num fst) (Num snd) = if fst /= snd then Num 1 else Num 0
termReduceOp2 lv LT  (Num fst) (Num snd) = if fst < snd then Num 1 else Num 0
termReduceOp2 lv GT  (Num fst) (Num snd) = if fst > snd then Num 1 else Num 0
termReduceOp2 lv LTE (Num fst) (Num snd) = if fst <= snd then Num 1 else Num 0
termReduceOp2 lv GTE (Num fst) (Num snd) = if fst >= snd then Num 1 else Num 0
termReduceOp2 lv opr fst snd             = Op2 opr fst snd

termReduceMat :: Int -> String -> Term -> Term -> (Term -> Term) -> (Term -> Term) -> Term
termReduceMat lv nam (Num 0) z s p = termReduce lv z
termReduceMat lv nam (Num n) z s p = termReduce lv (s (Num (n - 1)))
termReduceMat lv nam val     z s p = Mat nam val z s p

termReduceRef :: Int -> String -> [(String, Term)] -> Term -> Term
termReduceRef lv nam sub val = Ref nam sub val

termReduceMet :: Int -> String -> Maybe Term -> Term
termReduceMet lv nam Nothing    = Met nam Nothing
termReduceMet lv nam (Just val) = termReduce lv val

termReduceTxt :: Int -> String -> Term
termReduceTxt lv txt = Txt txt

termNormal :: Int -> Term -> Int -> Term
termNormal lv term dep = termNormalGo lv (termNormalPrefer (termReduce 0 term) (termReduce lv term)) dep where
  termNormalPrefer soft (Lam _ _)   = soft
  termNormalPrefer soft (Slf _ _ _) = soft
  termNormalPrefer soft (All _ _ _) = soft
  termNormalPrefer soft hard        = hard
  termNormalGo lv (All nam inp bod) dep = All nam (termNormal lv inp dep) (\x -> termNormal lv (bod (Var nam dep)) (dep + 1))
  termNormalGo lv (Lam nam bod)     dep = Lam nam (\x -> termNormal lv (bod (Var nam dep)) (dep + 1))
  termNormalGo lv (App fun arg)     dep = App (termNormal lv fun dep) (termNormal lv arg dep)
  termNormalGo lv (Ann val typ)     dep = Ann (termNormal lv val dep) (termNormal lv typ dep)
  termNormalGo lv (Slf nam typ bod) dep = Slf nam typ (\x -> termNormal lv (bod (Var nam dep)) (dep + 1))
  termNormalGo lv (Ins val)         dep = Ins (termNormal lv val dep)
  termNormalGo lv (Ref nam sub val) dep = Ref nam sub (termNormal lv val dep)
  termNormalGo lv (Let nam val bod) dep = Let nam (termNormal lv val dep) (\x -> termNormal lv (bod (Var nam dep)) (dep + 1))
  termNormalGo lv (Hol nam ctx)     dep = Hol nam ctx
  termNormalGo lv (Met nam val)     dep = Met nam (maybeMatch val (\x -> Just (termNormal lv x dep)) Nothing)
  termNormalGo lv Set               dep = Set
  termNormalGo lv U60               dep = U60
  termNormalGo lv (Num val)         dep = Num val
  termNormalGo lv (Op2 opr fst snd) dep = Op2 opr (termNormal lv fst dep) (termNormal lv snd dep)
  termNormalGo lv (Mat nam x z s p) dep = Mat nam (termNormal lv x dep) (termNormal lv z dep) (\k -> termNormal lv (s (Var (stringConcat nam "-1") dep)) dep) (\k -> termNormal lv (p (Var nam dep)) dep)
  termNormalGo lv (Txt val)         dep = Txt val
  termNormalGo lv (Var nam idx)     dep = Var nam idx
  termNormalGo lv (Src src val)     dep = Src src (termNormal lv val dep)

data Info
  = Found String Term [Term] Int
  | Error Int Term Term Term Int
  | Solve String Term Int
  | Vague String

data Result a = Done [Info] a | Fail [Info] Info
data Checker a = Checker ([Info] -> Result a)

resultMatch :: Result a -> ([Info] -> a -> b) -> ([Info] -> Info -> b) -> b
resultMatch (Done logs value) done _    = done logs value
resultMatch (Fail logs error) _    fail = fail logs error

checkerBind :: Checker a -> (a -> Checker b) -> Checker b
checkerBind (Checker a) b = Checker $ \logs -> case a logs of
  Done logs' value -> let Checker b' = b value in b' logs'
  Fail logs' error -> Fail logs' error

checkerPure :: a -> Checker a
checkerPure a = Checker $ \logs -> Done logs a

checkerFail :: Info -> Checker a
checkerFail e = Checker $ \logs -> Fail logs e

checkerRun :: Checker a -> Result a
checkerRun (Checker chk) = chk []

checkerLog :: Info -> Checker Int
checkerLog msg = Checker $ \logs -> Done (msg:logs) 1

checkerSave :: Checker [Info]
checkerSave = Checker $ \logs -> Done logs logs

checkerLoad :: [Info] -> Checker Int
checkerLoad logs = Checker $ \_ -> Done logs 0

instance Functor Checker where
  fmap f (Checker chk) = Checker $ \logs -> case chk logs of
    Done logs' a -> Done logs' (f a)
    Fail logs' e -> Fail logs' e

instance Applicative Checker where
  pure = checkerPure
  (Checker chkF) <*> (Checker chkA) = Checker $ \logs -> case chkF logs of
    Done logs' f -> case chkA logs' of
      Done logs'' a -> Done logs'' (f a)
      Fail logs'' e -> Fail logs'' e
    Fail logs' e -> Fail logs' e

instance Monad Checker where
  (Checker a) >>= b = checkerBind (Checker a) b

termEquality :: Term -> Term -> Int -> Checker Bool
termEquality a b dep = do
  logs <- checkerSave
  let a' = termReduce 2 a
  let b' = termReduce 2 b
  identical <- termCompare a' b' dep (checkerLoad logs >> termSimilar a' b' dep)
  if identical then checkerPure True else checkerLoad logs >> checkerPure False

termCompare :: Term -> Term -> Int -> Checker Bool -> Checker Bool
termCompare a b dep elseCheck = do
  logs <- checkerSave
  equal <- termIdentical a b dep
  if equal then checkerPure True else checkerLoad logs >> elseCheck

termSimilar :: Term -> Term -> Int -> Checker Bool
termSimilar (All aNam aInp aBod) (All bNam bInp bBod) dep = do
  eInp <- termEquality aInp bInp dep
  eBod <- termEquality (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
  checkerPure (eInp && eBod)
termSimilar (Lam aNam aBod) (Lam bNam bBod) dep =
  termEquality (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
termSimilar (App aFun aArg) (App bFun bArg) dep = do
  eFun <- termEquality aFun bFun dep
  eArg <- termEquality aArg bArg dep
  checkerPure (eFun && eArg)
termSimilar (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
  termSimilar (termReduce 0 aTyp) (termReduce 0 bTyp) dep
termSimilar (Hol aNam aCtx) (Hol bNam bCtx) dep =
  checkerPure (aNam == bNam)
termSimilar (Met aNam aVal) (Met bNam bVal) dep =
  checkerPure (aNam == bNam)
termSimilar (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep = do
  eFst <- termEquality aFst bFst dep
  eSnd <- termEquality aSnd bSnd dep
  checkerPure (eFst && eSnd)
termSimilar a b dep = checkerPure False

termIdentical :: Term -> Term -> Int -> Checker Bool
termIdentical (All aNam aInp aBod) (All bNam bInp bBod) dep = do
  iInp <- termIdentical aInp bInp dep
  iBod <- termIdentical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
  checkerPure (iInp && iBod)
termIdentical (Lam aNam aBod) (Lam bNam bBod) dep =
  termIdentical (aBod (Var aNam dep)) (bBod (Var bNam dep)) (dep + 1)
termIdentical (App aFun aArg) (App bFun bArg) dep = do
  iFun <- termIdentical aFun bFun dep
  iArg <- termIdentical aArg bArg dep
  checkerPure (iFun && iArg)
termIdentical (Slf aNam aTyp aBod) (Slf bNam bTyp bBod) dep =
  termIdentical aTyp bTyp dep
termIdentical (Hol aNam aCtx) (Hol bNam bCtx) dep =
  checkerPure (aNam == bNam)
termIdentical (Met aNam (Just aVal)) (Met bNam (Just bVal)) dep =
  termIdentical aVal bVal dep
termIdentical (Met aNam Nothing) (Met bNam Nothing) dep =
  checkerPure (aNam == bNam)
termIdentical (Op2 aOpr aFst aSnd) (Op2 bOpr bFst bSnd) dep = do
  iFst <- termIdentical aFst bFst dep
  iSnd <- termIdentical aSnd bSnd dep
  checkerPure (iFst && iSnd)
termIdentical (Num aVal) (Num bVal) dep =
  checkerPure (aVal == bVal)
termIdentical a b dep = checkerPure False

termIfAll :: Term -> (String -> Term -> (Term -> Term) -> a) -> a -> a
termIfAll (All nam inp bod) yep _   = yep nam inp bod
termIfAll _                 _   nop = nop

termIfSlf :: Term -> (String -> Term -> (Term -> Term) -> a) -> a -> a
termIfSlf (Slf nam typ bod) yep _   = yep nam typ bod
termIfSlf _                 _   nop = nop

termInfer :: Term -> Int -> Checker Term
termInfer (All nam inp bod) dep =
  checkerBind (termCheck 0 inp Set dep) $ \_ ->
  checkerBind (termCheck 0 (bod (Ann (Var nam dep) inp)) Set (dep + 1)) $ \_ ->
  checkerPure Set
termInfer (App fun arg) dep =
  checkerBind (termInfer fun dep) $ \fun_typ ->
  (termIfAll (termReduce 2 fun_typ)
    (\fun_nam fun_typ_inp fun_typ_bod fun arg ->
      checkerBind (termCheck 0 arg fun_typ_inp dep) $ \_ ->
      checkerPure (fun_typ_bod arg))
    (\fun arg ->
      checkerFail (Error 0 fun_typ (Hol "function" []) (App fun arg) dep))
    fun arg)
termInfer (Ann val typ) dep =
  checkerPure typ
termInfer (Slf nam typ bod) dep =
  checkerBind (termCheck 0 (bod (Ann (Var nam dep) typ)) Set (dep + 1)) $ \_ ->
  checkerPure Set
termInfer (Ins val) dep =
  checkerBind (termInfer val dep) $ \vty ->
  (termIfSlf (termReduce 2 vty)
    (\vty_nam vty_typ vty_bod val ->
      checkerPure (vty_bod (Ins val)))
    (\val ->
      checkerFail (Error 0 vty (Hol "self-type" []) (Ins val) dep))
    val)
termInfer (Ref nam sub val) dep = 
  termInfer val dep
termInfer Set dep =
  checkerPure Set
termInfer U60 dep =
  checkerPure Set
termInfer (Num num) dep =
  checkerPure U60
termInfer (Txt txt) dep =
  checkerPure bookString
termInfer (Op2 opr fst snd) dep =
  checkerBind (termCheck 0 fst U60 dep) $ \_ ->
  checkerBind (termCheck 0 snd U60 dep) $ \_ ->
  checkerPure U60
termInfer (Mat nam x z s p) dep =
  checkerBind (termCheck 0 x U60 dep) $ \_ ->
  checkerBind (termCheck 0 (p (Ann (Var nam dep) U60)) Set dep) $ \_ ->
  checkerBind (termCheck 0 z (p (Num 0)) dep) $ \_ ->
  checkerBind (termCheck 0 (s (Ann (Var (stringConcat nam "-1") dep) U60)) (p (Op2 ADD (Num 1) (Var (stringConcat nam "-1") dep))) (dep + 1)) $ \_ ->
  checkerPure (p x)
termInfer (Lam nam bod) dep =
  checkerFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Lam nam bod) dep)
termInfer (Let nam val bod) dep =
  checkerFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Let nam val bod) dep)
termInfer (Hol nam ctx) dep =
  checkerFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Hol nam ctx) dep)
termInfer (Met nam (Just val)) dep =
  termInfer val dep
termInfer (Met nam Nothing) dep =
  checkerFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Met nam Nothing) dep)
termInfer (Var nam idx) dep =
  checkerFail (Error 0 (Hol "untyped_term" []) (Hol "type_annotation" []) (Var nam idx) dep)
termInfer (Src src val) dep =
  termInfer val dep

termCheck :: Int -> Term -> Term -> Int -> Checker Int
termCheck src (Lam termNam termBod) typx dep =
  (termIfAll (termReduce 2 typx)
    (\typeNam typeInp typeBod termBod ->
      let ann  = Ann (Var termNam dep) typeInp
          term = termBod ann
          typx = typeBod ann
      in termCheck 0 term typx (dep + 1))
    (\termBod ->
      checkerBind (termInfer (Lam termNam termBod) dep) $ \x ->
      checkerPure 0)
    termBod)
termCheck src (Ins termVal) typx dep =
  (termIfSlf (termReduce 2 typx)
    (\typeNam typeTyp typeBod termVal ->
      termCheck 0 termVal (typeBod (Ins termVal)) dep)
    (\termVal ->
      checkerBind (termInfer (Ins termVal) dep) $ \x ->
      checkerPure 0)
    termVal)
termCheck src (Let termNam termVal termBod) typx dep =
  termCheck 0 (termBod termVal) typx (dep + 1)
termCheck src (Hol termNam termCtx) typx dep =
  checkerBind (checkerLog (Found termNam typx termCtx dep)) $ \x ->
  checkerPure 0
termCheck src (Met termNam (Just termVal)) typx dep =
  termCheck src termVal typx dep
termCheck src (Met termNam Nothing) typx dep =
  checkerPure 0
termCheck src (Ref termNam termSub (Ann termVal termTyp)) typx dep =
  checkerBind (termEquality typx termTyp dep) $ \equal ->
  termCheckReport src equal termTyp typx termVal dep
termCheck src (Src termSrc termVal) typx dep =
  termCheck termSrc termVal typx dep
termCheck src term typx dep =
  termCheckVerify src term typx dep

termCheckVerify :: Int -> Term -> Term -> Int -> Checker Int
termCheckVerify src term typx dep =
  checkerBind (termInfer term dep) $ \infer ->
  checkerBind (termEquality typx infer dep) $ \equal ->
  termCheckReport src equal infer typx term dep

termCheckReport :: Int -> Bool -> Term -> Term -> Term -> Int -> Checker Int
termCheckReport src False detected expected value dep =
  checkerFail (Error src detected expected value dep)
termCheckReport src True detected expected value dep =
  checkerPure 0

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
termShow (Ref nam sub val) dep = nam
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
termShow (Met nam Nothing) dep = "_"
termShow (Met nam (Just val)) dep = termShow val dep
termShow (Var nam idx) dep = nam
termShow (Src src val) dep = termShow val dep

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

contextShow :: [Term] -> Int -> String
contextShow []     dep = ""
contextShow (x:xs) dep = stringJoin [" " , contextShowAnn x dep , contextShow xs dep]

contextShowAnn :: Term -> Int -> String
contextShowAnn (Ann val typ) dep = stringJoin ["{" , termShow (termNormal 0 val dep) dep , ": " , termShow (termNormal 0 typ dep) dep , "}"]
contextShowAnn term          dep = termShow (termNormal 0 term dep) dep

infoShow :: Info -> String
infoShow (Found name typ ctx dep) =
  let typ' = termShow (termNormal 1 typ dep) dep
      ctx' = stringTail (contextShow ctx dep)
  in stringJoin ["#found{", name, " ", typ', " [", ctx', "]}"]
infoShow (Error src detected expected value dep) =
  let det = termShow (termNormal 1 detected dep) dep
      exp = termShow (termNormal 1 expected dep) dep
      val = termShow (termNormal 0 value dep) dep
  in stringJoin ["#error{", exp, " ", det, " ", val, " ", u60Show src, "}"]
infoShow (Solve name term dep) =
  let term' = termShow (termNormal 1 term dep) dep
  in stringJoin ["#solve{", name, " ",  term', "}"]
infoShow (Vague name) =
  stringJoin ["#vague{", name, "}"]

hvmPrint :: String -> a -> a
hvmPrint = undefined

compile :: Term -> Term
compile = undefined

bookString = undefined

main :: IO ()
main = print $ u60ToBits 500
