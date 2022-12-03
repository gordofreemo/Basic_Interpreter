import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.State.Lazy as State
import Data.Map as Map hiding (foldr,filter,take)
import Data.Char
import Data.Bits
import Text.Read
import qualified System.Random (randomIO)
import System.Environment
import System.IO


{-
  TODO: 
  ADD ARRAYS / MULTIPLE STATEMENTS ON A LINE
-}
---------- BASIC Program Grammar Types ------------
data Expr = Val Value | ID {getID :: String } | FUN String Expr 
          | OP String (Expr -> Expr -> Expr) Expr Expr  
          | RND Expr | LINEREF (Integer,Expr) 
          | ARR [Expr] | INDEX Expr Expr | NULL

data Stm = ExprStm Expr | LET Expr Expr | GOTO Integer
         | PRINT [Expr] | IF Expr Integer | NEXT [Expr] 
         | INPUT String [Expr] | GOSUB Integer | RETURN
         | FOR Integer Expr Expr Expr | FOR_STEP Integer Expr Expr Expr Expr 
         | DIM Expr Expr | REM String | END


data Value = Int' Integer | String' String | Float' Float
  deriving Eq

-- Normal Version
{-
instance Show Expr where
  show (Val x)          = show x
  show (FUN name e)     = name ++ "(" ++ (show e) ++ ")"
  show (RND e)          = "RND(" ++ (show e) ++ ")"
  show (OP str f e1 e2) = "(" ++ (show e1) ++ str ++ (show e2) ++ ")"
  show (ARR xs)         = show xs
  show (INDEX e1 e2)    = (show e1) ++ "(" ++ (show e2) ++ ")"
  show (LINEREF (_,e))  = (show e)
  show (ID str)         = str
-}

-- Debug Version
--{- 
instance Show Expr where 
  show (Val (Int' x)) = "Int' " ++ (show x) 
  show (Val (Float' x)) = "Float' " ++ (show x)
  show (Val (String' x)) = "" ++ x
  show (FUN name e)     = name ++ "(" ++ (show e) ++ ")"
  show (RND e)          = "RND(" ++ (show e) ++ ")"
  show (OP str f e1 e2) = "(" ++ (show e1) ++ str ++ (show e2) ++ ")"
  show (ARR xs)         = show xs
  show (INDEX e1 e2)    = (show e1) ++ "(" ++ (show e2) ++ ")"
  show (LINEREF x) = "LINEREF " ++ (show x)
  show (ID str)         = "ID " ++ str
---}
--
instance Show Stm where
  show (ExprStm e) = show e
  show (LET e1 e2) = "LET " ++ (show e1) ++ " = " ++ (show e2)
  show (GOTO x) = "GOTO " ++ (show x)
  show (GOSUB x) = "GOSUB " ++ (show x)
  show RETURN = "RETURN"
  show (IF e x) = "IF " ++ (show e) ++ " THEN " ++ (show x)
  show (PRINT [e]) = "PRINT " ++ (show e)
  show (PRINT e) = "PRINT " ++ (concatMap (\x -> (show x) ++ ",") e) 
  show (INPUT str [e]) = "INPUT " ++ (show str) ++ (show e)
  show (INPUT str e) = "INPUT " ++ (show str) ++ (concatMap (\x -> (show x) ++ ",") e)
  show (FOR _ e0 e1 e2) = "FOR " ++ (show e0) ++ " = " ++ (show e1) ++ " TO " ++ (show e2)
  show (FOR_STEP _ e0 e1 e2 e3) = "FOR " ++ (show e0) ++ " = " ++ (show e1) ++ " TO " 
                                 ++ (show e2) ++ " STEP " ++ (show e3)
  show (NEXT e) = "NEXT " ++ (show e)
  show (DIM x e)  = "DIM " ++ (show x) ++ "(" ++ (show e) ++ ")"
  show (REM str) = "REM " ++ str
  show END       = "END"

instance Show Value where 
  show (Int' x) = show x
  show (String' x) = x
  show (Float' x) = show x
---------------------------------------------------


--------  STANDARD PARSER DEFINITIONS  ---------
type Parser a = StateT String [] a

item :: Parser Char
item = StateT $ \str -> case str of 
  [] -> mzero 
  (x:xs) -> return (x,xs)

sat :: (Char -> Bool) -> Parser Char
sat f = do
  x <- item
  if (f x) then (return x) else mzero

string :: String -> Parser String
string [] = return ""
string (x:xs) = do
  y <- sat (== x)
  ys <- string xs
  return (y:ys)

word :: String -> Parser String 
word [] = do {sat isSpace; return ""}
word (x:xs) = do 
  y <- sat (== x)
  ys <- string xs 
  return (y:ys)

token :: Parser a -> Parser a
token p = do {space; a <- p; space; return a}

symb :: String -> Parser String
symb cs = token (word cs)

digit :: Parser Integer
digit = do {c <- sat isDigit; return $ toInteger (ord c - ord '0')}

natural :: Parser Integer
natural = do
  digits <- many1 digit
  return (foldr (+) 0 (zipWith (*) (reverse digits) (fmap (10^) [0..])))

number :: Parser Integer 
number = natural `mplus` do {sat (== '-'); x <- natural; return (-x)}

float :: Parser Float 
float = do 
  x <- many (sat (\x -> (isDigit x) || (x == '.')))
  guard ('.' `elem` x)
  case (readMaybe x :: Maybe Float) of 
    Nothing -> mzero
    Just x  -> return x

many :: Parser a -> Parser [a]
many p = (many1 p) `mplus` (return [])

many1 :: Parser a -> Parser [a]
many1 p = do {a <- p; as <- (many p); return (a:as)}

sepby           :: Parser a -> Parser b -> Parser [a]
p `sepby` sep    = (p `sepby1` sep) `mplus` mzero

sepby1          :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep   = do {a <- p; as <- many (do {sep; p}); return (a:as)}

space :: Parser String
space = many (sat isSpace)
------------------------------------------------


--------  BASIC PARSER DEFINITIONS  ---------
constString :: Parser Expr
constString = do 
  space
  sat (== '"')
  xs <- (many (sat (/= '"')))
  sat (== '"')
  space
  return (Val (String' xs))

constInt :: Parser Expr
constInt = do {space; xs <- number; space; return (Val $ Int' xs)}

constFloat :: Parser Expr 
constFloat = do {space; xs <- float; space; return (Val $ Float' xs)}

constant :: Parser Expr 
constant = constString `mplus` constFloat `mplus` constInt

iden :: Parser Expr
iden = do
  space
  xs <- (many (sat isLetter))
  space
  guard (xs /= [])
  return (ID xs)

expr :: Parser Expr
expr = do {space; x <- andExpr; symb "OR"; y <- expr; return (OP "OR" bitOR x y)}
       `mplus` andExpr

andExpr :: Parser Expr
andExpr = do {space; x <- notExpr; symb "AND"; y <- andExpr; return (OP "AND" bitAND x y)}
          `mplus` notExpr

notExpr :: Parser Expr 
notExpr = do {space; symb "NOT"; x <- compExpr; return (OP "NOT" bitNOT x NULL)}
          `mplus` compExpr

compExpr :: Parser Expr
compExpr = do {space; x <- addExpr; op <- check; y <- compExpr; return (OP op (f op) x y)} 
           `mplus` addExpr
  where check = foldr mplus mzero (fmap word ["=","<>",">",">=","<","<="])
        f op = opTable ! op

addExpr :: Parser Expr 
addExpr = do {space; x <- multExpr; op <- check; y <- addExpr; return (OP [op] (f [op]) x y)}
          `mplus` multExpr
  where check = sat (\x -> (x == '+') || (x == '-'))
        f op = opTable ! op

multExpr :: Parser Expr
multExpr = do {space; x <- negExpr; op <- check; y <- multExpr; return (OP [op] (f [op]) x y)}
           `mplus` negExpr
  where check = sat (\x -> (x == '*') || (x == '/'))
        f op = opTable ! op
  
negExpr :: Parser Expr
negExpr = do {space; sat (== '-'); x <- powExpr; return (OP "NEG" neg x NULL)}
          `mplus` powExpr

powExpr :: Parser Expr
powExpr = do {space; x <- value; sat (== '^'); y <- powExpr; return (OP "^" pow x y)}
          `mplus` value

value :: Parser Expr
value =  function `mplus` constant `mplus` index `mplus` iden `mplus`
         do {x <- iden; sat (== '('); e <- expr; sat (== ')'); return (INDEX x e)}
        `mplus` (do {sat (== '('); x <- expr; sat (== ')'); return x}) 

exprList :: Parser [Expr]
exprList = (expr `sepby` do {space; sat (== ',')}) 
           `mplus` do {x <- expr; return [x]}

printList :: Parser [Expr]
printList = (expr `sepby1` do {space; sat (\x -> x == ',' || x == ';'); space}) 
            `mplus` do {x <- expr; return [x]}

idList :: Parser [Expr]
idList =  (iden `sepby` do {space; sat (== ',')}) `mplus`
          do {x <- iden; return [x]}

randParse :: Parser Expr
randParse = do {symb "RND"; sat (== '('); e <- expr; sat (== ')'); return (RND e)}

funParse :: Parser Expr
funParse = do {symb "INT"; sat (== '('); e <- expr; sat (== ')'); return (FUN "INT" e)}

function :: Parser Expr
function = randParse `mplus` funParse

index :: Parser Expr 
index = do 
  x <- iden
  sat (== '(')
  e <- expr
  sat (== ')')
  space
  return (INDEX x e)

endParse :: Parser Stm
endParse = do {symb "END"; return END} 

gotoParse :: Parser Stm 
gotoParse = do {symb "GOTO"; x <- natural; return (GOTO x)}

gosubParse :: Parser Stm
gosubParse = do {symb "GOSUB"; x <- natural; return (GOSUB x)}

returnParse :: Parser Stm
returnParse = do {symb "RETURN"; return RETURN}

ifParse :: Parser Stm 
ifParse = do {symb "IF"; e <- expr; symb "THEN"; x <- natural; return (IF e x)}

inputParse1 :: Parser Stm
inputParse1 = do 
  symb "INPUT"
  (Val (String' x)) <- constString
  sat (== ';')
  ls <- idList
  return (INPUT x ls)

inputParse2 :: Parser Stm
inputParse2 = do 
  symb "INPUT"
  ls <- idList 
  return (INPUT "" ls)

letParse :: Parser Stm
letParse = do 
  symb "LET"
  x <- (index `mplus` iden)
  symb "="
  e <- expr
  return (LET x e)

forParse :: Parser Stm
forParse = do 
  symb "FOR"
  x <- iden
  symb "="
  e1 <- expr
  symb "TO"
  e2 <- expr
  return (FOR (-1) x e1 e2)

forstepParse :: Parser Stm
forstepParse = do
  symb "FOR"
  x <- iden
  symb "="
  e1 <- expr
  symb "TO"
  e2 <- expr
  symb "STEP"
  e3 <- expr
  return (FOR_STEP (-1) x e1 e2 e3)

nextParse :: Parser Stm
nextParse = do 
  symb "NEXT"
  xs <- idList
  return (NEXT xs)

printParse :: Parser Stm
printParse = do 
  symb "PRINT"
  e <- printList 
  return (PRINT e)

dimParse :: Parser Stm 
dimParse = do 
  symb "DIM"
  x <- iden
  sat (== '(')
  e <- expr
  sat (== ')')
  return (DIM x e)

remParse :: Parser Stm
remParse = do
  symb "REM"
  xs <- many item
  return (REM xs)

stmParse :: Parser Stm 
stmParse = endParse `mplus` gotoParse `mplus` ifParse `mplus`
           inputParse1 `mplus` inputParse2 `mplus` letParse `mplus` 
           printParse `mplus` gosubParse `mplus` returnParse `mplus` 
           forstepParse `mplus` forParse  `mplus` nextParse `mplus`
           dimParse `mplus` remParse

lineParse :: Parser (Integer, Stm)
lineParse = do 
  x <- natural
  space
  stm <- stmParse 
  case stm of
    (FOR _ str e1 e2) -> return (x, FOR x str e1 e2)
    (FOR_STEP _ str e1 e2 e3) -> return (x, FOR_STEP x str e1 e2 e3)
    _ ->  return (x,stm)

parseSource :: String -> Program
parseSource str = fromList . (fmap fst) . (fmap head) $ parseLines (lines str')
  where parseLines = filter (not . Prelude.null) . fmap (runStateT lineParse)
        str' = fmap toUpper str
---------------------------------------------

-------- LIFTED OPERATORS ------------
liftInt :: Integer -> Expr 
liftInt = Val . Int'

liftFloat :: Float -> Expr
liftFloat = Val . Float'

l1 :: Expr 
l1 = liftInt 1
l0 :: Expr 
l0 = liftInt 0 

liftbitOP :: (Integer -> Integer -> Integer) -> (Expr -> Expr -> Expr)
liftbitOP f (Val (Int' x)) (Val (Int' y)) = liftInt (x `f` y)
liftbitOP f (Val (Int' x)) (Val (Float' y)) = liftInt (x `f` (floor y))
liftbitOP f (Val (Float' x)) (Val (Int' y)) = liftInt ((floor x) `f` y)
liftbitOP f (Val (Float' x)) (Val (Float' y)) = liftInt ((floor x) `f` (floor y))

bitAND :: Expr -> Expr -> Expr 
bitAND = liftbitOP (.&.)

bitOR :: Expr -> Expr -> Expr
bitOR = liftbitOP (.|.)

bitNOT :: Expr -> Expr -> Expr
bitNOT (Val (Int' x)) _ = if x == 0 then l1 else l0 
bitNOT (Val (Float' x)) _ = if x == 0.0 then l1 else l0

liftComp :: (Float -> Float -> Bool) -> (Expr -> Expr -> Expr)
liftComp f (Val (Int' x)) (Val (Int' y)) = if (x' `f` y') then l1 else l0
  where (x',y') = (fromIntegral x, fromIntegral y)
liftComp f (Val (Int' x)) (Val (Float' y)) = if ((fromIntegral x) `f` y) then l1 else l0
liftComp f (Val (Float' x)) (Val (Int' y)) = if (x `f` (fromIntegral y)) then l1 else l0
liftComp f (Val (Float' x)) (Val (Float' y)) = if (x `f` y) then l1 else l0

equal :: Expr -> Expr -> Expr 
equal = liftComp (==)

noteq :: Expr -> Expr -> Expr
noteq = liftComp (/=)

greater :: Expr -> Expr -> Expr
greater = liftComp (>)

greaterEQ :: Expr -> Expr -> Expr
greaterEQ = liftComp (>=)

less :: Expr -> Expr -> Expr
less = liftComp (<)

lessEQ :: Expr -> Expr -> Expr
lessEQ = liftComp (<=)

liftOP :: (Integer -> Integer -> Integer) -> (Float -> Float -> Float) ->
          (Expr -> Expr -> Expr)
liftOP op1 op2 (Val (Int' x)) (Val (Int' y)) = liftInt (x `op1` y)
liftOP op1 op2 (Val (Float' x)) (Val (Int' y)) = liftFloat (x `op2` (fromIntegral y))
liftOP op1 op2 (Val (Int' x)) (Val (Float' y)) = liftFloat ((fromIntegral x) `op2` y)
liftOP op1 op2 (Val (Float' x)) (Val (Float' y)) = liftFloat (x `op2` y)

add :: Expr -> Expr -> Expr
add = liftOP (+) (+) 

sub :: Expr -> Expr -> Expr
sub = liftOP (-) (-)

mul :: Expr -> Expr -> Expr
mul = liftOP (*) (*)

divide :: Expr -> Expr -> Expr
divide (Val (Int' x)) (Val (Int' y)) = liftFloat ((fromIntegral x) / (fromIntegral y))
divide x y = (liftOP const (/)) x y

neg :: Expr -> Expr -> Expr
neg (Val (Int' x)) _ = liftInt (-x)
neg (Val (Float' x)) _ = liftFloat (-x)

pow :: Expr -> Expr -> Expr 
pow = liftOP (^) (**)

opTable :: Map String (Expr -> Expr -> Expr)
opTable = fromList (pt1 ++ pt2 ++ pt3 ++ pt4 ++ pt5 ++ pt6)
  where pt1 = [("AND",bitAND),("OR",bitOR),("NOT",bitNOT)]
        pt2 = [("=",equal),("<>",noteq),(">",greater),(">=",greaterEQ),("<",less),("<=",lessEQ)]
        pt3 = [("+",add),("-",sub)]
        pt4 = [("*",mul),("/",divide)]
        pt5 = [("-.",neg)]
        pt6 = [("^",pow)]

--------------------------------------


-------- BASIC INTERPRETER ------------
-- Reader is threading line number -> statement map (Program)
-- State is threading the (current line, SymbolTable, CallStack) pair (PC)
type SymbolTable = Map String Expr
type LineNum = Integer
type Program = Map LineNum Stm
type CallStack = [Integer]
type PC = (LineNum, SymbolTable, CallStack)
type Environment = StateT PC (ReaderT Program IO) ()

runProgram :: Program -> IO ()
runProgram prog = do 
  runEnv programEnv prog (line1, Map.empty, [])
  return ()
  where line1 = fst (findMin prog)

runProgramDebug :: Program -> IO ()
runProgramDebug prog = do 
  runEnv debugEnv prog (line1, Map.empty, [])
  return ()
  where line1 = fst (findMin prog)

runEnv :: Environment -> Program -> PC -> IO ((),PC)
runEnv e prog pc = (runReaderT $ (runStateT e) pc) prog 

programEnv :: Environment 
programEnv = do 
  (line, _,_) <- State.get 
  if (line == (-1)) then return () else go line
  where go line = do { 
    program <- ask;
    execStatement (program ! line);
    programEnv;
    }

debugEnv :: Environment
debugEnv = do 
  (line, table, stack) <- State.get
  program <- ask
  liftIO (putStrLn $ "LINE " ++ (show line))
  when (line /= (-1)) (liftIO (putStrLn $ "STATEMENT " ++ (show (program ! line))))
  liftIO (putStrLn $ "SYMBOL TABLE " ++ (show table))
  liftIO (putStrLn $ "CALL STACK " ++ (show stack))
  if (line == (-1)) then return () else go line 
  where go line = do {
    program <- ask; 
    execStatement (program ! line);
    debugEnv;
  }

runLine :: Environment
runLine = do 
  (line, _, _) <- State.get
  program <- ask
  execStatement (program ! line)

setAt :: Integer -> a -> [a] -> [a]
setAt 0 x (y:xs) = (x:xs)
setAt n x (y:xs) = y:(setAt (n-1) x xs)

execStatement :: Stm -> Environment
execStatement (LET iden expr) = do
  (line, table, stack) <- State.get
  program <- ask
  z <- liftIO (eval expr table)
  case iden of 
    (INDEX i n) -> do 
      (ARR arr) <- liftIO (eval i table)
      e <- liftIO (eval n table)
      let (Val (Int' n')) = e
      put (nextLine line program, insert (getID i) (ARR (setAt n' z arr)) table, stack)
    _ -> do {put (nextLine line program, insert (getID iden) z table, stack)}
execStatement (PRINT expr) = do 
  (line, table, stack) <- State.get
  program <- ask 
  z <- liftIO (sequence (fmap (flip eval table) expr))
  let exprs =  fmap show z
  liftIO (putStrLn (concat exprs))
  put (nextLine line program, table, stack)
execStatement (INPUT str xs) = do {liftIO (putStrLn str); go xs}
  where go [] = do {
         prog <- ask;
         modify (\(line,table,stack) -> (nextLine line prog, table, stack))
        }
        go (x:xs) = do {
          (line,table,stack) <- State.get;
          y <- liftIO getLine;
          z <- liftIO (eval ((fst . head) $ runStateT expr y) table);
          put (line, insert (getID x) z table,stack);
          go xs
        }
execStatement END = do {modify (\(_,y,z) -> (-1,y,z))}
execStatement (GOTO x) = do {modify (\(_,y,z) -> (x,y,z))}
execStatement (GOSUB n) = do {modify (\(x,y,z) -> (n,y,x:z))}
execStatement RETURN = do 
  (line, table, stack) <- State.get
  prog <- ask
  case stack of 
    [] -> put (nextLine line prog, table, [])
    xs -> put (nextLine (head stack) prog, table, tail stack)
execStatement (FOR n e1 e2 e3) = do
  prog <- ask
  (_, table, _) <- State.get
  e2' <- liftIO (eval e2 table)
  e3' <- liftIO (eval e3 table)
  modify (\(x,y,z) -> (nextLine x prog, insert (getID e1) (LINEREF (n,e2')) y, z))
execStatement (FOR_STEP x e1 e2 e3 e4) = do 
  (line, table, stack) <- State.get
  program <- ask
  e2' <- liftIO (eval e2 table)
  e3' <- liftIO (eval e3 table)
  e4' <- liftIO (eval e3 table)
  put (nextLine line program, insert (getID e1) (LINEREF (x,e2')) table, stack)
execStatement (NEXT []) = do 
  prog <- ask
  modify (\(x,y,z) -> (nextLine x prog, y, z))
execStatement (NEXT xs) = execFor xs
execStatement (IF e x) = do 
  (line, table,stack) <- State.get
  program <- ask
  y <- liftIO (eval e table)
  case y `equal` (Val $ Int' 0) of 
    (Val (Int' 0)) -> put (x, table, stack)
    (Val (Int' 1)) -> put (nextLine line program, table,stack)
execStatement (DIM e x) = do 
  (line, table, stack) <- State.get
  program <- ask
  (Val (Int' x')) <- liftIO (eval x table)
  let (ID e') = e
  let nLine = nextLine line program
  put (nLine, insert e' (ARR (take (fromIntegral (x'+1)) (repeat (Val (Int' 0))))) table, stack)
execStatement (REM _) = do 
  prog <- ask
  modify (\(x,y,z) -> (nextLine x prog, y, z))
  
  
execFor :: [Expr] -> Environment
execFor ((ID x):xs) = do
  (line, table, stack) <- State.get 
  prog <- ask
  let (LINEREF (n,e)) = table ! x
  case (prog ! n) of 
    (FOR n' _ _ e3) -> do
      e1 <- liftIO (eval e table)
      e2 <- liftIO (eval e3 table)
      case ((e1 `add` l1) `equal` e2) of 
        (Val (Int' 1)) -> execStatement (NEXT xs)
        _ -> put (nextLine n' prog, insert x (LINEREF (n',(e `add` l1))) table, stack)
    (FOR_STEP n' _ _ e4 e5) -> do
      e1 <- liftIO (eval e table)
      e2 <- liftIO (eval e4 table)
      e3 <- liftIO (eval e5 table)
      case ((e1 `add` e3) `greater` e2) of
        (Val (Int' 1)) -> execStatement (NEXT xs)
        _ -> put (nextLine n' prog, insert x (LINEREF (n',e `add` e3)) table, stack)

nextLine :: LineNum -> Program -> LineNum
nextLine x m  = if (Map.null snd_map) then (-1) else ((fst . findMin) snd_map)
  where snd_map = snd $ split x m

eval :: Expr -> SymbolTable -> IO Expr 
eval (Val x) _ = return $ Val x
eval (ARR xs) _ = return $ ARR xs
eval (ID str) sym = do {eval (sym ! str) sym}
eval (LINEREF (x,e)) sym = eval e sym
eval (OP _ f x y) sym = do
  e1 <- (eval x sym)
  e2 <- (eval y sym)
  eval (f e1 e2) sym
eval (FUN "INT" e) sym = do {x <- eval e sym; return $ f x}
  where f (Val (Int' x)) = Val $ Int' x 
        f (Val (Float' x )) = Val $ Int' $ floor x
eval NULL _ = return NULL
eval (INDEX iden e) sym = do 
  (ARR arr) <- eval iden sym 
  (Val (Int' i)) <- eval e sym 
  eval (arr !! (fromIntegral (i))) sym
eval (RND e) sym = do {x <- eval e sym; f x}
  where f (Val (Float' _)) = do {
        y <- System.Random.randomIO :: IO Float;
        return (Val $ Float' y)}
        f (Val (Int' 1)) = do {
        y <- System.Random.randomIO :: IO Float; 
        return (Val $ Float' y)
        }
        f (Val (Int'   x)) = do {
        y <- System.Random.randomIO :: IO Float; 
        return (Val $ Int' (floor $ (fromIntegral x)*y))}


--------------- MAIN FUNCTION ---------------------------
main :: IO ()
main = do 
  args <- getArgs
  args <- getLine
  guard (not $ Prelude.null args)
  handle <- openFile (args) ReadMode
  contents <- hGetContents handle
  putStrLn (show (parseSource contents))
  runProgram (parseSource contents)
  hClose handle

mainDebug :: IO ()
mainDebug = do
  args <- getArgs 
  args <- getLine
  guard (not $ Prelude.null args)
  handle <- openFile (args) ReadMode
  contents <- hGetContents handle
  putStrLn (show (parseSource contents))
  runProgramDebug (parseSource contents)
  hClose handle
----------------------------------------------------------
