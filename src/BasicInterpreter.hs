import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.State.Lazy as State
import Data.Map as Map hiding (foldr,filter)
import Data.Char
import Data.Bits
import Text.Read

{-
  SUCCESSFULLY ABLE TO RUN PROGRAM #1. 
  PARSES SIMPLE EXPRESSIONS AND LETS
  NEED TO IMPLEMENT LOOPS AND GOTO NEXT 
  PROBABLY NEED TO ADD A CALL STACK
-}
---------- BASIC Program Grammar Types ------------
data Expr = Val Value | ID {getID :: String } | FUN String Expr
          | OP String (Expr -> Expr -> Expr) Expr Expr  | NULL

data Stm = ExprStm Expr | LET Expr Expr
         | PRINT Expr | END

data Value = Int' Integer | String' String
  deriving Eq

instance Show Expr where
  show (Val x)          = show x
  show (FUN name e)     = name ++ "(" ++ (show e) ++ ")"
  show (OP str f e1 e2) = "(" ++ (show e1) ++ str ++ (show e2) ++ ")"
  show (ID str)         = str

instance Show Stm where
  show (ExprStm e) = show e
  show (LET e1 e2) = "LET " ++ (show e1) ++ " = " ++ (show e2)
  show (PRINT e) = "PRINT " ++ (show e)
  show END       = "END"

instance Show Value where 
  show (Int' x) = show x
  show (String' x) = x
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
token p = do {a <- p; space; return a}

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

many :: Parser a -> Parser [a]
many p = (many1 p) `mplus` (return [])

many1 :: Parser a -> Parser [a]
many1 p = do {a <- p; as <- (many p); return (a:as)}

space :: Parser String
space = many (sat isSpace)
------------------------------------------------


--------  BASIC PARSER DEFINITIONS  ---------
constString :: Parser Expr
constString = do 
  space
  sat (== '"')
  xs <- (many (sat (\x -> (x /= '"') && (isLetter x))))
  sat (== '"')
  space
  return (Val (String' xs))

constInt :: Parser Expr
constInt = do {space; xs <- number; return (Val $ Int' xs)}

constant :: Parser Expr 
constant = constString `mplus` constInt

iden :: Parser Expr
iden = do
  space
  xs <- (many (sat isLetter))
  space
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
value = (do {sat (== '('); x <- expr; sat (== ')'); return x}) `mplus` constant `mplus` iden

endParse :: Parser Stm
endParse = do {symb "END"; return END} 

letParse :: Parser Stm
letParse = do 
  symb "LET"
  x <- iden
  symb "="
  e <- expr
  return (LET x e)

printParse :: Parser Stm
printParse = do 
  symb "PRINT"
  e <- expr 
  return (PRINT e)

stmParse :: Parser Stm 
stmParse = endParse `mplus` letParse `mplus` printParse

lineParse :: Parser (Integer, Stm)
lineParse = do 
  x <- natural
  space
  stm <- stmParse 
  return (x,stm)

parseSource :: String -> Program
parseSource str = fromList . (fmap fst) . (fmap head) $ parseLines (lines str')
  where parseLines = filter (not . Prelude.null) . fmap (runStateT lineParse)
        str' = fmap toUpper str
---------------------------------------------

-------- LIFTED OPERATORS ------------
liftInt :: Integer -> Expr 
liftInt = Val . Int'

bitAND :: Expr -> Expr -> Expr 
bitAND (Val (Int' x)) (Val (Int' y)) = liftInt (x .&. y)

bitOR :: Expr -> Expr -> Expr
bitOR (Val (Int' x)) (Val (Int' y)) = liftInt (x .|. y)

bitNOT :: Expr -> Expr -> Expr
bitNOT (Val (Int' x)) _ = if x == 0 then liftInt 1 else liftInt 0

equal :: Expr -> Expr -> Expr 
equal (Val (Int' x)) (Val (Int' y)) = if (x == y) then liftInt 1 else liftInt 0

noteq :: Expr -> Expr -> Expr
noteq x y = bitNOT (equal x y) NULL

greater :: Expr -> Expr -> Expr
greater (Val (Int' x)) (Val (Int' y)) = if (x > y) then liftInt 1 else liftInt 0

greaterEQ :: Expr -> Expr -> Expr
greaterEQ x y = (equal x y) `bitOR` (greater x y)

less :: Expr -> Expr -> Expr
less (Val (Int' x)) (Val (Int' y)) = if (x < y) then liftInt 1 else liftInt 0

lessEQ :: Expr -> Expr -> Expr
lessEQ x y = (equal x y) `bitOR` (less x y)

add :: Expr -> Expr -> Expr
add (Val (Int' x)) (Val (Int' y)) = liftInt (x+y)

sub :: Expr -> Expr -> Expr
sub (Val (Int' x)) (Val (Int' y)) = liftInt (x-y)

mul :: Expr -> Expr -> Expr
mul (Val (Int' x)) (Val (Int' y)) = liftInt (x*y)

divide :: Expr -> Expr -> Expr
divide (Val (Int' x)) (Val (Int' y)) = liftInt (x `div` y)

neg :: Expr -> Expr -> Expr
neg (Val (Int' x)) _ = liftInt (-x)

pow :: Expr -> Expr -> Expr 
pow (Val (Int' x)) (Val (Int' y)) = liftInt (x^y)

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
-- State is threading the (current line, SymbolTable) pair (PC)
type SymbolTable = Map String Expr
type LineNum = Integer
type Program = Map LineNum Stm
type PC = (LineNum, SymbolTable)
type Environment = StateT PC (ReaderT Program IO) ()

runProgram :: Program -> IO ()
runProgram prog = do 
  runEnv programEnv prog (line1, Map.empty)
  return ()
  where line1 = fst (findMin prog)

runProgramDebug :: Program -> IO ()
runProgramDebug prog = do 
  runEnv debugEnv prog (line1, Map.empty)
  return ()
  where line1 = fst (findMin prog)

runEnv :: Environment -> Program -> PC -> IO ((),PC)
runEnv e prog pc = (runReaderT $ (runStateT e) pc) prog 

programEnv :: Environment 
programEnv = do 
  (line, _) <- State.get 
  if (line == (-1)) then return () else go line
  where go line = do { 
    program <- ask;
    execStatement (program ! line);
    programEnv;
    }

debugEnv :: Environment
debugEnv = do 
  (line, table) <- State.get
  program <- ask
  liftIO (putStrLn $ "LINE " ++ (show line))
  when (line /= (-1)) (liftIO (putStrLn $ "STATEMENT " ++ (show (program ! line))))
  liftIO (putStrLn $ "SYMBOL TABLE " ++ (show table))
  if (line == (-1)) then return () else go line 
  where go line = do {
    program <- ask; 
    execStatement (program ! line);
    debugEnv;
  }

runLine :: Environment
runLine = do 
  (line, table) <- State.get
  program <- ask
  execStatement (program ! line)

execStatement :: Stm -> Environment
execStatement (LET iden expr) = do
  (line, table) <- State.get
  program <- ask
  put (nextLine line program, insert (getID iden) (eval expr table) table)
  return ()
execStatement (PRINT expr) = do 
  (line, table) <- State.get
  program <- ask 
  liftIO (putStrLn (show $ eval expr table))
  put (nextLine line program, table)
  return ()
execStatement END = do {(_, table) <- State.get; put (-1, table);}

nextLine :: LineNum -> Program -> LineNum
nextLine x m  = if (Map.null snd_map) then (-1) else ((fst . findMin) snd_map)
  where snd_map = snd $ split x m

eval :: Expr -> SymbolTable -> Expr 
eval (Val x) _ = Val x
eval (ID str) sym = sym ! str
eval (OP _ f x y) sym = eval (f (eval x sym) (eval y sym)) sym
eval NULL _ = NULL
