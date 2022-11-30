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

data Stm = ExprStm Expr | LET Expr Expr | GOTO Integer
         | PRINT [Expr] | IF Expr Integer | NEXT [Expr] 
         | INPUT String [Expr] | END


data Value = Int' Integer | String' String | Float' Float
  deriving Eq

instance Show Expr where
  show (Val x)          = show x
  show (FUN name e)     = name ++ "(" ++ (show e) ++ ")"
  show (OP str f e1 e2) = "(" ++ (show e1) ++ str ++ (show e2) ++ ")"
  show (ID str)         = str

instance Show Stm where
  show (ExprStm e) = show e
  show (LET e1 e2) = "LET " ++ (show e1) ++ " = " ++ (show e2)
  show (GOTO x) = "GOTO " ++ (show x)
  show (IF e x) = "IF " ++ (show e) ++ " THEN " ++ (show x)
  show (PRINT [e]) = "PRINT " ++ (show e)
  show (PRINT e) = "PRINT " ++ (concatMap (\x -> (show x) ++ ",") e) 
  show (INPUT str [e]) = "INPUT " ++ (show str) ++ (show e)
  show (INPUT str e) = "INPUT " ++ (show str) ++ (concatMap (\x -> (show x) ++ ",") e)
  show END       = "END"

instance Show Value where 
  show (Int' x) = show x
  show (String' x) =  x
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
constInt = do {space; xs <- number; return (Val $ Int' xs)}

constFloat :: Parser Expr 
constFloat = do {space; xs <- float; return (Val $ Float' xs)}

constant :: Parser Expr 
constant = constString `mplus` constFloat `mplus` constInt

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

exprList :: Parser [Expr]
exprList = (expr `sepby` do {space; sat (== ',')}) 
           `mplus` do {x <- expr; return [x]}

printList :: Parser [Expr]
printList = (expr `sepby` do {space; sat (\x -> x == ',' || x == ';')}) 
            `mplus` do {x <- expr; return [x]}

idList :: Parser [Expr]
idList = (iden `sepby` do {space; sat (== ',')})
         `mplus` do {x <- iden; return [x]}

endParse :: Parser Stm
endParse = do {symb "END"; return END} 

gotoParse :: Parser Stm 
gotoParse = do {symb "GOTO"; x <- natural; return (GOTO x)}

ifParse :: Parser Stm 
ifParse = do {symb "IF"; e <- expr; symb "THEN"; x <- natural; return (IF e x)}

inputParse :: Parser Stm
inputParse = do 
  symb "INPUT"
  (Val (String' x)) <- constString
  sat (== ';')
  ls <- idList
  return (INPUT x ls)

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
  e <- printList 
  return (PRINT e)

stmParse :: Parser Stm 
stmParse = endParse `mplus` gotoParse `mplus` ifParse `mplus`
           inputParse `mplus` letParse `mplus` printParse

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

l1 :: Expr 
l1 = liftInt 1
l0 :: Expr 
l0 = liftInt 0 

liftFloat :: Float -> Expr
liftFloat = Val . Float'

bitAND :: Expr -> Expr -> Expr 
bitAND (Val (Int' x)) (Val (Int' y)) = liftInt (x .&. y)
bitAND (Val (Int' x)) (Val (Float' y)) = liftInt (x .&. (floor y))
bitAND (Val (Float' x)) (Val (Int' y)) = liftInt ((floor x) .&. y)
bitAND (Val (Float' x)) (Val (Float' y)) = liftInt ((floor x) .&. (floor y))

bitOR :: Expr -> Expr -> Expr
bitOR (Val (Int' x)) (Val (Int' y)) = liftInt (x .|. y)
bitOR (Val (Int' x)) (Val (Float' y)) = liftInt (x .|. (floor y))
bitOR (Val (Float' x)) (Val (Int' y)) = liftInt ((floor x) .|. y)
bitOR (Val (Float' x)) (Val (Float' y)) = liftInt ((floor x) .|. (floor y))

bitNOT :: Expr -> Expr -> Expr
bitNOT (Val (Int' x)) _ = if x == 0 then l1 else l0 
bitNOT (Val (Float' x)) _ = if x == 0.0 then l1 else l0

equal :: Expr -> Expr -> Expr 
equal (Val (Int' x)) (Val (Int' y)) = if (x == y) then  l1 else l0
equal (Val (Int' x)) (Val (Float' y)) = if (fromIntegral x == y) then l1 else l0
equal (Val (Float' x)) (Val (Int' y)) = if (x == fromIntegral y) then l1 else l0
equal (Val (Float' x)) (Val (Float' y)) = if (x == y) then l1 else l0

noteq :: Expr -> Expr -> Expr
noteq x y = bitNOT (equal x y) NULL

greater :: Expr -> Expr -> Expr
greater (Val (Int' x)) (Val (Int' y)) = if (x > y) then liftInt 1 else liftInt 0
greater (Val (Float' x)) (Val (Int' y)) = if (x > fromIntegral y) then liftInt 1 else liftInt 0
greater (Val (Int' x)) (Val (Float' y)) = if (fromIntegral x > y) then liftInt 1 else liftInt 0
greater (Val (Float' x)) (Val (Float' y)) = if (x > y) then liftInt 1 else liftInt 0


greaterEQ :: Expr -> Expr -> Expr
greaterEQ x y = (equal x y) `bitOR` (greater x y)

less :: Expr -> Expr -> Expr
less (Val (Int' x)) (Val (Int' y)) = if (x < y) then liftInt 1 else liftInt 0
less (Val (Float' x)) (Val (Int' y)) = if (x < fromIntegral y) then liftInt 1 else liftInt 0
less (Val (Int' x)) (Val (Float' y)) = if (fromIntegral x < y) then liftInt 1 else liftInt 0
less (Val (Float' x)) (Val (Float' y)) = if (x < y) then liftInt 1 else liftInt 0

lessEQ :: Expr -> Expr -> Expr
lessEQ x y = (equal x y) `bitOR` (less x y)

add :: Expr -> Expr -> Expr
add (Val (Int' x)) (Val (Int' y)) = liftInt (x+y)
add (Val (Float' x)) (Val (Int' y)) = liftFloat (x+(fromIntegral y))
add (Val (Int' x)) (Val (Float' y)) = liftFloat ((fromIntegral x)+y)
add (Val (Float' x)) (Val (Float' y)) = liftFloat (x+y)

sub :: Expr -> Expr -> Expr
sub (Val (Int' x)) (Val (Int' y)) = liftInt (x-y)
sub (Val (Float' x)) (Val (Int' y)) = liftFloat (x-(fromIntegral y))
sub (Val (Int' x)) (Val (Float' y)) = liftFloat ((fromIntegral x)-y)
sub (Val (Float' x)) (Val (Float' y)) = liftFloat (x-y)

mul :: Expr -> Expr -> Expr
mul (Val (Int' x)) (Val (Int' y)) = liftInt (x*y)
mul (Val (Float' x)) (Val (Int' y)) = liftFloat (x*(fromIntegral y))
mul (Val (Int' x)) (Val (Float' y)) = liftFloat ((fromIntegral x)*y)
mul (Val (Float' x)) (Val (Float' y)) = liftFloat (x*y)

divide :: Expr -> Expr -> Expr
divide (Val (Int' x)) (Val (Int' y)) = liftFloat ((fromIntegral x) / (fromIntegral y))
divide (Val (Float' x)) (Val (Int' y)) = liftFloat (x/(fromIntegral y))
divide (Val (Int' x)) (Val (Float' y)) = liftFloat ((fromIntegral x)/y)
divide (Val (Float' x)) (Val (Float' y)) = liftFloat (x/y)

neg :: Expr -> Expr -> Expr
neg (Val (Int' x)) _ = liftInt (-x)
neg (Val (Float' x)) _ = liftFloat (-x)

pow :: Expr -> Expr -> Expr 
pow (Val (Int' x)) (Val (Int' y)) = liftInt (x^y)
pow (Val (Float' x)) (Val (Int' y)) = liftFloat (x**(fromIntegral y))
pow (Val (Int' x)) (Val (Float' y)) = liftFloat ((fromIntegral x)**y)
pow (Val (Float' x)) (Val (Float' y)) = liftFloat (x**y)

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
type CallStack = [Stm]
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
execStatement (PRINT expr) = do 
  (line, table) <- State.get
  program <- ask 
  let exprs = fmap (show . (flip eval table)) expr
  liftIO (putStrLn (concat exprs))
  put (nextLine line program, table)
execStatement (INPUT str xs) = do {liftIO (putStrLn str); go xs}
  where go [] = do {
    (line, table) <- State.get;
    prog <- ask;
    put (nextLine line prog, table)
    }
        go (x:xs) = do {
        (line,table) <- State.get;
        y <- liftIO getLine;
        put (line, insert (getID x) (eval ((fst . head) $ runStateT expr y) table) table);
        go xs
        }
execStatement END = do {(_, table) <- State.get; put (-1, table);}
execStatement (GOTO x) = do {(_, table) <- State.get; put (x, table)}
execStatement (IF e x) = do 
  (line, table) <- State.get
  program <- ask
  case ((eval e table) `equal` (Val $ Int' 0)) of 
    (Val (Int' 0)) -> put (x, table)
    (Val (Int' 1)) -> put (nextLine line program, table)

nextLine :: LineNum -> Program -> LineNum
nextLine x m  = if (Map.null snd_map) then (-1) else ((fst . findMin) snd_map)
  where snd_map = snd $ split x m

eval :: Expr -> SymbolTable -> Expr 
eval (Val x) _ = Val x
eval (ID str) sym = sym ! str
eval (OP _ f x y) sym = eval (f (eval x sym) (eval y sym)) sym
eval (FUN "INT" e) sym = f evaled
  where f (Val (Int' x)) = Val $ Int' x 
        f (Val (Float' x )) = Val $ Int' $ floor x
        evaled = eval e sym
eval NULL _ = NULL
