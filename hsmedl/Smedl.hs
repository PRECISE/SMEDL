{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Smedl where

import           Control.Applicative
import           Data.Bits (complement)
import           Data.Functor.Identity
import           Data.List as L
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Debug.Trace
import           Text.Parsec hiding ((<|>), optional)
import           Text.Parsec.Expr
import           Text.Parsec.Language (emptyDef)
import           Text.Parsec.String
import           Text.Parsec.Token (GenLanguageDef(..), LanguageDef)
import qualified Text.Parsec.Token as P

(??) :: (a -> b -> c) -> b -> a -> c
(??) = flip

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = (fmap ??)

truth :: Alternative f => f a -> f Bool
truth p = True <$ p <|> pure False

traceP :: String -> Parser ()
traceP = traceM

------------------------------------------------------------------------------
-- Fundamental structures of the SMEDL language for Parsec
------------------------------------------------------------------------------

smedlDef :: LanguageDef st
smedlDef = emptyDef
    { commentStart   = "{-"
    , commentEnd     = "-}"
    , commentLine    = "--"
    , nestedComments = True
    , identStart     = letter
    , identLetter    = alphaNum <|> oneOf "_'"
    , opStart        = opLetter smedlDef
    , opLetter       = oneOf "=|&/<>+-*/%~![].:;,"
    , reservedOpNames= [ "=", "++", "--", "||", "&&", "==", "/=", "<"
                       , "<=", ">", ">=", "+", "-", "*", "/", "%", "~"
                       , "!", "->" ]
    , reservedNames  = [ "when", "object", "identity", "state"
                       , "events", "scenarios", "raise", "imported"
                       , "internal", "exported", "int", "pointer" ]
    , caseSensitive  = True
    }

lexer :: P.GenTokenParser String u Identity
lexer = P.makeTokenParser smedlDef

parens :: Parser a -> Parser a
parens = P.parens lexer

braces :: Parser a -> Parser a
braces = P.braces lexer

identifier :: Parser String
identifier = P.identifier lexer

reserved :: String -> Parser ()
reserved = P.reserved lexer

reservedOp :: String -> ParsecT String u Identity ()
reservedOp = P.reservedOp lexer

natural :: Parser Integer
natural = P.natural lexer

naturalOrFloat :: Parser (Either Integer Double)
naturalOrFloat = P.naturalOrFloat lexer

commaSep :: Parser a -> Parser [a]
commaSep = P.commaSep lexer

commaSep1 :: Parser a -> Parser [a]
commaSep1 = P.commaSep1 lexer

semiSep :: Parser a -> Parser [a]
semiSep = P.semiSep lexer

semiSep1 :: Parser a -> Parser [a]
semiSep1 = P.semiSep1 lexer

binary :: String -> (a -> a -> a) -> Assoc -> Operator String u Identity a
binary  name fun = Infix (do { reservedOp name; return fun })

prefix :: String -> (a -> a) -> Operator String u Identity a
prefix  name fun = Prefix (do { reservedOp name; return fun })

postfix :: String -> (a -> a) -> Operator String u Identity a
postfix name fun = Postfix (do { reservedOp name; return fun })

------------------------------------------------------------------------------
-- An AST for the SMEDL grammar, Parsec parsers for each AST term, and a Show
-- instance for pretty-printing AST terms
------------------------------------------------------------------------------

{- type            = ?/[a-zA-Z][A-Za-z0-9_]*/? ;
   identifier      = ?/[a-zA-Z][A-Za-z0-9_]*/? ;
   identifier_list = @:identifier {',' @:identifier}* | () ;
   target          = identifier  ;
   integer         = ?/[-+]?[0-9]+/? ;
   float           = ?/[-+]?[0-9]*\.?[0-9]+/? ; -}

{- variable_declaration
       = type:type var:identifier {',' var:identifier}* ';' ; -}

{- atom = integer | float | identifier | 'true' | 'false' | 'null' ; -}

data Atom
    = AInt Integer
    | AFloat Double
    | AIdent String
    | ABool Bool
    | ANull
    deriving Eq

instance Show Atom where
    show (AInt n)   = show n
    show (AFloat d) = show d
    show (AIdent s) = s
    show (ABool b)  = if b then "true" else "false"
    show ANull      = "null"

instance Ord Atom where
    compare (AInt x)   (AInt y)   = compare x y
    compare (AFloat x) (AFloat y) = compare x y
    compare (AIdent x) (AIdent y) = compare x y
    compare (ABool x)  (ABool y)  = compare x y

    compare ANull ANull = EQ

    compare (AInt _) _            = LT
    compare (AFloat _) (AInt _)   = GT
    compare (AFloat _) _          = LT
    compare (AIdent _) (AInt _)   = GT
    compare (AIdent _) (AFloat _) = GT
    compare (AIdent _) _          = LT
    compare (ABool _) (AInt _)    = GT
    compare (ABool _) (AFloat _)  = GT
    compare (ABool _) (AIdent _)  = GT
    compare (ABool _) _           = LT
    compare ANull _               = GT

parseAtom :: Parser Atom
parseAtom = choice
    [ ABool True <$ reserved "true"
    , ABool False <$ reserved "false"
    , ANull <$ reserved "null"
    , naturalOrFloat <&> \case Left i  -> AInt i
                               Right f -> AFloat f
    , AIdent <$> identifier ] <?> "atom"

{- expression = or_ex:and_expr {'||' or_ex:and_expr}+ | @:and_expr ;
   expression_list = @:expression {',' @:expression}* | () ;
   and_expr = and_ex:sub_expr {'&&' and_ex:sub_expr}+ | @:sub_expr ;
   sub_expr = {'!!'}*'!(' not_ex:expression ')'
            | {'!!'}*'(' @:expression ')'
            | @:comp_expr ;
   comp_expr = comp:arith_expr
                 {operator:('>=' | '<=' | '==' | '!=' | '>' | '<')
                      comp:arith_expr}+
             | '(' @:comp_expr ')'
             | @:arith_expr ;
   arith_expr = arith:term {operator:('+' | '-' | '*' | '/' | '%') arith:term}+
              | @:term ;
   term = {unary:('+' | '-' | '~' | '!')}* atom:atom {trailer:trailer}*
        | {unary:('+' | '-' | '~')}* '(' @:arith_expr ')' ;
   trailer = '[' [index:expression] ']'
           | '(' [params:expression_list] ')'
           | '.' dot:identifier {trailer:trailer}* ; -}

data Expr
    = EOr   Expr Expr            -- or_expr
    | EAnd  Expr Expr            -- and_expr
    | EEq   Expr Expr            -- comp_expr
    | ENeq  Expr Expr
    | ELt   Expr Expr
    | ELe   Expr Expr
    | EGt   Expr Expr
    | EGe   Expr Expr
    | EAdd  Expr Expr            -- arith_expr
    | ESub  Expr Expr
    | EMul  Expr Expr
    | EDiv  Expr Expr
    | EMod  Expr Expr
    | EPos  Expr                 -- term
    | ENeg  Expr
    | ECmp  Expr
    | ENot  Expr
    | EAtom Atom
    | EIdx  Atom Int             -- jww (2016-08-15): TODO
    | EApp  Atom [Expr]          -- jww (2016-08-15): TODO
    | EDot  Expr Expr            -- jww (2016-08-15): TODO
    deriving Eq

instance Show Expr where
    show (EOr  x1 x2)  = show x1 ++ " || " ++ show x2
    show (EAnd x1 x2)  = show x1 ++ " && " ++ show x2
    show (EEq  x1 x2)  = show x1 ++ " == " ++ show x2
    show (ENeq x1 x2)  = show x1 ++ " != " ++ show x2
    show (ELt  x1 x2)  = show x1 ++ " < " ++ show x2
    show (ELe  x1 x2)  = show x1 ++ " <= " ++ show x2
    show (EGt  x1 x2)  = show x1 ++ " > " ++ show x2
    show (EGe  x1 x2)  = show x1 ++ " >= " ++ show x2
    show (EAdd x1 x2)  = show x1 ++ " + " ++ show x2
    show (ESub x1 x2)  = show x1 ++ " - " ++ show x2
    show (EMul x1 x2)  = show x1 ++ " * " ++ show x2
    show (EDiv x1 x2)  = show x1 ++ " / " ++ show x2
    show (EMod x1 x2)  = show x1 ++ " % " ++ show x2
    show (EPos x)      = "+" ++ show x
    show (ENeg x)      = "-" ++ show x
    show (ECmp x)      = "~" ++ show x
    show (ENot x)      = "!" ++ show x
    show (EAtom a)     = show a
    show (EIdx a n)    = show a ++ "[" ++ show n ++ "]"
    show (EApp f args) = show f ++ " " ++ unwords (map show args)
    show (EDot x1 x2)  = show x1 ++ "." ++ show x2

exprTable :: [[Operator String u Identity Expr]]
exprTable =
    [ [ prefix "~" ECmp
      , prefix "-" ENeg
      , prefix "+" EPos
      , prefix "!" ENot ]
    , [ binary "." EDot AssocLeft ]
    , [ binary "*" EMul AssocLeft
      , binary "/" EDiv AssocLeft
      , binary "%" EMod AssocLeft ]
    , [ binary "+" EAdd AssocLeft
      , binary "-" ESub AssocLeft ]
    , [ binary "==" EEq AssocNone
      , binary "!=" ENeq AssocNone
      , binary "<"  ELt AssocNone
      , binary "<=" ELe AssocNone
      , binary ">"  EGt AssocNone
      , binary ">=" EGe AssocNone ]
    , [ binary "&&" EAnd AssocRight ]
    , [ binary "||" EOr AssocRight ]
    ]

parseTerm :: Parser Expr
parseTerm = traceP "parseTerm" >>
    parens parseExpr <|> EAtom <$> parseAtom <?> "term"

parseExpr :: Parser Expr
parseExpr = traceP "parseExpr" >>
    buildExpressionParser exprTable parseTerm <?> "expr"

{- event_definition =
       error:['error'] event_id:identifier ['(' params:parameter_list ')']
           ['=' definition:expression] ;
   parameter_list = @:type {',' @:type}* | () ;
   event_definition_list = @:event_definition {',' @:event_definition}* ';' ; -}

data EventKind = Internal | Imported | Exported deriving Eq

instance Show EventKind where
    show Internal = "internal"
    show Imported = "imported"
    show Exported = "exported"

data EventDef = EventDef
    { eventKind   :: EventKind
    , eventError  :: Bool
    , eventId     :: String
    , eventParams :: [Type]
    , eventDef    :: Maybe Expr }
    deriving Eq

instance Show EventDef where
    show EventDef {..}
        = show eventKind ++ " " ++ (if eventError then "error " else "")
       ++ eventId ++ "("
       ++ foldl' (\acc x -> if null acc
                            then show x
                            else ", " ++ show x) "" eventParams
       ++ ")"
       ++ (case eventDef of
               Just x  -> " = " ++ show x
               Nothing -> "")
       ++ ";"

parseEventDefs :: Parser [EventDef]
parseEventDefs = do
    traceP "parseEventDefs"
    kind <- choice
        [ Internal <$ reserved "internal"
        , Imported <$ reserved "imported"
        , Exported <$ reserved "exported" ] <?> "event definition kind"
    isErr <- truth (reserved "error") <?> "error keyword"
    xs <- commaSep1 $ do
        name   <- identifier <?> "event name"
        params <- parens (commaSep parseType) <?> "event params"
        def    <- optional (reservedOp "=" *> parseExpr) <?> "event definiton"
        return (name, params, def)
    return $ map (\(n, p, d) -> EventDef kind isErr n p d) xs

{- actions = '{' actions:action_item_list '}' ;
   action_item_list = @:action_item ';' { @:action_item ';' }* ;

   action_item
       = state_update:state_update
       | raise_stmt:raise_stmt
       | instantiation:instantiation_stmt
       | call_stmt:call_stmt ;

   state_update = target:target operator:('++' | '--')
       | target:target operator:'=' expression:expression ;
   state_update_list = @:state_update {',' @:state_update}* | () ;

   raise_stmt = 'raise' id:identifier ['(' expr_list+:expression_list ')'] ;

   instantiation_stmt
       = 'new' id:identifier ['(' state_update_list+:state_update_list ')'] ;

   call_stmt = target:target '(' expr_list+:expression_list ')' ; -}

data StateUpdate
    = SUIncrement String
    | SUDecrement String
    | SUAssign String Expr
    deriving Eq

instance Show StateUpdate where
    show (SUIncrement x)  = x ++ "++"
    show (SUDecrement x)  = x ++ "--"
    show (SUAssign x1 x2) = x1 ++ " = " ++ show x2

parseStateUpdate :: Parser StateUpdate
parseStateUpdate = do
    traceP "parseStateUpdate"
    x <- identifier <?> "variable name"
    choice
        [ SUIncrement x <$ reservedOp "++"
        , SUDecrement x <$ reservedOp "--"
        , reservedOp "=" *> (SUAssign x <$> parseExpr) ] <?> "state update"

-- jww (2016-08-15): TODO: Teng writes: "Moreover, the meaning of CallStmt is
-- to call the helper function. Maybe you should add a element in namespaces
-- to represents the namespace of helper function defined in '#import'?" This
-- means adding a new namespace.

data Action
    = AStateUpdate StateUpdate
      -- jww (2016-08-15): This should be a typed list of expressions,
      -- corresponding to the types defined for the arguments of the error
      -- event that is being raised.
    | ARaiseStmt String [Expr]

      -- jww (2016-08-15): Types should carry through to each [state_update].
    | AInstantiation String [StateUpdate]

      -- jww (2016-08-15): The arguments should be typed based on the defined
      -- event within the environment.
    | ACallStmt String [Expr]
    deriving Eq

showArgs :: [String] -> String
showArgs args = if null args
                    then ""
                    else "(" ++ intercalate ", " args ++ ")"

showExprArgs :: [Expr] -> String
showExprArgs = showArgs . map show

instance Show Action where
    show (AStateUpdate su)       = show su
    show (ARaiseStmt ident args) = "raise " ++ ident ++ showExprArgs args
    show (AInstantiation _ _)    = "AInstantiation"
    show (ACallStmt _ _)         = "ACallStmt"

parseAction :: Parser Action
parseAction = do
    traceP "parseAction"
    -- <|> -- jww (2016-08-21): parseActionInstantiation NYI
    -- <|> -- jww (2016-08-21): parseActionCallStmt NYI
    choice
        [ reserved "raise" *>
          (ARaiseStmt <$> (identifier <?> "event name")
                      <*> (parens (commaSep parseExpr) <|> return [])
                      <?> "raise action")
        , AStateUpdate <$> parseStateUpdate ] <?> "action"

{- event_instance = expression:expression ['when' when:expression] ; -}

data EventInstance = EventInstance
    { eventName     :: String
    , eventArgs     :: [String]
    , eventWhenExpr :: Maybe Expr }
    deriving Eq

instance Show EventInstance where
    show EventInstance {..}
        = eventName
       ++ showArgs eventArgs
       ++ (case eventWhenExpr of
               Just x  -> " when " ++ show x
               Nothing -> "")

parseEventInstance :: String -> Parser EventInstance
parseEventInstance ident = traceP "parseEventInstance" >>
    EventInstance
        <$> pure ident
        <*> (parens (commaSep (identifier <?> "event name")) <|> return [])
        <*> (Just <$> (reserved "when" *> parseExpr) <|> return Nothing)

{- step_definition = step_event:event_instance [step_actions:actions] ; -}

data Step = Step
    { stepEvent   :: EventInstance
    , stepActions :: [Action] }
    deriving Eq

showActions :: [Action] -> String
showActions acts | null acts = ""
showActions acts = " { " ++ intercalate "; " (map show acts) ++ " }"

instance Show Step where
    show Step {..} = show stepEvent ++ showActions stepActions

parseStep :: String -> Parser Step
parseStep ident = do
    traceP "parseStep"
    eventInst <- parseEventInstance ident
    acts <- braces (semiSep1 parseAction) <|> return []
    return $ Step eventInst acts

{- trace_definition
       = start_state:identifier '->'
           {trace_steps+:step_definition '->'}+  end_state:identifier
           ['else' [else_actions:actions] '->' else_state:identifier] ; -}

data Trace = Trace
    { startState  :: String
    , traceSteps  :: [Step]      -- non-empty
    , endState    :: String
    , elseActions :: [Action]
    , elseState   :: Maybe String }
    deriving Eq

instance Show Trace where
    show Trace {..}
        = startState ++ " -> "
       ++ intercalate (leader ++ "-> ") (map show traceSteps)
       ++ " -> " ++ endState
       ++ (case elseState of
               Just s -> leader ++ "else" ++ showActions elseActions
                               ++ " -> " ++ s
               Nothing -> "")
      where
        leader = "\n" ++ replicate (length startState + 1) ' '

parseTrace :: [EventDef] -> Parser Trace
parseTrace defs = trace "parseTrace" $ do
    start_state <- identifier <?> "start state"
    _ <- char ':' *> fail "scenario keyword" <|> pure ()
    reservedOp "->"
    trace_steps <- many1 $ do
        ident <- identifier <?> "possible event name"
        if any (\ev -> eventId ev == ident) defs
            then parseStep ident <* reservedOp "->"
            else fail "Event name did not match"
    end_state <- identifier <?> "end state"
    (else_actions, else_state) <-
        (do reserved "else"
            acts <- braces (many1 (parseAction <* reservedOp ";")) <|> return []
            reservedOp "->"
            name <- identifier <?> "else state name"
            return (acts, Just name)) <|> return ([], Nothing)
    return $ Trace start_state trace_steps end_state else_actions else_state

{- scenario_definition
       = atomic:['atomic'] scenario_id:identifier
           ':' traces:{trace_definition}+ ; -}

data Scenario = Scenario
    { isAtomic   :: Bool
    , scenarioId :: String
    , traces     :: [Trace] }       -- non-empty
    deriving Eq

instance Show Scenario where
    show Scenario {..}
        = (if isAtomic then "atomic " else "")
       ++ scenarioId ++ ":\n"
       ++ indent 2 (intercalate "\n" (map show traces))

parseScenario :: [EventDef] -> Parser Scenario
parseScenario defs = do
    traceP "parseScenario"
    atomic <- (True <$ reserved "atomic") <|> return False
    name   <- (identifier <?> "scenario name") <* reservedOp ":"
    traces <- many1 (parseTrace defs)
    return $ Scenario atomic name traces

{- import_definition = '#import' import_id:identifier ;
   object =
       imports+:{import_definition}*
       'object' object:identifier
       ['identity' identity+:{variable_declaration}+]
       ['state' state+:{variable_declaration}+]
       'events'
           { 'internal' internal_events+:event_definition_list
           | 'exported' exported_events+:event_definition_list}*
           'imported' imported_events+:event_definition_list
           { 'imported' imported_events+:event_definition_list
           | 'internal' internal_events+:event_definition_list
           | 'exported' exported_events+event_definition_list}*
       'scenarios'
           scenarios+:{scenario_definition}+ $ ; -}

data Type
    = TInt
    | TFloat
    | TBool
    | TPointer
    | TUser String
    deriving Eq

instance Show Type where
    show TInt      = "int"
    show TFloat    = "float"
    show TBool     = "bool"
    show TPointer  = "pointer"
    show (TUser s) = s

atomType :: Atom -> Type
atomType (AInt _)   = TInt
atomType (AFloat _) = TFloat
atomType (ABool _)  = TBool
atomType ANull      = TPointer

data Object = Object
    { imports    :: [String]
    , objectId   :: String
    , identities :: Map String Type      -- name -> type
    , variables  :: Map String Type      -- name -> type
    , events     :: [EventDef]
    , scenarios  :: [Scenario] }         -- non-empty
    deriving Eq

indent :: Int -> String -> String
indent n = (replicate n ' ' ++)
             . intercalate (replicate n ' ')
             . map (++ "\n") . lines

instance Show Object where
    show Object {..}
        = "object " ++ objectId ++ "\n"
       ++ (if M.null identities
           then ""
           else "identity\n" ++ indent 2 (showVars identities))
       ++ (if M.null variables
           then ""
           else "state\n" ++ indent 2 (showVars variables))
       ++ (if null events
           then ""
           else "events\n" ++ indent 2 (intercalate "\n" (map show events)))
       ++ ("scenarios\n" ++ indent 2 (intercalate "\n" (map show scenarios)))
      where
          showVars =
              M.foldlWithKey'
                  (\acc n ty -> show ty ++ " " ++ n ++ ";\n" ++ acc) ""

parseImports :: Parser [String]
parseImports = return []

parseType :: Parser Type
parseType = choice
    [ TInt     <$ reserved "int"
    , TPointer <$ reserved "pointer"
    , TUser    <$> (identifier <?> "user type name") ] <?> "type"

parseVarDecl :: Parser (Type, [String]) -- type, names
parseVarDecl = traceP "parseVarDecl" >>
    (,) <$> parseType <*> commaSep1 (identifier <?> "variable name")

parseVarDecls :: Parser (Map String Type)
parseVarDecls = traceP "parseVarDecls" >>
    foldr (\(t, ns) -> foldr (\n -> M.insert n t) ?? ns) mempty
        <$> many1 (parseVarDecl <* reservedOp ";")
        <?> "variable declarations"

parseObject :: Parser Object
parseObject = do
    traceP "parseObject"
    imps   <- parseImports
    name   <- reserved "object" *> identifier <?> "object name"
    idents <- reserved "identity" *> parseVarDecls <|> pure mempty
    state  <- reserved "state" *> parseVarDecls <|> pure mempty
    evs    <- reserved "events"
                  *> (concat <$> many1 (parseEventDefs <* reservedOp ";"))
                  <|> pure mempty
    scs    <- reserved "scenarios" *> many1 (parseScenario evs)
    eof                         -- confirm nothing more to parse
    return $ Object imps name idents state evs scs

------------------------------------------------------------------------------
-- Evaluator for SMEDL expressions down to SMEDL atoms
------------------------------------------------------------------------------

eval :: Expr -> Atom
eval (EOr x' y') =
    case (eval x', eval y') of
        (ABool x, ABool y) -> ABool (x || y)
        _ -> error "|| used with a non-boolean"

eval (EAnd x' y') =
    case (eval x', eval y') of
        (ABool x, ABool y) -> ABool (x && y)
        _ -> error "&& used with a non-boolean"

eval (EEq x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y)   -> ABool (x == y)
        (AInt x,   AFloat y) -> ABool (fromIntegral x == y)
        (AFloat x, AInt y)   -> ABool (x == fromIntegral y)
        (AFloat x, AFloat y) -> ABool (x == y)
        (ABool x,  ABool y)  -> ABool (x == y)
        (AIdent x, AIdent y) -> ABool (x == y)
        _ -> error "== used with incompatible arguments"

eval (ENeq x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y)   -> ABool (x /= y)
        (AInt x,   AFloat y) -> ABool (fromIntegral x /= y)
        (AFloat x, AInt y)   -> ABool (x /= fromIntegral y)
        (AFloat x, AFloat y) -> ABool (x /= y)
        (ABool x,  ABool y)  -> ABool (x /= y)
        (AIdent x, AIdent y) -> ABool (x /= y)
        _ -> error "!= used with incompatible arguments"

eval (ELt  x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y)   -> ABool (x < y)
        (AInt x,   AFloat y) -> ABool (fromIntegral x < y)
        (AFloat x, AInt y)   -> ABool (x < fromIntegral y)
        (AFloat x, AFloat y) -> ABool (x < y)
        _ -> error "< used with incompatible arguments"

eval (ELe  x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y)   -> ABool (x <= y)
        (AInt x,   AFloat y) -> ABool (fromIntegral x <= y)
        (AFloat x, AInt y)   -> ABool (x <= fromIntegral y)
        (AFloat x, AFloat y) -> ABool (x <= y)
        _ -> error "<= used with incompatible arguments"

eval (EGt  x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y)   -> ABool (x > y)
        (AInt x,   AFloat y) -> ABool (fromIntegral x > y)
        (AFloat x, AInt y)   -> ABool (x > fromIntegral y)
        (AFloat x, AFloat y) -> ABool (x > y)
        _ -> error "> used with incompatible arguments"

eval (EGe  x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y)   -> ABool (x >= y)
        (AInt x,   AFloat y) -> ABool (fromIntegral x >= y)
        (AFloat x, AInt y)   -> ABool (x >= fromIntegral y)
        (AFloat x, AFloat y) -> ABool (x >= y)
        _ -> error ">= used with incompatible arguments"

eval (EAdd  x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y) -> AInt (x + y)
        (AInt x,   AFloat y) -> AFloat (fromIntegral x + y)
        (AFloat x, AInt y) -> AFloat (x + fromIntegral y)
        (AFloat x, AFloat y) -> AFloat (x + y)
        _ -> error "+ used with incompatible arguments"

eval (ESub x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y) -> AInt (x - y)
        (AInt x,   AFloat y) -> AFloat (fromIntegral x - y)
        (AFloat x, AInt y) -> AFloat (x - fromIntegral y)
        (AFloat x, AFloat y) -> AFloat (x - y)
        _ -> error "- used with incompatible arguments"

eval (EMul  x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y) -> AInt (x * y)
        (AInt x,   AFloat y) -> AFloat (fromIntegral x * y)
        (AFloat x, AInt y) -> AFloat (x * fromIntegral y)
        (AFloat x, AFloat y) -> AFloat (x * y)
        _ -> error "* used with incompatible arguments"

eval (EDiv   x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y) -> AFloat (fromIntegral x / fromIntegral y)
        (AInt x,   AFloat y) -> AFloat (fromIntegral x / y)
        (AFloat x, AInt y) -> AFloat (x / fromIntegral y)
        (AFloat x, AFloat y) -> AFloat (x / y)
        _ -> error "/ used with incompatible arguments"

eval (EMod   x' y') =
    case (eval x', eval y') of
        (AInt x,   AInt y) -> AInt (x `mod` y)
        _ -> error "% used with incompatible arguments"

eval (EPos x') =
    case eval x' of
        AInt x -> AInt (abs x)
        AFloat x -> AFloat (abs x)
        _ -> error "+ used with incompatible arguments"

eval (ENeg x') =
    case eval x' of
        AInt x -> AInt (- x)
        AFloat x -> AFloat (- x)
        _ -> error "- used with incompatible arguments"

eval (ECmp x') =
    case eval x' of
        AInt x -> AInt (complement x)
        _ -> error "~ used with incompatible arguments"

eval (ENot x') =
    case eval x' of
        ABool x -> ABool (not x)
        _ -> error "! used with incompatible arguments"

eval (EAtom x') =
    case x' of
        AIdent i ->
            -- jww (2016-08-16): Lookup the variable's value here.
            AIdent i
        x -> x

eval (EApp _f _args) = error "jww (2016-08-16): TODO: EApp"
eval (EIdx _x _n)    = error "jww (2016-08-16): TODO: EIdx"
eval (EDot _x1 _x2)  = error "jww (2016-08-16): TODO: EDot"

------------------------------------------------------------------------------
-- Execution semantics for stateful SMEDL monitors
------------------------------------------------------------------------------

importedEvent :: EventDef -> Bool
importedEvent ev = case eventKind ev of
    Imported -> True
    Internal -> False
    Exported -> False

data Monitor = Monitor
    { idents :: Map String Atom
    , vars   :: Map String Atom
    , states :: Map String String -- each scenario has a current state
    }
    deriving (Eq, Show)

newMonitor :: Object -> Map String Atom -> Monitor
newMonitor obj idents =
    -- Initial state for each scenario is the start state of its first trace
    Monitor idents M.empty (startStates obj)
  where
    startStates
        = M.fromList
        . concatMap (\s -> case traces s of
                             [] -> []
                             (t:_) -> [(scenarioId s, startState t)])
        . scenarios

data Event = Event { ieName :: String, ieArgs :: [Atom] }
    deriving Eq

instance Show Event where
    show Event {..} = ieName ++ showExprArgs (map EAtom ieArgs)

lookupEventDef :: Object -> Event -> Maybe EventDef
lookupEventDef obj (Event name args) =
    case concatMap checkEvent (events obj) of
        [] -> Nothing
        e:_ -> Just e
  where
    checkEvent e@EventDef {..} =
        if eventId == name
               && length args == length eventParams
               && all (== True) (map (\(t, a) -> t == atomType a)
                                     (zip eventParams args))
        then [e] else []

instance Ord Event where
    compare (Event xn xargs) (Event yn yargs) =
        compare xn yn `mappend` compare xargs yargs

data Evolution = Evolution (Monitor -> Monitor) (Set Event)

instance Monoid Evolution where
    mempty = Evolution id S.empty
    mappend (Evolution f xs) (Evolution g ys) =
        Evolution
            -- jww (2016-08-21): NYI
            (\m@(Monitor _i vs ss) ->
                 let Monitor fi fvs fss = f m in
                 let Monitor gi gvs gss = g m in
                 -- If they have the same effect, or if 'g' has no effect,
                 -- then use 'f'
                 if (fss == gss && fvs == gvs) || (gss == ss && gvs == vs)
                 then Monitor fi fvs fss
                 else if fss == ss && fvs == vs
                 then Monitor gi gvs gss
                 else if fss == ss && gvs == vs
                 then Monitor fi fvs gss
                 else if ss == gss && vs == fvs
                 then Monitor fi gvs fss
                 else error $ "Incompatible Monitor updates: "
                          ++ show m
                          ++ " (f = " ++ show (f m)
                          ++ ") (g = " ++ show (g m) ++ ")")
            (xs `mappend` ys)

runScenario :: Scenario -> Monitor -> Event -> Either String Evolution
runScenario = undefined

runMonitor :: Object -> Monitor -> Event -> Either String (Monitor, Set Event)
runMonitor obj mon ev = case go mon ev of
    Left err -> Left err
    Right (_, Evolution k events) -> Right (k mon, events)
  where
    go :: Monitor -> Event -> Either String (EventDef, Evolution)
    go mon' ev' =
        case lookupEventDef obj ev' of
            Nothing ->
                Left $ "Event (" ++ show ev'
                    ++ ") does not match any known event definitions"
            Just edef -> do
                -- Loop through all the scenario steps, looking for those that
                -- match on the current state. If so, process them (which will
                -- include logic to test whether the step is indeed applicable,
                -- based on the input event and monitor state).
                evolutions <- mapM (\s -> runScenario s mon' ev')
                                   (scenarios obj)
                let evolve = mconcat evolutions
                evolve' <- apply mon' evolve
                return (edef, evolve')

    apply :: Monitor -> Evolution -> Either String Evolution

    -- If no events were produced, this is the simplest termination condition.
    apply _ a@(Evolution _ s) | S.null s = return a

    apply m (Evolution k evs) = do
        -- Determine the next monitor state.
        let m' = k m

        -- Take all the events produced, and feed them back into the monitor;
        -- if any external event fails to result in further action, retain it
        -- for the caller.
        a'@(Evolution k' evs') <- S.foldr (combine m') (pure mempty) evs

        -- If the list of external events has stabilized, and there are no
        -- further state changes to be made, then the work is done; otherwise,
        -- try again.
        Evolution k'' evs'' <-
                if m == k' m && evs == evs'
                then return a'
                else apply m' a'

        -- Make sure that the state change function in the Evolution relates
        -- the initial Monitor to the final one.
        return $ Evolution (k'' . k) evs''
      where
        combine :: Monitor -> Event -> Either String Evolution
                -> Either String Evolution
        combine m' e rest = do
            x <- rest
            (edef, a@(Evolution f es)) <- go m' e
            return $ x `mappend`
                if m' == f m'
                       && null es
                       && eventKind edef /= Internal
                then Evolution id (S.singleton e)
                else a
