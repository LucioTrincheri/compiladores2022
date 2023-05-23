{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)
import Data.Maybe

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> (do x <- var
                 return (SNameTy x))
         <|> parens typeP

typeP :: P STy
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- (optionMaybe atom)
  return (SPrint i str a)

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, STy)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

-- Read 1 or more bindings 
readparams :: P [([Name], STy)]
readparams = many1 ((try (parens readparam)) <|> readparam)

lamreadparams :: P [([Name], STy)]
lamreadparams = parens (many1 ((try (parens readparam)) <|> readparam))

readparam :: P ([Name], STy)
readparam = do l <- many1 var
               reservedOp ":"
               t <- typeP
               return (l, t)

-- Read 0 or more bindings 
readparams0 :: P [([Name], STy)]
readparams0 = many ((parens readparam) <|> readparam)


lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         params <- lamreadparams
         reservedOp "->"
         t <- expr
         return (SLam i params t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         (x, xty) <- parens binding
         params <- readparams0
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) (x,xty) params t)

lets :: P STerm
lets = do
          try (do letexp) <|> try (do letfun)

letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  (v,ty) <- (parens binding) <|> binding
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i (v,ty) def body)


letfun :: P STerm
letfun = do
  i <- getPos
  reserved "let"
  bool <- fmap isJust (optionMaybe (reserved "rec"))
  f <- var
  params <- readparams
  reservedOp ":"
  ty2 <- typeP
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLetLam i bool (f, params, ty2) def body)

-- | Parser de términos
tm :: P STerm
tm = (try lam) <|> (try ifz) <|> (try printOp) <|> (try fix) <|> (try lets) <|> (try app)

-- | Parser de declaraciones
decl :: P (SDecl STerm)
decl = do 
        try (do declfun) <|> (do declexp) <|> (do decltype)

declexp :: P (SDecl STerm)
declexp = do
  i <- getPos
  reserved "let"
  v <- var
  (do 
    reservedOp ":"
    typeP
    reservedOp "="
    def <- expr
    return (SDecl i v def))
    <|> (do reservedOp "="
            def <- expr
            return (SDecl i v def))

declfun :: P (SDecl STerm)
declfun = do
  i <- getPos
  reserved "let"
  bool <- fmap isJust (optionMaybe (reserved "rec"))
  f <- var
  params <- readparams
  reservedOp ":"
  ty2 <- typeP
  reservedOp "="
  def <- expr
  return (SDeclLam i bool f params ty2 def)

decltype :: P (SDecl STerm)
decltype = do
  i <- getPos
  reserved "type"
  n <- var
  reservedOp "="
  t <- typeP
  return (SDeclType i n t)

-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm =  (try (Right <$> expr)) <|> (Left <$> decl)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
