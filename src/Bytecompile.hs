{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental
Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import Subst
import MonadFD4
import Common

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le, putWord8 )
import Data.Binary.Get ( getWord32le, getWord8, isEmpty )
import Data.Word

import Data.List (intercalate)
import Data.List.Split
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un8 :: [Word8] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord8 bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord8
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:
   f (CALL : cs) = ...
 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.
 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern JUMP     = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern IJUMP    = 15
pattern TAILCALL = 16
pattern POP      = 17

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:NULL:NULL:NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i1:i2:i3:i4:xs)     = ("CONST " ++ (show (fourBytesToInt [i1,i2,i3,i4]))) : showOps xs 
showOps (ACCESS:i:xs)    = "ACCESS" : show i : showOps xs
showOps (FUNCTION:i:xs)  = "FUNCTION" : show i : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:i:xs)       = "FIX" : (show i) : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = "JUMP" : show i: showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg:rest) = splitOn [NULL,NULL,NULL,NULL] xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps (concat rest)
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (POP:xs)         = "POP" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

intTo4Bytes :: Int -> [Int]
intTo4Bytes x = [mod (div x (256 ^ 3)) 256, mod (div x (256 ^ 2)) 256, mod (div x 256) 256, mod x 256]

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V i (Global x)) = failPosFD4 (fst i) "No deberia pasar nunca"
bcc (V i (Bound x)) = return [ACCESS, x]                 
bcc (Const i (CNat x)) = return ([CONST] ++ intTo4Bytes x)
bcc (Lam i x ty (Sc1 y)) = do y' <- bct y
                              return ([FUNCTION] ++ [(length y')] ++ y')
bcc (App i x y ) = do x' <- bcc x
                      y' <- bcc y
                      return (x' ++ y' ++ [CALL])                     
bcc (BinaryOp i x y z ) = do y' <- bcc y
                             z' <- bcc z
                             case x of
                              Add -> return (z' ++ y' ++ [ADD])
                              Sub -> return (z' ++ y' ++ [SUB])
bcc (Fix i x xty y yty (Sc2 z)) = do z' <- bct z
                                     return ([FIX] ++ [(length z')] ++ z')
bcc (Let i x xty y (Sc1 z)) = do y' <- bcc y
                                 let oz = (betterOpen x (Sc1 z))
                                 if (countFree z == countFree oz)
                                 then do oz' <- bcc oz
                                         return (y' ++ [POP] ++  oz')
                                 else do z' <- bcc z
                                         return (y' ++ [SHIFT] ++ z' ++ [DROP])
bcc (IfZ i x y z) = do x' <- bcc x
                       y' <- bcc y
                       z' <- bcc z
                       return (x' ++ [JUMP] ++ [(length y') + 2] ++ y' ++ [IJUMP] ++ [length z'] ++ z')
bcc (Print i msg y) = do y' <- bcc y
                         return ([PRINT] ++ (string2bc msg) ++ [NULL,NULL,NULL,NULL] ++ y' ++ [PRINTN])

bct :: MonadFD4 m => TTerm -> m Bytecode
bct (App i x y ) = do x' <- bcc x
                      y' <- bcc y
                      return (x' ++ y' ++ [TAILCALL])
bct (IfZ i x y z) = do x' <- bcc x
                       y' <- bct y
                       z' <- bct z
                       return (x' ++ [JUMP] ++ [length y'] ++ y' ++ z')
bct (Let i x xty y (Sc1 z)) = do y' <- bcc y
                                 let oz = (betterOpen x (Sc1 z))
                                 if (countFree z == countFree oz)
                                 then do oz' <- bct oz
                                         return (y' ++ [POP] ++ oz')
                                 else do z' <- bct z
                                         return (y' ++ [SHIFT] ++ z')
bct x = do x' <- bcc x
           return (x' ++ [RETURN])

bss :: MonadFD4 m => TTerm -> m Bytecode
bss (IfZ i x y z) = do x' <- bcc x  
                       y' <- bss y
                       z' <- bss z
                       return (x' ++ [JUMP] ++ [length y'] ++ y' ++ z')
bss (Let i x xty y (Sc1 z)) = do y' <- bcc y
                                 let oz = (betterOpen x (Sc1 z))
                                 if (countFree z == countFree oz)
                                 then do oz' <- bss oz
                                         return (y' ++ [POP] ++ oz')
                                 else do z' <- bss z
                                         return (y' ++ [SHIFT] ++ z')
bss x = do x' <- bcc x
           return (x' ++ [STOP])


-- La funcion bss puede salir por la aplicacion cuando no deberia

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
charTo32:: Char -> Bytecode
charTo32 c = intTo4Bytes (ord c)

string2bc :: String -> Bytecode
string2bc s = concat (map charTo32 s)

thirty2toChar:: Bytecode -> Char
thirty2toChar xs = chr (fourBytesToInt xs)

bc2string :: Bytecode -> String
 -- bc2string (i1:i2:i3:i4:[]) = [(thirty2toChar [i1,i2,i3,i4])]
bc2string [] = []
bc2string (i1:i2:i3:i4:s) = (thirty2toChar [i1,i2,i3,i4]) : (bc2string s)

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule i = do let i' = map (\(Decl a b t) -> (Decl a b (globalToFree t))) i
                         by <- (bytecompileModule' i')
                         com <- (bss by)
                         return com

bytecompileModule' :: MonadFD4 m => Module -> m TTerm
bytecompileModule' ((Decl i name body):[]) = return body
bytecompileModule' ((Decl i name body):xs) = do by <- (bytecompileModule' xs)
                                                return (Let (i, (getTy body)) name (getTy body) body (close name by))

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = do 
  BS.writeFile filename (encode $ BC $ fromIntegral' <$> bs)
  where fromIntegral' x = if x < 256 && x >= 0 then fromIntegral x else error "Msal codificado"

---------------------------
-- * Ejecución de bytecode
---------------------------

data MVal = MNat Int | MClos [MVal] Bytecode | MDir [MVal] Bytecode


-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un8) . decode <$> BS.readFile filename

fourBytesToInt :: Bytecode -> Int
fourBytesToInt (i1:i2:i3:i4:xs) = (256 ^ 3) * i1 + (256 ^ 2) * i2 + 256 * i3 + i4

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = runBD' bc [] []

runBD' :: MonadFD4 m => Bytecode -> [MVal] -> [MVal] -> m ()
runBD' (NULL:c) _ _ = printFD4 "No deberiamos llegar aca"
runBD' (RETURN:_) _ (v:(MDir e c):s) = runBD' c e (v:s)
runBD' (CONST:i1:i2:i3:i4:c) e s = runBD' c e ((MNat (fourBytesToInt [i1,i2,i3,i4])):s)
runBD' (ACCESS:(i:c)) e s  = runBD' c e ((e!!i):s)
runBD' (FUNCTION:(fl:c)) e s = let c' = (drop fl c)
                             in runBD' c' e ((MClos e c):s)
runBD' (CALL:c) e (v:(MClos ef cf):s) = runBD' cf (v:ef) ((MDir e c):s)
runBD' (ADD:c) e ((MNat x):((MNat y):s)) = runBD' c e ((MNat (x+y)):s)
runBD' (SUB:c) e ((MNat x):((MNat y):s)) = runBD' c e ((MNat (x-y)):s)
runBD' (FIX:(fl:c)) e s = let c' = (drop fl c)
                              efix = (MClos efix c):e
                          in runBD' c' e ((MClos efix c):s)
runBD' (STOP:_) e s = printFD4 "Fin ejecucion"
runBD' (SHIFT:c) e (v:s) = runBD' c (v:e) s
runBD' (DROP:c) (v:e) s = runBD' c e s
runBD' (PRINT:c) e s = runBD'' c e s
                       where runBD'' (NULL:NULL:NULL:NULL:c) e s = runBD' c e s
                             runBD'' (i1:i2:i3:i4:c) e s = do printFD4Char [(thirty2toChar [i1,i2,i3,i4])]
                                                              runBD'' c e s
-- runBD' (PRINT:c) e s = let (st, c') = splitAt NULL c
--                       in do printFD4 (map chr st)
--                             runBD' c' e s
runBD' (PRINTN:c) e s@((MNat n):_) = do printFD4 (show n)
                                        runBD' c e s
runBD' (JUMP:(tl:c)) e ((MNat n):s) = if n == 0 
                                      then runBD' c e s
                                      else runBD' c' e s
                                        where c' = drop tl c
runBD' (IJUMP:(fl:c)) e s = let c' = (drop fl c)
                            in runBD' c' e s
runBD' (TAILCALL:c) e (!v:(MClos ef cf):s) = runBD' cf (v:ef) s
runBD' (POP:c) e (v:s) = runBD' c e s
runBD' _ _ _ = failFD4 "Error de ejecucion"