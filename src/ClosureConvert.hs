module ClosureConvert where

import IR
import Subst
import Lang

import Control.Monad.State
import Control.Monad.Writer
import Data.List

tyToirty :: Ty -> IrTy
tyToirty NatTy = IrInt
tyToirty (FunTy _ _) = IrClo

runCC :: [Decl TTerm] -> [IrDecl]
runCC decls = concatMap (\(Decl _ _ t) -> runCC' t) decls

runCC' :: TTerm -> [IrDecl]
runCC' t = let ((x,z),y) = (runWriter ( runStateT (closureConvert t []) 0 ))
           in (IrVal "main" IrClo x):y

closureConvert :: TTerm -> [Name] -> StateT Int (Writer [IrDecl]) Ir
    -- si no es 0 no referencia al lam actual
closureConvert (V p (Bound i)) nenv = error "Error de apertura de Variables bound??"
closureConvert (V (i,ty) (Free x)) nenv = do
    case elemIndex x nenv of
        Nothing -> error "Error de apertura de Variables"
        Just n -> return (IrAccess (IrVar x) (tyToirty ty) (n + 1))
closureConvert (V p (Global x)) nenv = return (IrGlobal x)
closureConvert (Const _ tt) nenv = return (IrConst tt)
closureConvert (IfZ p c t f) nenv = do 
    irc <- closureConvert c nenv
    irt <- closureConvert t nenv
    irf <- closureConvert f nenv
    return (IrIfZ irc irt irf)
closureConvert (Print p str t) nenv = do
    irt <- closureConvert t nenv
    return (IrPrint str irt)
closureConvert (BinaryOp p op t u) nenv = do
    irt <- closureConvert t nenv
    iru <- closureConvert u nenv
    return (IrBinaryOp op irt iru)
closureConvert (Let p v vty def body) nenv = do
    irdef <- closureConvert def nenv
    name <- getNewName
    let obody = open (v ++ name) body
    cbody <- closureConvert obody nenv
    return (IrLet (v ++ name) (tyToirty vty) irdef cbody)
closureConvert tt@(App (i, ty) l r)  nenv = do
    irl <- closureConvert l nenv
    irr <- closureConvert r nenv
    return (IrCall irl [irr] (tyToirty ty))
closureConvert (Fix p f fty x xty (Sc2 t)) _ = error "Fix"
closureConvert tt@(Lam (pos, fty) name ty body) nenv = do
    irname <- getNewName
    mkname <- getNewName
    let nenv = getFree tt
    let obody = open irname body
    irtt <- closureConvert obody nenv
    -- crear un let para bindindear cada nombre libre de nenv con su ir correspondiente.
    -- para obtener los ir 
    let decl = IrFun mkname (tyToirty fty) [(mkname, IrClo), (name, tyToirty ty)] irtt
    tell [decl]
    return (MkClosure mkname (map (\x -> IrVar x) nenv)) -- Los nombres de nenv pasan a ser nombres de Ir simplemente.
 
getNewName :: StateT Int (Writer [IrDecl]) Name
getNewName = do
    irname <- get
    put (irname + 1)
    return (show irname)

