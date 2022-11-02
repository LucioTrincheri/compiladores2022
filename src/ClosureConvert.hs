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
runCC' t = let ((x,z),y) = (runWriter ( runStateT (closureConvert t) 0 ))
           in (IrVal "main" IrClo x):y

closureConvert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
    -- si no es 0 no referencia al lam actual
closureConvert (V p (Bound i)) = error "Error de apertura de Variables bound??"
closureConvert (V (i,ty) (Free x)) = return (IrVar x)
closureConvert (V p (Global x)) = return (IrGlobal x)
closureConvert (Const _ tt) = return (IrConst tt)
closureConvert (IfZ p c t f) = do 
    irc <- closureConvert c
    irt <- closureConvert t
    irf <- closureConvert f
    return (IrIfZ irc irt irf)
closureConvert (Print p str t) = do
    irt <- closureConvert t
    return (IrPrint str irt)
closureConvert (BinaryOp p op t u) = do
    irt <- closureConvert t
    iru <- closureConvert u
    return (IrBinaryOp op irt iru)
closureConvert (Let p v vty def body) = do
    irdef <- closureConvert def
    name <- getNewName
    let obody = open (v ++ name) body
    cbody <- closureConvert obody
    return (IrLet (v ++ name) (tyToirty vty) irdef cbody)
closureConvert (App (i, ty) l r)  = do
    irl <- closureConvert l
    irr <- closureConvert r
    auxClos <- getNewName
    let clos = auxClos ++ "_clos"
    -- [[f x]] = let clos = [[f]] in clos[0] (clos, [[x]])
    -- IrClo es correcto??
    return (IrLet clos IrClo irl (IrCall (IrAccess (IrVar clos) IrClo 0) [(IrVar clos), irr] (tyToirty ty)))
closureConvert (Fix p f fty x xty (Sc2 t)) = error "Fix"
closureConvert tt@(Lam (pos, fty) name ty body) = do
    varName <- getNewName
    clos <- getNewName
    let codef = clos ++ "f"
    let obody = open varName body
    -- variables que escapan (busco todos los free y saco el argumento de la funcion)
    let nenv = (filter (\x -> not (x == varName)) (getFree obody))
    irtt <- closureConvert obody
    let irtt' = foldl (makeLet nenv clos) irtt nenv
    let decl = IrFun codef (tyToirty fty) [(clos, IrClo), (varName, tyToirty ty)] irtt'
    tell [decl]
    return (MkClosure codef (map (\x -> IrVar x) nenv)) -- Los nombres de nenv pasan a ser nombres de Ir simplemente.
 

makeLet nenv cname y x = case elemIndex x nenv of
        Nothing -> error "Error de apertura de Variables"
        -- el tipo debe corresponder con el de la variable, IrInt no esta bien.
        Just n -> IrLet x IrInt (IrAccess (IrVar cname) IrInt (n + 1)) y
   
 

getNewName :: StateT Int (Writer [IrDecl]) Name
getNewName = do
    irname <- get
    put (irname + 1)
    return (show irname)