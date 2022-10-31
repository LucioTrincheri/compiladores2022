module Closureconvert where

import IR
import Subst

tyToirty :: Ty -> IrTy
tyToirty NatTy = IrInt
tyToirty FunTy _ _ = IrClo

runCC :: [Decl TTerm] -> [IrDecl]
runCC t = runState (execWriter closureConvert t []) 0

closureConvert :: TTerm -> [Name] -> StateT Int (Writer [IrDecl]) Ir
    -- si no es 0 no referencia al lam actual
closureConvert (V p (Bound i)) nenv = _  i
closureConvert (V (i,ty) (Free x)) nenv = do
    case elemIndex x nenv of
        Nothing -> _ -- morir junto con bound
        Just n -> IrAccess (IrVar x) (tyToirty ty) (n+1)
closureConvert (V p (Global x)) nenv = 0
closureConvert tt@(Const _ _) nenv = IrConst tt
closureConvert (IfZ p c t f) nenv = do 
    irc <- closureConvert c
    irt <- closureConvert t
    irf <- closureConvert f
    return IrIfZ irc irt irf
closureConvert (Print p str t) nenv = do
    irt <- closureConvert t
    IrPrint str irt
closureConvert (BinaryOp p op t u) nenv = do
    irt <- closureConvert t
    iru <- closureConvert u
    return IrBinaryOp op irt iru
closureConvert (Let p v vty def body) nenv =
    irdef <- closureConvert def
    name <- get
    put (name + 1)
    let obody = open (v ++ show name) body
    cbody <- closureConvert obody
    return IrLet (v ++ show name) (tyToirty ty) irdef cbody
closureConvert (App p l r)   = 
closureConvert (Fix p f fty x xty (Sc2 t)) = (closureConvert (n+2) t)
closureConvert tt@(Lam (pos, fty) name ty body) _ = do
    irname <- get
    put (irname + 1)
    mkname <- get
    put (mkname + 1)
    let nenv = getFree tt
    let obody = open (show irname) body 
    --d <- generarDeclMagicmente obody irname nenv
    irtt <- closureConvert obody nenv
    -- crear un let para bindindear cada nombre libre de nenv con su ir correspondiente.
    -- para obtener los ir 
    let decl = IrFun mkname (tyToirty fty) [(mkname, IrClo),(name, tyToirty ty)] 
    tell [decl]
    return (MkClosure mkname nenv) -- Los nombres de nenv pasan a ser nombres de Ir simplemente.

generarDeclMagicmente :: TTerm -> Name -> [Name] -> IrDecl
generarDeclMagicmente tt name env = do 
    irtt <- closureConvert tt env
    return IrCall irtt 

delc tterm -> closureConvert tterm -> ir -> decl ir 
                                   -> [decl ir]

let suma : Nat -> (Nat -> Nat) =
    fun (x:Nat) ->
    fun (y:Nat) -> x + y

let suma : Nat -> (Nat -> Nat) =
    (fun (x:Nat) -> 
    (fun (y:Nat) -> e0 + y)[x])[]

let _g0 (y:Nat) : Nat = e0 + y
let _g1 (x:Nat) : Nat -> Nat = _g0[x]
let suma : Nat -> (Nat -> Nat) = _g1[]