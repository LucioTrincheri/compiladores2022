module CEK where

import Common 
import Lang
import Subst ( subst2, subst )
import Eval ( semOp )
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4, failPosFD4 )
import PPrint ( ppName, pp )


data Clos = ClosFun CEKEnv Name Ty TTerm | ClosFix CEKEnv Name Ty Name Ty TTerm
-- TODO Preguntar lo de los tipos para search de lam y fix
type CEKEnv = [Val]

data Val = VNat Int
         | VClos Clos

data Fr = CEKTerm CEKEnv TTerm 
        | CEKClos Clos 
        | CEKIfz CEKEnv TTerm TTerm
        | CEKBinaryOpTerm CEKEnv BinaryOp TTerm
        -- Tal vez sea Int o VNat en ves de Val
        | CEKBinaryOpVal Val BinaryOp
        | CEKPrint String
        | CEKLet CEKEnv Name TTerm

type FrStack = [Fr]

search :: MonadFD4 m => TTerm -> CEKEnv -> FrStack -> m Val
search (Print i s t) p k = search t p ((CEKPrint s):k)
search (BinaryOp i b t1 t2) p k = search t1 p ((CEKBinaryOpTerm p b t2):k)
search (App i t1 t2) p k = search t1 p ((CEKTerm p t2):k)
search (IfZ i c t1 t2) p k = search c p ((CEKIfz p t1 t2):k)
search (V i (Bound n)) p k = destroy (p!!n) k
search (V i (Free x)) p k = failPosFD4 (fst i) "Variable libre que no deberia estar aca"
search (V i (Global x)) p k = do 
    xVal <- lookupDecl x
    case xVal of
        Just val -> search val p k
        Nothing -> failPosFD4 (fst i) "Variable indefinida"
search (Const i (CNat n)) p k = destroy (VNat n) k
search (Lam i x t1 (Sc1 t)) p k = destroy (VClos (ClosFun p x t1 t)) k
search (Fix i x1 t1 x2 t2 (Sc2 t)) p k = destroy (VClos (ClosFix p x1 t1 x2 t2 t)) k
search (Let i x _ t (Sc1 t')) p k = search t p ((CEKLet p x t'):k)

destroy :: MonadFD4 m => Val -> FrStack -> m Val
destroy v@(VNat n) ((CEKPrint s):k) = do 
    printFD4 (s ++ (show n))
    destroy v k
destroy v ((CEKBinaryOpTerm p op t):k) = search t p ((CEKBinaryOpVal v op):k)
destroy (VNat n') ((CEKBinaryOpVal (VNat n) op):k) = destroy (VNat (semOp op n n')) k
destroy (VNat 0) ((CEKIfz p t1 t2):k) = search t1 p k
destroy (VNat np) ((CEKIfz p t1 t2):k) = search t2 p k
destroy (VClos c) ((CEKTerm p t):k) = search t p ((CEKClos c):k)
destroy v ((CEKClos (ClosFun p x _ t)):k) = search t (v:p) k
destroy v ((CEKClos (ClosFix p x1 t1 x2 t2 t)):k) = search t (v:((VClos (ClosFix p x1 t1 x2 t2 t)):p)) k --Puede ser que v:f sea f:v
destroy v ((CEKLet p x t):k) = search t (v:p) k

destroy v [] = return v

-- | Evaluador de términos en CEK
evalCEK ::  MonadFD4 m => TTerm -> m TTerm
evalCEK t = do s <- search t [] []
               case s of
                  VNat n -> return (Const (NoPos, NatTy) (CNat n))
                  VClos (ClosFun _ x t1 t) -> return (Lam (NoPos, t1) x t1 (Sc1 t))
                  VClos (ClosFix _ x1 t1 x2 t2 t) -> return (Fix (NoPos, t1) x1 t1 x2 t2 (Sc2 t))
