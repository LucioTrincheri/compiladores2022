module Optimize where

import Common 
import Lang
import Subst
import Eval (semOp)
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4, failPosFD4 )

optimize :: Decl TTerm -> Decl TTerm
optimize (Decl n ty t) = let t' = constantFolding t
                         in if (ttermSize t) == (ttermSize t')
                            then (Decl n ty t')
                            else optimize (Decl n ty t')

-- const = CNat Int

-- recorrer el arbol y buscar las operaciones que trivialemnte se puedan reducir
-- Hacer monada simple que lleve un booleano que represente si se realizo un cambio.
-- Luego ver de juntar las funciones en una generica que ya sea optimizar los hijos y que se le pasela funcion sobre los que faltan.
constantFolding :: TTerm -> TTerm
constantFolding t@(V _ var) = t
constantFolding t@(Const _ (CNat n)) = t
constantFolding (App inf l r) = (App inf (constantFolding l) (constantFolding r))
constantFolding (Print inf s n) = (Print inf s (constantFolding n))
constantFolding (IfZ inf (Const _ (CNat 0)) true false) = constantFolding true
constantFolding (IfZ inf (Const _ (CNat _)) true false) = constantFolding false
constantFolding (IfZ inf cond true false) = (IfZ inf (constantFolding cond) (constantFolding true) (constantFolding false))
constantFolding (BinaryOp inf op (Const inf (CNat nl)) (Const _ (CNat nr))) = (Const inf (CNat (semOp op nl nr)))
constantFolding (BinaryOp inf op l r) =  (BinaryOp inf op (constantFolding l) (constantFolding r))
constantFolding (Lam inf name ty (Sc1 b)) = (Lam inf name ty (Sc1 (constantFolding b)))
constantFolding (Fix inf name ty name2 ty2 (Sc2 b)) = (Fix inf name ty name2 ty2 (Sc2 (constantFolding b)))
constantFolding (Let inf name ty var@(Const _ _) sc) = constantFolding (subst var sc)
-- este caso seria para constant propagation puede que luego de hacer lo que esta arriba comentado se pueda separar para que quede mas claro
constantFolding (Let inf name ty var (Sc1 b)) = (Let inf name ty var (Sc1 (constantFolding b)))

-- esta manera de de comprobar el punto fijo esta feo, usar la del comentario
ttermSize :: TTerm -> Int
ttermSize (V _ var) = 1
ttermSize (Const _ _) = 1
ttermSize (App inf l r) = 1 + ttermSize l + ttermSize r
ttermSize (Print inf s n) = 1 + ttermSize n
ttermSize (IfZ inf cond true false) = 1 + ttermSize cond + ttermSize true + ttermSize false
ttermSize (BinaryOp infS op l r) = 1 + ttermSize l + ttermSize r
ttermSize (Lam inf name ty (Sc1 b)) = 1 + ttermSize b
ttermSize (Fix inf name ty name2 ty2 (Sc2 b)) = 1 + ttermSize b
ttermSize (Let inf name ty var (Sc1 b)) = 1 + ttermSize b + ttermSize var