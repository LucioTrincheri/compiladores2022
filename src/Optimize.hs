module Optimize where

import Common 
import MonadOpt 
import Lang
import Subst
import Subst
import Eval (semOp)
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4, failPosFD4 )

optimize :: Decl TTerm -> Decl TTerm
optimize (Decl n ty t) = Decl n ty (fst (runChanges (optimize' t) 0))

optimize' :: MonadOptimization m => TTerm -> m TTerm
optimize' t = do t1 <- total
                 op1 <- visit constantFolding t
                 op2 <- visit deadCodeElimination op1
                 t2 <- total
                 if (t1 == t2) 
                 then return op2
                 else optimize' op2
   


constantFolding :: MonadOptimization m => TTerm -> m TTerm
constantFolding (IfZ inf (Const _ (CNat 0)) true false) = do add 1
                                                             constantFolding true
constantFolding (IfZ inf (Const _ (CNat _)) true false) = do add 1
                                                             constantFolding false
constantFolding (BinaryOp inf op (Const infs (CNat nl)) (Const _ (CNat nr))) = do add 1
                                                                                  return (Const inf (CNat (semOp op nl nr)))
constantFolding (Let inf name ty var@(Const _ _) sc) = do add 1
                                                          constantFolding (subst var sc)
constantFolding t = return t

deadCodeElimination :: MonadOptimization m => TTerm -> m TTerm
deadCodeElimination (App inf lm@(Lam _ name ty body) r) = do add 1
                                                             deadCodeElimination (Let inf name ty r body) -- Podria ser return
deadCodeElimination lt@(Let inf name ty var (Sc1 z)) = do let oz = (betterOpen name (Sc1 z))
                                                          if (countFree z == countFree oz)
                                                          then do add 1
                                                                  return oz
                                                          else return lt
deadCodeElimination t = return t

visit :: MonadOptimization m => (TTerm -> m TTerm) -> TTerm -> m TTerm
visit f t@(V _ var) = f t
visit f t@(Const _ (CNat n)) = f t
visit f (App inf l r) = do l' <- visit f l
                           r' <- visit f r
                           f (App inf l' r')
visit f (Print inf s n) = do n' <- visit f n
                             f (Print inf s n')
visit f (IfZ inf cond true false) = do cond' <- visit f cond
                                       true' <- visit f true
                                       false' <- visit f false
                                       f (IfZ inf cond' true' false')
visit f (BinaryOp inf op l r) = do l' <- visit f l
                                   r' <- visit f r
                                   f (BinaryOp inf op l' r')
visit f (Lam inf name ty (Sc1 b)) = do b' <- visit f b
                                       f (Lam inf name ty (Sc1 b'))
visit f (Fix inf name ty name2 ty2 (Sc2 b)) = do b' <- visit f b
                                                 f (Fix inf name ty name2 ty2 (Sc2 b'))
visit f (Let inf name ty var (Sc1 b)) = do b' <- visit f b
                                           f (Let inf name ty var (Sc1 b'))

-- Agregar entorno de nombres a la monada y sus funciones para que podamos abrir con nombres frescos en cada binder (para no tener variables que escapan).
-- Como los lams que se aplicaban fueron reemplazados por lets, tenemos que ver en los lets si sustituimos o no. 
-- Los fix son otra historia.