module Optimize where

import Common 
import MonadOpt
import Control.Monad
import Lang
import Subst
import Subst
import Eval (semOp)
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4, failPosFD4 )

optimize :: Decl TTerm -> Decl TTerm
optimize (Decl n ty t) = Decl n ty (fst (runChanges (optimize' t) (StateOpt 0 [])))

optimize' :: MonadOptimization m => TTerm -> m TTerm
optimize' t = do t1 <- total
                 op <- return t
                 op <- visit constantFolding op
                 op <- visit deadCodeElimination op
                 op <- visit inlineExpansion op
                 t2 <- total
                 if (t1 == t2) 
                 then return op
                 else optimize' op
   


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

libres :: Name -> Tm info Var -> Int -> info -> Name -> Tm info Var
libres name def i p n = if n == name then def else V p (Free n)

bounds :: Int -> info -> Int -> Tm info Var
bounds i p n = V p (Bound n)

inlineExpansion :: MonadOptimization m => TTerm -> m TTerm
inlineExpansion (Let inf name ty def z) = do add 1
                                             return (subst def z)
inlineExpansion t = return t


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
visit f (Lam inf sname ty b) = do name <- freshenM sname
                                  b' <- visit f (open name b)
                                  f (Lam inf name ty (close name b'))
visit f (Fix inf sname1 ty sname2 ty2 b) = do name1 <- freshenM sname1
                                              name2 <- freshenM sname2
                                              b' <- visit f (open2 name1 name2 b)
                                              f (Fix inf name1 ty name2 ty2 (close2 name1 name2 b'))
visit f (Let inf sname ty var b) = do name <- freshenM sname
                                      v' <- visit f var
                                      b' <- visit f (open name b)
                                      f (Let inf name ty v' (close name b'))

freshenM :: MonadOptimization m => Name -> m Name
freshenM name = do env <- getNEnv
                   let sname = freshen env name
                   update sname
                   return sname 

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..] 
               in head (filter (`notElem` ns) cands)


-- Como los lams que se aplicaban fueron reemplazados por lets, tenemos que ver en los lets si sustituimos o no. 
-- Los fix son otra historia.