module Main where

import Control.Monad
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Control.Monad.State.Strict
import Data.IORef
import qualified Data.Map.Strict as M
import Data.Maybe as Maybe
import Data.STRef
import System.IO.Unsafe

type Varname = String

type Level = Int

-- Mapのkが子、vが親
newtype UF key = UF (M.Map key key)
  deriving (Show)

data Exp
  = Var Varname
  | App Exp Exp
  | Lam Varname Exp
  | Let Varname Exp Exp
  deriving (Show)

type Qname = String

data TV = TV String Level
  deriving (Show, Eq)

data Typ
  = TVar TV
  | QVar Qname
  | TArrow Typ Typ
  deriving (Show)

type Env = M.Map Varname Typ

data TypecheckState = TypecheckState
  { levelMap_ :: M.Map String Level,
    uf_ :: UF String,
    genSymCount_ :: Int,
    levelCount_ :: Int
  }

newtype TypecheckM a = TypecheckM
  { impl :: State TypecheckState a
  }
  deriving (Functor, Applicative, Monad, MonadState TypecheckState)

runTypecheckM :: TypecheckM Typ -> Typ
runTypecheckM x =
  let (a, s) = flip runState (TypecheckState (M.empty) (UF M.empty) 0 0) $ impl (pathCompression =<< x)
   in a
  where
    -- 一通り終わった後にTVarをUnionFindの親に書き換える
    pathCompression :: Typ -> TypecheckM Typ
    pathCompression t@(TVar tv) = do
      case tv of
        TV _ _ -> do
          tp' <- findTV tv
          pure . TVar $ tp'
    pathCompression (TArrow l r) = TArrow <$> pathCompression l <*> pathCompression r
    pathCompression t = pure t

-- private
getUF :: TypecheckM (UF String)
getUF = do
  uf <- uf_ <$> get
  pure uf

-- private
putUF :: UF String -> TypecheckM ()
putUF x = do
  s <- get
  put s {uf_ = x}

genSym :: TypecheckM String
genSym = do
  s@(TypecheckState _ _ i _) <- get
  put s {genSymCount_ = i + 1}
  pure $ show i

-- 本来なら型が確定している方を親にする処理がいりそう?(今は単純型付きラムダ計算的なやつなので不要)
union :: String -> String -> TypecheckM ()
union l r = do
  (UF map) <- getUF
  let lp = M.lookup l map
      rp = M.lookup r map
      newmap = case (lp, rp) of
        (Nothing, Nothing) -> UF do M.insert l l . M.insert r l $ map
        (Just lp', Nothing) -> UF do M.insert r lp' map
        (Nothing, Just rp') -> UF do M.insert l rp' map
        (Just lp', Just rp') -> UF do M.insert lp' rp' map
   in putUF newmap

-- private
find :: String -> TypecheckM String
find k = do
  (UF map) <- getUF
  let getparent child =
        let par = M.lookup child map
         in case par of
              Just p -> p
              Nothing -> child
  let fix f x = if f x == x then x else fix f (f x)
  let root = fix getparent k
  putUF $ UF $ M.insert k root map -- 為されないtodo: 経路上のpath compression
  pure root

findTV :: TV -> TypecheckM TV
findTV (TV s l) = do
  sp <- find s
  lp <- getLevel sp
  pure $ TV sp lp

-- private
getLevelMap :: TypecheckM (M.Map String Level)
getLevelMap = do
  x <- levelMap_ <$> get
  pure x

-- private
putLevelMap :: M.Map String Level -> TypecheckM ()
putLevelMap x = do
  s <- get
  put $ s {levelMap_ = x}

-- private?
getLevel :: String -> TypecheckM Level
getLevel s = do
  m <- getLevelMap
  pure $ Maybe.fromJust $ M.lookup s m

updateLevelMap :: String -> Level -> TypecheckM ()
updateLevelMap s l = do
  map <- getLevelMap
  putLevelMap $ M.insert s l map

enterLevel :: TypecheckM ()
enterLevel = do
  s@(TypecheckState _ _ _ l) <- get
  put $ s {levelCount_ = l + 1}
  pure ()

leaveLevel :: TypecheckM ()
leaveLevel = do
  s@(TypecheckState _ _ _ l) <- get
  put $ s {levelCount_ = l -1}
  pure ()

currentLevel :: TypecheckM Int
currentLevel = do 
  s@(TypecheckState _ _ _ l) <- get
  pure l


-- typecheckrefで言うUnboundの場合にTrue
-- UnionFindでparentが同じ場合Unbound
-- 備考:他の型がこのTVにLinkされていることはありうる
isUnbound :: TV -> TypecheckM Bool
isUnbound tv = do
  (== tv) <$> findTV tv

getTVLevel :: TV -> Level
getTVLevel (TV _ l) = l

setLevel :: TV -> Level -> TV
setLevel (TV s l) l' = TV s l'

occurs :: TV -> Typ -> TypecheckM ()
occurs tv@(TV s _) =
  \case
    TVar tv'@(TV s' l') -> do
      sp <- find s
      sp' <- find s'
      when
        (sp == sp')
        do error "occurs check"
      tvisUnbound' <- isUnbound tv'
      if tvisUnbound'
        then do
          tvisUnbound <- isUnbound tv
          let min_level =
                if tvisUnbound
                  then min (getTVLevel tv) (getTVLevel tv')
                  else getTVLevel tv'
          updateLevelMap s min_level
          pure ()
        else do
          tvp' <- findTV tv'
          occurs tv (TVar $ tvp')
    TArrow tl tr -> do
      occurs tv tl
      occurs tv tr
    _ -> pure ()

unify :: Typ -> Typ -> TypecheckM ()
unify (TVar tv) t' = do
  -- どちらにしろfindしてoccursしてunionでいい?
  tvisUnbound <- isUnbound tv
  let TV s r = tv
  if tvisUnbound
    then do
      occurs tv t'
      let TVar (TV s' _) = t'
      union s s'
    else do
      tvp <- findTV tv
      unify (TVar tvp) t'
unify t' t@(TVar tv) = unify t t'
unify (TArrow l1 l2) (TArrow r1 r2) = do
  unify l1 r1
  unify l2 r2

-- Typ内のQVarをgensymしたTVarにする
inst :: Typ -> TypecheckM Typ
inst ty = fst <$> go M.empty ty
  where
    go :: M.Map String Typ -> Typ -> TypecheckM (Typ, M.Map String Typ)
    go subst (QVar name) = case M.lookup name subst of
      Just x -> pure (x, subst)
      Nothing -> do
        tv <- newvar
        pure (tv, M.insert name tv subst)
    go subst (TVar tv) = do
      typ <- findTV tv
      pure (TVar typ, subst)
    go subst (TArrow l r) = do
      (lt, subst) <- go subst l
      (rt, subst) <- go subst r
      pure (TArrow lt rt, subst)

newvar :: TypecheckM Typ
newvar = do
  s <- genSym
  lvl <- currentLevel
  m <- getLevelMap
  putLevelMap $ M.insert s lvl m
  pure do TVar do { TV s lvl }

gen :: Typ -> TypecheckM Typ
gen (TVar tv) = do
  current <- currentLevel
  tvisUnbound <- isUnbound tv
  if tvisUnbound
    then do
      let (TV s lvl) = tv
      if lvl > current
        then pure do QVar s
        else pure do TVar tv
    else do
      tvp <- findTV tv
      gen do TVar tvp
gen (TArrow l r) = do
  l' <- gen l
  r' <- gen r
  pure do TArrow l' r'
gen t = pure t

typeof :: Env -> Exp -> TypecheckM Typ
typeof env (Var x) = inst (env M.! x)
typeof env (Lam x e) = do
  ty_x <- newvar
  ty_e <- typeof (M.insert x ty_x env) e
  pure do TArrow ty_x ty_e
typeof env (App f x) = do
  ft <- typeof env f
  xt <- typeof env x
  rt <- newvar
  unify ft (TArrow xt rt)
  pure rt
typeof env (Let x e e2) = do
  enterLevel
  et <- typeof env e
  leaveLevel
  et' <- gen et
  e2t <- typeof (M.insert x et' env) e2
  typeof (M.insert x et' env) e2

main :: IO ()
main = do
  let e0 =
        Lam "x" (Var "x")
  print $ runTypecheckM $ typeof (M.empty) e0

  -- fun x -> let f = fun a -> a in f x
  let e1 =
        Lam
          "x"
          ( Let
              "f"
              (Lam "a" (Var "a"))
              (App (Var "f") (Var "x"))
          )
  print $ runTypecheckM $ typeof (M.empty) e1

  -- fun x -> let y = x in y
  let e2 =
        Lam
          "x"
          ( Let
              "y"
              (Var "x")
              (Var "y")
          )
  print $ runTypecheckM $ typeof (M.empty) e2
