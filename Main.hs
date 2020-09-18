module Main where

import Control.Monad
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Control.Monad.State.Strict
import Data.IORef
import qualified Data.Map.Strict as M
import Data.STRef
import System.IO.Unsafe

type Varname = String

type Level = Int

-- level, gensymは手抜きでグローバル変数
-- 真面目にやるならStateなりSTなり使って
currentLevel :: IORef Int
currentLevel = unsafePerformIO do newIORef 1

enterLevel :: IO ()
enterLevel = do
  modifyIORef' currentLevel (+ 1)

leaveLevel :: IO ()
leaveLevel = do
  modifyIORef' currentLevel (\x -> x - 1)

genSymCount :: IORef Int
genSymCount = unsafePerformIO do newIORef 0

genSym :: IO String
genSym = do
  x <- readIORef genSymCount
  modifyIORef' genSymCount (+ 1)
  pure do show x

-- Mapのkが子、vが親
newtype UF key = UF (M.Map key key)
  deriving (Show)

type UnionFindT key m a = StateT (UF key) m a

runUFMT :: UnionFindT key m a -> m (a, UF key)
runUFMT = flip runStateT (UF M.empty)

-- 本来なら型が確定している方を親にする処理がいりそう(今は単純型付きラムダ計算的なやつなので不要)
union :: (Monad m, Eq key, Ord key) => key -> key -> UnionFindT key m ()
union l r = do
  (UF map) <- get
  let lp = M.lookup l map
      rp = M.lookup r map
      newmap = case (lp, rp) of
        (Nothing, Nothing) -> UF do M.insert l l . M.insert r l $ map
        (Just lp', Nothing) -> UF do M.insert r lp' map
        (Nothing, Just rp') -> UF do M.insert l rp' map
        (Just lp', Just rp') -> UF do M.insert lp' rp' map
   in put newmap

find :: (Monad m, Eq key, Ord key) => key -> UnionFindT key m key
find k = do
  (UF map) <- get
  let getparent child =
        let par = M.lookup child map
         in case par of
              Just p -> p
              Nothing -> child
  let fix f x = if f x == x then x else fix f (f x)
  let root = fix getparent k
  put $ UF $ M.insert k root map -- 為されないtodo: 経路上のpath compression
  pure root

data Exp
  = Var Varname
  | App Exp Exp
  | Lam Varname Exp
  | Let Varname Exp Exp
  deriving (Show)

type Qname = String

data TV = TV String Level
  deriving (Show)

data Typ
  = TVar TV
  | QVar Qname
  | TArrow Typ Typ
  deriving (Show)

type Env = M.Map Varname Typ

instance Show (IORef TV) where
  show ref = unsafePerformIO do show <$> readIORef ref

type TypecheckM a = UnionFindT IO a

occurs :: IORef TV -> Typ -> TypecheckM ()
occurs tvref =
  \case
    TVar tvref' -> do
      when
        (tvref == tvref')
        do error "occurs check"
      tvr' <- readIORef tvref'
      case tvr' of
        Unbound s l' -> do
          tvr <- readIORef tvref
          min_level <- case tvr of
            Unbound _ l -> pure do min l l'
            _ -> pure l'
          writeIORef tvref' do Unbound s min_level
        Link ty -> occurs tvref ty
    TArrow tl tr -> do
      occurs tvref tl
      occurs tvref tr
    _ -> pure ()

unify :: Typ -> Typ -> IO ()
unify (TVar tv) t' = do
  tv' <- readIORef tv
  case tv' of
    Unbound _ lvl -> do
      occurs tv t'
      writeIORef tv (Link t')
    Link t1 -> do
      unify t1 t'
unify t' t@(TVar tv) = unify t t'
unify (TArrow l1 l2) (TArrow r1 r2) = do
  unify l1 r1
  unify l2 r2

-- Typ内のQVarをgensymしたTVarにする
inst :: Typ -> TypecheckM Typ
inst ty = fst <$> go M.empty ty
  where
    go :: M.Map String Typ -> Typ -> IO (Typ, M.Map String Typ)
    go subst (QVar name) = case M.lookup name subst of
      Just x -> pure (x, subst)
      Nothing -> do
        tv <- newvar
        pure (tv, M.insert name tv subst)
    go subst (TVar ty) = do
      link <- readIORef ty
      case link of
        Link t -> go subst t
        Unbound s lvl -> pure (TVar ty, subst)
    go subst (TArrow l r) = do
      (lt, subst) <- go subst l
      (rt, subst) <- go subst r
      pure (TArrow lt rt, subst)

newvar :: IO Typ
newvar = do
  s <- genSym
  lvl <- readIORef currentLevel
  tv <- newIORef do Unbound s lvl
  pure do TVar tv

gen :: Typ -> TypecheckM Typ
gen (TVar tv) = do
  tv' <- readIORef tv
  current <- readIORef currentLevel
  case tv' of
    Unbound s lvl -> if lvl > current then pure do QVar s else pure do TVar tv
    Link t -> gen t
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

-- これがないと TArrow (TVar Link (TVar Unbound "6" 1)) (TVar Unbound "6" 1) のようになる
-- fun x -> let f = fun a -> a in f x のケース参照
pathCompression :: Typ -> IO Typ
pathCompression t@(TVar tvref) = do
  tv <- readIORef tvref
  case tv of
    Link t' -> pathCompression t'
    _ -> pure t
pathCompression (TArrow l r) = TArrow <$> pathCompression l <*> pathCompression r
pathCompression t = pure t

main :: IO ()
main = do
  r <- runUFMT $ do
    union 2 1
    union 3 4
    find 4
  print r
  let e0 =
        Lam "x" (Var "x")
  print =<< pathCompression =<< typeof (M.empty) e0

  -- fun x -> let f = fun a -> a in f x
  let e1 =
        Lam
          "x"
          ( Let
              "f"
              (Lam "a" (Var "a"))
              (App (Var "f") (Var "x"))
          )
  print =<< pathCompression =<< typeof (M.empty) e1

  -- fun x -> let y = x in y
  let e2 =
        Lam
          "x"
          ( Let
              "y"
              (Var "x")
              (Var "y")
          )
  print =<< pathCompression =<< typeof (M.empty) e2
