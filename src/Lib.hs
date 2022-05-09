module Lib where
import           Control.Exception              ( TypeError(TypeError)
                                                , throw
                                                )
import           Control.Monad                  ( unless )
import           GHC.Generics                   ( Generic1(to1) )
import           GHC.RTS.Flags                  ( DebugFlags(interpreter) )


someFunc :: IO ()
someFunc = pure ()

type DeBruijn = Int

-- | A term for which the type can by synthesized
data TermS = Annotated TermC TermC
           | Star Int
           | Pi TermC TermC
           | Bound DeBruijn
           | Free Name
           | TermS :@: TermC -- application
           -- Natural Number
           | Nat
           | Zero
           | Succ TermC
           | NatElim TermC TermC TermC TermC
  deriving (Eq, Show)

-- | A term for which its type can be checked
data TermC = Inferrable TermS
           | Lambda TermC
  deriving (Eq, Show)

-- | A variable name
data Name = Global String
          | Local Int
          | Quote Int
  deriving (Eq, Show)

type Type = Value

-- | The interpreter-level value
data Value = VLambda (Value -> Value)
           | VStar Int
           | VPi Value (Value -> Value)
           | VNeutral Neutral
           | VNat
           | VZero
           | VSucc Value

-- | A non-reducable neutral term
data Neutral = NFree Name
             | NApp Neutral Value
             | NNatElim Value Value Value Neutral

vfree :: Name -> Value
vfree = VNeutral . NFree

type Env = [Value]

evalS :: TermS -> Env -> Value
evalS (Annotated t _) env = evalC t env
evalS (Free  x      ) _   = vfree x
evalS (Bound i      ) env = env !! i
evalS (t1 :@: t2    ) env = vapp (evalS t1 env) (evalC t2 env)
evalS (Star n       ) _   = VStar n
evalS (Pi t1 t2     ) env = VPi (evalC t1 env) (\x -> evalC t2 (x : env))
evalS Nat             _   = VNat
evalS Zero            _   = VZero
evalS (Succ k)        env = VSucc (evalC k env)
evalS (NatElim m mz ms k) env =
  let mzVal = evalC mz env
      msVal = evalC ms env
      rec' kval = case kval of
        VZero      -> mzVal
        VSucc    l -> msVal @: l @: rec' l
        VNeutral n -> VNeutral (NNatElim (evalC m env) mzVal msVal n)
        _          -> error "internal: eval natElim"
  in  rec' (evalC k env)

vapp :: Value -> Value -> Value
vapp (VLambda  f) v2 = f v2
vapp (VNeutral n) v2 = VNeutral (NApp n v2)
vapp _            _  = error "internal: vapp"

(@:) :: Value -> Value -> Value
(@:) = vapp

evalC :: TermC -> Env -> Value
evalC (Inferrable t) env = evalS t env
evalC (Lambda     t) env = VLambda (\v -> evalC t (v : env))

type Context = [(Name, Type)]

type Result a = Either String a

throwError :: a -> Either a b
throwError = Left

synthesizeType0 :: Context -> TermS -> Result Type
synthesizeType0 = synthesizeType 0

synthesizeType :: DeBruijn -> Context -> TermS -> Result Type
synthesizeType i c (Annotated e p) = do
  checkType i c p (VStar 0)
  let t = evalC p []
  checkType i c e t
  pure t
synthesizeType i c (Star n  ) = pure (VStar (n + 1))
synthesizeType i c (Pi p1 p2) = do
  checkType i c p1 (VStar 0)
  let t = evalC p2 []
  checkType (i + 1) ((Local i, t) : c) (substC 0 (Free (Local i)) p2) (VStar 0)
  pure (VStar 0)
synthesizeType i c (Free t) = case lookup t c of
  Just t  -> pure t
  Nothing -> throwError "unknown identifier"
synthesizeType i c (e1 :@: e2) = do
  s <- synthesizeType i c e1
  case s of
    VPi t1 t2 -> do
      checkType i c e2 t1
      pure (t2 (evalC e2 []))
    _ -> throwError "illegal application"
synthesizeType i c Nat      = pure VNat
synthesizeType i c Zero     = pure VZero
synthesizeType i c (Succ k) = do
  checkType i c k VNat
  pure VNat
synthesizeType i c (NatElim m mz ms k) = do
  checkType i c m (VPi VNat (const (VStar 0)))
  let mVal = evalC m []
  checkType i c mz (mVal @: VZero)
  checkType i c ms (VPi VNat (\l -> VPi (mVal @: l) (\_ -> mVal @: VSucc l)))
  checkType i c k  VNat
  let kVal = evalC k []
  pure $ mVal `vapp` kVal

checkType :: Int -> Context -> TermC -> Type -> Result ()
checkType i c (Inferrable e) t = do
  t' <- synthesizeType i c e
  unless (quote0 t == quote0 t') (throwError "type mismatch")
checkType i c (Lambda e) (VPi t1 t2) = checkType
  (i + 1)
  ((Local i, t1) : c)
  (substC 0 (Free (Local i)) e)
  (t2 (vfree (Local i)))
checkType _ _ _ _ = throwError "type mismatch"

substS :: DeBruijn -> TermS -> TermS -> TermS
substS i r (Annotated e t) = Annotated (substC i r e) t
substS i r (Bound j      ) = if i == j then r else Bound j
substS i r (Free  t      ) = Free t
substS i r (t1 :@: t2    ) = substS i r t1 :@: substC i r t2
substS i r (Star n       ) = Star n
substS i r (Pi t1 t2     ) = Pi (substC i r t1) (substC (i + 1) r t2)

substC :: DeBruijn -> TermS -> TermC -> TermC
substC i r (Inferrable e) = Inferrable (substS i r e)
substC i r (Lambda     e) = Lambda (substC (i + 1) r e)

quote0 :: Value -> TermC
quote0 = quote 0

quote :: DeBruijn -> Value -> TermC
quote i (VLambda  f) = Lambda (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inferrable (neutralQuote i n)
quote i (VStar    n) = Inferrable (Star n)
quote i (VPi v f) =
  Inferrable (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))
quote i VNat      = Inferrable Nat
quote i VZero     = Inferrable Zero
quote i (VSucc v) = Inferrable (Succ (quote i v))

neutralQuote :: DeBruijn -> Neutral -> TermS
neutralQuote i (NFree t ) = boundfree i t
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v
neutralQuote i (NNatElim m mz ms k) =
  NatElim (quote i m) (quote i mz) (quote i ms) (Inferrable (neutralQuote i k))

boundfree :: DeBruijn -> Name -> TermS
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i t         = Free t

