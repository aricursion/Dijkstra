import Dijkstra.OrderedMonad

namespace Dijkstra.SM

inductive SMType (M : Type → Type) : Type → Type 2
| ty (A : Type) : SMType M (M A)
| prod          : SMType M f → SMType M g → SMType M (f × g)
| dep {A : Type} {t : A → Type}
    : (f : (a : A) → SMType M (t a)) → SMType M ((a : A) → t a)
| arr : SMType M dom → SMType M cod → SMType M (dom → cod)

inductive SMTerm (M : Type → Type) [Monad M] : SMType M τ → τ → Type 2
| ret (a : A) : SMTerm M (.ty A) (pure a)
| bind (ma f) : SMTerm M (.ty A) (bind ma f)
| prod (a : A) (b : B) : SMTerm M (.prod f g) (a,b)
| proj₁ {A B : Type} (mab : A × B) : SMTerm M (.ty A) (pure mab.1)
| proj₂ {A B : Type} (mab : A × B) : SMTerm M (.ty B) (pure mab.2)
| lam (f) : SMTerm M (.arr A B) f
| dlam (f) : SMTerm M (.dep F) f

structure SMTrans (M : Type → Type) [Monad M] where
  monad : Type → Type
  monad_sm : ∀ X, SMType M (monad X)
  pure (a : A) : monad A
  pure_sm : SMTerm M (.ty (monad A)) (pure a)

open SMType

def SMType.StateT (A : Type) : SMType M (StateT σ M A) := (dep fun _ => ty _)

def SMType.ReaderT (A : Type) : SMType M (ReaderT I M A) := (dep fun _ => ty _)

def SMType.ExceptT (A : Type) : SMType M (ExceptT O M A) := (ty _)
