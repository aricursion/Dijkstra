import Dijkstra.OrderedMonad

namespace Dijkstra

/-! Dijkstra Monad -/
class DijkstraMonad [OrderedMonad W] (D : ∀ A, W A → Type) where
  ret : (a : A) → D A (pure a)
  bind : D A w₁ → ((x : A) → D B (w₂ x)) → D B (w₁ >>= w₂)

open DijkstraMonad

variable (W) [OrderedMonad W] [LawfulOrderedMonad W]

class LawfulDijkstraMonad (D : ∀ A, W A → Type) extends DijkstraMonad D where
  bind_ret {m : D A w} : bind m ret = cast (by simp) m
  bind_of_ret : bind (ret a) f = cast (by simp) (f a)
  bind_assoc : bind (bind m f) g = cast (by simp) (bind m (λx => bind (f x) g))

namespace DijkstraMonad

def ofEffObs [Monad M] [LawfulMonad M]
  (obs : ∀ {A}, M A → W A)
  (obs_pure : ∀ {A} {a : A},
    obs (return a) = return a)
  (obs_bind : ∀ {A B} {m : M A} {f : A → M B},
    obs (m >>= f) = (obs m) >>= (fun a => obs (f a)))
  : LawfulDijkstraMonad (W := W) (λ A w => { m : M A // w ≤ obs m }) where
  ret a :=
    ⟨return a, by rw [obs_pure]; apply LawfulOrderedMonad.le_refl⟩
  bind
  | ⟨m,pf⟩, f =>
    ⟨m >>= (fun a => f a), by
      rw [obs_bind]
      apply LawfulOrderedMonad.bind_mono
      . exact pf
      . intro a; apply (f a).property⟩
  bind_ret := by
    intros; simp; sorry
  bind_of_ret := by
    intros; simp; sorry
  bind_assoc := by
    intros; simp; sorry

def toMonad (D : ∀ A, W A → Type) [DijkstraMonad D]
  : Monad (fun A => Σ w, D A w) where
  pure a := ⟨return a, ret a⟩
  bind m f := ⟨m.1 >>= (fun a => (f a).1), bind m.2 (fun a => (f a).2)⟩
