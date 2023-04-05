import Dijkstra.OrderedMonad

namespace Dijkstra

/-! Dijkstra Monad -/
class DMonad [Monad W] (D : ∀ (A : Type u), W A → Type v) where
  ret : (a : A) → D A (pure a)
  bind : D A w₁ → ((x : A) → D B (w₂ x)) → D B (w₁ >>= w₂)

open DMonad

variable {W} [OrderedMonad W] [LawfulMonad W]

class LawfulDMonad (D : ∀ A, W A → Type) extends DMonad D where
  bind_ret {m : D A w} : bind m ret = cast (by simp) m
  bind_of_ret : bind (ret a) f = cast (by simp) (f a)
  bind_assoc : bind (bind m f) g = cast (by simp) (bind m (λx => bind (f x) g))

class Weaken (D : ∀ A, W A → Type) where
  weaken (ma : D A w) (w' : W A) (h : w ≤ w') : D A w'

class LawfulOrderedDMonad (D : ∀ A, W A → Type) extends LawfulDMonad D, Weaken D

namespace DMonad

@[simp, reducible] def verify {w : W A} [DMonad D] (ma : D A w) (w' : W A) := w ≤ w'

@[simp, reducible] def ofEffObs [Monad M] (obs : ∀ {A}, M A → W A) := λ A w => { m : M A // obs m ≤ w }

instance instOfEffObs [Monad M] [LawfulMonad M] [LawfulOrderedMonad W]
  (obs_pure : ∀ {A} {a : A},
    obs (return a) = return a)
  (obs_bind : ∀ {A B} {m : M A} {f : A → M B},
    obs (m >>= f) = (obs m) >>= (fun a => obs (f a)))
  : LawfulOrderedDMonad (W := W) (ofEffObs obs) where
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
  weaken := by
    intro A w d w' h
    match d with
    | ⟨m,hm⟩ =>
      exact ⟨m, LawfulOrderedMonad.le_trans hm h⟩

def toMonad (D : ∀ A, W A → Type) [DMonad D]
  : Monad (fun A => Σ w, D A w) where
  pure a := ⟨return a, ret a⟩
  bind m f := ⟨m.1 >>= (fun a => (f a).1), bind m.2 (fun a => (f a).2)⟩



