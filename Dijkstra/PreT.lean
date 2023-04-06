import Dijkstra.MonadTrans

namespace Dijkstra

/- we need some way to allow computation under some
preconditions for safety. I *think* we can characterize
"safety" as a monad transformer that works nicely with
the other monad transformer stuff
-/
structure PreT (m : Type u → Type v) (α : Type u) : Type (max u v) where
  pre : Prop
  run : pre → m α

namespace PrePostT

instance [Monad m] : Pure (PreT m) where
  pure a := {
    pre := True
  , run := λ _ => pure a }

instance [Monad m] : Bind (PreT m) where
  bind ma f :=
    match ma with
    | {pre,run} =>
      { pre   := pre ∧ ∀ a, (f a).pre
      , run   := λ ⟨hp, hf⟩ => do
        let a ← run hp
        let b ← (f a).run (hf a)
        pure b }

instance [Monad m] : Monad (PreT m) where

instance [Monad m] : MonadLift m (PreT m) where
  monadLift ma := {
    pre := True
  , run := λ _ => ma
  }

instance : MonadTrans PreT where
  monad := inferInstance
  lift := monadLift

-- TODO: see if we can prove the lawfulness conditions
instance : LawfulMonadTrans PreT where
  lift_is_monadMorphism := {
    natural := by
      intros
      simp [Functor.map, MonadTrans.lift, monadLift, MonadLift.monadLift, bind, pure]
      simp [← LawfulMonad.bind_pure_comp]
      sorry
  , bind := by
      intros
      sorry
  , pure := by
      intros
      sorry
  }
