import Dijkstra.OrderedMonad

namespace Dijkstra

variable {m w} [Monad m] [Monad w]

class MonadMorphism (lift : ∀ {a}, m a → w a) where
  natural : ∀ (f : a → b) {ma : m a}, lift (f <$> ma) = f <$> (lift ma)
  pure : lift (pure a) = pure a
  bind : lift (bind ma f) = bind (lift ma) (lift ∘ f)

class MonadTrans (T : (Type _ → Type _) → (Type _ → Type _)) where
  monad : ∀ [Monad M], Monad (T M)
  lift : ∀ {M} [Monad M] {α}, M α → T M α

class LawfulMonadTrans (T) extends MonadTrans T where
  lift_is_monadMorphism : ∀ {M} [Monad M] [LawfulMonad M],
    MonadMorphism (@lift M _)

class OrderedMonadTrans (T) extends MonadTrans T where
  le : ∀ {m} [OrderedMonad m] {α}, T m α → T m α → Prop

class LawfulOrderedMonadTrans (T) [OrderedMonadTrans T] extends LawfulMonadTrans T where
  lift_mono : ∀ [OrderedMonad M] [LawfulOrderedMonad M] {m1 m2 : M α},
    m1 ≤ m2 → OrderedMonadTrans.le (MonadTrans.lift (T := T) m1) (MonadTrans.lift m2)


namespace StateT

instance : OrderedMonadTrans (StateT σ) where
  monad := inferInstance
  lift := liftM
  le m1 m2 := ∀ s, m1 s ≤ m2 s

instance : LawfulOrderedMonadTrans (StateT σ) where
  lift_is_monadMorphism := {
    natural := by
      intros
      simp [MonadTrans.lift, liftM, monadLift, MonadLift.monadLift, StateT.lift,
            ← LawfulMonad.bind_pure_comp, Functor.map, StateT.map]
  , pure := by
      intros; simp [MonadTrans.lift, pure, liftM, pure, monadLift, MonadLift.monadLift, StateT.lift, StateT.pure]
  , bind := by
      intros; simp [MonadTrans.lift, bind, liftM, bind, monadLift, MonadLift.monadLift, StateT.lift, StateT.bind]
  }
  lift_mono := by
    intros; simp [MonadTrans.lift, liftM, monadLift, MonadLift.monadLift, StateT.lift, LE.le, OrderedMonad.le, OrderedMonadTrans.le]
    intro s; apply LawfulOrderedMonad.bind_mono
    . assumption
    . simp [LawfulOrderedMonad.le_refl]

end StateT

namespace ExceptT

instance {ε : Type u} : OrderedMonadTrans (ExceptT ε) where
  monad := inferInstance
  lift := liftM
  le {m _ α} (m1 m2 : m (Except ε α)) := m1 ≤ m2

instance {ε : Type u} : LawfulOrderedMonadTrans (ExceptT ε) where
  lift_is_monadMorphism := {
    natural := by
      intros
      simp [MonadTrans.lift, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.map,
            ← LawfulMonad.bind_pure_comp, Functor.map]
  , pure := by
      intros; simp [MonadTrans.lift, pure, liftM, pure, monadLift, MonadLift.monadLift]
  , bind := by
      intros
      simp [MonadTrans.lift, bind, ExceptT.bindCont, liftM, ExceptT.bind, monadLift, MonadLift.monadLift,
        ExceptT.lift, ExceptT.mk, Except.ok, ← LawfulMonad.bind_pure_comp]
  }
  lift_mono := by
    intros; simp [MonadTrans.lift, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ← LawfulMonad.bind_pure_comp, LE.le, OrderedMonad.le, OrderedMonadTrans.le]
    apply LawfulOrderedMonad.bind_mono
    . assumption
    . simp [LawfulOrderedMonad.le_refl]

end ExceptT