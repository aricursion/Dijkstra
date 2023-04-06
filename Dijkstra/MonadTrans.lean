import Dijkstra.OrderedMonad
namespace Dijkstra

class MonadTrans (T : (Type _ → Type _) → (Type _ → Type _)) where
  pure : [Monad M] → α → T M α
  bind : [Monad M] → T M α → (α → T M β) → T M β
  lift : [Monad M] → M α → T M α

instance [Monad m] [MonadTrans T] : Monad (T m) where
  pure := MonadTrans.pure
  bind := MonadTrans.bind

class LawfulMonadTrans (T) [MonadTrans T] where
  lift_pure : [Monad M] → [LawfulMonad M] → ∀ {a : α},
    MonadTrans.lift (T := T) (M := M) (pure a) = pure a
  lift_bind : [Monad M] → [LawfulMonad M] → ∀ {m : M α} {k : α → M β},
    MonadTrans.lift (T := T) (M := M) (m >>= k) = (MonadTrans.lift m) >>= (fun x => (MonadTrans.lift <| k x) >>= fun kx => pure kx)

class OrderedMonadTrans (T) extends MonadTrans T where
  le : [OrderedMonad m] → ∀ {α}, T m α → T m α → Prop

instance [OrderedMonad m] [OrderedMonadTrans T] : OrderedMonad (T m) where
  le := OrderedMonadTrans.le

class LawfulOrderedMonadTrans (T) [OrderedMonadTrans T] extends LawfulMonadTrans T where
  lift_mono : [OrderedMonad M] → [LawfulOrderedMonad M] → ∀ {m1 m2 : M α}, m1 ≤ m2 → MonadTrans.lift (T := T) m1 ≤ MonadTrans.lift m2

instance : OrderedMonadTrans (StateT σ) where
  pure := pure
  bind := bind
  lift := liftM
  le m1 m2 := ∀ s, m1 s ≤ m2 s

instance : LawfulOrderedMonadTrans (StateT σ) where
  lift_pure := by intros; simp [MonadTrans.lift, MonadTrans.pure, liftM, pure, monadLift, MonadLift.monadLift, StateT.lift, StateT.pure]
  lift_bind := by intros; simp [MonadTrans.lift, MonadTrans.bind, liftM, bind, monadLift, MonadLift.monadLift, StateT.lift, StateT.bind]; rfl
  lift_mono := by intros; simp [MonadTrans.lift, liftM, monadLift, MonadLift.monadLift, StateT.lift, LE.le, OrderedMonad.le, OrderedMonadTrans.le]
                  intro s; apply LawfulOrderedMonad.bind_mono; assumption; simp [LawfulOrderedMonad.le_refl]

instance : OrderedMonadTrans (ExceptT ε) where
  pure := pure
  bind := bind
  lift := liftM
  le {m _ α} (m1 m2 : m (Except ε α)) := m1 ≤ m2
