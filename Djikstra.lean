import Std

class OMonad (W) extends Monad W where
  le : ∀ {A}, W A → W A → Prop

instance [OMonad w] : LE (w α) where
  le := OMonad.le

class LawfulOMonad (W) [OMonad W] extends LawfulMonad W where
  le_refl : ∀ a : W α, a ≤ a
  le_trans : ∀ a b c : W α, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : W α, a ≤ b → b ≤ a → a = b
  bind_mono : ∀ {A B} (w1 w2 : W A) (f1 f2 : A → W B),
    w1 ≤ w2 → (∀ a, (f1 a) ≤ (f2 a)) → (bind w1 f1) ≤ (bind w2 f2)

/-! Dijkstra Monad -/
class DijkstraMonad (M W) [Monad M] [OMonad W] [LawfulOMonad W] where
  obs : ∀ {A}, M A → W A
  obsPure : obs (pure a) = pure a
  obsBind : obs (bind m f) = bind (obs m) (fun a => obs (f a))


def Cont (ρ α) := (α → ρ) → ρ
def IDSpec (A) := { w : Cont Prop A // ∀ {p1 p2}, (∀ a, p1 a → p2 a) → w p1 → w p2}

instance : OMonad IDSpec where
  pure a := ⟨(· a), (· a)⟩
  bind
  | ⟨w,hw⟩, f => ⟨fun P => w (fun x => (f x).val P),
    by
      intro p1 p2 mono h; refine hw ?_ h; intro a; generalize f a = w'
      match w' with | ⟨w',hw'⟩ => simp; apply hw'; exact mono⟩
  le w1 w2 := ∀ p, w2.val p → w1.val p

@[ext] theorem Subtype.ext (s1 s2 : Subtype p) (h : s1.val = s2.val) : s1 = s2 := by
  cases s1; cases s2; simp at h ⊢; assumption
@[ext] theorem IDSpec.ext (s1 s2 : IDSpec p) (h : s1.val = s2.val) : s1 = s2 := Subtype.ext _ _ h

instance : LawfulOMonad IDSpec where
  map_const       := by intros; congr
  id_map          := by intros; congr
  seqLeft_eq      := by intros; congr
  seqRight_eq     := by intros; congr
  pure_seq        := by intros; congr
  bind_pure_comp  := by intros; congr
  bind_map        := by intros; congr
  pure_bind       := by intros; congr
  le_refl := by simp [LE.le, OMonad.le]
  le_trans := by simp (config := {contextual := true}) [LE.le, OMonad.le]
  le_antisymm := by simp only [LE.le, OMonad.le]; intros; ext; funext p; simp; constructor <;> (intro; simp [*])
  bind_assoc := by
    intros; simp [bind]
    split
    next h =>
    split at h
    cases h
    congr
  bind_mono
  | _w1, w2, f1, f2, h1, h2, p, h =>
    h1 _ (w2.property (λ a hf2 => h2 a _ hf2) h)

instance : DijkstraMonad Id IDSpec where
  obs a := ⟨(· a), (· a)⟩
  obsPure := rfl
  obsBind := rfl


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
  le : [OMonad m] → ∀ {α}, T m α → T m α → Prop

instance [OMonad m] [OrderedMonadTrans T] : OMonad (T m) where
  le := OrderedMonadTrans.le

class LawfulOrderedMonadTrans (T) [OrderedMonadTrans T] extends LawfulMonadTrans T where
  lift_mono : [OMonad M] → [LawfulOMonad M] → ∀ {m1 m2 : M α}, m1 ≤ m2 → MonadTrans.lift (T := T) m1 ≤ MonadTrans.lift m2


instance : OrderedMonadTrans (StateT σ) where
  pure := pure
  bind := bind
  lift := liftM
  le m1 m2 := ∀ s, m1 s ≤ m2 s

instance : LawfulOrderedMonadTrans (StateT σ) where
  lift_pure := by intros; simp [MonadTrans.lift, MonadTrans.pure, liftM, pure, monadLift, MonadLift.monadLift, StateT.lift, StateT.pure]
  lift_bind := by intros; simp [MonadTrans.lift, MonadTrans.bind, liftM, bind, monadLift, MonadLift.monadLift, StateT.lift, StateT.bind]; rfl
  lift_mono := by intros; simp [MonadTrans.lift, liftM, monadLift, MonadLift.monadLift, StateT.lift, LE.le, OMonad.le, OrderedMonadTrans.le]
                  intro s; apply LawfulOMonad.bind_mono; assumption; simp [LawfulOMonad.le_refl]

instance : OrderedMonadTrans (ExceptT ε) where
  pure := pure
  bind := bind
  lift := liftM
  le {m _ α} (m1 m2 : m (Except ε α)) := m1 ≤ m2

-- instance : @LawfulOrderedMonadTrans _ (ExceptT ε) where
--   lift_pure := sorry
--   lift_bind := sorry
--   lift_mono := sorry

-- instance {ε : Type} : DijkstraMonad (ExceptT ε Id) (ExceptT ε IDSpec) where
--   obs m := pure (f := IDSpec) m
--   obsPure := by sorry
--   obsBind := by sorry

instance : LawfulOMonad (StateT σ IDSpec) where
  le_refl := by simp [LE.le, OMonad.le, OrderedMonadTrans.le]
  le_trans := by simp (config := {contextual := true}) [LE.le, OMonad.le, OrderedMonadTrans.le]
  le_antisymm := by 
    simp only [LE.le, OMonad.le, OrderedMonadTrans.le]
    intros
    sorry
  bind_mono := sorry


instance {σ : Type} : DijkstraMonad (StateT σ Id) (StateT σ IDSpec) where
  obs m := λ s => DijkstraMonad.obs (m s)
  obsPure := by sorry
  obsBind := by sorry


instance [OrderedMonadTrans T] [LawfulOrderedMonadTrans T] : DijkstraMonad (T Id) (T IDSpec) where
  obs t := sorry
  obsPure := sorry
  obsBind := sorry

variable (σ : Type)

def DijkstraVerify M [Monad M] W [OMonad W] [LawfulOMonad W] [D : DijkstraMonad M W] A (w : W A) (m : M A)  : Prop :=
  D.obs m ≤ w


def IdObs {A : Type} (a : Id A) : IDSpec A := ⟨fun p => p a , by
  intro p1 p2 p3 p4
  exact p3 a p4
  ⟩


def gt0 : IDSpec (Nat) := ⟨fun (p : Nat → Prop) => (∀ n, n > 0 → p n), 
  by
  intros p1 _ p3 p4 n ng0
  specialize p4 n ng0
  exact p3 n p4
  ⟩

def encodeNatPre (p : Nat → Prop): IDSpec Nat := ⟨fun (q : Nat → Prop) => (∀ n, p n → q n),
  by
    intro p1 p2 p3 p4 n pn
    specialize p4 n pn
    exact p3 n p4
⟩



#check DijkstraVerify Id IDSpec Nat gt0 (do return 0)
