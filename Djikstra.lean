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
  obs m := fun s => DijkstraMonad.obs (m s)
  obsPure := rfl
  obsBind := rfl


instance [OrderedMonadTrans T] [LawfulOrderedMonadTrans T] : DijkstraMonad (T Id) (T IDSpec) where
  obs t := sorry
  obsPure := sorry
  obsBind := sorry

variable (σ : Type)

def DijkstraVerify M [Monad M] W [OMonad W] [LawfulOMonad W] [D : DijkstraMonad M W] A (w : W A) (m : M A) : Prop :=
  D.obs m ≤ w


theorem IDSpec.pure_iff_eq : DijkstraVerify Id IDSpec A (pure x) a ↔ x = a
  := by simp [DijkstraVerify, DijkstraMonad.obs, LE.le, OMonad.le, pure]
        constructor
        intro h; apply h; rfl
        intro h; cases h; intro; apply id

def foldSpec (inv : α → Prop) : IDSpec α :=
  ⟨ fun (p : α → Prop) => ∀ a, inv a → p a, by
    intro p1 p2 hp hinv a ha
    apply hp; apply hinv; exact ha ⟩

def foldMSpec [Monad M] (inv : M α → Prop) : IDSpec (M α) :=
  ⟨ fun (p : M α → Prop) => ∀ ma, inv ma → p ma, by 
    intro p1 p2 hp hinv ma hma
    apply hp; apply hinv; exact hma ⟩

theorem foldlInv' (L : List τ) (inv : α → Prop) (f : α → τ → α) (init : α)
    (h_init : inv init) (h_f : ∀ {a t}, t ∈ L → inv a → inv (f a t))
  : DijkstraVerify Id IDSpec α (foldSpec inv) (L.foldl f init) := by
  intro post h
  induction L generalizing init with
  | nil =>
    simp; apply h; assumption
  | cons x xs ih =>
    simp; apply ih; apply h_f <;> simp [h_init, h_f]; 
    intro a t ht inv_a
    specialize @h_f a t 
    simp [ht] at h_f
    exact h_f inv_a

theorem foldlInv (L : List τ) (inv : α → Prop) (f : α → τ → α) (init : α)
    (h_init : inv init) (h_f : ∀ {a t}, inv a → inv (f a t))
  : DijkstraVerify Id IDSpec α (foldSpec inv) (L.foldl f init) := 
    foldlInv' L inv f init h_init (@fun _ _ _ inv => h_f inv)

theorem foldlMInv [Monad M] (A : Array τ) (inv : M α → Prop) (f : α → τ → M α) (init : α) (start := 0) (stop := A.size) 
    (stop_h : stop ≤ A.size) (h_init : inv (pure init)) (h_f : ∀ {ma t}, inv ma → inv (ma >>= (fun a => f a t))) :
    DijkstraVerify Id IDSpec (M α) (foldMSpec inv) (@Array.foldlM τ α M _ f init A start stop) := by 
    intro post h
    simp [DijkstraMonad.obs, Array.foldlM]
    split <;> apply h <;> cases A
    case inl L h_stop =>
      induction L generalizing init with
      | nil => 
        simp [Array.size] at h_stop
        rw [Array.foldlM.loop]
        simp [h_stop]
        assumption
      | cons x xs ih => 
        rw [Array.foldlM.loop]
        split
        case inl start_lt_stop => 
          have : ∃ i', stop - start = Nat.succ i' := by sorry
          cases this with
          | _ i h_i =>
            simp [*] at *
            sorry
    
        case inr _ => exact h_init
    case inr L h_stop => exfalso; exact h_stop stop_h
    
      

theorem foldrInv' (L : List τ) (inv : α → Prop) (f : τ → α → α) (init : α)
    (h_init : inv init) (h_f : ∀ {a t}, t ∈ L → inv a → inv (f t a))
  : DijkstraVerify Id IDSpec α (foldSpec inv) (L.foldr f init) := by
  intro post h
  induction L generalizing post with
  | nil =>
    simp; apply h; assumption
  | cons x xs ih =>
    simp [foldSpec] at h
    apply h; apply h_f; 
    simp only [List.mem_cons, true_or]; apply ih;
    intro a t txs inva
    apply h_f (by simp only [List.mem_cons, txs, or_true]) inva;
    simp [foldSpec]
    
theorem foldrInv (L : List τ) (inv : α → Prop) (f : τ → α → α) (init : α)
    (h_init : inv init) (h_f : ∀ {a t}, inv a → inv (f t a))
  : DijkstraVerify Id IDSpec α (foldSpec inv) (L.foldr f init) := 
  foldrInv' L inv f init h_init (@fun _ _ _ inv => h_f inv)


def sum_zeros (L : List Nat) (_ : ∀ x ∈ L, x = 0) := L.foldl (fun acc x => acc + x) 0


--playing with stuff
theorem sum_zeros_eq_zero (L : List Nat) (h : ∀ x ∈ L, x = 0) : sum_zeros L h = 0 := by
  rw [sum_zeros]
  induction L with 
  | nil => simp
  | cons x xs ih => 
    rw [List.foldl]
    have := h x (by simp)
    simp [this]
    apply ih
    intro x' hx'
    specialize h x'
    simp [hx'] at h
    exact h

theorem sum_zeros_eq_zero' (L : List Nat) (h : ∀ x ∈ L, x = 0) : sum_zeros L h = 0 := by
  have := foldlInv' L (fun a => a = 0) (fun acc x => acc + x) 0 rfl (@fun n m mL ih => by simp [*] at *; exact h m mL)
  simp [DijkstraVerify, DijkstraMonad.obs, LE.le, OMonad.le, foldSpec] at this
  exact this (fun n => n = 0) rfl

