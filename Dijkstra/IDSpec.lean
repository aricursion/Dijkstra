import Dijkstra.DijkstraMonad

namespace Dijkstra

def IDSpec (A) := { w : Cont Prop A // ∀ {p1 p2}, (∀ a, p1 a → p2 a) → w p1 → w p2 }

namespace IDSpec

instance : OrderedMonad IDSpec where
  pure a := ⟨(· a), (· a)⟩
  bind
  | ⟨w,hw⟩, f => ⟨fun P => w (fun x => (f x).val P),
    by
      intro p1 p2 mono h; refine hw ?_ h; intro a; generalize f a = w'
      match w' with | ⟨w',hw'⟩ => simp; apply hw'; exact mono⟩
  le w1 w2 := ∀ p, w2.val p → w1.val p

@[ext] theorem ext (s1 s2 : IDSpec p) (h : s1.val = s2.val) : s1 = s2 := Subtype.ext _ _ h

instance : LawfulOrderedMonad IDSpec where
  map_const       := by intros; congr
  id_map          := by intros; congr
  seqLeft_eq      := by intros; congr
  seqRight_eq     := by intros; congr
  pure_seq        := by intros; congr
  bind_pure_comp  := by intros; congr
  bind_map        := by intros; congr
  pure_bind       := by intros; congr
  le_refl := by simp [LE.le, OrderedMonad.le]
  le_trans := by simp (config := {contextual := true}) [LE.le, OrderedMonad.le]
  le_antisymm := by simp only [LE.le, OrderedMonad.le]; intros; ext; funext p; simp; constructor <;> (intro; simp [*])
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

def assert (p : Prop) : IDSpec Unit := ⟨fun p' => p → p' (), by simp (config := {contextual := true})⟩
