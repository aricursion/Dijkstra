import Dijkstra.OrderedMonad

namespace Dijkstra

structure WeakestPre (A) where
  w : Cont Prop A
  monotonic : ∀ {p1 p2}, (∀ a, p1 a → p2 a) → w p1 → w p2

namespace WeakestPre

instance : OrderedMonad WeakestPre where
  pure a := ⟨(· a), (· a)⟩
  bind
  | ⟨w,hw⟩, f => ⟨fun P => w (fun x => (f x).w P),
    by
      intro p1 p2 mono h; refine hw ?_ h; intro a; generalize f a = w'
      match w' with | ⟨w',hw'⟩ => simp; apply hw'; exact mono⟩
  le w1 w2 := ∀ p, w2.w p → w1.w p

@[ext] theorem ext (s1 s2 : WeakestPre p) (h : s1.w = s2.w) : s1 = s2 :=
  by cases s1; cases s2; simp at h; simp [h]

instance : LawfulOrderedMonad WeakestPre where
  map_const       := by intros; congr
  id_map          := by intros; congr
  seqLeft_eq      := by intros; congr
  seqRight_eq     := by intros; congr
  pure_seq        := by intros; congr
  bind_pure_comp  := by intros; congr
  bind_map        := by intros; congr
  pure_bind       := by intros; congr
  le_refl := by
    simp [LE.le, OrderedMonad.le]
  le_trans := by
    simp (config := {contextual := true}) [LE.le, OrderedMonad.le]
  le_antisymm := by
    simp only [LE.le, OrderedMonad.le]
    intros; ext; funext p
    simp; constructor <;> (intro; simp [*])
  bind_assoc := by
    intros; simp [bind]
  bind_mono
  | _w1, w2, f1, f2, h1, h2, p, h =>
    h1 _ (w2.monotonic (λ a hf2 => h2 a _ hf2) h)

end WeakestPre





/-! TODO: work out RelPrePost conditions necessary to prove lawfulness -/
structure RelPrePost (A) where
  rel : Prop → (A → Prop) → Prop

namespace RelPrePost

instance : OrderedMonad RelPrePost where
-- no clue what the right pure/bind is for this
  pure a := ⟨λ pre post => pre → post a⟩
  bind
  | ⟨rel⟩, f => ⟨λ pre post =>
      /- I think we want the `∀ a` outside the `∃ post'`?
        but seems impossible to prove the laws with this -/
      ∀ a, ∃ post', rel pre post' ∧ (f a).rel (post' a) post
    ⟩
  le w1 w2 := ∀ pre post, w2.rel pre post → w1.rel pre post

@[ext] theorem ext (s1 s2 : RelPrePost p) (h : s1.rel = s2.rel) : s1 = s2 :=
  by cases s1; cases s2; simp at h; simp [h]

/-
instance : LawfulOrderedMonad RelPrePost where
  map_const       := by intros; congr
  id_map          := by
    intro α x; cases x; simp [Functor.map]; funext pre post; apply propext
    constructor
    . intro h; sorry
    . sorry
  seqLeft_eq      := by intros; congr
  seqRight_eq     := by intros; congr
  pure_seq        := by intros; congr
  bind_pure_comp  := by intros; congr
  bind_map        := by intros; congr
  pure_bind       := by intros; congr
  le_refl := by
    simp [LE.le, OrderedMonad.le]
  le_trans := by
    simp (config := {contextual := true}) [LE.le, OrderedMonad.le]
  le_antisymm := by
    simp only [LE.le, OrderedMonad.le]
    intros; ext; funext p
    simp; constructor <;> (intro; simp [*])
  bind_assoc := by
    intros; simp [bind]
  bind_mono
  | _w1, w2, f1, f2, h1, h2, p, h =>
    h1 _ (w2.monotonic (λ a hf2 => h2 a _ hf2) h)
-/
