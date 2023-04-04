import Std

def Cont (ρ α) := (α → ρ) → ρ

@[ext] theorem Subtype.ext (s1 s2 : Subtype p) (h : s1.val = s2.val) : s1 = s2 := by
  cases s1; cases s2; simp at h ⊢; assumption
