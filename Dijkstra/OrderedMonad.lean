import Dijkstra.AuxDefs

namespace Dijkstra

class OrderedMonad (W) extends Monad W where
  le : ∀ {A}, W A → W A → Prop

instance [OrderedMonad w] : LE (w α) where
  le := OrderedMonad.le

class LawfulOrderedMonad (W) [OrderedMonad W] extends LawfulMonad W where
  le_refl : ∀ {a : W α}, a ≤ a
  le_trans : ∀ {a b c : W α}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : W α}, a ≤ b → b ≤ a → a = b
  bind_mono : ∀ {A B} (w1 w2 : W A) (f1 f2 : A → W B),
    w1 ≤ w2 → (∀ a, (f1 a) ≤ (f2 a)) → (bind w1 f1) ≤ (bind w2 f2)
