import Dijkstra.OrderedMonad

namespace Dijkstra

/-! Dijkstra Monad -/
class DijkstraMonad (M W) [Monad M] [OrderedMonad W] [LawfulOrderedMonad W] where
  obs : ∀ {A}, M A → W A
  obsPure : obs (pure a) = pure a
  obsBind : obs (bind m f) = bind (obs m) (fun a => obs (f a))

instance [Monad M] [OrderedMonad W] [LawfulOrderedMonad W] [DijkstraMonad M W]
  : MonadLift M W := ⟨DijkstraMonad.obs⟩

def DijkstraVerify M [Monad M] W [OrderedMonad W] [LawfulOrderedMonad W]
                    [D : DijkstraMonad M W] A (w : W A) (m : M A) : Prop :=
  D.obs m ≤ w
