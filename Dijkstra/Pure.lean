import Dijkstra.DMonad
import Dijkstra.BaseSpecs.IDSpec

namespace Dijkstra

def DPure := DMonad.ofEffObs (M := Id) (W := IDSpec) (obs := pure)

instance : LawfulOrderedDMonad (W := IDSpec) DPure :=
  DMonad.instOfEffObs rfl rfl

namespace Hidden

def ret := @DMonad.ret _ _ (D := DPure)
def bind := @DMonad.bind _ _ (D := DPure)

def prog := bind (ret 5) (fun x => ret (x + 1))

example : DMonad.verify prog (pure 6) := by
  simp [DMonad.verify]
  apply LawfulOrderedMonad.le_refl
  
