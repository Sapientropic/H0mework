import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Copy
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Validation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

open Institutions.Capitalism.Universal.Source.Program

def copyLaborProbe (labor : ℚ) : Current :=
  { (source.frameAt 9).raw with
    stock := fun actor good => if actor = 1 ∧ good = .labor then labor else (source.frameAt 9).raw.stock actor good }

def copyRefusalIndex (current : Current) (parent child : Party) : Option Nat :=
  match attemptCopy current parent child with
  | .paid _ => none
  | .blocked item _ _ => some item.index

theorem copying_pays_both_audit_and_transferred_labor :
    (attemptCopy (copyLaborProbe 2) 1 4).isPaid = true ∧
    (attemptCopy (copyLaborProbe 1) 1 4).isPaid = false ∧
    copyRefusalIndex (copyLaborProbe 1) 1 4 = some 1 ∧
    (attemptCopy (copyLaborProbe 0) 1 4).isPaid = false ∧
    copyRefusalIndex (copyLaborProbe 0) 1 4 = some 0 := by
  decide +kernel

theorem refused_copy_is_not_a_partial_execution :
    (attemptCopy (copyLaborProbe 1) 1 4).word = [] ∧
    (law.next (copyLaborProbe 1) (attemptCopy (copyLaborProbe 1) 1 4).word).stock =
      (copyLaborProbe 1).stock ∧
    (law.next (copyLaborProbe 1) (attemptCopy (copyLaborProbe 1) 1 4).word).claims =
      (copyLaborProbe 1).claims := by
  have denied := copying_pays_both_audit_and_transferred_labor.2.1
  cases selected : attemptCopy (copyLaborProbe 1) 1 4 with
  | paid accepted => rw [selected] at denied; cases denied
  | blocked item original refused => exact ⟨rfl, rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
