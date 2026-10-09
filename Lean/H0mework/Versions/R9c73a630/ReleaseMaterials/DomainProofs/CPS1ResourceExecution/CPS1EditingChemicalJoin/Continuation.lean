import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EditingChemicalJoin.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1EditingChemicalJoin.Continuation
open CPS1ResourceExecution CPS1LocalChemicalExecution

/-- A new complete substrate shot continues the existing pending suffix. Once
that suffix is empty, the next registered three-step cycle is requested. -/
def nextCycle (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame) : Source.Occurrence frame :=
  let actions := if current.current.pending = [] then CPS1LocalChemicalExecution.Source.chemicalActions else []
  Source.advance frame current actions Source.rawFuel

def cycles (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame) (depth : Nat) : Source.Occurrence frame :=
  Nat.rec current (fun _ previous => nextCycle frame previous) depth

theorem advance_does_not_rejoin (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction) (feed : List Source.RawMaterial) :
    (Source.advance frame current actions feed).previous = current.previous ∧
    (Source.advance frame current actions feed).editingFirst = current.editingFirst ∧
    (Source.advance frame current actions feed).editing = current.editing := ⟨rfl,rfl,rfl⟩

theorem cycles_retain_sources (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame) (depth : Nat) :
    (cycles frame current depth).previous = current.previous ∧
    (cycles frame current depth).editingFirst = current.editingFirst ∧
    (cycles frame current depth).editing = current.editing := by
  induction depth with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ depth ih =>
    have same := advance_does_not_rejoin frame (cycles frame current depth)
      (if (cycles frame current depth).current.pending = [] then CPS1LocalChemicalExecution.Source.chemicalActions else [])
      Source.rawFuel
    exact ⟨same.1.trans ih.1,same.2.1.trans ih.2.1,same.2.2.trans ih.2.2⟩

theorem next_cycle_complete (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame)
    (present : molecule frame .ammonia ∈ current.current.stock)
    (captured : current.current.captureRemaining = []) (pending : current.current.pending = []) :
    (nextCycle frame current).current.stock.Perm
      (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
        current.current.stock.erase (molecule frame .ammonia)) ∧
    (nextCycle frame current).current.captureRemaining = [] ∧
    (nextCycle frame current).current.pending = [] ∧ (nextCycle frame current).current.cut = none := by
  have paid := Source.advance_chemical_complete frame current present captured pending
  simpa only [nextCycle,if_pos pending] using ⟨paid.1,paid.2.1,paid.2.2.1,paid.2.2.2.1⟩

theorem chemical_products_no_ammonia (frame : CPS1Recycling.Frame) :
    (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count (molecule frame .ammonia) = 0 := rfl

theorem next_cycle_count (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame)
    (present : molecule frame .ammonia ∈ current.current.stock)
    (captured : current.current.captureRemaining = []) (pending : current.current.pending = [])
    (species : Species frame) :
    (nextCycle frame current).current.stock.count species + (if species = molecule frame .ammonia then 1 else 0) =
      current.current.stock.count species +
        (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count species := by
  have counted := (next_cycle_complete frame current present captured pending).1.count_eq species
  by_cases same : species = molecule frame .ammonia
  · subst species
    have positive : 0 < current.current.stock.count (molecule frame .ammonia) := List.count_pos_iff.mpr present
    simp only [List.count_append,List.count_erase_self,chemical_products_no_ammonia,ite_true] at counted ⊢
    omega
  · simp only [List.count_append,List.count_erase_of_ne same,if_neg same,Nat.add_zero] at counted ⊢
    omega

theorem complete_cycles (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame) (depth : Nat)
    (captured : current.current.captureRemaining = []) (pending : current.current.pending = [])
    (fuel : depth ≤ current.current.stock.count (molecule frame .ammonia)) :
    (cycles frame current depth).current.captureRemaining = [] ∧
    (cycles frame current depth).current.pending = [] ∧
    (∀ species, (cycles frame current depth).current.stock.count species +
      (if species = molecule frame .ammonia then depth else 0) = current.current.stock.count species +
      depth * (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count species) := by
  induction depth with
  | zero =>
    refine ⟨captured,pending,?_⟩
    intro species
    simp only [cycles,Nat.rec_zero,Nat.zero_mul,Nat.add_zero,ite_self]
  | succ depth ih =>
    have smaller : depth ≤ current.current.stock.count (molecule frame .ammonia) := by omega
    have previous := ih smaller
    have ammonia := previous.2.2 (molecule frame .ammonia)
    simp only [ite_true,chemical_products_no_ammonia,Nat.mul_zero,Nat.add_zero] at ammonia
    have positive : 0 < (cycles frame current depth).current.stock.count (molecule frame .ammonia) := by omega
    have present := List.count_pos_iff.mp positive
    have paid := next_cycle_complete frame (cycles frame current depth) present previous.1 previous.2.1
    refine ⟨paid.2.1,paid.2.2.1,?_⟩
    intro species
    have step := next_cycle_count frame (cycles frame current depth) present previous.1 previous.2.1 species
    have earlier := previous.2.2 species
    change (nextCycle frame (cycles frame current depth)).current.stock.count species + _ = _
    by_cases same : species = molecule frame .ammonia <;>
      simp only [same,ite_true,ite_false,Nat.succ_mul] at earlier step ⊢ <;> omega

end CPS1EditingChemicalJoin.Continuation
