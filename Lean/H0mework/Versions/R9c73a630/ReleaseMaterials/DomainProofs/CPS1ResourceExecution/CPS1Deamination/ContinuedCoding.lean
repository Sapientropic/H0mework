import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Continuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.CodingReadout

set_option autoImplicit false

namespace CPS1Deamination.ContinuedCoding
open CPS1ResourceExecution ExecutionReadout Continuation CodingReadout
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def continuedCoding (edits : Target.Edits) (water additional : Nat) : Option Bases :=
  (readDNA (sourceContinuation edits water additional).stock).map
    (codingFromGenomic ∘ Source.plusReadout)

def continuedStopChain (edits : Target.Edits) (water additional : Nat) : Option (List String) := do
  let coding ← continuedCoding edits water additional
  let translated ← Coding.coding? coding
  Coding.translate Coding.code translated

theorem continued_coding_actual_stock (edits : Target.Edits) (water additional : Nat) :
    continuedCoding edits water additional = actualCoding edits (water+additional) := by
  have sameStock := congrArg Execution.stock (source_continuation_composes edits water additional)
  dsimp only [stitch] at sameStock
  unfold continuedCoding actualCoding
  rw [sameStock]

theorem continued_stop_all_capacities (edits : Target.Edits) (water additional : Nat) :
    continuedStopChain edits water additional =
      some (if paidEighth edits (water+additional) then
        Source.referenceProtein ++ ["*"] else Source.referenceProtein.take 334 ++ ["*"]) := by
  unfold continuedStopChain
  rw [continued_coding_actual_stock]
  exact actual_first_stop_all_capacities edits (water+additional)

structure ContinuedCodingContract : Prop where
  continuation : type_of% source_continuation_update
  onlyRemaining : type_of% source_continuation_only_remaining
  settled : type_of% source_refill_settles
  alreadyPaid : type_of% source_complete_then_refill
  actualReadout : type_of% source_continuation_actual_readout
  coding : type_of% continued_coding_actual_stock
  firstStop : type_of% continued_stop_all_capacities

theorem sourceGeneratedContinuedCoding : ContinuedCodingContract :=
  ⟨source_continuation_update,source_continuation_only_remaining,source_refill_settles,
   source_complete_then_refill,source_continuation_actual_readout,
   continued_coding_actual_stock,continued_stop_all_capacities⟩

end CPS1Deamination.ContinuedCoding
