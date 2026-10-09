import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Continuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Programme

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution
open CPS1Deamination CPS1Deamination.ExecutionReadout
variable {frame : CPS1Recycling.Frame}

/-- Decode the retained native constructors; historical stock is not an input. -/
def liveResource? : CPS1ReactiveField.LiveMaterial frame → Option CPS1ResourceExecution.Species
  | .old (.retained (.retained (.retained (.retained (.retained (.retained (.retained (.retained
      (.retained (.retained (.old species))))))))))) => some species
  | .reactive (.inherited (.retained (.retained (.old species)))) => some species
  | _ => none

def liveResources (current : CPS1ReactiveField.Occurrence frame) : Stock :=
  (CPS1ReactiveField.liveStock current).filterMap liveResource?

def resume (current : CPS1ReactiveField.Occurrence frame) (water : Nat) : Execution :=
  execute (CPS1ReactiveField.editingSource current.old).editing.remaining
    (Continuation.refillWater (liveResources current) water)

def currentDNA (current : CPS1ReactiveField.Occurrence frame) (water : Nat) : Option (List Base) :=
  readDNA (resume current water).stock

private theorem actual_suffix_composes
    (current : CPS1ReactiveField.Occurrence frame)
    (initial final : List Base) (steps : List Source.Step)
    (trace : Source.follows initial steps final) (paid water additional : Nat)
    (saved : (CPS1ReactiveField.editingSource current.old).editing.remaining = steps.map Source.Step.reaction)
    (normal : liveResources current = workingStock initial paid water) :
    let first := resume current 0
    let second := execute first.remaining (Continuation.refillWater first.stock additional)
    Continuation.stitch first second = execute (steps.map Source.Step.reaction)
      (workingStock initial paid (water+additional)) := by
  simpa only [resume,saved,normal,Continuation.refillWater,List.replicate_zero,List.append_nil] using
    Continuation.native_continuation_of_follows initial final steps trace paid water additional

end
end CPS1LiveEditing
