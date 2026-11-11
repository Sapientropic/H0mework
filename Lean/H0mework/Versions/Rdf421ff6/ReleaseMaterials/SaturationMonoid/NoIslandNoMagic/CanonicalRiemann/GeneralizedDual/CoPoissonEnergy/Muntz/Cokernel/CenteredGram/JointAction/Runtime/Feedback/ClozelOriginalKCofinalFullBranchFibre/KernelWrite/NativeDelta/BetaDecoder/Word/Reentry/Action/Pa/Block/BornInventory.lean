import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.Programme
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Pair.Transport

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.BornInventory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace B
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block
 (parentProgramme parentBorn sourceRelationBody sourcePairInventory programme fullWrite lowBase
  nativeBorn selected whole_first target_next compiles actual_receipt_next)
end B
namespace PT
export SourceGeneratedInquiryReceiptAction.Configured.PairTransport
 (bornPairInventory born_pair_inventory bornSegment)
end PT
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured (lowPairWritten lowBareInitial)
end CF
namespace RI
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullRBlockRelationInstall
 (pair_np_occurrence pair_pn_occurrence)
end RI
namespace T
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (liftEvent)
end T
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR

local instance baseGroups (initial : Nat) : ∀ t, AddCommGroup (BaseValue initial t) :=
 DR.L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t, AddCommGroup (DR.L.Value (BaseValue initial) 2 t) :=
 DR.L.groups (BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ t,
 AddCommGroup (DR.L.Value (DR.L.Value (BaseValue initial) 2) 0 t) := DR.L.groups (DR.L.Value (BaseValue initial) 2) 0

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (frame : Reentry.A.M.Frame (Value := PairValue (BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : Inventory (V := BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (BaseValue initial) C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))
variable (sourceFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))

local notation "parent" => B.parentBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "cfg" => B.programme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "source" => B.sourcePairInventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame parent

def sourceLift := (source).map T.liftEvent

theorem initial_pair_inventory : (CF.lowBareInitial parent cfg).pairInventory =
 some (sourceLift observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := rfl

def initialSegment : SourceInventoryTraceSegment
 (sourceLift observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (CF.lowPairWritten parent cfg) := by
 unfold CF.lowPairWritten
 rw [initial_pair_inventory]
 exact .left _ _

def inventory := PT.bornPairInventory parent cfg (B.fullWrite initial)

theorem born_pair_inventory : (B.nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).pairInventory =
 some (inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 PT.born_pair_inventory _ _ _

def bornSegment : SourceInventoryTraceSegment
 (sourceLift observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 (initialSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).trans
  (PT.bornSegment parent cfg (B.fullWrite initial))

def sourceNP : WR.RelationOccurrence source :=
 RI.pair_np_occurrence initial C.Var observation nontrivial half
  (((B.parentProgramme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).nextPairInventory parent).get (by rfl))
  (B.sourceRelationBody observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def sourcePN : WR.RelationOccurrence source :=
 RI.pair_pn_occurrence initial C.Var observation nontrivial half
  (((B.parentProgramme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).nextPairInventory parent).get (by rfl))
  (B.sourceRelationBody observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def np : WR.RelationOccurrence (inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 (sourceNP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).lift.transport
  (bornSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def pn : WR.RelationOccurrence (inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 (sourcePN observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).lift.transport
  (bornSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

theorem np_position : (np observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).before.length =
 (bornSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).before.length +
 (sourceNP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).before.length := by
 rw [np, WordReceipt.RelationOccurrence.transport_position, WordReceipt.RelationOccurrence.lift_position]

theorem pn_position : (pn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).before.length =
 (np observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).before.length + 1 := by
 rw [pn, WordReceipt.RelationOccurrence.transport_position, WordReceipt.RelationOccurrence.lift_position, np_position]
 change _ + (List.length (_ ++ [_])) = _ + List.length _ + 1
 rw [List.length_append, List.length_singleton, Nat.add_assoc]
 rfl

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.BornInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
