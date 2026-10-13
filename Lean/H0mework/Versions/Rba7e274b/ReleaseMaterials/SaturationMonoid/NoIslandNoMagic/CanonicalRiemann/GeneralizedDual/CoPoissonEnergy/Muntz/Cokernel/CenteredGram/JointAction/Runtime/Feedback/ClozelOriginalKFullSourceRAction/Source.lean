import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace L
export OriginalKDefectAction.L (Value groups)
end L
namespace AI
export OriginalKDefectAction.AI (withActualInput HasActualInput native_after_admission_input born_after_native_input)
end AI
namespace CF
export OriginalKDefectAction.CF (collapseValue code_base_value)
end CF
namespace AS
export OriginalKDefectAction.AS (AdmissionPacket nativeAfterAdmission bornAfterNative nativeAfterAdmission_grade)
end AS
namespace R
export OriginalKDefectAction.R (actualMaterial actionResultAt actionReader)
end R
namespace Root
export OriginalKDefectAction.Root (actualOccurrence baseRoot)
end Root
namespace Paid
export OriginalKDefectAction.Paid (value_of_actual_input material_raw_at)
end Paid
namespace Dyn
export OriginalKDefectAction.Dyn (packet_native_value collapse_generated_successor)
end Dyn
namespace N
export OriginalKDefectAction.N (input)
end N
local instance sourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

/-- Install the variable R programme before the original149 emitter's next
admission. The source environment and all inventory callbacks stay inherited. -/
def factory:=AI.withActualInput (sourceCode observation nontrivial half) (Prior.defectFactory observation nontrivial half)
abbrev parentPacket (ordinal : Nat):=Prior.defectPacket observation nontrivial half depth ordinal

def actionPacket (ordinal : Nat) : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()) :=
  AS.bornAfterNative (AS.nativeAfterAdmission (factory observation nontrivial half)
    (parentPacket observation nontrivial half depth ordinal))
abbrev configuration (ordinal : Nat):=(actionPacket observation nontrivial half depth ordinal).2.2.1
abbrev material (ordinal : Nat):=R.actualMaterial (actionPacket observation nontrivial half depth ordinal).2.1.1
  (configuration observation nontrivial half depth ordinal)
abbrev receipt (ordinal : Nat):=R.actionResultAt (actionPacket observation nontrivial half depth ordinal).2.1.1
  (configuration observation nontrivial half depth ordinal)
  (Root.actualOccurrence (actionPacket observation nontrivial half depth ordinal).2.1.1)

def actualEnvironment (ordinal : Nat) : Env (PairValue (PairValue C.Value)) C.Var:=
  fun target name=>CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
    ((actionPacket observation nontrivial half depth ordinal).2.1.1.activeEnvironment target name,0)

theorem actual_admitted_input (ordinal : Nat) : AI.HasActualInput (sourceCode observation nontrivial half)
    (actionPacket observation nontrivial half depth ordinal).1
    (actionPacket observation nontrivial half depth ordinal).2.2.1
    (actionPacket observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (Prior.defectFactory observation nontrivial half) _)

theorem actual_source_value (ordinal : Nat) :
    CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1=
      variableAction observation nontrivial half (actualEnvironment observation nontrivial half depth ordinal () ()) :=
  (Paid.value_of_actual_input (sourceCode observation nontrivial half)
    (actionPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)).trans
    (source_code_read observation nontrivial half _)

theorem actual_material_source_ast (ordinal : Nat) : type_of%
    (Paid.material_raw_at (sourceCode observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)) :=
  Paid.material_raw_at _ _ (actual_admitted_input observation nontrivial half depth ordinal)

/-- The incoming value is the actual149 written value, proved through its
emitted native successor. No D-stream recognition by scalar equality occurs. -/
theorem actual_parent_input (ordinal : Nat) :
    actualEnvironment observation nontrivial half depth ordinal () ()=
      Prior.actualWriteRead observation nontrivial half depth ordinal := by
  let parent:=parentPacket observation nontrivial half depth ordinal
  let child:=actionPacket observation nontrivial half depth ordinal
  let computed:=(R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
    (N.input (R.actualMaterial parent.2.1.1 parent.2.2.1)).environment
  have grade:child.1=parent.1+1 := by
    unfold child actionPacket
    exact AS.nativeAfterAdmission_grade (factory observation nontrivial half) parent
  have generated:HEq (child.2.1.1.activeEnvironment () ()) computed := by
    unfold child actionPacket
    exact Dyn.packet_native_value (factory observation nontrivial half) parent ()
  have collapsed:=Dyn.collapse_generated_successor parent.1 child.1 grade _ computed generated
  have source:computed=OriginalKDefectAction.actualWrite observation nontrivial half depth ordinal := by
    unfold computed
    rw [OriginalKDefectAction.actual_defect_write]
    change (R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
      ((R.actualMaterial parent.2.1.1 parent.2.2.1).environment+(R.actualMaterial parent.2.1.1 parent.2.2.1).increment)=_
    exact Expr.eval_update (R.actualMaterial parent.2.1.1 parent.2.2.1).raw
      (R.actualMaterial parent.2.1.1 parent.2.2.1).environment (R.actualMaterial parent.2.1.1 parent.2.2.1).increment
  change CF.collapseValue child.1 (child.2.1.1.activeEnvironment () (),0)=_
  exact collapsed.trans (congrArg (CF.collapseValue parent.1) source)

theorem actual_complete_R_source (ordinal : Nat) :
    CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1=
      variableAction observation nontrivial half (Prior.actualWriteRead observation nontrivial half depth ordinal) := by
  rw [actual_source_value,actual_parent_input]

attribute [irreducible] factory actionPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
