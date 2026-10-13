import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace L
export OriginalKFullSourceRAction.L (Value groups)
end L
namespace AI
export OriginalKFullSourceRAction.AI (withActualInput HasActualInput native_after_admission_input born_after_native_input)
end AI
namespace CF
export OriginalKFullSourceRAction.CF (collapseValue code_base_value)
end CF
namespace AS
export OriginalKFullSourceRAction.AS (AdmissionPacket nativeAfterAdmission bornAfterNative nativeAfterAdmission_grade)
end AS
namespace R
export OriginalKFullSourceRAction.R (actualMaterial actionResultAt actionReader)
end R
namespace Root
export OriginalKFullSourceRAction.Root (actualOccurrence baseRoot)
end Root
namespace Paid
export OriginalKFullSourceRAction.Paid (value_of_actual_input material_raw_at)
end Paid
namespace Dyn
export OriginalKFullSourceRAction.Dyn (packet_native_value collapse_generated_successor)
end Dyn
namespace N
export OriginalKFullSourceRAction.N (input)
end N
local instance sourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

variable (ordinal : Nat) (h : ℝ)
/-- Install the actual corrected-source orbit before the original R emitter's next admission. -/
def factory:=AI.withActualInput (sourceCode observation nontrivial half depth ordinal h) (Prior.factory observation nontrivial half)
abbrev parentPacket:=Prior.actionPacket observation nontrivial half depth ordinal

def actionPacket : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()) :=
  AS.bornAfterNative (AS.nativeAfterAdmission (factory observation nontrivial half depth ordinal h)
    (parentPacket observation nontrivial half depth ordinal))
abbrev configuration:=(actionPacket observation nontrivial half depth ordinal h).2.2.1
abbrev material:=R.actualMaterial (actionPacket observation nontrivial half depth ordinal h).2.1.1
  (configuration observation nontrivial half depth ordinal h)
abbrev receipt:=R.actionResultAt (actionPacket observation nontrivial half depth ordinal h).2.1.1
  (configuration observation nontrivial half depth ordinal h)
  (Root.actualOccurrence (actionPacket observation nontrivial half depth ordinal h).2.1.1)

def actualEnvironment : Env (PairValue (PairValue C.Value)) C.Var:=
  fun target name=>CF.collapseValue (actionPacket observation nontrivial half depth ordinal h).1
    ((actionPacket observation nontrivial half depth ordinal h).2.1.1.activeEnvironment target name,0)

theorem actual_admitted_input : AI.HasActualInput (sourceCode observation nontrivial half depth ordinal h)
    (actionPacket observation nontrivial half depth ordinal h).1
    (actionPacket observation nontrivial half depth ordinal h).2.2.1
    (actionPacket observation nontrivial half depth ordinal h).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (Prior.factory observation nontrivial half) _)

theorem actual_source_value :
    CF.collapseValue (actionPacket observation nontrivial half depth ordinal h).1
      (receipt observation nontrivial half depth ordinal h).2.2.1=
      sourceFields ((pairedAction h - ContinuousLinearMap.id ℂ BurnolL2)
        (correctedSource observation nontrivial half depth ordinal (actualEnvironment observation nontrivial half depth ordinal h () ()))) :=
  (Paid.value_of_actual_input (sourceCode observation nontrivial half depth ordinal h)
    (actionPacket observation nontrivial half depth ordinal h) (actual_admitted_input observation nontrivial half depth ordinal h)).trans
    (source_code_read observation nontrivial half depth ordinal h _)

theorem actual_material_source_ast : type_of%
    (Paid.material_raw_at (sourceCode observation nontrivial half depth ordinal h)
      (actionPacket observation nontrivial half depth ordinal h) (actual_admitted_input observation nontrivial half depth ordinal h)) :=
  Paid.material_raw_at _ _ (actual_admitted_input observation nontrivial half depth ordinal h)

/-- The incoming value is the actual R written value, proved through its
emitted native successor. No D-stream recognition by scalar equality occurs. -/
theorem actual_parent_input :
    actualEnvironment observation nontrivial half depth ordinal h () ()=
      Prior.actualWriteRead observation nontrivial half depth ordinal := by
  let parent:=parentPacket observation nontrivial half depth ordinal
  let child:=actionPacket observation nontrivial half depth ordinal h
  let computed:=(R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
    (N.input (R.actualMaterial parent.2.1.1 parent.2.2.1)).environment
  have grade:child.1=parent.1+1 := by
    unfold child actionPacket
    exact AS.nativeAfterAdmission_grade (factory observation nontrivial half depth ordinal h) parent
  have generated:HEq (child.2.1.1.activeEnvironment () ()) computed := by
    unfold child actionPacket
    exact Dyn.packet_native_value (factory observation nontrivial half depth ordinal h) parent ()
  have collapsed:=Dyn.collapse_generated_successor parent.1 child.1 grade _ computed generated
  have source:computed=OriginalKFullSourceRAction.actualWrite observation nontrivial half depth ordinal := by
    unfold computed
    rw [OriginalKFullSourceRAction.actual_R_write]
    change (R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
      ((R.actualMaterial parent.2.1.1 parent.2.2.1).environment+(R.actualMaterial parent.2.1.1 parent.2.2.1).increment)=_
    exact Expr.eval_update (R.actualMaterial parent.2.1.1 parent.2.2.1).raw
      (R.actualMaterial parent.2.1.1 parent.2.2.1).environment (R.actualMaterial parent.2.1.1 parent.2.2.1).increment
  change CF.collapseValue child.1 (child.2.1.1.activeEnvironment () (),0)=_
  exact collapsed.trans (congrArg (CF.collapseValue parent.1) source)

theorem actual_complete_corrected_source :
    CF.collapseValue (actionPacket observation nontrivial half depth ordinal h).1
      (receipt observation nontrivial half depth ordinal h).2.2.1=
      sourceFields ((pairedAction h - ContinuousLinearMap.id ℂ BurnolL2)
        (Source.value (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))) := by
  rw [actual_source_value,actual_parent_input,actual_corrected_source_recovered]

attribute [irreducible] factory actionPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
