import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDefectAction.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace D
export OriginalKFiniteReaction.D (factory)
end D
namespace L
export OriginalKFiniteReaction.L (Value groups)
end L
namespace AI
export OriginalKFiniteReaction.AI (withActualInput HasActualInput native_after_admission_input born_after_native_input)
end AI
namespace CF
export OriginalKFiniteReaction.CF (collapseValue code_base_value)
end CF
namespace AS
export OriginalKFiniteReaction.AS (AdmissionPacket nativeAfterAdmission bornAfterNative)
end AS
namespace Native
export OriginalKFiniteReaction.Native (sourceBorn nativePacket nativeValue selected born_environment native_packet_actual born_transport packetTransport)
end Native
namespace Paid
export OriginalKFiniteReaction.Paid (value_of_actual_input material_raw_at)
end Paid
namespace R
export OriginalKFiniteReaction.R (actualMaterial actionResultAt actionReader)
end R
namespace Root
export OriginalKFiniteReaction.Root (actualOccurrence baseRoot)
end Root
namespace Dyn
export OriginalKFiniteReaction.Dyn (packet_native_value collapse_generated_successor)
end Dyn
namespace AS
export OriginalKFiniteReaction.AS (nativeAfterAdmission_grade)
end AS
local instance sourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

-- The own signed 148 source occurrence is the parent; the defect action is installed before emission.
def defectFactory := AI.withActualInput (sourceCode (RSource.coordinate observation nontrivial half))
  (D.factory observation nontrivial half)
abbrev defectParent (ordinal : Nat) := Prior.reactionPacket observation nontrivial half depth ordinal
def defectPacket (ordinal : Nat) : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
  AS.bornAfterNative (AS.nativeAfterAdmission (defectFactory observation nontrivial half)
    (defectParent observation nontrivial half depth ordinal))
abbrev material (ordinal : Nat) := R.actualMaterial (defectPacket observation nontrivial half depth ordinal).2.1.1
  (defectPacket observation nontrivial half depth ordinal).2.2.1
abbrev receipt (ordinal : Nat) := R.actionResultAt (defectPacket observation nontrivial half depth ordinal).2.1.1
  (defectPacket observation nontrivial half depth ordinal).2.2.1
  (Root.actualOccurrence (defectPacket observation nontrivial half depth ordinal).2.1.1)
def actualEnvironment (ordinal : Nat) : Env (PairValue (PairValue C.Value)) C.Var :=
  fun target name => CF.collapseValue (defectPacket observation nontrivial half depth ordinal).1
    ((defectPacket observation nontrivial half depth ordinal).2.1.1.activeEnvironment target name,0)
theorem actual_admitted_input (ordinal : Nat) : AI.HasActualInput
    (sourceCode (RSource.coordinate observation nontrivial half))
    (defectPacket observation nontrivial half depth ordinal).1
    (defectPacket observation nontrivial half depth ordinal).2.2.1
    (defectPacket observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (D.factory observation nontrivial half) _)
theorem actual_admitted_value (ordinal : Nat) :
    CF.collapseValue (defectPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1 =
      actionFields (sourceField (RSource.coordinate observation nontrivial half)
        (actualEnvironment observation nontrivial half depth ordinal () ())) :=
  (Paid.value_of_actual_input (sourceCode (RSource.coordinate observation nontrivial half))
    (defectPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)).trans
      (source_code_read (RSource.coordinate observation nontrivial half) _)

theorem actual_material_source_ast (ordinal : Nat) : type_of%
    (Paid.material_raw_at (sourceCode (RSource.coordinate observation nontrivial half))
      (defectPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)) :=
  Paid.material_raw_at _ _ (actual_admitted_input observation nontrivial half depth ordinal)

attribute [irreducible] defectFactory defectPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
