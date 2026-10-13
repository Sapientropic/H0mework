import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteReaction.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace D
export OriginalKNativeSourceReturn.D (factory)
end D
namespace L
export OriginalKNativeSourceReturn.L (Value groups)
end L
namespace AI
export OriginalKNativeSourceReturn.AI (withActualInput HasActualInput native_after_admission_input born_after_native_input)
end AI
namespace CF
export OriginalKNativeSourceReturn.CF (collapseValue code_base_value)
end CF
namespace AS
export OriginalKNativeSourceReturn.AS (AdmissionPacket nativeAfterAdmission bornAfterNative)
end AS
namespace Native
export OriginalKNativeSourceReturn.Native (sourceBorn nativePacket nativeValue selected born_environment native_packet_actual born_transport packetTransport)
end Native
namespace Paid
export OriginalKNativeSourceReturn.Paid (value_of_actual_input material_raw_at)
end Paid
namespace R
export OriginalKNativeSourceReturn.R (actualMaterial actionResultAt actionReader)
end R
namespace Root
export OriginalKNativeSourceReturn.S (actualOccurrence baseRoot)
end Root
namespace Dyn
export OriginalKNativeSourceReturn.Dyn (packet_native_value collapse_generated_successor)
end Dyn
namespace AS
export OriginalKNativeSourceReturn.AS (nativeAfterAdmission_grade)
end AS
local instance sourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

-- The own 147 returned source is the parent occurrence; this finite reaction programme is installed before emission.
def reactionFactory := AI.withActualInput (sourceCode (RSource.coordinate observation nontrivial half) RSource.sourceShift)
  (D.factory observation nontrivial half)
abbrev reactionParent (ordinal : Nat) := Prior.returnPacket observation nontrivial half depth ordinal
def reactionPacket (ordinal : Nat) : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
  AS.bornAfterNative (AS.nativeAfterAdmission (reactionFactory observation nontrivial half)
    (reactionParent observation nontrivial half depth ordinal))
abbrev material (ordinal : Nat) := R.actualMaterial (reactionPacket observation nontrivial half depth ordinal).2.1.1
  (reactionPacket observation nontrivial half depth ordinal).2.2.1
abbrev receipt (ordinal : Nat) := R.actionResultAt (reactionPacket observation nontrivial half depth ordinal).2.1.1
  (reactionPacket observation nontrivial half depth ordinal).2.2.1
  (Root.actualOccurrence (reactionPacket observation nontrivial half depth ordinal).2.1.1)
def actualEnvironment (ordinal : Nat) : Env (PairValue (PairValue C.Value)) C.Var :=
  fun target name => CF.collapseValue (reactionPacket observation nontrivial half depth ordinal).1
    ((reactionPacket observation nontrivial half depth ordinal).2.1.1.activeEnvironment target name,0)
theorem actual_admitted_input (ordinal : Nat) : AI.HasActualInput
    (sourceCode (RSource.coordinate observation nontrivial half) RSource.sourceShift)
    (reactionPacket observation nontrivial half depth ordinal).1
    (reactionPacket observation nontrivial half depth ordinal).2.2.1
    (reactionPacket observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (D.factory observation nontrivial half) _)
theorem actual_admitted_value (ordinal : Nat) :
    CF.collapseValue (reactionPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1 =
      finiteFields RSource.sourceShift
        (fieldReader (actualEnvironment observation nontrivial half depth ordinal () ()))+
          reaction_source (RSource.coordinate observation nontrivial half) RSource.sourceShift :=
  (Paid.value_of_actual_input (sourceCode (RSource.coordinate observation nontrivial half) RSource.sourceShift)
    (reactionPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)).trans
      (source_code_read (RSource.coordinate observation nontrivial half) RSource.sourceShift _)

theorem actual_material_source_ast (ordinal : Nat) : type_of%
    (Paid.material_raw_at (sourceCode (RSource.coordinate observation nontrivial half) RSource.sourceShift)
      (reactionPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)) :=
  Paid.material_raw_at _ _ (actual_admitted_input observation nontrivial half depth ordinal)

attribute [irreducible] reactionFactory reactionPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
