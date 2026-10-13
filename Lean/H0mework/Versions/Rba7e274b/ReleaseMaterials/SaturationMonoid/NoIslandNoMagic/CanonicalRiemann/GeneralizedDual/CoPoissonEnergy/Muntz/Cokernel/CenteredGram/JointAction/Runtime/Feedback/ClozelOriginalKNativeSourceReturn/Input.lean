import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace D
export OriginalKFiniteWard.D (factory packet initial firstCfg raw)
end D
namespace L
export OriginalKFiniteWard.L (Value groups)
end L
namespace AI
export OriginalKFiniteWard.AI (withActualInput HasActualInput native_after_admission_input born_after_native_input)
end AI
namespace CF
export OriginalKFiniteWard.CF (collapseValue codeAt code_base_value)
end CF
namespace AS
export OriginalKFiniteWard.AS (AdmissionPacket nativeAfterAdmission bornAfterNative)
end AS
namespace Native
export OriginalKFiniteWard.Native (sourceBorn nativePacket nativeValue selected born_environment)
export ActualCofinalSourceAction (native_packet_actual born_ast packetTransport born_transport)
end Native
namespace Paid
export OriginalKFiniteWardGram.Paid (value_of_actual_input material_raw_at)
end Paid
namespace R
export OriginalKFiniteWard.R (actualMaterial actionResultAt actionReader)
end R
namespace S
export OriginalKFiniteWard.S (actualOccurrence baseRoot)
end S
local instance sourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def inputFactory := AI.withActualInput (inputCode observation nontrivial half) (D.factory observation nontrivial half)
abbrev inputParent (ordinal : Nat) := D.packet observation nontrivial half depth ordinal
abbrev inputIncoming (ordinal : Nat) := AS.nativeAfterAdmission (inputFactory observation nontrivial half)
  (inputParent observation nontrivial half depth ordinal)
def inputPacket (ordinal : Nat) : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
  AS.bornAfterNative (inputIncoming observation nontrivial half depth ordinal)
abbrev inputBorn (ordinal : Nat) := AS.bornAfterNative
  (AS.nativeAfterAdmission (inputFactory observation nontrivial half)
    (inputPacket observation nontrivial half depth ordinal))

theorem input_born_same_source (ordinal : Nat) :
    inputBorn observation nontrivial half depth ordinal =
      Native.packetTransport (inputPacket observation nontrivial half depth ordinal).2.2.2.down
        (Native.sourceBorn (inputFactory observation nontrivial half)
          (inputPacket observation nontrivial half depth ordinal)) := by
  unfold inputBorn
  rw [Native.native_packet_actual, Native.born_transport]

theorem input_admitted_input (ordinal : Nat) :
    AI.HasActualInput (inputCode observation nontrivial half)
      (inputPacket observation nontrivial half depth ordinal).1
      (inputPacket observation nontrivial half depth ordinal).2.2.1
      (inputPacket observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (D.factory observation nontrivial half) _)

theorem input_born_input (ordinal : Nat) :
    AI.HasActualInput (inputCode observation nontrivial half)
      (inputBorn observation nontrivial half depth ordinal).1
      (inputBorn observation nontrivial half depth ordinal).2.2.1
      (inputBorn observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (D.factory observation nontrivial half) _)

theorem input_admitted_value (ordinal : Nat) :
    CF.collapseValue (inputPacket observation nontrivial half depth ordinal).1
      (R.actionResultAt (inputPacket observation nontrivial half depth ordinal).2.1.1
        (inputPacket observation nontrivial half depth ordinal).2.2.1
        (S.actualOccurrence (inputPacket observation nontrivial half depth ordinal).2.1.1)).2.2.1 =
      inputValue observation nontrivial half :=
  (Paid.value_of_actual_input (inputCode observation nontrivial half)
    (inputPacket observation nontrivial half depth ordinal) (input_admitted_input observation nontrivial half depth ordinal)).trans
      (input_code_source observation nontrivial half _)

attribute [irreducible] inputFactory inputPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
