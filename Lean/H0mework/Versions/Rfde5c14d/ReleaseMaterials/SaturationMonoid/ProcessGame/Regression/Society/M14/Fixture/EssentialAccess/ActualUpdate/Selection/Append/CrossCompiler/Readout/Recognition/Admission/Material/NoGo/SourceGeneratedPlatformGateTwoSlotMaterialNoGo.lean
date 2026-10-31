import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Transport.OldGate.ProofCarryingPlatformGateOldPaidChannelTransport

/-!
# Existing two-slot settlement cannot fake platform material

At the exact right Payment current, tenure and health occupy the two existing
served slots.  A platform material admission which preserves both must use a
third distinct slot; that fibre is empty.  This is a carrier-local no-go, not
a claim that later actual occurrences cannot generate new service capacity.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo

noncomputable section

open M14EssentialAccessSectorRegression
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14ProofCarryingPlatformGateOldPaidChannelTransport

abbrev ExistingTwoSlotPlatformMaterialAdmissionAt
    (oldVisit : M14SourceGeneratedContributionMergeActionSource.OldVisit)
    (sourceIndex boundary : Nat) :=
  { slot : Fin (anomiePhaseAt
      (rightCurrentAt oldVisit sourceIndex boundary)).served.length //
    slot ≠ channelSlotAt
        (rightCurrentAt oldVisit sourceIndex boundary) tenureAuthority ∧
      slot ≠ channelSlotAt
        (rightCurrentAt oldVisit sourceIndex boundary) healthAuthority }

theorem existingTwoSlotPlatformMaterialAdmission_isEmpty
    (oldVisit : M14SourceGeneratedContributionMergeActionSource.OldVisit)
    (sourceIndex boundary : Nat) :
    IsEmpty (ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
      boundary) :=
  ⟨fun admission => by
    have slotLt := admission.1.isLt
    have lengthExact := anomiePhaseAt_served_length
      (rightCurrentAt oldVisit sourceIndex boundary)
    have slotLtTwo : admission.1.val < 2 := by
      omega
    have slotCases : admission.1.val = 0 ∨ admission.1.val = 1 := by
      omega
    rcases slotCases with slotZero | slotOne
    · exact admission.2.1 (Fin.ext slotZero)
    · exact admission.2.2 (Fin.ext slotOne)⟩

theorem platformGateTwoSlotMaterialNoGo_directConsumer
    (oldVisit : M14SourceGeneratedContributionMergeActionSource.OldVisit)
    (sourceIndex boundary : Nat) :
    type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
        sourceIndex boundary tenureAuthority) ∧
      type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
        sourceIndex boundary healthAuthority) ∧
      type_of% (platformGateTenureHealthPaidTransports_sameNext oldVisit
        sourceIndex boundary) ∧
      IsEmpty (ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
        boundary) :=
  ⟨platformGateOldPaidChannelTransport_directConsumer oldVisit sourceIndex
      boundary tenureAuthority,
    platformGateOldPaidChannelTransport_directConsumer oldVisit sourceIndex
      boundary healthAuthority,
    platformGateTenureHealthPaidTransports_sameNext oldVisit sourceIndex
      boundary,
    existingTwoSlotPlatformMaterialAdmission_isEmpty oldVisit sourceIndex
      boundary⟩

end
end M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo.existingTwoSlotPlatformMaterialAdmission_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo.platformGateTwoSlotMaterialNoGo_directConsumer
