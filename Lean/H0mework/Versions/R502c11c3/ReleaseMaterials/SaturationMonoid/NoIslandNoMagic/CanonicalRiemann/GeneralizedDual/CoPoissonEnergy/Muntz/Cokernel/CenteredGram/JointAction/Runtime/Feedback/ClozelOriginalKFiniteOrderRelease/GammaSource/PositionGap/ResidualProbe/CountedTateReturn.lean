import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CountedNativeReentry
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.CoupledAction
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSourceGreen.Dissipation

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CountedTateReturn

open BurnolPhysicalState BurnolPhysicalState.OriginalPaPhysicalGreen
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private vector_ne from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn

namespace Query
export OriginalKDirectRCofinalMobiusSourceAction
  (actualQueryTate actualReentryPairing actualReentryVector actual_reentry_vector_memPa actual_query_Tate_coupled)
end Query

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "V" => Query.actualReentryVector observation half
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Tate" => Query.actualQueryTate observation nontrivial half depth
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "M" => burnolTateReciprocalL2.comp burnolMobiusSourceL2

/-- The other two feet are calculated from the original current query and its owned unit coefficient. -/
def baseTate (ordinal : Nat) : BurnolL2 :=
  sourceVolterraWindow c (Tate ordinal) +
    OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal •
      M (E (OriginalKDirectRCofinalPaUpdate.sourceWholeUnit observation nontrivial half : BurnolL2))

/-- The returned source is the actual next query after its own two already calculated feet are removed. -/
def tateReturn (ordinal : Nat) : BurnolL2 :=
  Tate (ordinal + 1) - baseTate observation nontrivial half depth ordinal

private theorem same_pairing (ordinal : Nat) :
    Query.actualReentryPairing observation nontrivial half depth ordinal = fee ordinal := by
  rw [ReentryDifferenceClock.literal_fee]
  exact OriginalKDirectRCofinalReentrySourceAction.source_unit_invisible_pair_Q
    observation nontrivial half.down (raw ordinal)

/-- The complete arithmetic inverse fibre writes back the very same original Pa innovation. -/
theorem generated_tate_return (ordinal : Nat) :
    tateReturn observation nontrivial half depth ordinal = fee ordinal • M V := by
  have actual := Query.actual_query_Tate_coupled observation nontrivial half depth ordinal
  rw [same_pairing observation nontrivial half depth ordinal] at actual
  unfold tateReturn
  change Tate (ordinal + 1) - baseTate observation nontrivial half depth ordinal = _
  rw [actual]
  change (baseTate observation nontrivial half depth ordinal + fee ordinal • M V) -
    baseTate observation nontrivial half depth ordinal = _
  exact add_sub_cancel_left _ _

/-- This fixed arithmetic test is generated from the same Pa correction of the source Riesz vector. -/
def greenTest : BurnolL2 :=
  M (burnolPaSourceCorrection c ⟨V, Query.actual_reentry_vector_memPa observation half⟩)

def greenGain : ℂ := inner ℂ (greenTest observation half) (M V)

include nontrivial in
theorem green_gain_negative : (greenGain observation half).re < 0 :=
  burnolPaSourceGreen_strict_dissipation c V (Query.actual_reentry_vector_memPa observation half)
    (vector_ne observation nontrivial half)

/-- The test reads the full native next input against a fixed source-generated Green witness. -/
def greenRead (ordinal : Nat) : ℂ :=
  inner ℂ (greenTest observation half) (tateReturn observation nontrivial half depth ordinal)

theorem green_read_generated (ordinal : Nat) :
    greenRead observation nontrivial half depth ordinal = fee ordinal * greenGain observation half := by
  rw [greenRead, generated_tate_return, inner_smul_right, greenGain]

include nontrivial in
/-- Independently recover each original receipt's fee directly from the written arithmetic query. -/
theorem actual_green_fee (ordinal : Nat) :
    greenRead observation nontrivial half depth ordinal / greenGain observation half = fee ordinal := by
  have live : greenGain observation half ≠ 0 := by
    intro zero
    have negative := green_gain_negative observation nontrivial half
    rw [zero, Complex.zero_re] at negative
    exact lt_irrefl _ negative
  rw [green_read_generated, mul_div_cancel_right₀ _ live]

/-- The actual returned query contributes its own Green norm and boundary flux. -/
theorem actual_return_green_balance (ordinal : Nat) :
    let correction := fee ordinal • greenTest observation half;
    let flux := fee ordinal * (((1 / 4 : ℝ) : ℂ) ^ ((c).value - 1) *
      burnolPaResolventSourceCoefficient c V);
    -4 * (inner ℂ correction (tateReturn observation nontrivial half depth ordinal)).re =
      (2 * (c).value.re - 1) * ‖correction‖ ^ 2 + (1 / 2 : ℝ) * ‖flux‖ ^ 2 := by
  let inside := Query.actual_reentry_vector_memPa observation half
  let Pa := burnolCompactCoPoissonClosedRange.toSubmodule
  have admitted : fee ordinal • V ∈ Pa := Pa.smul_mem _ inside
  let lifted : ↥Pa := ⟨V, inside⟩
  have exactInput : (⟨fee ordinal • V, admitted⟩ : ↥Pa) = fee ordinal • lifted :=
    Subtype.ext rfl
  have correction : M (burnolPaSourceCorrection c (⟨fee ordinal • V, admitted⟩ : ↥Pa)) =
      fee ordinal • greenTest observation half := by
    rw [exactInput, map_smul, map_smul]
    rfl
  have returned : M (fee ordinal • V) = tateReturn observation nontrivial half depth ordinal :=
    (map_smul M _ _).trans (generated_tate_return observation nontrivial half depth ordinal).symm
  have flux : ((1 / 4 : ℝ) : ℂ) ^ ((c).value - 1) *
      burnolPaResolventSourceCoefficient c (fee ordinal • V) =
      fee ordinal * (((1 / 4 : ℝ) : ℂ) ^ ((c).value - 1) *
        burnolPaResolventSourceCoefficient c V) := by
    rw [map_smul, smul_eq_mul]
    ring
  let green := M (burnolPaSourceCorrection c (⟨fee ordinal • V, admitted⟩ : ↥Pa))
  have paid : -4 * (inner ℂ green (M (fee ordinal • V))).re =
      (2 * (c).value.re - 1) * ‖green‖ ^ 2 +
        (1 / 2 : ℝ) * ‖((1 / 4 : ℝ) : ℂ) ^ ((c).value - 1) *
          burnolPaResolventSourceCoefficient c (fee ordinal • V)‖ ^ 2 :=
    burnolPaSourceGreen c (fee ordinal • V) admitted
  have generated : green = fee ordinal • greenTest observation half := correction
  rw [generated, returned, flux] at paid
  exact paid

include nontrivial in
/-- The original nonzero cofinal physical return also survives the complete next arithmetic source. -/
theorem cofinal_green_return (cutoff : Nat) :
    ∃ ordinal ≥ cutoff, greenRead observation nontrivial half depth ordinal ≠ 0 ∧
      tateReturn observation nontrivial half depth ordinal ≠ 0 ∧
      greenRead observation nontrivial half depth ordinal / greenGain observation half = fee ordinal := by
  refine (CountedNativeReentry.literal_return_cofinal observation nontrivial half depth cutoff).elim ?_
  intro ordinal actual
  have after := actual.1
  have live := actual.2.1
  have recovered := actual_green_fee observation nontrivial half depth ordinal
  have readLive : greenRead observation nontrivial half depth ordinal ≠ 0 := by
    intro erased
    rw [erased, zero_div] at recovered
    exact live recovered.symm
  refine ⟨ordinal, after, readLive, ?_, recovered⟩
  intro erased
  apply readLive
  rw [greenRead, erased, inner_zero_right]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CountedTateReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
