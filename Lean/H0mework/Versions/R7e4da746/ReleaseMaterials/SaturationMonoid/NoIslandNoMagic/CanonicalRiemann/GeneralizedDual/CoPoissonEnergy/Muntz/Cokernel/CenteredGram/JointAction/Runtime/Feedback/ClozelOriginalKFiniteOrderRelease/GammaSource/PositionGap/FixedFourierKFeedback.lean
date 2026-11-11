import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.PositiveTailAnnihilator
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Price

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.FixedFourierKFeedback

open BurnolPhysicalState OriginalKSourceResolventReconstruction
open BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace

open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "K" => burnolCompletedMellinRieszVector c
local notation "FK" => fourierL2 (K : BurnolL2)
local notation "R" => burnolDirectRightResolventCLM c
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "V" => physicalOutsideColumn c
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth

def price (ordinal : Nat) : ℂ := inner ℂ FK (PA.Q (raw ordinal) : BurnolL2)

def feedback (ordinal : Nat) : BurnolL2 :=
  (input (ordinal+1)).2 - O (R (input ordinal).2)

local notation "amount" => price observation nontrivial half depth
local notation "delta" => feedback observation nontrivial half depth

include nontrivial in
private theorem column_ne_zero : V ≠ 0 := by
  intro zero
  have opening := actor_first_outside_source observation nontrivial half.down 0
  rw [zero, smul_zero] at opening
  exact actor_first_outside_ne_zero observation nontrivial half.down 0 opening

include nontrivial in
/-- The actual exact-order Xi source supplies the first fixed original price. -/
theorem original_opening_price_ne_zero : inner ℂ FK ((R^m) seed) ≠ 0 := by
  let actorAt : BurnolPaAmbientCarrier :=
    ⟨actor observation half.down 0 m, actor_physical observation nontrivial half.down 0 m le_rfl⟩
  have generated := original_R_physical_outside_source c actorAt
  rw [generatedK_eq_original] at generated
  have opening := actor_first_outside_ne_zero observation nontrivial half.down 0
  rw [actor_succ] at opening
  change O (burnolDirectRightResolvent (observation.coordinate/2) (actorAt : BurnolL2)) ≠ 0 at opening
  intro zero
  change inner ℂ FK (actorAt : BurnolL2) = 0 at zero
  rw [zero, mul_zero, zero_smul] at generated
  exact opening generated

private theorem raw_power (ordinal : Nat) : raw ordinal = (R^(m+(ordinal+2))) seed := by
  have direct : OriginalKCombPhysicalAction.R observation nontrivial half = R :=
    ContinuousLinearMap.ext (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half)
  rw [OriginalKCombFirstFullSourceDynamics.raw_xi_source, direct, ← ContinuousLinearMap.toLinearMap_pow]
  rfl

/-- The fixed original price sees the entire raw source through its native Q face. -/
theorem actual_whole_price (ordinal : Nat) : inner ℂ FK (raw ordinal) = amount ordinal := by
  let k : BurnolPaOrthogonalCarrier :=
    ⟨K, riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero⟩
  let fk := burnolCompactCoPoissonActionSquare.orthogonalAction k
  have read := OriginalKPaCountingSourceAction.actual_original_Q_orthogonal_reader fk (raw ordinal)
  exact read.symm

/-- The next outside write over its self action is exactly the actual Q return. -/
theorem actual_outside_feedback (ordinal : Nat) : delta ordinal = (-2 * amount ordinal) • V := by
  have outside (n : Nat) : (input n).2 = O (raw n) :=
    (congrArg Prod.snd (literal_split observation nontrivial half depth n)).symm
  unfold feedback
  rw [outside, outside]
  change O (raw (ordinal+1)) -
      O (burnolDirectRightResolvent (observation.coordinate/2) (O (raw ordinal))) = _
  simp only [actual_outside_successor_two_sources observation nontrivial half depth ordinal,
    add_sub_cancel_left, generatedK_eq_original, price]

/-- The actual outside increment returns the fixed original price with its native normalization. -/
theorem actual_feedback_price_inverse (ordinal : Nat) :
    amount ordinal = inner ℂ V (delta ordinal) / (-2 * inner ℂ V V) := by
  have square : inner ℂ V V ≠ 0 := fun zero =>
    column_ne_zero observation nontrivial half (inner_self_eq_zero.mp zero)
  apply (eq_div_iff (mul_ne_zero (by norm_num) square)).2
  rw [actual_outside_feedback, inner_smul_right]
  ring

/-- Every cofinal tail contains an actual Q return which changes the literal outside successor. -/
theorem actual_feedback_visible_from_each_tail (start : Nat) :
    ∃ j > 0, amount (start+j) ≠ 0 ∧
      (input (start+j+1)).2 ≠ O (R (input (start+j)).2) := by
  have visible : ∃ j > 0, amount (start+j) ≠ 0 := by
    by_contra! silent
    let read : BurnolL2 →L[ℂ] ℂ := innerSL ℂ FK
    have quiet (n : Nat) (after : m+start+3 ≤ n) : read ((R^n) seed) = 0 := by
      let j := n - (m+start+2)
      have pos : 0 < j := by dsimp [j]; omega
      have slot : m+(start+j+2) = n := by dsimp [j]; omega
      have actual := silent j pos
      rw [← actual_whole_price observation nontrivial half depth, raw_power observation nontrivial half depth,
        slot] at actual
      exact actual
    exact original_opening_price_ne_zero observation nontrivial half
      (original_power_read_zero_of_tail read c seed (m+start+3) quiet m)
  obtain ⟨j, later, paid⟩ := visible
  refine ⟨j, later, paid, ?_⟩
  intro erased
  have gone : delta (start+j) = 0 := sub_eq_zero.mpr erased
  rw [actual_outside_feedback] at gone
  exact smul_ne_zero (mul_ne_zero (by norm_num) paid) (column_ne_zero observation nontrivial half) gone

end OriginalKFiniteOrderRelease.FixedFourierKFeedback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
