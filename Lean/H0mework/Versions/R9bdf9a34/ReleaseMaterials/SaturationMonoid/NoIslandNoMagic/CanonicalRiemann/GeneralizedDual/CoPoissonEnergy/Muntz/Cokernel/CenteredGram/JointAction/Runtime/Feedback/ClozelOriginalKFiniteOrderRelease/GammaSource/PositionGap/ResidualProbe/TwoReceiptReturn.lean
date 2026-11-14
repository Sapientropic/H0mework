import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ReentryDifferenceClock

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.TwoReceiptReturn

open BurnolPhysicalState Complex Set MeasureTheory
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKDirectRCofinalReentrySourceAction
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private step_source_coefficient from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.Source
open private right_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
open private betaRead from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private beta_zero_of_pa drop from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ReentryDifferenceClock

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "δ" => (sourceDamping c : ℂ)
local notation "J" => ContinuousLinearMap.adjoint (sourceCayley c)
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "Q" => OriginalKCombCofinalPaAction.Q
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "seed" => burnolPaCombApproximation 0
local notation "u" => fourierL2 (burnolUnitTailResponse barC 4)
local notation "β" => betaRead observation half
local notation "k" => FirstPaReturn.exitIndex observation nontrivial half

private theorem seed_inside : seed ∈ burnolCompactCoPoissonClosedRange := burnolPaCombApproximation_mem 0

private theorem ambient_pa (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    (p : BurnolL2) ∈ burnolOriginalPaInL2 := Submodule.mem_map.mpr ⟨p,inside,rfl⟩

private theorem fourier_inside {p : BurnolPaAmbientCarrier} (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    F p ∈ burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside

/-- The actual inverse-side counted shell supplies the first adjoint coefficient. -/
def shellCoefficient : ℂ := burnolPaResolventSourceCoefficient barC (F seed)
local notation "α" => shellCoefficient observation half

theorem shell_coefficient_ne : α ≠ 0 := by
  let upper := 1+burnolPaCombSourceWidth 0
  have ordered : (1 : ℝ) ≤ upper := by dsimp [upper]; linarith [(burnolPaCombSourceWidth_bounds 0).1]
  have bounded : upper < 4 := by dsimp [upper]; linarith [(burnolPaCombSourceWidth_bounds 0).2]
  have larger : 1 < upper := by dsimp [upper]; linarith [(burnolPaCombSourceWidth_bounds 0).1]
  let wave := burnolReciprocalStepPhysicalState 1 upper (by norm_num) ordered bounded.le
  have counted : seed = (2 : ℂ) • F wave := by
    simp only [burnolPaCombApproximation,Nat.cast_zero,zero_add,wave,upper]
  have double : F (F wave) = wave := evenFaceFourier_involutive burnolUnscaledCommonGapRadius wave
  have reflected : F seed = (2 : ℂ) • wave := by rw [counted,map_smul,double]
  unfold shellCoefficient
  rw [reflected,map_smul,smul_eq_mul]
  have paid : burnolPaResolventSourceCoefficient barC wave =
      2 * ∫ x : ℝ in (1 : ℝ)..upper, (x : ℂ)^(-(barC).value) :=
    step_source_coefficient barC 1 upper (by norm_num) ordered bounded
  rw [paid]
  have exponent : 0 < (1-(barC).value).re := by
    simp only [Complex.sub_re,Complex.one_re]
    linarith [(barC).belowOne]
  have power : (upper : ℂ)^(1-(barC).value) ≠ 1 := by
    intro erased
    have normed := congrArg norm erased
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < upper),norm_one] at normed
    exact (Real.one_lt_rpow larger exponent).ne' normed
  have denominator : 1-(barC).value ≠ 0 := by
    intro erased
    rw [erased,Complex.zero_re] at exponent
    exact (lt_irrefl _ exponent)
  have integral := integral_cpow (a := (1 : ℝ)) (b := upper) (r := -(barC).value)
    (Or.inr ⟨by intro equal; apply denominator; linear_combination equal,
      by rw [uIcc_of_le ordered]; norm_num⟩)
  rw [integral,show -(barC).value+1 = 1-(barC).value by ring,Complex.ofReal_one,one_cpow]
  exact mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (div_ne_zero (sub_ne_zero.mpr power) denominator))

private theorem first_adjoint :
    ∃ correction : BurnolPaAmbientCarrier, correction ∈ burnolCompactCoPoissonClosedRange ∧
      J (seed : BurnolL2) = (seed : BurnolL2) + δ • ((correction : BurnolL2) + α • u) := by
  let input : ↥(burnolCompactCoPoissonClosedRange.toSubmodule) := ⟨F seed,fourier_inside seed_inside⟩
  let corrected := burnolPaSourceCorrection barC input
  have still := burnolPaSourceCorrection_mem barC input
  refine ⟨F corrected,fourier_inside still,?_⟩
  have step : burnolDirectRightResolvent ((barC).value/2) (F seed : BurnolL2) =
      (corrected : BurnolL2) + α • burnolUnitTailResponse barC 4 := by
    change _ = (burnolDirectRightResolvent ((barC).value/2) (F seed : BurnolL2) -
      α • burnolUnitTailResponse barC 4) + α • burnolUnitTailResponse barC 4
    abel
  have reflected := FiniteMobiusResolventFlux.fourier_R ((barC).value/2) (right_quarter barC) (F seed : BurnolL2)
  have twice : fourierL2 (F seed : BurnolL2) = (seed : BurnolL2) :=
    congrArg Subtype.val (evenFaceFourier_involutive burnolUnscaledCommonGapRadius seed)
  rw [step,map_add,map_smul,twice] at reflected
  have actual : OriginalKFullAdjointSource.sourceAdjoint c (seed : BurnolL2) =
      (F corrected : BurnolL2) + α • u := reflected.symm
  rw [sourceCayley_actual_adjoint,sourceAdjointCayley,actual]

include nontrivial in
private theorem unit_Q_ne : Q u ≠ 0 := by
  let conjugate := GeneratedRiemannZeroObservationAt.ofMathlibZero ActualAnalyticOwner
    (starRingEnd ℂ observation.coordinate) observation.conjugate_mathlibZero
  have cHalf : 1/2 < conjugate.coordinate.re := by
    change 1/2 < (starRingEnd ℂ observation.coordinate).re
    simpa only [Complex.conj_re] using half.down
  have notTrivial : ¬ ∃ j : Nat, conjugate.coordinate = -2*(j+1) :=
    observation.conjugate_nontrivial nontrivial
  let field := burnolZeroOwnedUnitTailState conjugate notTrivial cHalf
  let fu := F field
  have coord : burnolDivisionZeroCompletedMellinCoordinate conjugate cHalf = barC := by
    apply coordinate_eq
    rfl
  have actual : (fu : BurnolL2) = u := by
    change fourierL2 (burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate conjugate cHalf) 4) = _
    rw [coord]
  have physical : burnolEvenAmbientProjection (fu : BurnolL2) = fu :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self fu
  intro erased
  rw [← actual] at erased
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
    (burnolEvenAmbientProjection (fu : BurnolL2)) = 0 at erased
  rw [physical] at erased
  have inside := (Submodule.starProjection_apply_eq_zero_iff _).mp erased
  rw [Submodule.orthogonal_orthogonal] at inside
  have back := fourier_inside inside
  change F (F field) ∈ burnolCompactCoPoissonClosedRange at back
  have twice : F (F field) = field := evenFaceFourier_involutive burnolUnscaledCommonGapRadius field
  rw [twice] at back
  exact burnolZeroOwnedUnitTailState_notInPa conjugate notTrivial cHalf back

include nontrivial in
private theorem unit_energy :
    β u = inner ℂ (Q u) (Q u) := by
  let actual : BurnolPaAmbientCarrier := ⟨u,conjugate_F_unit_physical observation nontrivial half.down⟩
  have projection : burnolEvenAmbientProjection u = actual :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self actual
  have split : E u + Q u = actual :=
    (Submodule.starProjection_add_starProjection_orthogonal (burnolEvenAmbientProjection u)).trans projection
  have normal : Q u ∈ burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := Submodule.starProjection_apply_mem _ _
  have silent : inner ℂ (E u) (Q u) = 0 := normal _ (Submodule.starProjection_apply_mem _ _)
  change inner ℂ actual (Q u) = _
  rw [← split,inner_add_left,silent,zero_add]

include nontrivial in
/-- The first actual adjoint return price is the counted shell coefficient times the original Q-unit energy. -/
theorem first_return_amount :
    β (J (seed : BurnolL2)) = δ * α * inner ℂ (Q u) (Q u) := by
  obtain ⟨correction,inside,performed⟩ := first_adjoint observation half
  rw [performed,map_add β,map_smul β,map_add β,map_smul β,smul_eq_mul,smul_eq_mul,
    beta_zero_of_pa observation half (ambient_pa _ seed_inside),
    beta_zero_of_pa observation half (ambient_pa _ inside),zero_add,zero_add,
    unit_energy observation nontrivial half]
  ring

include nontrivial in
private theorem first_return_ne : β (J (seed : BurnolL2)) ≠ 0 := by
  rw [first_return_amount observation nontrivial half]
  exact mul_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne')
      (shell_coefficient_ne observation half))
    (fun gone => unit_Q_ne observation nontrivial half (inner_self_eq_zero.mp gone))

theorem exit_one : k = 1 := by
  have paid := FirstPaReturn.first_exit observation nontrivial half
  by_contra different
  have later : 1 < k := by have positive := paid.1; omega
  have still : J (seed : BurnolL2) ∈ burnolOriginalPaInL2 := by
    have before : (J^1) (seed : BurnolL2) ∈ burnolOriginalPaInL2 := paid.2.2.2 1 later
    simpa only [pow_one] using before
  exact first_return_ne observation nontrivial half (beta_zero_of_pa observation half still)

local notation "clock" => ReentryDifferenceClock.clock observation nontrivial half depth
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth

/-- Two consecutive original receipt prices suffice for the literal native return at every ordinal. -/
theorem actual_two_receipts (ordinal : Nat) :
    fee ordinal = clock ordinal 0 - clock ordinal 1 := by
  unfold ReentryDifferenceClock.fee
  rw [exit_one observation nontrivial half,Function.iterate_one]
  exact neg_sub _ _

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.TwoReceiptReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
