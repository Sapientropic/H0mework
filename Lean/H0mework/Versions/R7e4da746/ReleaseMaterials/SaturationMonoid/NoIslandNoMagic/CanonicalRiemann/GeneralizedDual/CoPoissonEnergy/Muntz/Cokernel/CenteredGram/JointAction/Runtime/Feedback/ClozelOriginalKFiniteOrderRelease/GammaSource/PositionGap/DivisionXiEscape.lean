import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.AdjointGerm
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.DivisionXiEscape

open Complex Filter Set BurnolPhysicalState
open OriginalUnitXiConjugateOrderSource OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKFiniteOrderRelease.PositionGapCayley.AdjointGerm
open scoped Topology

open private actual_comb_heat_factor coefficient_analytic from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.Source
open private bare_factor bare_analytic bare_nonzero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
open private original_R_iterate_gap from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalRAction.Source
open private seed_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
open private right_quarter below_half damping_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
open private source_left_inverse source_right_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "T" => sourceCayley
local notation "δ" => sourceDamping
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "owner" => ActualAnalyticOwner
local notation "order" => generatedRiemannXiZeroOrder owner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum owner
local notation "seed" => burnolPaCombApproximation 0

private theorem original_seed_read (w : ℂ) (right : 1/4 < w.re) (below : w.re < 1/2) :
    M (burnolDivisionCompletedMellinCoordinate w right below) (seed : BurnolL2) =
      riemannZeta (2*w) * burnolPaCombResponseCoefficient (1-2*w) 0 := by
  let chart := burnolDivisionCompletedMellinCoordinate w right below
  have bridge := burnolGenericHomogeneousGammaMellinBridge seed chart
  rw [burnolDivisionCompletedMellinCoordinate_value, show (2*w)/2=w by ring] at bridge
  have gammaNe : Gammaℝ (2*w) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    simp only [Complex.mul_re]
    norm_num
    linarith)
  have heat : burnolDivisionNormalizedPhysicalHeatMellin seed w = 2*burnolCompletedMellinEvaluator chart seed := by
    unfold burnolDivisionNormalizedPhysicalHeatMellin
    change Gammaℝ (2*w)*burnolCompletedMellinEvaluator chart seed =
      (1/2:ℂ)*mellin (burnolGenericGaussianHeatPairTotal (seed : BurnolL2)) w at bridge
    field_simp [gammaNe]
    linear_combination -2*bridge
  have restricted := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f seed)
    (burnolAmbientCompletedMellinEvaluator_restrict chart)
  change M chart (seed : BurnolL2) = burnolCompletedMellinEvaluator chart seed at restricted
  have actual := heat.symm.trans (actual_comb_heat_factor 0 w right below)
  rw [restricted]
  linear_combination actual/2

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "origR" => OriginalKCombPhysicalAction.R observation nontrivial half
local notation "currentRaw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "m" => order observation.coordinate

private theorem original_power_read (j : Nat) (w : ℂ) (right : 1/4 < w.re) (below : w.re < 1/2) :
    M (burnolDivisionCompletedMellinCoordinate w right below) (((origR).toLinearMap^j) (seed : BurnolL2)) =
      (-(1/(observation.coordinate/2+w-1/2)))^j *
        M (burnolDivisionCompletedMellinCoordinate w right below) (seed : BurnolL2) := by
  induction j with
  | zero =>
    change M (burnolDivisionCompletedMellinCoordinate w right below) (seed : BurnolL2) =
      (-(1/(observation.coordinate/2+w-1/2)))^0 *
        M (burnolDivisionCompletedMellinCoordinate w right below) (seed : BurnolL2)
    rw [pow_zero, one_mul]
  | succ j earlier =>
    rw [pow_succ', Module.End.mul_apply]
    change M _ (origR (((origR).toLinearMap^j) (seed : BurnolL2))) = _
    rw [OriginalKCombCofinalRAction.original_R_direct]
    rw [CombSource.Pricing.ambient_R_scalar_action _
      (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) _
      (original_R_iterate_gap observation nontrivial half j) w right below,
      earlier, ← mul_assoc, ← pow_succ']

/-- The literal cofinal field keeps the exact comb factor and its original R power. -/
theorem actual_division_ambient_price (ordinal : Nat) (w : ℂ) (right : 1/4 < w.re) (below : w.re < 1/2) :
    M (burnolDivisionCompletedMellinCoordinate w right below) (currentRaw ordinal) =
      (-(1/(observation.coordinate/2+w-1/2)))^(sourceIndex observation ordinal) *
        (riemannZeta (2*w) * burnolPaCombResponseCoefficient (1-2*w) 0) := by
  rw [OriginalKCombFirstFullSourceDynamics.raw_xi_source,
    original_power_read observation nontrivial half _ w right below, original_seed_read]
  rfl

/-- The original Xi leading coefficient, carried through the same actual R power and the Cayley chart. -/
def divisionLeading (ordinal : Nat) (t : ℝ) : ℂ :=
  (-(1/denominator coord t))^(sourceIndex observation ordinal) *
    ((2:ℂ)*denominator coord t)^m *
    (bare (d coord).value (probe coord t).value *
      burnolPaCombResponseCoefficient (1-(probe coord t).value) 0)

private theorem leading_continuous (ordinal : Nat) : ContinuousAt (divisionLeading observation half ordinal) 0 := by
  let w (t : ℝ) := (probe coord t).value/2
  have den : ContinuousAt (denominator coord) 0 := (denominator_continuous coord).continuousAt
  have resolvent : ContinuousAt (fun t : ℝ => -(1/denominator coord t)) 0 :=
    (continuousAt_const.div den (denominator_nonzero coord 0)).neg
  have scaled : ContinuousAt (fun t : ℝ => (2:ℂ)*denominator coord t) 0 := continuousAt_const.mul den
  have shift : ContinuousAt (fun t => (probe coord t).value) 0 := (probe_continuous coord).continuousAt
  have bareAt : ContinuousAt (bare (d coord).value) (probe coord 0).value := by
    rw [probe_zero]
    exact (bare_analytic (d coord)).continuousAt
  have shape : ContinuousAt w 0 := shift.div_const (2:ℂ)
  have inside : w 0 ∈ burnolPhysicalHeatMellinStrip :=
    ⟨lt_trans (by norm_num) (right_quarter (probe coord 0)), below_half (probe coord 0)⟩
  have response := ((coefficient_analytic 0 (w 0) inside).continuousAt.comp shape)
  have responseAt : ContinuousAt (fun t => burnolPaCombResponseCoefficient (1-(probe coord t).value) 0) 0 := by
    have align (t : ℝ) : 1 - 2*w t = 1 - (probe coord t).value := by
      dsimp only [w]
      ring
    simpa only [Function.comp_def, align] using response
  have bareComp : ContinuousAt (fun t : ℝ => bare (d coord).value (probe coord t).value) 0 :=
    ContinuousAt.comp' (f := fun t : ℝ => (probe coord t).value) bareAt shift
  exact ((resolvent.pow _).mul (scaled.pow _)).mul (bareComp.mul responseAt)

private theorem leading_nonzero (ordinal : Nat) : divisionLeading observation half ordinal 0 ≠ 0 := by
  have denom := denominator_nonzero coord 0
  have first := pow_ne_zero (sourceIndex observation ordinal) (neg_ne_zero.mpr (div_ne_zero one_ne_zero denom))
  have second := pow_ne_zero m (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) denom)
  have response := burnolPaCombResponseCoefficient_ne_zero (1-(d coord).value)
    (by rw [Complex.sub_re, Complex.one_re]; linarith [(d coord).belowOne]) 0
  simpa only [divisionLeading, probe_zero] using
    (mul_ne_zero (mul_ne_zero first second) (mul_ne_zero (bare_nonzero (d coord)) response))

/-- The original Xi germ supplies exactly its conjugate multiplicity to the actual cofinal raw field. -/
theorem actual_division_germ (ordinal : Nat) :
    (fun t => M (probe coord t) (currentRaw ordinal)) =ᶠ[𝓝 (0:ℝ)]
      fun t => (factor coord t)^m * divisionLeading observation half ordinal t := by
  have toward : Tendsto (fun t => (probe coord t).value) (𝓝 (0:ℝ)) (𝓝 (d coord).value) := by
    rw [← probe_zero coord]
    exact (probe_continuous coord).continuousAt
  filter_upwards [toward.eventually (bare_factor (d coord))] with t zeta
  let reader := probe coord t
  let w := reader.value/2
  have right : 1/4 < w.re := right_quarter reader
  have below : w.re < 1/2 := below_half reader
  have chart : burnolDivisionCompletedMellinCoordinate w right below = reader := by
    apply coordinate_eq
    change 2*(reader.value/2)=reader.value
    ring
  have scale : 2*w = reader.value := by dsimp only [w]; ring
  have source := actual_division_ambient_price observation nontrivial half depth ordinal w right below
  rw [chart, scale] at source
  change M reader (currentRaw ordinal) =
    (-(1/denominator coord t))^(sourceIndex observation ordinal) *
      (riemannZeta reader.value * burnolPaCombResponseCoefficient (1-reader.value) 0) at source
  change riemannZeta reader.value = (reader.value-(d coord).value)^order (d coord).value *
    bare (d coord).value reader.value at zeta
  have sameOrder : order (d coord).value = m := actual_original_Xi_order_conjugate coord
  rw [sameOrder] at zeta
  have factorized : reader.value-(d coord).value = factor coord t * (2*denominator coord t) := by
    calc
      reader.value-(d coord).value = (t:ℂ)*Complex.I := by
        dsimp only [reader,probe,OriginalPrimitiveRankBalance.conjugateCoordinate]
        ring
      _ = 2*(factor coord t*denominator coord t) := by
        rw [factor_read, div_mul_cancel₀ _ (denominator_nonzero coord t)]
        ring
      _ = _ := by ring
  change M reader (currentRaw ordinal) = (factor coord t)^m * divisionLeading observation half ordinal t
  rw [source, zeta, factorized, mul_pow, divisionLeading]
  dsimp only [reader]
  ring

/-- Each original literal frame leaves its position gap at the same exact Xi depth. -/
theorem actual_division_exact_adjoint_escape (ordinal : Nat) :
    (∀ i < m, M (d coord) ((((T coord).adjoint)^i) (currentRaw ordinal)) = 0) ∧
      M (d coord) ((((T coord).adjoint)^m) (currentRaw ordinal)) = divisionLeading observation half ordinal 0 ∧
      divisionLeading observation half ordinal 0 ≠ 0 ∧
      (((T coord).adjoint)^m) (currentRaw ordinal) ∈ G ∧
      ¬ (((T coord).adjoint)^(m+1)) (currentRaw ordinal) ∈ G := by
  have gap := OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal
  have even : reflectL2 (currentRaw ordinal) = currentRaw ordinal := by
    rw [actual_raw_field observation nontrivial half]
    exact actual_iterate_even coord seed seed_even _
  have live := leading_nonzero observation half ordinal
  obtain ⟨before, read, inside, outside⟩ := actual_adjoint_germ_exit coord (currentRaw ordinal) gap even m
    (divisionLeading observation half ordinal) (leading_continuous observation half ordinal) live
    (actual_division_germ observation nontrivial half depth ordinal)
  exact ⟨before, read, live, inside, outside⟩

private theorem denominator_zero_read : denominator coord 0 = (δ coord : ℂ) := by
  unfold denominator
  rw [probe_zero]
  exact (damping_read coord).symm

/-- The two literal frames' first nonzero reads retain the original R action at the same probe. -/
theorem actual_division_exact_price_next (ordinal : Nat) :
    divisionLeading observation half (ordinal+1) 0 =
      (-(1/(δ coord:ℂ))) * divisionLeading observation half ordinal 0 := by
  have clock : sourceIndex observation (ordinal+1) = sourceIndex observation ordinal + 1 := by
    unfold sourceIndex
    omega
  rw [divisionLeading, divisionLeading, clock, pow_succ', denominator_zero_read observation half]
  ring

private theorem adjoint_R (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    (T c).adjoint (burnolDirectRightResolventCLM c v) =
      burnolDirectRightResolventCLM c ((T c).adjoint v) := by
  have left := source_left_inverse c v
  have right := source_right_inverse c v
  rw [sourceCayley_apply, map_add, map_smul] at left
  rw [sourceCayley_apply] at right
  have nonzero : (δ c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'
  apply smul_right_injective BurnolL2 nonzero
  exact add_left_cancel (left.trans right.symm)

private theorem adjoint_powers_R (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (n : Nat) :
    (((T c).adjoint)^n) (burnolDirectRightResolventCLM c v) =
      burnolDirectRightResolventCLM c ((((T c).adjoint)^n) v) := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n earlier => simp only [pow_succ', mul_apply_eq_comp, earlier, adjoint_R]

/-- The adjoint terminal fields of the original two frames retain the actual original R action. -/
theorem actual_division_adjoint_terminal_next (ordinal : Nat) :
    (((T coord).adjoint)^m) (currentRaw (ordinal+1)) = origR ((((T coord).adjoint)^m) (currentRaw ordinal)) := by
  simp only [OriginalKCombFirstFullSourceDynamics.raw_successor, OriginalKCombCofinalRAction.original_R_direct]
  exact adjoint_powers_R coord (currentRaw ordinal) m

end OriginalKFiniteOrderRelease.PositionGapCayley.DivisionXiEscape
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
