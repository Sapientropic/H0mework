import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.RelativeCellBound
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedContinuousInverse
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedError

open BurnolPhysicalState MeasureTheory Set OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource

open private trajectory clockTime BoundaryCountedGenerator.weight defect defect_derivative trajectory_continuous
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedGenerator
open private right_quarter
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "U" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolventCLM
local notation "T" => sourceCayley
local notation "I" => BoundaryCountedContinuousInverse.index
local notation "E" => BoundaryCountedContinuousInverse.finiteEquiv

private def flow (h : ℝ) : End :=
  (Real.exp (-h/2) : ℂ) • (U (-h)).toContinuousLinearEquiv.toContinuousLinearMap

private theorem warp (h : ℝ) (value : BurnolL2) :
    trajectory value (Real.exp h-1) = flow h value := by
  have clock : clockTime (Real.exp h-1) = 2*h := by
    rw [clockTime, show 1+(Real.exp h-1)=Real.exp h by ring, Real.log_exp]
  have factor : BoundaryCountedGenerator.weight (Real.exp h-1) = (Real.exp (-h/2) : ℂ) := by
    rw [BoundaryCountedGenerator.weight, clock, positiveMellinQuarterRightResolventCharacter_exp, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [trajectory, factor, clock, show -(2*h)/2=-h by ring]
  rfl

private theorem flow_trajectory (t : ℝ) (nonnegative : 0 ≤ t) (value : BurnolL2) :
    trajectory value t = flow (Real.log (1+t)) value := by
  have same := warp (Real.log (1+t)) value
  rw [Real.exp_log (by linarith), add_sub_cancel_left] at same
  exact same

private theorem flow_zero (value : BurnolL2) : flow 0 value = value := by
  change (Real.exp (-(0:ℝ)/2) : ℂ) • U (-(0:ℝ)) value = _
  simp only [neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one, one_smul, burnolMultiplicativeDilation_zero]

private theorem flow_add (s t : ℝ) (value : BurnolL2) :
    flow (s+t) value = flow s (flow t value) := by
  change (Real.exp (-(s+t)/2) : ℂ) • U (-(s+t)) value =
    (Real.exp (-s/2) : ℂ) • U (-s) ((Real.exp (-t/2) : ℂ) • U (-t) value)
  rw [map_smul, smul_smul, burnolMultiplicativeDilation_add, ← Complex.ofReal_mul, ← Real.exp_add,
    show -s/2 + -t/2 = -(s+t)/2 by ring, show -s + -t = -(s+t) by ring]

private theorem flow_norm (h : ℝ) (nonnegative : 0 ≤ h) (value : BurnolL2) :
    ‖flow h value‖ ≤ ‖value‖ := by
  change ‖(Real.exp (-h/2) : ℂ) • U (-h) value‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), LinearIsometryEquiv.norm_map]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))

private def amplitude (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  2 / sourceDamping coordinate

private theorem amplitude_pos (coordinate : BurnolCompletedMellinCoordinate) : 0 < amplitude coordinate :=
  div_pos (by norm_num) (sourceDamping_pos coordinate)

private theorem resolvent_bound (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ‖R coordinate value‖ ≤ amplitude coordinate * ‖value‖ := by
  have source : (sourceDamping coordinate : ℂ) • R coordinate value = T coordinate value - value := by
    rw [sourceCayley_apply]
    change _ = value + (sourceDamping coordinate : ℂ) • R coordinate value - value
    abel
  have comparison := norm_sub_le (T coordinate value) value
  rw [← source, norm_smul, Complex.norm_real, Real.norm_of_nonneg (sourceDamping_pos coordinate).le,
    sourceCayley_norm] at comparison
  calc
    _ ≤ (‖value‖ + ‖value‖) / sourceDamping coordinate :=
      (le_div_iff₀ (sourceDamping_pos coordinate)).mpr (by linarith only [comparison])
    _ = _ := by unfold amplitude; ring

private def speed (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ‖coordinate.value-1‖ * amplitude coordinate + 2

private theorem speed_nonneg (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ speed coordinate :=
  add_nonneg (mul_nonneg (norm_nonneg _) (amplitude_pos coordinate).le) (by norm_num)

private def slope (coordinate : BurnolCompletedMellinCoordinate) : End :=
  (coordinate.value-1) • R coordinate + (2 : ℂ) • 1

private theorem slope_bound (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ‖slope coordinate value‖ ≤ speed coordinate * ‖value‖ := by
  change ‖(coordinate.value-1) • R coordinate value + (2 : ℂ) • value‖ ≤ _
  calc
    _ ≤ ‖(coordinate.value-1) • R coordinate value‖ + ‖(2 : ℂ) • value‖ := norm_add_le _ _
    _ ≤ ‖coordinate.value-1‖ * (amplitude coordinate * ‖value‖) + 2*‖value‖ := by
      simp only [norm_smul, Complex.norm_ofNat]
      exact add_le_add (mul_le_mul_of_nonneg_left (resolvent_bound coordinate value) (norm_nonneg (coordinate.value-1))) le_rfl
    _ = _ := by unfold speed; ring

private theorem slope_commutes (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    slope coordinate (R coordinate value) = R coordinate (slope coordinate value) := by
  change (coordinate.value-1) • R coordinate (R coordinate value) + (2 : ℂ) • R coordinate value =
    R coordinate ((coordinate.value-1) • R coordinate value + (2 : ℂ) • value)
  rw [map_add, map_smul, map_smul]

private theorem flow_derivative_zero (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    HasDerivAt (fun h : ℝ => flow h (R coordinate value)) (slope coordinate value) 0 := by
  have time : HasDerivAt (fun h : ℝ => Real.exp h-1) (1 : ℝ) 0 := by
    simpa only [Real.exp_zero] using (Real.hasDerivAt_exp (0 : ℝ)).sub_const 1
  have derivative := defect_derivative (coordinate.value/2) (right_quarter coordinate) value
  have source := (derivative.scomp_of_eq 0 time (by simp)).add_const (R coordinate value)
  have same (h : ℝ) : defect (-(R coordinate value)) (Real.exp h-1) + R coordinate value =
      flow h (R coordinate value) := by
    rw [defect, warp, map_neg]
    abel
  have coefficient : (1 : ℝ) • (2 : ℝ) •
      (value - (coordinate.value/2-1/2) • (-burnolDirectRightResolvent (coordinate.value/2) value)) =
      slope coordinate value := by
    change _ = (coordinate.value-1) • burnolDirectRightResolvent (coordinate.value/2) value + (2 : ℂ) • value
    simp only [one_smul, smul_sub, smul_neg]
    module
  change HasDerivAt (fun h => defect (-(R coordinate value)) (Real.exp h-1) + R coordinate value) _ 0 at source
  rw [coefficient, show (fun h => defect (-(R coordinate value)) (Real.exp h-1) + R coordinate value) =
    (fun h => flow h (R coordinate value)) from funext same] at source
  exact source

private theorem flow_derivative (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) :
    HasDerivAt (fun t : ℝ => flow t (R coordinate value)) (flow h (slope coordinate value)) h := by
  have shifted := (flow_derivative_zero coordinate value).scomp_of_eq h ((hasDerivAt_id h).sub_const h) (sub_self h).symm
  have source := ((flow h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt h shifted
  have same : (fun t : ℝ => flow h (flow (t-h) (R coordinate value))) =
      fun t : ℝ => flow t (R coordinate value) := by
    funext t
    rw [← flow_add, show h+(t-h)=t by ring]
  change HasDerivAt (fun t : ℝ => flow h (flow (t-h) (R coordinate value)))
    (flow h ((1 : ℝ) • slope coordinate value)) h at source
  rw [same, one_smul] at source
  exact source

private theorem flow_lipschitz (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    ‖flow h (R coordinate value) - R coordinate value‖ ≤ h * (speed coordinate * ‖value‖) := by
  have source := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (flow_derivative coordinate value t).hasDerivWithinAt)
    (fun t inside => (flow_norm t inside.1 (slope coordinate value)).trans (slope_bound coordinate value))
    ⟨le_rfl,nonnegative⟩ ⟨nonnegative,le_rfl⟩
  rw [flow_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg nonnegative] at source
  exact source.trans_eq (mul_comm _ _)

private theorem flow_quadratic (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    let x := -(R coordinate (R coordinate value))
    let g := R coordinate (-slope coordinate value)
    ‖flow h x - x - h • g‖ ≤ h^2 * (speed coordinate)^2 * ‖value‖ := by
  let x := -(R coordinate (R coordinate value))
  let g := R coordinate (-slope coordinate value)
  have direction : slope coordinate (-(R coordinate value)) = g := by
    rw [map_neg, slope_commutes, ← map_neg]
  have path (s : ℝ) : HasDerivAt (fun t => flow t x - x - t • g) (flow s g - g) s := by
    have moved := flow_derivative coordinate (-(R coordinate value)) s
    have same : R coordinate (-(R coordinate value)) = x := map_neg _ _
    rw [same, direction] at moved
    have linear : HasDerivAt (fun t : ℝ => t • g) g s := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id s).smul_const g
    exact (moved.sub_const x).sub linear
  have speedPos := speed_nonneg coordinate
  have control (s : ℝ) (inside : s ∈ Icc (0 : ℝ) h) :
      ‖flow s g-g‖ ≤ h * ((speed coordinate)^2 * ‖value‖) := by
    have first := flow_lipschitz coordinate (-slope coordinate value) s inside.1
    rw [norm_neg] at first
    calc
      _ ≤ s * (speed coordinate * ‖slope coordinate value‖) := first
      _ ≤ s * (speed coordinate * (speed coordinate * ‖value‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (slope_bound coordinate value) speedPos) inside.1
      _ ≤ h * (speed coordinate * (speed coordinate * ‖value‖)) :=
        mul_le_mul_of_nonneg_right inside.2 (by positivity)
      _ = _ := by ring
  have bound := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (path s).hasDerivWithinAt) control ⟨le_rfl,nonnegative⟩ ⟨nonnegative,le_rfl⟩
  simp only [flow_zero, sub_self, zero_smul, sub_zero, Real.norm_eq_abs, abs_of_nonneg nonnegative] at bound
  exact bound.trans_eq (by ring)

private def cellError (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  (speed coordinate)^2 + amplitude coordinate * speed coordinate

private theorem cellError_nonneg (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ cellError coordinate :=
  add_nonneg (sq_nonneg _) (mul_nonneg (amplitude_pos coordinate).le (speed_nonneg coordinate))

private theorem local_error (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (t : ℝ) (nonnegative : 0 ≤ t) :
    let x := -(R coordinate (R coordinate value))
    let g := R coordinate (-slope coordinate value)
    ‖defect x t - t • (-g)‖ ≤ (cellError coordinate * ‖value‖) * t^2 := by
  let x := -(R coordinate (R coordinate value))
  let g := R coordinate (-slope coordinate value)
  let h := Real.log (1+t)
  have scale : 0 < 1+t := by linarith
  have hPos : 0 ≤ h := Real.log_nonneg (by linarith)
  have short : h ≤ t := by
    have bound := Real.log_le_sub_one_of_pos scale
    change h ≤ t
    linarith
  have loss : t-h ≤ t^2 := by
    have below := Real.one_sub_inv_le_log_of_pos scale
    calc
      _ ≤ t - (1-(1+t)⁻¹) := by linarith only [below]
      _ = t^2/(1+t) := by field_simp; ring
      _ ≤ _ := (div_le_iff₀ scale).mpr (le_mul_of_one_le_right (sq_nonneg _) (by linarith))
  have changed : defect x t - t • (-g) = -(flow h x-x-h•g) + (t-h) • g := by
    rw [defect, flow_trajectory t nonnegative]
    change x - flow h x - t • (-g) = _
    module
  have square : h^2 ≤ t^2 := (sq_le_sq₀ hPos nonnegative).mpr short
  have first : ‖-(flow h x-x-h•g)‖ ≤ t^2 * (speed coordinate)^2 * ‖value‖ := by
    rw [norm_neg]
    exact (flow_quadratic coordinate value h hPos).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right square (sq_nonneg _)) (norm_nonneg _))
  have source : ‖g‖ ≤ amplitude coordinate * (speed coordinate * ‖value‖) := by
    change ‖R coordinate (-slope coordinate value)‖ ≤ _
    have bound := resolvent_bound coordinate (-slope coordinate value)
    rw [norm_neg] at bound
    exact bound.trans (mul_le_mul_of_nonneg_left (slope_bound coordinate value) (amplitude_pos coordinate).le)
  have second : ‖(t-h) • g‖ ≤ t^2 * (amplitude coordinate * (speed coordinate * ‖value‖)) := by
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr short)]
    calc
      _ ≤ (t-h) * (amplitude coordinate * (speed coordinate * ‖value‖)) :=
        mul_le_mul_of_nonneg_left source (sub_nonneg.mpr short)
      _ ≤ _ := mul_le_mul_of_nonneg_right loss
        (mul_nonneg (amplitude_pos coordinate).le (mul_nonneg (speed_nonneg coordinate) (norm_nonneg _)))
  change ‖defect x t - t • (-g)‖ ≤ _
  rw [changed]
  exact ((norm_add_le _ _).trans (add_le_add first second)).trans_eq (by unfold cellError; ring)

private theorem finite_clock_error (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (N : Nat) (positive : 0 < N) :
    ‖BoundaryCountedGenerator.clock (coordinate.value/2) N positive (-(R coordinate (R coordinate value))) -
      R coordinate value‖ ≤ cellError coordinate * ‖value‖ / (N : ℝ) := by
  let x := -(R coordinate (R coordinate value))
  let g := R coordinate (-slope coordinate value)
  have exactRate : (1/2 : ℝ) • (-g) + (coordinate.value/2-1/2) • x = R coordinate value := by
    change (1/2 : ℝ) • (-(R coordinate (-slope coordinate value))) +
      (coordinate.value/2-1/2) • (-(R coordinate (R coordinate value))) = _
    rw [map_neg, neg_neg]
    change (1/2 : ℝ) • R coordinate ((coordinate.value-1) • R coordinate value + (2 : ℂ) • value) +
      (coordinate.value/2-1/2) • (-(R coordinate (R coordinate value))) = _
    simp only [map_add, map_smul, smul_add, smul_neg]
    module
  have paid := SourceGeneratedRelativeCell.integral_error (-g)
    (mul_nonneg (cellError_nonneg coordinate) (norm_nonneg value))
    (by exact_mod_cast positive : (1 : ℝ) ≤ N)
    (continuousOn_const.sub (trajectory_continuous x))
    (fun t inside => local_error coordinate value t inside.1)
  change ‖BoundaryCountedGenerator.clock (coordinate.value/2) N positive x - R coordinate value‖ ≤ _
  rw [BoundaryCountedGenerator.clock_source, ← exactRate, add_sub_add_right_eq_sub]
  exact paid

/-- The original previous input and damping pay the whole finite-error budget. -/
def budget (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ((((coordinate.value/2).re-1/4)/2)⁻¹) * cellError coordinate

/-- The finite inverse pays an explicit error on the actual original R-born range. -/
theorem inverse_error (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (n : Nat) :
    ‖-(E (coordinate.value/2) (right_quarter coordinate) n).symm (R coordinate value) -
      R coordinate (R coordinate value)‖ ≤
      budget coordinate * ‖value‖ / (I (coordinate.value/2) n : ℝ) := by
  let z := coordinate.value/2
  let right := right_quarter coordinate
  let e := E z right n
  let old := R coordinate value
  let next := R coordinate old
  let k := ((z.re-1/4)/2)⁻¹
  have kNonneg : 0 ≤ k := inv_nonneg.mpr (by linarith)
  have residual : ‖e (-next) - old‖ ≤ cellError coordinate * ‖value‖ / (I z n : ℝ) := by
    rw [BoundaryCountedContinuousInverse.finiteEquiv_source]
    exact finite_clock_error coordinate value _ _
  have difference : -e.symm old - next = e.symm (e (-next) - old) := by
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
    abel
  change ‖-e.symm old-next‖ ≤ _
  rw [difference]
  calc
    _ ≤ k * ‖e (-next)-old‖ := BoundaryCountedContinuousInverse.inverse_bound z right n _
    _ ≤ k * (cellError coordinate * ‖value‖ / (I z n : ℝ)) := mul_le_mul_of_nonneg_left residual kNonneg
    _ = _ := by unfold budget; dsimp only [k,z]; ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

private theorem literal_next (ordinal : Nat) : raw (ordinal+1) = R c (raw ordinal) := by
  rw [OriginalKCombFirstFullSourceDynamics.raw_successor, OriginalKCombCofinalRAction.original_R_direct observation nontrivial half]
  rfl

/-- One finite source clock pays the full literal next field on each R-born ordinal. -/
theorem actual_next_error (ordinal n : Nat) :
    let approx := -(E ((c).value/2) (right_quarter c) n).symm (raw (ordinal+1))
    ‖approx - raw (ordinal+2)‖ ≤ budget c * ‖raw ordinal‖ / (I ((c).value/2) n : ℝ) := by
  dsimp only
  rw [show ordinal+2 = (ordinal+1)+1 by omega,
    literal_next observation nontrivial half depth (ordinal+1), literal_next observation nontrivial half depth ordinal]
  exact inverse_error c (raw ordinal) n

/-- The tolerance is priced before either physical port is read. -/
theorem actual_accuracy (ordinal : Nat) (epsilon : ℝ) (positive : 0 < epsilon) :
    let n := ⌈budget c * ‖raw ordinal‖ / epsilon⌉₊
    let approx := -(E ((c).value/2) (right_quarter c) n).symm (raw (ordinal+1))
    ‖approx - raw (ordinal+2)‖ < epsilon := by
  let n := ⌈budget c * ‖raw ordinal‖ / epsilon⌉₊
  let N := I ((c).value/2) n
  have paid := actual_next_error observation nontrivial half depth ordinal n
  have larger : n < N := by
    dsimp only [N, BoundaryCountedContinuousInverse.index]
    omega
  have cutoff : budget c * ‖raw ordinal‖ / epsilon < (N : ℝ) :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast larger)
  have indexPositive : (0 : ℝ) < N := by exact_mod_cast ((Nat.zero_le n).trans_lt larger)
  exact paid.trans_lt ((div_lt_iff₀ indexPositive).mpr
    (by simpa only [mul_comm] using (div_lt_iff₀ positive).mp cutoff))

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedError
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
