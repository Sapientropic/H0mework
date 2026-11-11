import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Arithmetic
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "D" => burnolMultiplicativeDilation
local notation "Q" => pairedBurnolMultiplicativeDilation
local notation "A" => sourceAnnulusCut

private theorem grid_first_cell (raw : ℝ → ℂ) (x : ℝ) (lower : q/2 < x) :
    (∑ n ∈ DualSourceRaw.channels x, raw ((n : ℝ) * |x|)) = if x ≤ q then raw x else 0 := by
  have positive : 0 < x := by linarith
  rw [DualSourceRaw.channels, abs_of_pos positive]
  by_cases inside : x ≤ q
  · have index : ⌊q/x⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ q/x)]
      constructor
      · norm_num
        exact (le_div_iff₀ positive).mpr (by simpa only [one_mul] using inside)
      · norm_num
        exact (div_lt_iff₀ positive).mpr (by linarith)
    rw [index, Finset.Icc_self, Finset.sum_singleton, if_pos inside]
    simp
  · have index : ⌊q/x⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one positive).mpr (lt_of_not_ge inside))
    rw [index, if_neg inside]
    simp

private theorem grid_outside (raw : ℝ → ℂ) (x : ℝ) (outside : q < x) :
    (∑ n ∈ DualSourceRaw.channels x, raw ((n : ℝ) * |x|)) = 0 := by
  have source := grid_first_cell raw x (by linarith)
  rw [if_neg (not_le.mpr outside)] at source
  exact source

def countedRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  -burnolTateReciprocalRaw (PositionCounting.eventRaw c) x - DualSourceRaw.eventRaw c x

private theorem counted_source (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    countedKernel c zero = -T (PositionCounting.value c zero) - CountingDual.value c := by
  rw [countedKernel, map_sub, map_neg, burnolTateReciprocalL2_involutive]

private theorem counted_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    (countedKernel c zero : ℝ → ℂ) =ᵐ[volume] countedRaw c := by
  let position := PositionCounting.value c zero
  have represented := PositionCounting.value_coeFn c zero
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp position)
    ((Lp.memLp position).ae_eq represented) represented
  have reciprocal := (burnolTateReciprocalL2_coeFn position).trans pulled
  rw [counted_source]
  filter_upwards [Lp.coeFn_sub (-T position) (CountingDual.value c),
    Lp.coeFn_neg (T position), reciprocal, DualLanding.original_coeFn c]
    with x subtraction negative tate dual
  rw [subtraction, Pi.sub_apply, negative, Pi.neg_apply, tate, dual]
  rfl

private theorem count_dilation_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) :
    ∀ᵐ x : ℝ ∂volume, D h (countedKernel c zero) x =
      (Real.exp (h/2) : ℂ) * countedRaw c (Real.exp h * x) := by
  have source := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (Real.exp_ne_zero h)).ae
    (counted_raw c zero)
  filter_upwards [burnolMultiplicativeDilation_coeFn h (countedKernel c zero), source] with x dilation raw
  rw [dilation]
  change (countedKernel c zero) (Real.exp h * x) = countedRaw c (Real.exp h * x) at raw
  change (Real.exp (h/2) : ℂ) * (countedKernel c zero) (Real.exp h * x) = _
  rw [raw]

private theorem reciprocal_threshold (h x : ℝ) (positive : 0 < x) :
    (Real.exp h * x)⁻¹ ≤ q ↔ 4 * Real.exp (-h) ≤ x := by
  have scale : 0 < Real.exp h * x := mul_pos (Real.exp_pos _) positive
  rw [inv_le_comm₀ scale (by norm_num : (0 : ℝ) < q)]
  norm_num
  constructor
  · intro order
    have read := mul_le_mul_of_nonneg_left order (Real.exp_pos (-h)).le
    have inverse : Real.exp (-h) * (Real.exp h * x) = x := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [inverse] at read
    nlinarith
  · intro order
    have read := mul_le_mul_of_nonneg_left order (Real.exp_pos h).le
    have inverse : Real.exp h * (4 * Real.exp (-h)) = 4 := by
      rw [mul_comm 4, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [inverse] at read
    exact read

private theorem lower_threshold (h x : ℝ) :
    Real.exp (-h) * x ≤ q ↔ x ≤ q * Real.exp h := by
  rw [Real.exp_neg, ← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos h)]

private theorem half_density (h : ℝ) :
    (Real.exp (h/2) : ℂ) * (Real.exp h : ℂ)⁻¹ = (Real.exp (-h/2) : ℂ) := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  ring

/-- The original moving K source reads exactly its n=1 position and B channels on both true collars. -/
theorem actual_joint_input_arithmetic_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    ∀ᵐ x : ℝ ∂volume, ∀ _inside : x ∈ Ioo q 4,
      jointInput c zero h x = -(Real.exp (-h/2) : ℂ)/2 *
        ((if x ≤ q * Real.exp h then burnolRieszSingleFourierSourceRaw c (Real.exp (-h)*x) else 0) +
          (x : ℂ)⁻¹ * (if 4 * Real.exp (-h) ≤ x then positionSource c ((Real.exp h*x)⁻¹) else 0)) := by
  have minusLower : 1/2 ≤ Real.exp (-h) := by
    have order := Real.exp_le_exp.mpr (neg_le_neg bounded)
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using order
  have minusUpper : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have plusLower : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr nonnegative
  have plusUpper : Real.exp h ≤ 2 := by
    have order := Real.exp_le_exp.mpr bounded
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at order
  filter_upwards [sourceAnnulusCut_coeFn (Q h (countedKernel c zero)),
    Lp.coeFn_smul (1/2 : ℂ) (D h (countedKernel c zero) + D (-h) (countedKernel c zero)),
    Lp.coeFn_add (D h (countedKernel c zero)) (D (-h) (countedKernel c zero)),
    count_dilation_raw c zero h, count_dilation_raw c zero (-h)] with x cut paired added plus minus inside
  have positive : 0 < x := by linarith [inside.1]
  have xp : 0 < Real.exp h * x := mul_pos (Real.exp_pos _) positive
  have xm : 0 < Real.exp (-h) * x := mul_pos (Real.exp_pos _) positive
  have pp : q < Real.exp h * x := by nlinarith [inside.1]
  have mm : q < (Real.exp (-h)*x)⁻¹ := by
    rw [← one_div, lt_div_iff₀ xm]
    nlinarith [inside.2]
  have pl : q/2 < (Real.exp h*x)⁻¹ := by
    rw [← one_div, lt_div_iff₀ xp]
    nlinarith [inside.2]
  have ml : q/2 < Real.exp (-h)*x := by nlinarith [inside.1]
  change A (Q h (countedKernel c zero)) x = _
  rw [cut, abs_of_pos positive, if_pos ⟨inside.1, inside.2.le⟩]
  change ((1/2 : ℂ) • (D h (countedKernel c zero) + D (-h) (countedKernel c zero)) : BurnolL2) x = _
  rw [paired, Pi.smul_apply, smul_eq_mul, added, Pi.add_apply, plus, minus]
  unfold countedRaw burnolTateReciprocalRaw
  rw [abs_of_pos xp, abs_of_pos xm]
  rw [show PositionCounting.eventRaw c (Real.exp (-h)*x)⁻¹ = 0 from
    grid_outside (positionSource c) _ mm,
    show DualSourceRaw.eventRaw c (Real.exp h*x) = 0 from
      grid_outside (burnolRieszSingleFourierSourceRaw c) _ pp,
    show PositionCounting.eventRaw c (Real.exp h*x)⁻¹ =
      if (Real.exp h*x)⁻¹ ≤ q then positionSource c (Real.exp h*x)⁻¹ else 0 from
        grid_first_cell (positionSource c) _ pl,
    show DualSourceRaw.eventRaw c (Real.exp (-h)*x) =
      if Real.exp (-h)*x ≤ q then burnolRieszSingleFourierSourceRaw c (Real.exp (-h)*x) else 0 from
        grid_first_cell (burnolRieszSingleFourierSourceRaw c) _ ml]
  simp only [reciprocal_threshold h x positive, lower_threshold]
  simp only [neg_div, mul_zero, sub_zero, Complex.ofReal_mul, mul_inv_rev]
  have coefficient := half_density h
  simp only [neg_div] at coefficient
  linear_combination (-(x : ℂ)⁻¹/2 *
    (if 4 * Real.exp (-h) ≤ x then positionSource c (x⁻¹ * (Real.exp h)⁻¹) else 0)) * coefficient

/-- The upper incidence is the actual independent q dual with the complete original log-B0 foot retained. -/
theorem actual_joint_input_dual_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    ∀ᵐ x : ℝ ∂volume, ∀ _inside : x ∈ Ioo q 4,
      jointInput c zero h x = -(Real.exp (-h/2) : ℂ)/2 *
        ((if x ≤ q * Real.exp h then burnolRieszSingleFourierSourceRaw c (Real.exp (-h)*x) else 0) +
          (x : ℂ)⁻¹ * (if 4 * Real.exp (-h) ≤ x then
            OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.dualRaw c.value c.belowOne ((Real.exp h*x)⁻¹) -
              ForcingPrimitive.leadingCoefficient c *
                burnolMeanZeroFourierRaw (OriginalKFiniteOrderRelease.UnitPowerJordanSource.logBFirst c 0) ((Real.exp h*x)⁻¹)
            else 0)) := by
  filter_upwards [actual_joint_input_arithmetic_raw c zero h nonnegative bounded] with x source inside
  rw [source inside]
  by_cases upper : 4 * Real.exp (-h) ≤ x
  · have xp : 0 < Real.exp h*x := mul_pos (Real.exp_pos _) (by linarith [inside.1])
    have original := actual_dual_original_position c ((Real.exp h*x)⁻¹) (inv_pos.mpr xp)
      ((reciprocal_threshold h x (by linarith [inside.1])).mpr upper)
    rw [if_pos upper, if_pos upper, original]
    ring
  · rw [if_neg upper, if_neg upper]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Arithmetic
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
