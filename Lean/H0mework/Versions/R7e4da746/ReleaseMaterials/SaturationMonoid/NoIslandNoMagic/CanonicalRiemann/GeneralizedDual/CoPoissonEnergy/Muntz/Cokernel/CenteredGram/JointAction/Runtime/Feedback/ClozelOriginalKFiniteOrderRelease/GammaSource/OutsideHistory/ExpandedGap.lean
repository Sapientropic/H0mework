import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Rectangular.Face.Covariance

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.ExpandedGap

open Filter MeasureTheory Set
open scoped ENNReal

local notation "F" => fourierL2
local notation "D" => burnolMultiplicativeDilation
local notation "q" => (1 / 4 : ℝ)

private theorem interval_read {radius : ℝ} {value : BurnolL2}
    (member : value ∈ locallyConstantFace radius) :
    ∃ coefficient : ℂ, ∀ᵐ x : ℝ ∂volume,
      x ∈ symmetricInterval radius → value x = coefficient := by
  obtain ⟨coefficient, read⟩ := mem_locallyConstantFace_iff_exists.mp member
  refine ⟨coefficient, (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp ?_⟩
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) value,
    intervalConstant_coeFn radius, Lp.coeFn_smul coefficient (intervalConstant radius)]
    with x restriction unit scalar
  calc
    value x = restrictToInterval radius value x := restriction.symm
    _ = (coefficient • intervalConstant radius) x := by rw [read]
    _ = coefficient * intervalConstant radius x := scalar
    _ = coefficient := by rw [unit, mul_one]

private theorem expanded_frequency_gap (v : BurnolL2)
    (inward : ∀ h : ℝ, 0 < h → F (D (-h / 2) v) ∈ locallyConstantFace q) (n : ℕ) :
    F v ∈ locallyConstantFace ((n : ℝ) + 1) := by
  let t := Real.log (4 * ((n : ℝ) + 1))
  have scale : 1 < 4 * ((n : ℝ) + 1) := by
    have nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have positive : 0 < t := Real.log_pos scale
  have expT : Real.exp t = 4 * ((n : ℝ) + 1) := Real.exp_log (zero_lt_one.trans scale)
  have fixed := inward (2 * t) (mul_pos (by norm_num) positive)
  rw [fourierL2_burnolMultiplicativeDilation, show - (-(2 * t) / 2) = t by ring] at fixed
  have expanded := burnolMultiplicativeDilation_mem_locallyConstantFace_scaled (-t) fixed
  have radius : q * Real.exp (-(-t)) = (n : ℝ) + 1 := by
    rw [neg_neg, expT]
    ring
  rw [radius, burnolMultiplicativeDilation_neg_eq_symm t, (D t).symm_apply_apply] at expanded
  exact expanded

/-- The full inward Fourier gaps of the original dilation determine the full field. -/
theorem zero_of_all_inward_frequency_gap (v : BurnolL2)
    (inward : ∀ h : ℝ, 0 < h → F (D (-h / 2) v) ∈ locallyConstantFace q) : v = 0 := by
  classical
  have byWindow (n : ℕ) : ∃ coefficient : ℂ, ∀ᵐ x : ℝ ∂volume,
      x ∈ symmetricInterval ((n : ℝ) + 1) → (F v) x = coefficient :=
    interval_read (expanded_frequency_gap v inward n)
  choose coefficient read using byWindow
  have simultaneous : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      x ∈ symmetricInterval ((n : ℝ) + 1) → (F v) x = coefficient n := ae_all_iff.mpr read
  have windowNonzero : (volume : Measure ℝ).restrict (symmetricInterval 1) ≠ 0 := by
    intro null
    have positive : (volume.restrict (symmetricInterval 1)) univ ≠ 0 := by
      rw [Measure.restrict_apply_univ, symmetricInterval, Real.volume_Icc]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
    exact positive (by simp [null])
  have := ae_neBot.mpr windowNonzero
  obtain ⟨point, atPoint, inside⟩ :=
    ((ae_restrict_of_ae simultaneous).and (ae_restrict_mem (measurableSet_symmetricInterval 1))).exists
  have atBase : (F v) point = coefficient 0 :=
    atPoint 0 (by simpa only [Nat.cast_zero, zero_add] using inside)
  have same (n : ℕ) : coefficient n = coefficient 0 := by
    have small : |point| ≤ (1 : ℝ) := abs_le.mpr inside
    have nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have within : point ∈ symmetricInterval ((n : ℝ) + 1) := abs_le.mp (by linarith)
    exact (atPoint n within).symm.trans atBase
  have allAxis : (F v : ℝ → ℂ) =ᵐ[volume] fun _ => coefficient 0 := by
    filter_upwards [simultaneous] with x readAt
    obtain ⟨n, enough⟩ := exists_nat_gt |x|
    have within : x ∈ symmetricInterval ((n : ℝ) + 1) := abs_le.mp (by linarith)
    exact (readAt n within).trans (same n)
  have constantLp : MemLp (fun _ : ℝ => coefficient 0) 2 volume :=
    (memLp_congr_ae allAxis).mp (Lp.memLp (F v))
  have constantZero : coefficient 0 = 0 := by
    rcases (memLp_const_iff (p := 2) (by norm_num) ENNReal.ofNat_ne_top).mp constantLp with zero | finite
    · exact zero
    · rw [Real.volume_univ] at finite
      exact (lt_irrefl _ finite).elim
  apply fourierL2.injective
  rw [map_zero]
  have readZero : (F v : ℝ → ℂ) =ᵐ[volume] fun _ => 0 := by
    simpa only [constantZero] using allAxis
  exact Lp.ext (readZero.trans (Lp.coeFn_zero ℂ 2 volume).symm)

end OriginalRSourceJointContact.OutsideHistory.ExpandedGap
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
