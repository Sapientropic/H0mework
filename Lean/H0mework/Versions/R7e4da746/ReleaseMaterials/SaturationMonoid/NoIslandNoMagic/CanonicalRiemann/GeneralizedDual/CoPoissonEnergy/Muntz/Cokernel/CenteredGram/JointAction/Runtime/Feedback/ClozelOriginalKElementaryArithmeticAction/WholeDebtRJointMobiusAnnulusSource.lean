import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceNormalSemantics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockEuler
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBFiniteAction.Source
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.Weighted

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace FourierTransform BigOperators ContDiff
namespace B
export OriginalKCoefficientBFiniteAction (sourceCore compactCorrection)
export OriginalKSourceFiniteUpdate.OriginalBFiniteRAction (calculatedSourceNormal)
end B
namespace J
export OriginalKPairedBEulerJunctionSource
  (junctionShift junctionPoint sourceAction sourceFirst sourceSecond)
end J
namespace T
export OriginalKPairedBEulerJunctionSource.TwoPieceFourierAction
  (state_fourier_hasDerivAt state_fourierSlope_continuous)
end T
namespace Flux
export FiniteMobiusResolventFlux (coefficient actualMean)
end Flux
local notation "q" => (1 / 4 : ℝ)
local notation "h" => J.junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection

/-- The physical face of the complete original boundary action, before any Pa split. -/



theorem actual_joint_carrier (c : BurnolCompletedMellinCoordinate) :
    jointValue c = character c • K c - P (J.sourceAction c) := by
  have normal : B.calculatedSourceNormal c h =
      OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (K c : BurnolL2) := by
    rw [OriginalKCoefficientBFiniteAction.calculated_normal_full_inventory c h
      OriginalKPairedBEulerJunctionSource.junctionShift_pos.le,
      ← OriginalKCoefficientBFiniteAction.source_boundary_full_inventory c h
        OriginalKPairedBEulerJunctionSource.junctionShift_pos.le,
      OriginalKCoefficientBFiniteAction.sourceKernel_original]
  unfold jointValue
  rw [OriginalKJointMobiusSourceCalculation.actual_source_code]
  change P (B.calculatedSourceNormal c h) = _
  rw [normal, OriginalKFixedBoundarySourceFibre.finiteBoundaryAction, map_sub, map_smul]
  have kernel : P (K c : BurnolL2) = K c := by
    change (evenBurnolClosedFace q).toSubmodule.orthogonalProjectionOnto (K c : BurnolL2) = _
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [kernel]
  rfl

theorem actual_core_price (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (K c : BurnolL2) (jointValue c : BurnolL2) =
      inner ℂ (K c : BurnolL2) (B.sourceCore c h) := by
  have read := OriginalKCoefficientBFiniteAction.original_K_self_cotest c h
    OriginalKPairedBEulerJunctionSource.junctionShift_pos.le
  rw [OriginalKCoefficientBFiniteAction.sourceKernel_original] at read
  change inner ℂ (K c : BurnolL2)
    (P ((OriginalKJointMobiusSourceCalculation.sourceCode c).eval
      OriginalKJointMobiusSourceCalculation.sourceEnvironment) : BurnolL2) = _
  rw [OriginalKJointMobiusSourceCalculation.actual_source_code]
  change inner ℂ (K c : BurnolL2) (P (B.calculatedSourceNormal c h) : BurnolL2) = _
  have projection := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (K c) (B.calculatedSourceNormal c h)
  exact projection.trans read

/-- Both branches are original B/return fields, with the literal source means retained. -/



private theorem positive_c1 (f df : ℝ → ℂ)
    (derivative : ∀ x > 0, HasDerivAt f (df x) x)
    (regular : ContinuousOn df (Ioi 0)) : ContDiffOn ℝ 1 f (Ioi 0) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (derivative x hx).differentiableAt.differentiableWithinAt,
    by norm_num, ?_⟩
  rw [contDiffOn_zero]
  exact regular.congr (fun x hx => (derivative x hx).deriv)

private theorem fourier_c1 (state : Hq) : ContDiff ℝ 1 (Constructor.fourierRaw state) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (T.state_fourier_hasDerivAt state x).differentiableAt, ?_⟩
  have same : deriv (Constructor.fourierRaw state) = Constructor.fourierDerivative state :=
    funext (fun x => (T.state_fourier_hasDerivAt state x).deriv)
  rw [same]
  exact T.state_fourierSlope_continuous state

private theorem kernel_outer_c1 (c : BurnolCompletedMellinCoordinate) :
    ContDiffOn ℝ 1 (kernelOuter c) (Ioi 0) := by
  let df := fun x : ℝ =>
    (1 / 2 : ℂ) * ((-star c.value) * (x : ℂ) ^ (-(star c.value + 1))) -
      burnolRieszReturnRawDerivative c x
  apply positive_c1 (kernelOuter c) df
  · intro x positive
    exact ((burnolMellinTailPower_hasDerivAt (star c.value) positive).const_mul (1 / 2 : ℂ)).sub
      ((burnolRieszReturnRaw_hasDerivAt c x).add_const _)
  · intro x positive
    exact ((continuousAt_const.mul
      ((continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const x
        (-(star c.value + 1)) (Or.inr positive.ne'))))).sub
          (burnolRieszReturnRawDerivative_continuous c).continuousAt).continuousWithinAt

private theorem joint_outer_c1 (c : BurnolCompletedMellinCoordinate) (branch : Fin 2) :
    ContDiffOn ℝ 1 (jointOuter c branch) (Ioi 0) := by
  intro x positive
  have k := (kernel_outer_c1 c).contDiffAt (Ioi_mem_nhds positive)
  have plus := (kernel_outer_c1 c).contDiffAt
    (Ioi_mem_nhds (mul_pos (Real.exp_pos h) positive))
  have minus := (kernel_outer_c1 c).contDiffAt
    (Ioi_mem_nhds (mul_pos (Real.exp_pos (-h)) positive))
  have movedPlus : ContDiffAt ℝ 1 (fun y : ℝ => kernelOuter c (Real.exp h * y)) x :=
    plus.comp x (by fun_prop)
  have movedMinus : ContDiffAt ℝ 1 (fun y : ℝ => kernelOuter c (Real.exp (-h) * y)) x :=
    minus.comp x (by fun_prop)
  unfold jointOuter
  split_ifs
  · simpa only [div_eq_mul_inv] using
      (((contDiffAt_const.mul k).sub (((contDiffAt_const.mul movedPlus).add contDiffAt_const).mul
        (show ContDiffAt ℝ 1 (fun _ : ℝ => (2 : ℂ)⁻¹) x from contDiffAt_const))).add
          (fourier_c1 (J.sourceSecond c : Hq)).contDiffAt).contDiffWithinAt
  · simpa only [div_eq_mul_inv] using
      (((contDiffAt_const.mul k).sub (((contDiffAt_const.mul movedPlus).add
        (contDiffAt_const.mul movedMinus)).mul
          (show ContDiffAt ℝ 1 (fun _ : ℝ => (2 : ℂ)⁻¹) x from contDiffAt_const))).add
            (fourier_c1 (J.sourceSecond c : Hq)).contDiffAt).contDiffWithinAt


/-- Reciprocal weighting converts the original row profile into the paid native source. -/

private theorem row_weight_c1 (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2) :
    ContDiffOn ℝ 1 (rowWeight c n branch) (Ioi 0) := by
  intro t positive
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have moved : ContDiffAt ℝ 1 (fun x : ℝ => x⁻¹ / (n : ℕ)) t :=
    ((contDiffAt_id.inv positive.ne').div_const _)
  have outer := ((joint_outer_c1 c branch).contDiffAt
    (Ioi_mem_nhds (div_pos (inv_pos.mpr positive) np))).comp t moved
  unfold rowWeight
  exact (((Complex.ofRealCLM.contDiff.contDiffAt).inv
    (Complex.ofReal_ne_zero.mpr positive.ne')).mul (outer.sub contDiffAt_const)).contDiffWithinAt




private theorem row_bounds (n : ℕ+) (_slot : n ∈ burnolCenteredMobiusCutoffFinset 4)
    (branch : Fin 2) : q ≤ lower n branch ∧ upper n branch ≤ 4 ∧ 0 < lower n branch := by
  have one : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast (Nat.succ_le_iff.mpr n.pos)
  have shift : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr
    OriginalKPairedBEulerJunctionSource.junctionShift_pos.le
  by_cases branchZero : branch = 0
  · rw [lower, upper, if_pos branchZero, if_pos branchZero]
    exact ⟨by nlinarith, min_le_left _ _, by positivity⟩
  · rw [lower, upper, if_neg branchZero, if_neg branchZero]
    exact ⟨by nlinarith, le_rfl, by positivity⟩

private theorem inverse_bounds (a b : ℝ) (positive : 0 < a)
    (ordered : a < b) (lowerBound : q ≤ a) (upperBound : b ≤ 4) :
    b⁻¹ ∈ Icc q 4 ∧ a⁻¹ ∈ Icc q 4 := by
  have bp := positive.trans ordered
  constructor
  · constructor
    · simpa only [one_div] using (le_div_iff₀ bp).mpr (show q * b ≤ 1 by nlinarith)
    · simpa only [one_div] using (div_le_iff₀ bp).mpr (show (1 : ℝ) ≤ 4 * b by nlinarith)
  · constructor
    · simpa only [one_div] using (le_div_iff₀ positive).mpr (show q * a ≤ 1 by nlinarith)
    · simpa only [one_div] using (div_le_iff₀ positive).mpr (show (1 : ℝ) ≤ 4 * a by nlinarith)

private theorem row_slope_continuous (c : BurnolCompletedMellinCoordinate) (n : ℕ+)
    (branch : Fin 2) (positive : 0 < lower n branch) (ordered : lower n branch < upper n branch) :
    Continuous (rowSlope c n branch) := by
  have upPositive := positive.trans ordered
  have invOrder : (upper n branch)⁻¹ ≤ (lower n branch)⁻¹ :=
    (inv_le_inv₀ upPositive positive).mpr ordered.le
  have actual := (row_weight_c1 c n branch).continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  unfold rowSlope
  apply actual.comp_continuous (by fun_prop)
  intro t
  exact (inv_pos.mpr upPositive).trans_le (le_max_left _ _)

private theorem row_derivative (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2)
    (positive : 0 < lower n branch) (ordered : lower n branch < upper n branch)
    (t : ℝ) (inside : t ∈ Icc (upper n branch)⁻¹ (lower n branch)⁻¹) :
    HasDerivAt (rowWeight c n branch) (rowSlope c n branch t) t := by
  have tp : 0 < t := (inv_pos.mpr (positive.trans ordered)).trans_le inside.1
  have differentiable := ((row_weight_c1 c n branch).contDiffAt
    (Ioi_mem_nhds tp)).differentiableAt (by norm_num)
  simpa only [rowSlope, min_eq_right inside.2, max_eq_right inside.1] using differentiable.hasDerivAt

private theorem row_wave_inPa (c : BurnolCompletedMellinCoordinate) (n : ℕ+)
    (slot : n ∈ burnolCenteredMobiusCutoffFinset 4) (branch : Fin 2) :
    rowWave c n branch ∈ burnolOriginalPaInL2 := by
  unfold rowWave
  split_ifs with ordered
  · have bounds := row_bounds n slot branch
    have invBounds := inverse_bounds _ _ bounds.2.2 ordered bounds.1 bounds.2.1
    exact burnolWeightedReciprocalStepWave_inPa _ _ _ _ invBounds.1 invBounds.2
      (row_slope_continuous c n branch bounds.2.2 ordered).continuousOn
  · exact Submodule.zero_mem _

theorem actual_pa_wave (c : BurnolCompletedMellinCoordinate) : paWave c ∈ burnolOriginalPaInL2 := by
  unfold paWave
  apply Submodule.sum_mem
  intro n slot
  exact Submodule.smul_mem _ _ (Submodule.add_mem _
    (row_wave_inPa c n slot 0) (row_wave_inPa c n slot 1))

end OriginalWholeDebtRJointMobiusSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
