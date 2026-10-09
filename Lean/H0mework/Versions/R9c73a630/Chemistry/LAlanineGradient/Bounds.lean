import H0mework.Versions.AB.Chemistry.LAlanineGradient.Model
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.JetIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousGradient

open SourceGaussianModel SourceFiniteData SourceFiniteChecks SourceJetIncidence
open scoped BigOperators

noncomputable section

def sourceCentre : Point := fun axis => (boxCentre axis : ℝ)
def sourceRadius : ℝ := (boxRadius : ℝ)
def sourceCube : Set Point := {x | InsideCube boxCentre boxRadius x}

theorem sourceRadius_positive : 0 < sourceRadius := by
  have h : (0 : ℚ) < boxRadius := by decide +kernel
  unfold sourceRadius
  exact_mod_cast h

theorem sourceCube_eq_closedBall :
    sourceCube = Metric.closedBall sourceCentre sourceRadius := by
  ext x
  change InsideCube boxCentre boxRadius x ↔ x ∈ Metric.closedBall sourceCentre sourceRadius
  rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg sourceRadius_positive.le]
  rfl

theorem sourceCube_convex : Convex ℝ sourceCube := by
  rw [sourceCube_eq_closedBall]
  exact convex_closedBall sourceCentre sourceRadius

theorem sourceCentre_mem : sourceCentre ∈ sourceCube := by
  rw [sourceCube_eq_closedBall]
  exact Metric.mem_closedBall_self sourceRadius_positive.le

/-- A finite source envelope, not a sampled maximum of the gradient. -/
def sourceBilinearBound (left right : MultiIndex) : NNReal :=
  ‖(bilinearEnvelope densityMatrixBound sourceOrbitalBound left right : ℝ)‖₊

def sourceFirstBound (left right : MultiIndex) (axis : Fin 3) : NNReal :=
  sourceBilinearBound (raise left axis) right + sourceBilinearBound left (raise right axis)

def sourceHessianEntryBound (axis direction : Fin 3) : NNReal :=
  sourceFirstBound (raise zeroJet axis) zeroJet direction +
    sourceFirstBound zeroJet (raise zeroJet axis) direction

def sourceSpeedBound : NNReal := ∑ axis : Fin 3, sourceFirstBound zeroJet zeroJet axis

def sourceLipschitzBound : NNReal :=
  ∑ axis : Fin 3, ∑ direction : Fin 3, sourceHessianEntryBound axis direction

theorem source_bilinear_bound (x : Point) (inside : x ∈ sourceCube)
    (left right : MultiIndex) (hl : jetOrder left ≤ 4) (hr : jetOrder right ≤ 4) :
    |bilinear sourceTerms densityMatrix left right x| ≤ (sourceBilinearBound left right : ℝ) := by
  have h := bilinear_abs_bound sourceTerms densityMatrix densityMatrixBound sourceOrbitalBound
    left right x actual_density_matrix_envelope
    (full_source_jets_bounded x inside left hl) (full_source_jets_bounded x inside right hr)
  exact h.trans (le_abs_self _)

theorem source_first_bound (x : Point) (inside : x ∈ sourceCube)
    (left right : MultiIndex) (axis : Fin 3)
    (hl : jetOrder left ≤ 3) (hr : jetOrder right ≤ 3) :
    |firstBilinear sourceTerms densityMatrix left right axis x| ≤
      (sourceFirstBound left right axis : ℝ) := by
  have hl' : jetOrder (raise left axis) ≤ 4 := by rw [jetOrder_raise]; omega
  have hr' : jetOrder (raise right axis) ≤ 4 := by rw [jetOrder_raise]; omega
  exact (abs_add_le _ _).trans (add_le_add
    (source_bilinear_bound x inside (raise left axis) right hl' (by omega))
    (source_bilinear_bound x inside left (raise right axis) (by omega) hr'))

theorem sourceHessian_entry_le (x : Point) (inside : x ∈ sourceCube) (axis direction : Fin 3) :
    |sourceHessian x axis direction| ≤ (sourceHessianEntryBound axis direction : ℝ) := by
  have hz : jetOrder zeroJet = 0 := rfl
  have ha : jetOrder (raise zeroJet axis) = 1 := by rw [jetOrder_raise, hz]
  exact (abs_add_le _ _).trans (add_le_add
    (source_first_bound x inside (raise zeroJet axis) zeroJet direction (by omega) (by omega))
    (source_first_bound x inside zeroJet (raise zeroJet axis) direction (by omega) (by omega)))

theorem sourceGradient_norm_le (x : Point) (inside : x ∈ sourceCube) :
    ‖sourceGradient x‖ ≤ (sourceSpeedBound : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg sourceSpeedBound.coe_nonneg).mpr
  intro axis
  have h := source_first_bound x inside zeroJet zeroJet axis (by decide) (by decide)
  have hs : sourceFirstBound zeroJet zeroJet axis ≤ sourceSpeedBound :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ axis)
  exact h.trans (by exact_mod_cast hs)

theorem sourceHessianLinear_norm_le (x : Point) (inside : x ∈ sourceCube) :
    ‖sourceHessianLinear x‖ ≤ (sourceLipschitzBound : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ sourceLipschitzBound.coe_nonneg
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg sourceLipschitzBound.coe_nonneg (norm_nonneg v))).mpr
  intro axis
  rw [sourceHessianLinear_apply, Real.norm_eq_abs]
  calc
    |∑ direction : Fin 3, sourceHessian x axis direction * v direction| ≤
        ∑ direction : Fin 3, |sourceHessian x axis direction * v direction| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ direction : Fin 3, (sourceHessianEntryBound axis direction : ℝ) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro direction _
      rw [abs_mul]
      exact mul_le_mul (sourceHessian_entry_le x inside axis direction)
        (norm_le_pi_norm v direction) (abs_nonneg _) (by positivity)
    _ = (∑ direction : Fin 3, (sourceHessianEntryBound axis direction : ℝ)) * ‖v‖ := by
      rw [Finset.sum_mul]
    _ ≤ (sourceLipschitzBound : ℝ) * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      have h : (∑ direction : Fin 3, sourceHessianEntryBound axis direction) ≤ sourceLipschitzBound :=
        Finset.single_le_sum (f := fun a : Fin 3 => ∑ d : Fin 3, sourceHessianEntryBound a d)
          (fun _ _ => zero_le) (Finset.mem_univ axis)
      exact_mod_cast h

theorem sourceGradient_lipschitzOn_cube :
    LipschitzOnWith sourceLipschitzBound sourceGradient sourceCube := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (sourceGradient_hasFDerivAt x).differentiableAt) _ sourceCube_convex
  intro x hx
  rw [(sourceGradient_hasFDerivAt x).fderiv]
  exact_mod_cast sourceHessianLinear_norm_le x hx

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousGradient
