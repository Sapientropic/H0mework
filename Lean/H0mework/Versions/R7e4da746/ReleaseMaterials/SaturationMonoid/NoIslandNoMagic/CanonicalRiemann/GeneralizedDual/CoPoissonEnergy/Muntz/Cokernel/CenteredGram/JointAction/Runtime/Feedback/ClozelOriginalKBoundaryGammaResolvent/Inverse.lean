import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.PaBoundaryCommutator
import H0mework.Arithmetic.BurnolMellin.PairedMellinCharacterRigidity
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalBoundaryGammaResolvent
open Complex MeasureTheory Set Filter BurnolPhysicalState SourceGeneratedCompressedUnitaryDefectPort
open scoped InnerProductSpace Topology NNReal
local notation "H" => BurnolPaAmbientCarrier
local notation "h" => OriginalKPairedBEulerJunctionSource.junctionShift

local instance ambientComplete : CompleteSpace H :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The physical compression precedes every Pa-orthogonal projection. -/
def action : H →L[ℂ] H := burnolPairedAmbientCompression h

theorem action_symmetric : action.toLinearMap.IsSymmetric :=
  burnolPairedAmbientCompression_symmetric h

theorem action_contractive (x : H) : ‖action x‖ ≤ ‖x‖ := by
  unfold action burnolPairedAmbientCompression
  rw [smul_apply, add_apply, norm_smul]
  have halfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [halfNorm]
  calc
    (1 / 2 : ℝ) * ‖_ + _‖ ≤ (1 / 2 : ℝ) * (‖_‖ + ‖_‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (‖x‖ + ‖x‖) := by
      gcongr
      · exact norm_compression_le (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation h).toLinearIsometry x
      · exact norm_compression_le (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation (-h)).toLinearIsometry x
    _ = ‖x‖ := by ring

def character (c : BurnolCompletedMellinCoordinate) : ℂ :=
  pairedMellinTranslationCharacter c.value h

def realInterval : Set ℂ := Complex.ofReal '' Set.Icc (-1 : ℝ) 1

def gap (c : BurnolCompletedMellinCoordinate) : ℝ :=
  Metric.infDist (character c) realInterval

private theorem realInterval_closed : IsClosed realInterval :=
  (isCompact_Icc.image Complex.continuous_ofReal).isClosed

private theorem realInterval_nonempty : realInterval.Nonempty := by
  exact ⟨0, 0, by norm_num, by simp⟩

theorem character_not_mem (c : BurnolCompletedMellinCoordinate)
    (half : 1 / 2 < c.value.re) : character c ∉ realInterval := by
  rintro ⟨r, hr, same⟩
  have realCharacter : (character c).im = 0 := by rw [← same]; simp
  have contractive : ‖character c‖ ≤ 1 := by
    rw [← same, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr hr
  have centered := pairedMellinTranslationCharacter_rigidity c.value h
    OriginalKPairedBEulerJunctionSource.junctionShift_pos.ne' realCharacter contractive
  linarith

theorem gap_pos (c : BurnolCompletedMellinCoordinate) (half : 1 / 2 < c.value.re) :
    0 < gap c :=
  (realInterval_closed.notMem_iff_infDist_pos realInterval_nonempty).mp (character_not_mem c half)

def boundaryOperator (c : BurnolCompletedMellinCoordinate) : H →L[ℂ] H :=
  character c • ContinuousLinearMap.id ℂ H - action

private theorem numerical_gap (c : BurnolCompletedMellinCoordinate) (x : H) :
    ‖x‖ ^ 2 * gap c ≤ ‖inner ℂ (boundaryOperator c x) x‖ := by
  by_cases zero : x = 0
  · simp [zero]
  have squarePositive : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr zero)
  let s : ℝ := ‖x‖ ^ 2
  let r : ℝ := (inner ℂ x (action x)).re / s
  have innerBound : |(inner ℂ x (action x)).re| ≤ s :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by
      dsimp [s]
      calc ‖x‖ * ‖action x‖ ≤ ‖x‖ * ‖x‖ :=
             mul_le_mul_of_nonneg_left (action_contractive x) (norm_nonneg x)
           _ = ‖x‖ ^ 2 := by ring))
  have range : r ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ squarePositive).mpr
      linarith [(abs_le.mp innerBound).1]
    · apply (div_le_iff₀ squarePositive).mpr
      linarith [(abs_le.mp innerBound).2]
  have realRead : ((r * s : ℝ) : ℂ) = inner ℂ x (action x) := by
    have rs : r * s = (inner ℂ x (action x)).re := div_mul_cancel₀ _ squarePositive.ne'
    rw [rs]
    exact action_symmetric.coe_re_inner_self_apply x
  have innerRead : inner ℂ x (boundaryOperator c x) =
      (character c - (r : ℂ)) * (s : ℂ) := by
    change inner ℂ x (character c • x - action x) = _
    rw [inner_sub_right, _root_.inner_smul_right (𝕜 := ℂ) x x (character c),
      inner_self_eq_norm_sq_to_K, ← realRead]
    dsimp [s]
    push_cast
    ring
  have distance : gap c ≤ ‖character c - (r : ℂ)‖ := by
    simpa only [gap, dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (x := character c)
        (show (r : ℂ) ∈ realInterval from ⟨r, range, rfl⟩))
  calc
    ‖x‖ ^ 2 * gap c = s * gap c := rfl
    _ ≤ s * ‖character c - (r : ℂ)‖ :=
      mul_le_mul_of_nonneg_left distance squarePositive.le
    _ = ‖inner ℂ x (boundaryOperator c x)‖ := by
      rw [innerRead, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos squarePositive]
      ring
    _ = ‖inner ℂ (boundaryOperator c x) x‖ := norm_inner_symm _ _

theorem boundaryOperator_isUnit (c : BurnolCompletedMellinCoordinate)
    (half : 1 / 2 < c.value.re) : IsUnit (boundaryOperator c) := by
  exact ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (boundaryOperator c) (c := ⟨gap c, (gap_pos c half).le⟩)
    (show (0 : ℝ≥0) < ⟨gap c, (gap_pos c half).le⟩ from gap_pos c half)
    (numerical_gap c)

/-- Generated from the operator and its source parameter; no K or Gamma input. -/
def inverse (c : BurnolCompletedMellinCoordinate) (half : 1 / 2 < c.value.re) : H →L[ℂ] H :=
  ↑((boundaryOperator_isUnit c half).unit⁻¹)

theorem inverse_left (c : BurnolCompletedMellinCoordinate) (half : 1 / 2 < c.value.re)
    (x : H) : inverse c half (boundaryOperator c x) = x := by
  have identity : inverse c half * boundaryOperator c = 1 := by
    exact (boundaryOperator_isUnit c half).val_inv_mul
  exact congrArg (fun f : H →L[ℂ] H => f x) identity

theorem inverse_right (c : BurnolCompletedMellinCoordinate) (half : 1 / 2 < c.value.re)
    (x : H) : boundaryOperator c (inverse c half x) = x := by
  have identity : boundaryOperator c * inverse c half = 1 := by
    exact (boundaryOperator_isUnit c half).mul_val_inv
  exact congrArg (fun f : H →L[ℂ] H => f x) identity

theorem inverse_norm_apply (c : BurnolCompletedMellinCoordinate)
    (half : 1 / 2 < c.value.re) (x : H) :
    ‖inverse c half x‖ ≤ (gap c)⁻¹ * ‖x‖ := by
  have anti := ContinuousLinearMap.antilipschitz_of_forall_le_inner_map
    (boundaryOperator c) (c := ⟨gap c, (gap_pos c half).le⟩)
    (show (0 : ℝ≥0) < ⟨gap c, (gap_pos c half).le⟩ from gap_pos c half)
    (numerical_gap c)
  have bound := anti.le_mul_dist (inverse c half x) 0
  simp only [dist_zero_right, map_zero, inverse_right] at bound
  change ‖inverse c half x‖ ≤ (gap c)⁻¹ * ‖x‖ at bound
  exact bound

theorem inverse_norm (c : BurnolCompletedMellinCoordinate) (half : 1 / 2 < c.value.re) :
    ‖inverse c half‖ ≤ (gap c)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (gap_pos c half).le) (inverse_norm_apply c half)

theorem inverse_original_boundary (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (half : 1 / 2 < c.value.re) :
    inverse c half (burnolZeroPairedFixedAnnulusBoundary c zero h) =
      burnolCompletedMellinRieszVector c := by
  exact inverse_left c half (burnolCompletedMellinRieszVector c)

end OriginalBoundaryGammaResolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
