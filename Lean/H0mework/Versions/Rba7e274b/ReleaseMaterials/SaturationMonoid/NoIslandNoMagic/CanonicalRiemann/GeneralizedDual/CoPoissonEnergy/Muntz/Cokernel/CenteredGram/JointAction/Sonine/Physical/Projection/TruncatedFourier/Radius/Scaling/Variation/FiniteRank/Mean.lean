import H0mework.Arithmetic.SonineProjection.MeanZeroBlock
import H0mework.Versions.V2.Arithmetic.MellinProjection.GapTailDilation
import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace
abbrev H := BurnolUnitIntervalL2
def e : H := intervalConstant 1

def meanZeroFace : ClosedSubmodule ℂ H where
  toSubmodule := (intervalConstantLine 1)ᗮ
  isClosed' := Submodule.isClosed_orthogonal _
local instance meanZeroComplete : CompleteSpace meanZeroFace.toSubmodule :=
  IsComplete.completeSpace_coe meanZeroFace.isClosed.isComplete
local instance constantComplete : CompleteSpace (intervalConstantLine 1) :=
  IsComplete.completeSpace_coe (intervalConstantLine_isClosed 1).isComplete
def Q : H →L[ℂ] H := meanZeroFace.toSubmodule.starProjection

theorem e_self : inner ℂ e e = 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  exact (burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < 1)).trans (by norm_num)

theorem Q_read (x : H) : Q x = x - (1/2 : ℂ) • InnerProductSpace.rankOne ℂ e e x := by
  change meanZeroFace.toSubmodule.starProjection x = _
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · change x - (1/2 : ℂ) • (inner ℂ e x • e) ∈ (intervalConstantLine 1)ᗮ
    change x - (1/2 : ℂ) • (inner ℂ e x • e) ∈ (ℂ ∙ e)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [inner_sub_right, inner_smul_right, inner_smul_right, e_self]
    ring
  · change x - (x - (1/2 : ℂ) • InnerProductSpace.rankOne ℂ e e x) ∈ ((intervalConstantLine 1)ᗮ)ᗮ
    rw [Submodule.orthogonal_orthogonal]
    have same : x - (x - (1/2 : ℂ) • InnerProductSpace.rankOne ℂ e e x) =
        ((1/2 : ℂ) * inner ℂ e x) • e := by simp only [InnerProductSpace.rankOne_apply,smul_smul];module
    rw [same]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem Q_operator : Q = ContinuousLinearMap.id ℂ H - (1/2 : ℂ) • InnerProductSpace.rankOne ℂ e e := by
  apply ContinuousLinearMap.ext
  intro x
  exact Q_read x

theorem Q_idempotent : Q.comp Q = Q := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem meanZeroFace.toSubmodule x)

theorem Q_symmetric : Q.IsSymmetric := by
  exact Submodule.starProjection_isSymmetric _

-- Only the actual constant column needs the Fourier adjoint pairing.
theorem centered_square (T : H →L[ℂ] H) (constantPair : ∀ x : H, inner ℂ e (T x) = inner ℂ (T e) x) :
    (Q.comp (T.comp Q)).comp (Q.comp (T.comp Q)) =
      Q.comp ((T.comp T).comp Q) -
        (1/2 : ℂ) • InnerProductSpace.rankOne ℂ (Q (T e)) (Q (T e)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  rw [show Q (Q (T (Q x))) = Q (T (Q x)) by exact congrArg (fun A : H →L[ℂ] H => A (T (Q x))) Q_idempotent]
  rw [Q_read (T (Q x)),map_sub,map_smul,map_sub,map_smul]
  simp only [InnerProductSpace.rankOne_apply,map_smul,constantPair]
  have pair : inner ℂ (T e) (Q x) = inner ℂ (Q (T e)) x := (Q_symmetric _ _).symm
  rw [pair]
  rfl

-- The literal quarter constant rechart fixes the unit-chart projection authority.
local instance quarterConstantComplete : CompleteSpace (intervalConstantLine (1/4 : ℝ)) :=
  IsComplete.completeSpace_coe (intervalConstantLine_isClosed _).isComplete
def quarterChart : BurnolQuarterIntervalL2 ≃ₗᵢ[ℂ] H :=
  burnolRadiusRechartEquiv (by norm_num : (0 : ℝ) < 1/4)
theorem quarter_constant_chart : quarterChart (intervalConstant (1/4 : ℝ)) = (1/2 : ℂ) • e := by
  apply Lp.ext
  filter_upwards [burnolRadiusRechart_coe (by norm_num : (0 : ℝ) < 1/4) (intervalConstant (1/4 : ℝ)),
    (burnolRadiusScaleEquiv_measurePreserving (by norm_num : (0 : ℝ) < 1/4)).quasiMeasurePreserving.ae_eq
      (Measure.ae_smul_measure (intervalConstant_coeFn (1/4 : ℝ)) (ENNReal.ofReal (1/4 : ℝ)⁻¹)),
    Lp.coeFn_smul (1/2 : ℂ) e,intervalConstant_coeFn 1] with x chart constant scalar unit
  change (burnolRadiusRechart _ (intervalConstant (1/4 : ℝ)) : ℝ → ℂ) x = _
  change (intervalConstant (1/4 : ℝ) : ℝ → ℂ) ((1/4 : ℝ)*x) = 1 at constant
  change (e : ℝ → ℂ) x = 1 at unit
  rw [chart,scalar,constant]
  simp only [Pi.smul_apply,smul_eq_mul,unit]
  norm_num [smul_eq_mul,e,show Real.sqrt 4 = 2 by rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)];norm_num]

theorem quarter_projection_chart (x : BurnolQuarterIntervalL2) :
    quarterChart (burnolQuarterMeanZeroProjection x) = Q (quarterChart x) := by
  apply (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · change quarterChart (burnolQuarterMeanZeroProjection x) ∈ (ℂ ∙ e)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have quarterZero : inner ℂ (intervalConstant (1/4 : ℝ)) (burnolQuarterMeanZeroProjection x) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (burnolQuarterMeanZeroProjection_mem x)
    have actual := quarterChart.inner_map_map (intervalConstant (1/4 : ℝ)) (burnolQuarterMeanZeroProjection x)
    rw [quarter_constant_chart,inner_smul_left,quarterZero] at actual
    norm_num only [star_div₀,star_one,star_ofNat] at actual
    exact (mul_eq_zero.mp actual).resolve_left (by norm_num)
  · have quarterDifference : x - burnolQuarterMeanZeroProjection x ∈
        (burnolQuarterMeanZeroClosedFace.toSubmodule)ᗮ := Submodule.sub_starProjection_mem_orthogonal x
    change x - burnolQuarterMeanZeroProjection x ∈ ((intervalConstantLine (1/4 : ℝ))ᗮ)ᗮ at quarterDifference
    rw [Submodule.orthogonal_orthogonal] at quarterDifference
    rcases Submodule.mem_span_singleton.mp quarterDifference with ⟨c,source⟩
    change quarterChart x - quarterChart (burnolQuarterMeanZeroProjection x) ∈ ((intervalConstantLine 1)ᗮ)ᗮ
    rw [Submodule.orthogonal_orthogonal,← map_sub,← source,map_smul,quarter_constant_chart,smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
