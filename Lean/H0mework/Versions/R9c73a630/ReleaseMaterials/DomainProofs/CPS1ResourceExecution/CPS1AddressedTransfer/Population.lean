import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace CPS1AddressedTransfer.Generic
noncomputable section
open InnerProductSpace
open scoped BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def midpoint (before after : E) : E := (1/2 : ℂ) • (before+after)

theorem midpoint_norm_difference (before after : E) :
    ‖after‖^2-‖before‖^2 = 2*(inner ℂ (midpoint before after) (after-before)).re := by
  have halfRe : (starRingEnd ℂ (1/2 : ℂ)).re = (1/2 : ℝ) := by norm_num
  have halfIm : (starRingEnd ℂ (1/2 : ℂ)).im = 0 := by norm_num
  have beforeNorm : (inner ℂ before before).re = ‖before‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) before
  have afterNorm : (inner ℂ after after).re = ‖after‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) after
  have symmetric : (inner ℂ before after).re = (inner ℂ after before).re := inner_re_symm (𝕜 := ℂ) before after
  rw [midpoint,inner_smul_left,inner_add_left,inner_sub_right,inner_sub_right]
  simp only [Complex.mul_re,halfRe,halfIm,zero_mul,sub_zero,Complex.add_re,Complex.sub_re]
  rw [beforeNorm,afterNorm,symmetric]
  ring

theorem cayley_population_change (P H : E →L[ℂ] E) (before after : E) (time : ℝ)
    (law : after-before = -(Complex.I*(time:ℂ)) • H (midpoint before after)) :
    ‖P after‖^2-‖P before‖^2 =
      2*time*(inner ℂ (P (midpoint before after)) (P (H (midpoint before after)))).im := by
  have center : midpoint (P before) (P after) = P (midpoint before after) := by
    simp only [midpoint,map_smul,map_add]
  rw [midpoint_norm_difference,center,← map_sub,law,map_smul,inner_smul_right]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,one_mul,zero_sub,sub_zero,neg_zero]
  ring

theorem projected_complement_population (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (field : E) :
    ‖K.starProjection field‖^2+‖Kᗮ.starProjection field‖^2 = ‖field‖^2 :=
  (K.norm_sq_eq_add_norm_sq_starProjection field).symm

theorem projected_inner (K : Submodule ℂ E) [K.HasOrthogonalProjection] (first second : E) :
    inner ℂ (K.starProjection first) (K.starProjection second) =
      inner ℂ (K.starProjection first) second := by
  rw [← K.inner_starProjection_left_eq_right]
  exact congrArg (fun field => inner ℂ field second)
    (K.starProjection_eq_self_iff.mpr (by simp))

variable {ι : Type*} [Fintype ι]

def population (P : E →L[ℂ] E) (fields : ι → E) : ℝ := ∑ slot, ‖P (fields slot)‖^2

def midpointFlux (P H : E →L[ℂ] E) (before after : ι → E) : ℝ :=
  ∑ slot, (inner ℂ (P (midpoint (before slot) (after slot)))
    (P (H (midpoint (before slot) (after slot))))).im

theorem total_cayley_population_change (P H : E →L[ℂ] E) (before after : ι → E) (time : ℝ)
    (law : ∀ slot, after slot-before slot =
      -(Complex.I*(time:ℂ)) • H (midpoint (before slot) (after slot))) :
    population P after-population P before = 2*time*midpointFlux P H before after := by
  unfold population midpointFlux
  rw [← Finset.sum_sub_distrib]
  simp_rw [cayley_population_change P H _ _ time (law _)]
  rw [Finset.mul_sum]

theorem whole_population (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (fields : ι → E) (unit : ∀ slot, ‖fields slot‖^2 = 1) :
    population K.starProjection fields+population Kᗮ.starProjection fields = Fintype.card ι := by
  unfold population
  rw [← Finset.sum_add_distrib]
  simp_rw [projected_complement_population,unit]
  simp

theorem complementary_transfer (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (before after : ι → E) (beforeUnit : ∀ slot, ‖before slot‖^2 = 1)
    (afterUnit : ∀ slot, ‖after slot‖^2 = 1) :
    population Kᗮ.starProjection after-population Kᗮ.starProjection before =
      -(population K.starProjection after-population K.starProjection before) := by
  have first := whole_population K before beforeUnit
  have second := whole_population K after afterUnit
  linarith


end
end CPS1AddressedTransfer.Generic
