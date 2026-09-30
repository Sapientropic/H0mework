import H0mework.Arithmetic.Muntz.CoPoissonSchwartzEnergyAction
import H0mework.Arithmetic.SonineGap.BalancedSonineGapFace
import H0mework.Arithmetic.Tempered.RemainderReality

/-!
# Stage-zero Sonine gap motion

At the actual first q-rich scale q = sqrt 3, inverse half-density dilation
moves the balanced radius-one source/Fourier gap to the exact reciprocal
pair (q, q^-1).
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex FourierTransform MeasureTheory
open ClozelEndpointSourceEffect
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

/-- The fixed first-beat dilation ratio. -/
def stageZeroSonineQ : ℝ := Real.sqrt 3

theorem stageZeroSonineQ_pos : 0 < stageZeroSonineQ := by
  unfold stageZeroSonineQ
  positivity

/-- The inverse half-density source action.  Its argument scaling is
`q⁻¹`; consequently source and Fourier gaps move in reciprocal directions. -/
def stageZeroSonineInverseDilation : SonineSchwartz →ₗ[ℂ] SonineSchwartz :=
  coPoissonSchwartzEnergyTranslation (Real.log stageZeroSonineQ⁻¹)

@[simp] theorem stageZeroSonineInverseDilation_apply
    (test : SonineSchwartz) (x : ℝ) :
    stageZeroSonineInverseDilation test x =
      (stageZeroSonineQ : ℂ)⁻¹ ^ (1 / 2 : ℂ) *
        test (stageZeroSonineQ⁻¹ * x) := by
  change (Real.exp (Real.log stageZeroSonineQ⁻¹) : ℂ) ^
      (1 / 2 : ℂ) *
        test (Real.exp (Real.log stageZeroSonineQ⁻¹) * x) = _
  rw [Real.exp_log (inv_pos.mpr stageZeroSonineQ_pos)]
  norm_num

/-- Exact Fourier readback of the fixed inverse dilation. -/
theorem fourier_stageZeroSonineInverseDilation_apply
    (test : SonineSchwartz) (x : ℝ) :
    (𝓕 (stageZeroSonineInverseDilation test)) x =
      (stageZeroSonineQ : ℂ)⁻¹ ^ (1 / 2 : ℂ) *
        ((((stageZeroSonineQ⁻¹ : ℝ) : ℂ)⁻¹) *
          (𝓕 test) (stageZeroSonineQ * x)) := by
  have direct : stageZeroSonineInverseDilation test =
      (stageZeroSonineQ : ℂ)⁻¹ ^ (1 / 2 : ℂ) •
        scaledSchwartzTest stageZeroSonineQ⁻¹
          (inv_ne_zero (ne_of_gt stageZeroSonineQ_pos)) test := by
    apply SchwartzMap.ext
    intro y
    simp only [stageZeroSonineInverseDilation_apply, smul_apply,
      scaledSchwartzTest_apply, smul_eq_mul]
  rw [direct, FourierTransform.fourier_smul,
    scaledSchwartzTest_fourier stageZeroSonineQ⁻¹
      (inv_pos.mpr stageZeroSonineQ_pos) test]
  simp only [smul_apply, scaledSchwartzTest_apply, smul_eq_mul]
  rw [inv_inv]

/-- The stage-zero inverse dilation sends the balanced radius-one face to
the concrete moved face `(q, q⁻¹)`. -/
theorem stageZeroSonineInverseDilation_mem_movedFace
    (test : SonineSchwartz)
    (membership : test ∈ sonineTwoGapFace 1 1) :
    stageZeroSonineInverseDilation test ∈
      sonineTwoGapFace stageZeroSonineQ stageZeroSonineQ⁻¹ := by
  rw [mem_sonineTwoGapFace_iff] at membership ⊢
  constructor
  · intro x hx
    rw [stageZeroSonineInverseDilation_apply]
    rw [membership.1]
    · exact mul_zero _
    · have scaled := mul_lt_mul_of_pos_left hx
        (inv_pos.mpr stageZeroSonineQ_pos)
      simpa [abs_mul, abs_of_pos stageZeroSonineQ_pos,
        abs_of_pos (inv_pos.mpr stageZeroSonineQ_pos),
        inv_mul_cancel₀ (ne_of_gt stageZeroSonineQ_pos)] using scaled
  · intro x hx
    rw [fourier_stageZeroSonineInverseDilation_apply]
    rw [membership.2]
    · ring
    · have multiplied : stageZeroSonineQ * |x| < 1 := by
        calc
          stageZeroSonineQ * |x| <
              stageZeroSonineQ * stageZeroSonineQ⁻¹ :=
            mul_lt_mul_of_pos_left hx stageZeroSonineQ_pos
          _ = 1 := mul_inv_cancel₀ (ne_of_gt stageZeroSonineQ_pos)
      simpa [abs_mul, abs_of_pos stageZeroSonineQ_pos] using multiplied


end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

