import H0mework.Arithmetic.Mellin.QuarterL2
import H0mework.Arithmetic.CoPoisson.Energy

/-!
# Square-root co-Poisson chart in the quarter Mellin carrier

The additive co-Poisson variable is the square root of the theta/Mellin
variable.  Pulling an actual Schwartz orbit back along `t ↦ √t` therefore
produces a positive Mellin function whose log-quarter chart is exactly the
co-Poisson log orbit at half scale.  This removes a real factor-of-two
coordinate mismatch; it does not assert the general co-Poisson--Mellin value
formula or any zero annihilation.
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
open scoped SchwartzMap ENNReal

noncomputable section

/-- The positive Mellin function obtained from the actual co-Poisson
remainder at square-root scale. -/
def coPoissonQuarterMellinMap :
    SchwartzMap ℝ ℂ →ₗ[ℂ] ClozelPositiveMellinFunction where
  toFun test t :=
    clozelTemperedRemainder
      (scaledSchwartzTest (Real.sqrt t.1)
        (Real.sqrt_pos.2 t.2).ne' test)
  map_add' left right := by
    funext t
    simp only [Pi.add_apply]
    unfold scaledSchwartzTest
    rw [map_add, map_add]
  map_smul' coefficient test := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply]
    unfold scaledSchwartzTest
    rw [map_smul, map_smul]

private theorem complexExp_half_cpow (x : ℝ) :
    (Real.exp (x / 2) : ℂ) ^ (1 / 2 : ℂ) =
      (Real.exp (x / 4) : ℂ) := by
  calc
    _ = ((Real.exp (x / 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      symm
      convert Complex.ofReal_cpow (Real.exp_pos (x / 2)).le
        (1 / 2 : ℝ) using 1
      all_goals norm_num
    _ = _ := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos (x / 2)), Real.log_exp]
      congr 1
      ring_nf

/-- The exact coordinate law: the theta/Mellin logarithmic coordinate is
twice the additive co-Poisson coordinate. -/
theorem positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    positiveMellinLogQuarterTransform
        (coPoissonQuarterMellinMap test) x =
      coPoissonLogOrbitMap test (x / 2) := by
  change (Real.exp (x / 4) : ℂ) *
      clozelTemperedRemainder
        (scaledSchwartzTest (Real.sqrt (Real.exp x))
          (Real.sqrt_pos.2 (Real.exp_pos x)).ne' test) =
    (Real.exp (x / 2) : ℂ) ^ (1 / 2 : ℂ) *
      clozelTemperedRemainder
        (scaledSchwartzTest (Real.exp (x / 2))
          (Real.exp_ne_zero (x / 2)) test)
  rw [complexExp_half_cpow]
  have scaledEq :
      scaledSchwartzTest (Real.sqrt (Real.exp x))
          (Real.sqrt_pos.2 (Real.exp_pos x)).ne' test =
        scaledSchwartzTest (Real.exp (x / 2))
          (Real.exp_ne_zero (x / 2)) test := by
    apply SchwartzMap.ext
    intro y
    simp only [scaledSchwartzTest_apply]
    rw [← Real.exp_half]
  rw [scaledEq]

/-- Every actual co-Poisson orbit lands in the pre-existing quarter `L²`
carrier after the source-owned square-root recharting. -/
theorem coPoissonQuarterMellinMap_mem_quarterL2
    (test : SchwartzMap ℝ ℂ) :
    coPoissonQuarterMellinMap test ∈
      positiveMellinQuarterL2Submodule := by
  change MemLp
    (positiveMellinLogQuarterTransform
      (coPoissonQuarterMellinMap test)) (2 : ℝ≥0∞)
      (volume : Measure ℝ)
  rw [show positiveMellinLogQuarterTransform
      (coPoissonQuarterMellinMap test) =
        fun x : ℝ => coPoissonLogOrbitMap test (x / 2) by
    funext x
    exact positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap
      test x]
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => coPoissonLogOrbitMap test (x / 2))
      (volume : Measure ℝ) :=
    ((coPoissonLogOrbitMap_measurable test).comp
      (by fun_prop : Measurable fun x : ℝ => x / 2)).aestronglyMeasurable
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  have sourceMeas : AEStronglyMeasurable (coPoissonLogOrbitMap test)
      (volume : Measure ℝ) :=
    (coPoissonLogOrbitMap_measurable test).aestronglyMeasurable
  have sourceIntegrable : Integrable
      (fun x : ℝ => ‖coPoissonLogOrbitMap test x‖ ^ 2) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm sourceMeas).1
      (coPoissonLogOrbitMap_memLp test)
  have scaledIntegrable := sourceIntegrable.comp_mul_left'
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  apply scaledIntegrable.congr
  filter_upwards with x
  congr 2
  ring_nf

/-- Linear source map into the lawful quarter-`L²` face. -/
def coPoissonQuarterMellinL2Map :
    SchwartzMap ℝ ℂ →ₗ[ℂ] PositiveMellinQuarterL2 where
  toFun test :=
    ⟨coPoissonQuarterMellinMap test,
      coPoissonQuarterMellinMap_mem_quarterL2 test⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add coPoissonQuarterMellinMap left right
  map_smul' coefficient test := by
    apply Subtype.ext
    exact map_smul coPoissonQuarterMellinMap coefficient test

/-- Fourier transform on Schwartz tests becomes the already installed Tate
involution on the square-root co-Poisson chart. -/
theorem coPoissonQuarterMellinMap_fourier_tate
    (test : SchwartzMap ℝ ℂ) :
    coPoissonQuarterMellinMap (FourierTransform.fourier test) =
      positiveTateInvolution (coPoissonQuarterMellinMap test) := by
  apply positiveMellinLogQuarterTransform_injective
  funext x
  rw [positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap,
    positiveMellinLogQuarterTransform_tate,
    positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap]
  have reflection := coPoissonLogOrbitMap_fourier_reflection test (-x / 2)
  convert reflection using 1
  ring_nf

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
