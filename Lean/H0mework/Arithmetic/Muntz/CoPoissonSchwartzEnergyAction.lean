import H0mework.Realization.Topology.HilbertCokernelAction
import H0mework.Arithmetic.Muntz.CoPoissonEnergyNaturality

/-!
# Invertible Schwartz action for the co-Poisson energy map

The normalized Schwartz scaling is a genuine additive log-translation
action.  Together with the existing energy translation it supplies the
strict invertible action square consumed by the generic Hilbert cokernel.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex
open ClozelEndpointSourceEffect
open SourceGeneratedHilbertCokernel
open scoped SchwartzMap

noncomputable section

@[simp]
theorem coPoissonSchwartzEnergyTranslation_zero
    (test : SchwartzMap ℝ ℂ) :
    coPoissonSchwartzEnergyTranslation 0 test = test := by
  apply SchwartzMap.ext
  intro x
  change (Real.exp 0 : ℂ) ^ (1 / 2 : ℂ) *
      test (Real.exp 0 * x) = test x
  simp

theorem coPoissonSchwartzEnergyTranslation_add
    (left right : ℝ) :
    (coPoissonSchwartzEnergyTranslation left).comp
        (coPoissonSchwartzEnergyTranslation right) =
      coPoissonSchwartzEnergyTranslation (left + right) := by
  apply LinearMap.ext
  intro test
  apply SchwartzMap.ext
  intro x
  change
    (Real.exp left : ℂ) ^ (1 / 2 : ℂ) *
        ((Real.exp right : ℂ) ^ (1 / 2 : ℂ) *
          test (Real.exp right * (Real.exp left * x))) =
      (Real.exp (left + right) : ℂ) ^ (1 / 2 : ℂ) *
        test (Real.exp (left + right) * x)
  rw [Real.exp_add, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg
      (Real.exp_nonneg left) (Real.exp_nonneg right)]
  ring_nf

/-- The normalized source action has inverse shift `-h`. -/
def coPoissonSchwartzEnergyTranslationEquiv (h : ℝ) :
    SchwartzMap ℝ ℂ ≃ₗ[ℂ] SchwartzMap ℝ ℂ :=
  { coPoissonSchwartzEnergyTranslation h with
    invFun := coPoissonSchwartzEnergyTranslation (-h)
    left_inv := by
      intro test
      have applied := LinearMap.congr_fun
        (coPoissonSchwartzEnergyTranslation_add (-h) h) test
      simpa using applied
    right_inv := by
      intro test
      have applied := LinearMap.congr_fun
        (coPoissonSchwartzEnergyTranslation_add h (-h)) test
      simpa using applied }

@[simp]
theorem coPoissonSchwartzEnergyTranslationEquiv_apply
    (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    coPoissonSchwartzEnergyTranslationEquiv h test =
      coPoissonSchwartzEnergyTranslation h test :=
  rfl

/-- The source-generated energy map and its two actual translation actions
form the invertible square required by the generic closed-range cokernel. -/
def coPoissonLogOrbitEnergyActionSquare (h : ℝ) :
    SourceGeneratedHilbertCokernel.ActionSquare
      coPoissonLogOrbitEnergyMap where
  sourceAction := coPoissonSchwartzEnergyTranslationEquiv h
  targetAction := positiveMellinQuarterEnergyTranslationIsometry h
  commutes := fun source =>
    (coPoissonLogOrbitEnergyMap_translation_square h source).symm

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
