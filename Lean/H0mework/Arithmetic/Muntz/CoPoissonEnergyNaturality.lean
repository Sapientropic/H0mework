import H0mework.Arithmetic.CoPoisson.Energy
import H0mework.Arithmetic.MuntzAction.CoPoissonTranslationCarrier

/-!
# Scaling/translation naturality of the co-Poisson energy map

The raw Schwartz scaling square carries the exact Tate half-weight.  Absorbing
that cocycle into the source action gives a literal commuting square with the
existing measure-preserving energy translation.
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

open Complex MeasureTheory
open ClozelEndpointSourceEffect
open scoped SchwartzMap

noncomputable section

/-- Raw scaling naturality with the unavoidable Tate half-weight. -/
theorem coPoissonLogOrbitEnergyMap_scaledSchwartzTest
    (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    coPoissonLogOrbitEnergyMap
        (scaledSchwartzTest (Real.exp h) (Real.exp_ne_zero h) test) =
      (Real.exp h : ℂ) ^ (-(1 / 2 : ℂ)) •
        positiveMellinQuarterEnergyTranslation h
          (coPoissonLogOrbitEnergyMap test) := by
  apply Lp.ext
  let shiftMeasurePreserving :=
    measurePreserving_add_left (volume : Measure ℝ) h
  filter_upwards [
    coPoissonLogOrbitEnergyMap_coeFn
      (scaledSchwartzTest (Real.exp h) (Real.exp_ne_zero h) test),
    Lp.coeFn_smul ((Real.exp h : ℂ) ^ (-(1 / 2 : ℂ)))
      (positiveMellinQuarterEnergyTranslation h
        (coPoissonLogOrbitEnergyMap test)),
    Lp.coeFn_compMeasurePreserving (coPoissonLogOrbitEnergyMap test)
      shiftMeasurePreserving,
    shiftMeasurePreserving.quasiMeasurePreserving.ae
      (coPoissonLogOrbitEnergyMap_coeFn test)] with x hscaled hsmul hshift horbit
  rw [hscaled, hsmul]
  change coPoissonLogOrbitMap
      (scaledSchwartzTest (Real.exp h) (Real.exp_ne_zero h) test) x =
    (Real.exp h : ℂ) ^ (-(1 / 2 : ℂ)) *
      (Lp.compMeasurePreserving (fun y : ℝ => h + y)
        shiftMeasurePreserving (coPoissonLogOrbitEnergyMap test)) x
  rw [hshift]
  simp only [Function.comp_apply]
  rw [horbit]
  have pointwise := congrFun
    (coPoissonHalfWeightedTranslation_orbit h test) x
  simpa only [coPoissonHalfWeightedTranslation, LinearMap.coe_mk,
    AddHom.coe_mk, add_comm] using pointwise.symm

/-- Schwartz scaling normalized by the same half-weight as the co-Poisson
orbit. -/
def coPoissonSchwartzEnergyTranslation (h : ℝ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ where
  toFun test := (Real.exp h : ℂ) ^ (1 / 2 : ℂ) •
    scaledSchwartzTest (Real.exp h) (Real.exp_ne_zero h) test
  map_add' left right := by
    apply SchwartzMap.ext
    intro x
    change (Real.exp h : ℂ) ^ (1 / 2 : ℂ) *
        (left (Real.exp h * x) + right (Real.exp h * x)) =
      (Real.exp h : ℂ) ^ (1 / 2 : ℂ) * left (Real.exp h * x) +
        (Real.exp h : ℂ) ^ (1 / 2 : ℂ) * right (Real.exp h * x)
    ring
  map_smul' coefficient test := by
    apply SchwartzMap.ext
    intro x
    change (Real.exp h : ℂ) ^ (1 / 2 : ℂ) *
        (coefficient * test (Real.exp h * x)) =
      coefficient * ((Real.exp h : ℂ) ^ (1 / 2 : ℂ) *
        test (Real.exp h * x))
    ring

/-- The normalized source action and the existing energy translation commute
strictly through the source-owned energy map. -/
theorem coPoissonLogOrbitEnergyMap_translation_square
    (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    coPoissonLogOrbitEnergyMap
        (coPoissonSchwartzEnergyTranslation h test) =
      positiveMellinQuarterEnergyTranslation h
        (coPoissonLogOrbitEnergyMap test) := by
  change coPoissonLogOrbitEnergyMap
      ((Real.exp h : ℂ) ^ (1 / 2 : ℂ) •
        scaledSchwartzTest (Real.exp h) (Real.exp_ne_zero h) test) = _
  rw [map_smul, coPoissonLogOrbitEnergyMap_scaledSchwartzTest, smul_smul]
  have cancellation : (Real.exp h : ℂ) ^ (1 / 2 : ℂ) *
      (Real.exp h : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h))]
    norm_num
  rw [cancellation, one_smul]

end


end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
