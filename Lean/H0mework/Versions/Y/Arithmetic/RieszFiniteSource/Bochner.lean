import H0mework.Versions.Y.Arithmetic.RieszResponse.ResponseRead
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex MeasureTheory
open scoped Topology
noncomputable section

theorem nativeRead_continuous (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    Continuous (fun shift : ℝ =>
      (value : TemperedDistribution ℝ ℂ) (coPoissonSchwartzEnergyTranslation (-shift) test)) := by
  let read : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  exact (read.continuous.comp (burnolMultiplicativeDilation_stronglyContinuous value)).congr
    (OriginalRieszFiniteResponse.original_read value test)

theorem nativeWeightedRead_integrable (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ)
    (test : SchwartzMap ℝ ℂ) :
    IntervalIntegrable (fun time : ℝ =>
      Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) *
        (value : TemperedDistribution ℝ ℂ) (coPoissonSchwartzEnergyTranslation (-time) test))
      volume 0 endpoint := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact (weight.mul (nativeRead_continuous value test)).intervalIntegrable 0 endpoint

def nativeIntegrand (lambda : ℂ) (value : BurnolL2) (endpoint time : ℝ) : BurnolL2 :=
  Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) • burnolMultiplicativeDilation time value

theorem nativeIntegrand_continuous (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ) :
    Continuous (nativeIntegrand lambda value endpoint) := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact weight.smul (burnolMultiplicativeDilation_stronglyContinuous value)

def nativeIntegral (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ) : BurnolL2 :=
  ∫ time : ℝ in (0 : ℝ)..endpoint, nativeIntegrand lambda value endpoint time

theorem nativeIntegrand_integrable (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ) :
    IntervalIntegrable (nativeIntegrand lambda value endpoint) volume 0 endpoint :=
  (nativeIntegrand_continuous lambda value endpoint).intervalIntegrable 0 endpoint

theorem nativeIntegral_read (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ)
    (test : SchwartzMap ℝ ℂ) :
    (nativeIntegral lambda value endpoint : TemperedDistribution ℝ ℂ) test =
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) *
          (value : TemperedDistribution ℝ ℂ) (coPoissonSchwartzEnergyTranslation (-time) test) := by
  let read : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  have source := read.intervalIntegral_comp_comm (nativeIntegrand_integrable lambda value endpoint)
  change read (nativeIntegral lambda value endpoint) = _
  unfold nativeIntegral
  rw [← source]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only [nativeIntegrand]
  rw [map_smul]
  change Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) *
    (burnolMultiplicativeDilation time value : TemperedDistribution ℝ ℂ) test = _
  rw [OriginalRieszFiniteResponse.original_read]

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
