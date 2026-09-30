import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.FourierPrimitive
import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.Bochner

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex FourierTransform MeasureTheory
open scoped FourierTransform Topology
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

/-- The same Fourier primitive supplies the required `2λ` correction through its actual L² orbit. -/
def fourierEdgeIntegral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  (2 * (star coordinate.value - 1 / 2)) •
      nativeIntegral (star coordinate.value - 1 / 2) (fourierPrimitive coordinate) endpoint -
    (burnolMultiplicativeDilation endpoint (fourierPrimitive coordinate) -
      fullMellinTranslationCharacter (star coordinate.value) endpoint • fourierPrimitive coordinate)

theorem fourierEdgeIntegral_read (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    (fourierEdgeIntegral coordinate endpoint : TemperedDistribution ℝ ℂ) test =
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          (𝓕 (GapEuler.edge q)) (coPoissonSchwartzEnergyTranslation (-time) test) := by
  let lambda := star coordinate.value - 1 / 2
  let value := fun time : ℝ =>
    (burnolMultiplicativeDilation time (fourierPrimitive coordinate) : TemperedDistribution ℝ ℂ) test
  let forcing := fun time : ℝ =>
    (𝓕 (GapEuler.edge q)) (coPoissonSchwartzEnergyTranslation (-time) test)
  let weight := fun time : ℝ => Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ)))
  let read : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  have valueContinuous : Continuous value := read.continuous.comp
    (burnolMultiplicativeDilation_stronglyContinuous (fourierPrimitive coordinate))
  have forcingContinuous : Continuous forcing := fourierEdge_read_continuous coordinate test
  have derivative (shift : ℝ) :
      HasDerivAt value ((2 * lambda * value shift - forcing shift) - lambda * value shift) shift := by
    have source := fourierPrimitive_action coordinate test shift
    have rhs : (2 * lambda * value shift - forcing shift) - lambda * value shift =
        GapEuler.euler
          (burnolMultiplicativeDilation shift (fourierPrimitive coordinate) :
            TemperedDistribution ℝ ℂ) test := by
      dsimp only [lambda, value, forcing]
      linear_combination -source
    rw [rhs]
    exact Dilation.original_weak_derivative (fourierPrimitive coordinate) test shift
  have generated := _root_.OriginalRieszFiniteResponse.Integration.finite_response value
    (fun time : ℝ => 2 * lambda * value time - forcing time) lambda derivative
    ((continuous_const.mul valueContinuous).sub forcingContinuous) endpoint
  have base : value 0 = (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ) test := by
    dsimp only [value]
    rw [OriginalRieszFiniteResponse.original_read, neg_zero, coPoissonSchwartzEnergyTranslation_zero]
  have weightContinuous : Continuous weight :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  have valueIntegrable : IntervalIntegrable (fun time : ℝ => weight time * value time)
      volume 0 endpoint := (weightContinuous.mul valueContinuous).intervalIntegrable 0 endpoint
  have forcingIntegrable : IntervalIntegrable (fun time : ℝ => weight time * forcing time)
      volume 0 endpoint := fourierEdge_read_integrable coordinate test endpoint
  have split : (∫ time : ℝ in (0 : ℝ)..endpoint,
      weight time * (2 * lambda * value time - forcing time)) =
      2 * lambda * (∫ time : ℝ in (0 : ℝ)..endpoint, weight time * value time) -
        ∫ time : ℝ in (0 : ℝ)..endpoint, weight time * forcing time := by
    calc
      _ = ∫ time : ℝ in (0 : ℝ)..endpoint,
          2 * lambda * (weight time * value time) - weight time * forcing time := by
        apply intervalIntegral.integral_congr
        intro time _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (valueIntegrable.const_mul _) forcingIntegrable,
          intervalIntegral.integral_const_mul]
  change value endpoint = Complex.exp (-lambda * (endpoint : ℂ)) * value 0 +
    ∫ time : ℝ in (0 : ℝ)..endpoint, weight time * (2 * lambda * value time - forcing time) at generated
  rw [base, split] at generated
  have character : fullMellinTranslationCharacter (star coordinate.value) endpoint =
      Complex.exp (-lambda * (endpoint : ℂ)) := by
    unfold fullMellinTranslationCharacter
    dsimp only [lambda]
    congr 1
    ring
  have nativeRead :
      (∫ time : ℝ in (0 : ℝ)..endpoint, weight time *
        (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ)
          (coPoissonSchwartzEnergyTranslation (-time) test)) =
      ∫ time : ℝ in (0 : ℝ)..endpoint, weight time * value time := by
    apply intervalIntegral.integral_congr
    intro time _
    exact congrArg (fun result : ℂ => weight time * result)
      (OriginalRieszFiniteResponse.original_read (fourierPrimitive coordinate) test time).symm
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierEdgeIntegral coordinate endpoint)) test = _
  simp only [fourierEdgeIntegral, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    Lp.toTemperedDistributionCLM_apply]
  rw [nativeIntegral_read]
  change 2 * lambda *
      (∫ time : ℝ in (0 : ℝ)..endpoint, weight time *
        (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ)
          (coPoissonSchwartzEnergyTranslation (-time) test)) -
      (value endpoint - fullMellinTranslationCharacter (star coordinate.value) endpoint *
        (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ) test) =
    ∫ time : ℝ in (0 : ℝ)..endpoint, weight time * forcing time
  rw [nativeRead, character, generated]
  ring

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
