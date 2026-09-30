import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.Edge

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex FourierTransform MeasureTheory
open scoped FourierTransform Topology
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

def fourierPrimitive (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (edgePrimitive coordinate)

theorem fourierPrimitive_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ) +
      (star coordinate.value - 1 / 2) • (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ) =
      (2 * (star coordinate.value - 1 / 2)) •
        (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ) - 𝓕 (GapEuler.edge q) := by
  have source := congrArg (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (edgePrimitive_euler coordinate)
  simp only [map_add, map_smul, fourierCLM_apply] at source
  have same : (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ) =
      𝓕 (edgePrimitive coordinate : TemperedDistribution ℝ ℂ) := by
    rw [Lp.fourier_toTemperedDistribution_eq]
    rfl
  rw [same, GapEuler.euler_fourier, ← source]
  module

theorem fourierPrimitive_action (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (shift : ℝ) :
    GapEuler.euler
        (burnolMultiplicativeDilation shift (fourierPrimitive coordinate) : TemperedDistribution ℝ ℂ) test +
      (star coordinate.value - 1 / 2) *
        (burnolMultiplicativeDilation shift (fourierPrimitive coordinate) : TemperedDistribution ℝ ℂ) test =
      (2 * (star coordinate.value - 1 / 2)) *
        (burnolMultiplicativeDilation shift (fourierPrimitive coordinate) : TemperedDistribution ℝ ℂ) test -
      (𝓕 (GapEuler.edge q)) (coPoissonSchwartzEnergyTranslation (-shift) test) := by
  have source := congrArg (fun value : TemperedDistribution ℝ ℂ =>
    value (coPoissonSchwartzEnergyTranslation (-shift) test)) (fourierPrimitive_euler coordinate)
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul] at source
  rw [OriginalRieszFiniteResponse.original_euler_action, OriginalRieszFiniteResponse.original_read]
  exact source

theorem fourierEdge_read_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    Continuous (fun shift : ℝ => (𝓕 (GapEuler.edge q))
      (coPoissonSchwartzEnergyTranslation (-shift) test)) := by
  let eval : TemperedDistribution ℝ ℂ →L[ℂ] ℂ :=
    PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test
  let valueRead : BurnolL2 →L[ℂ] ℂ := eval.comp (Lp.toTemperedDistributionCLM ℂ volume 2)
  let eulerRead : BurnolL2 →L[ℂ] ℂ :=
    (eval.comp GapEuler.euler).comp (Lp.toTemperedDistributionCLM ℂ volume 2)
  have orbit := burnolMultiplicativeDilation_stronglyContinuous (fourierPrimitive coordinate)
  have generated : Continuous (fun shift : ℝ =>
      (star coordinate.value - 1 / 2) *
        valueRead (burnolMultiplicativeDilation shift (fourierPrimitive coordinate)) -
      eulerRead (burnolMultiplicativeDilation shift (fourierPrimitive coordinate))) :=
    (continuous_const.mul (valueRead.continuous.comp orbit)).sub (eulerRead.continuous.comp orbit)
  apply generated.congr
  intro shift
  have action := fourierPrimitive_action coordinate test shift
  change (star coordinate.value - 1 / 2) *
      (burnolMultiplicativeDilation shift (fourierPrimitive coordinate) : TemperedDistribution ℝ ℂ) test -
    GapEuler.euler
      (burnolMultiplicativeDilation shift (fourierPrimitive coordinate) : TemperedDistribution ℝ ℂ) test = _
  linear_combination -action

theorem fourierEdge_read_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    IntervalIntegrable (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
        (𝓕 (GapEuler.edge q)) (coPoissonSchwartzEnergyTranslation (-time) test)) volume 0 endpoint := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact (weight.mul (fourierEdge_read_continuous coordinate test)).intervalIntegrable 0 endpoint

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
