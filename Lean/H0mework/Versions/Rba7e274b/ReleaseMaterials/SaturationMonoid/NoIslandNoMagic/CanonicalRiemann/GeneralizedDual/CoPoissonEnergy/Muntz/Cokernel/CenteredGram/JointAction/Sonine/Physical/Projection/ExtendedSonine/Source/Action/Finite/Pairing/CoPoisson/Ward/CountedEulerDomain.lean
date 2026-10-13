import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DilationWard
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.EdgeSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ResponseCountingLimit

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedEulerDomain

open Complex Filter MeasureTheory
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section

def fourierValue (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  CountingDual.value coordinate - Kernel.beta coordinate • ConstantDual.value

def fourierVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (star coordinate.value - 1 / 2) • CountingDual.value coordinate +
    Kernel.A coordinate • ResponseCounting.value false -
    Kernel.beta coordinate • ResponseCounting.value true +
    ((1 / 2 : ℂ) * Kernel.beta coordinate) • ConstantDual.value

/-- The same original b and endpoint source generate the regularized field by actual finite counting. -/
theorem fourier_from_source (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => DualSource.source N
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) -
        Kernel.beta coordinate • ConstantDual.seed)) atTop (𝓝 (fourierValue coordinate)) := by
  have actual := (CountingDual.original_dual_tendsto coordinate).sub
    (ConstantDual.original_tendsto.const_smul (Kernel.beta coordinate))
  apply actual.congr'
  apply Eventually.of_forall
  intro N
  simp only [CountingDual.dual_eq_adjoint, map_sub, map_smul]

private def read (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)

/-- The original response limits and the computed whole edge generate an actual L² Euler value. -/
theorem fourier_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (fourierValue coordinate : TemperedDistribution ℝ ℂ) =
      (fourierVelocity coordinate : TemperedDistribution ℝ ℂ) := by
  ext test
  have u := ((read test).continuous.tendsto (ResponseCounting.value false)).comp
    (ResponseCounting.finite_tendsto false)
  have v := ((read test).continuous.tendsto (ResponseCounting.value true)).comp
    (ResponseCounting.finite_tendsto true)
  have paired := (u.const_mul (Kernel.A coordinate)).sub (v.const_mul (Kernel.beta coordinate))
  have original := tendsto_nhds_unique (EdgeSource.original_response_limit coordinate test) paired
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierValue coordinate)) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierVelocity coordinate)) test
  simp only [fourierValue, fourierVelocity, map_add, map_sub, map_smul,
    add_apply, sub_apply, smul_apply, smul_eq_mul, Lp.toTemperedDistributionCLM_apply]
  change GapEuler.euler (CountingDual.value coordinate : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test = _
  change GapEuler.euler (CountingDual.value coordinate : TemperedDistribution ℝ ℂ) test -
      (star coordinate.value - 1 / 2) * (CountingDual.value coordinate : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test +
        (1 / 2 : ℂ) * (ConstantDual.value : TemperedDistribution ℝ ℂ) test) =
    Kernel.A coordinate * (ResponseCounting.value false : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (ResponseCounting.value true : TemperedDistribution ℝ ℂ) test at original
  linear_combination original

theorem fourier_strong_derivative (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift (fourierValue coordinate))
      (fourierVelocity coordinate) 0 :=
  DilationWard.strong_derivative _ _ (fourier_euler coordinate)

/-- Both independent original source fields enter the actual unitary Ward consumer. -/
theorem fourier_cross_balance (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (fourierVelocity left) (fourierValue right) +
      inner ℂ (fourierValue left) (fourierVelocity right) = 0 :=
  DilationWard.cross_balance _ _ _ _ (fourier_euler left) (fourier_euler right)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountedEulerDomain
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
