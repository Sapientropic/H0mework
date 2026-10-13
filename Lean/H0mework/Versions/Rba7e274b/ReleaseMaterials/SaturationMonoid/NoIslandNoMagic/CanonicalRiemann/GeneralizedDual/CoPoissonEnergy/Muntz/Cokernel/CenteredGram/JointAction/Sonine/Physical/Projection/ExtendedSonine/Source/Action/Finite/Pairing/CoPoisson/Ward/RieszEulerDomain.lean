import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedPositionDomain

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.RieszEulerDomain

open Complex Filter FourierTransform MeasureTheory
open scoped Topology InnerProductSpace FourierTransform
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

/-- Both original jumps are corrected by the same original constant and its actual Fourier image. -/
def value (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (K coordinate : BurnolL2) - Kernel.A coordinate • ConstantDual.seed +
    Kernel.beta coordinate • fourierL2 ConstantDual.seed

def velocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(star coordinate.value - 1 / 2) • (K coordinate : BurnolL2) +
    Kernel.A coordinate • (fourierL2 Response.wholeU - Response.wholeV) +
    Kernel.beta coordinate • (Response.wholeU - fourierL2 Response.wholeV) +
    ((1 / 2 : ℂ) * Kernel.A coordinate) • ConstantDual.seed +
    ((1 / 2 : ℂ) * Kernel.beta coordinate) • fourierL2 ConstantDual.seed

private theorem constant_euler :
    GapEuler.euler (ConstantDual.seed : TemperedDistribution ℝ ℂ) =
      -GapEuler.edge q - (1 / 2 : ℂ) • (ConstantDual.seed : TemperedDistribution ℝ ℂ) := by
  ext test
  have source := ConstantDual.seed_edge test
  rw [ConstantDual.edgeRead_apply] at source
  simp only [sub_apply, neg_apply, smul_apply, smul_eq_mul]
  linear_combination -source

private theorem fourier_constant_euler :
    GapEuler.euler (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) =
      𝓕 (GapEuler.edge q) + (1 / 2 : ℂ) • (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) := by
  have native : 𝓕 (ConstantDual.seed : TemperedDistribution ℝ ℂ) =
      (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq _
  rw [← native, GapEuler.euler_fourier, constant_euler]
  change -(fourierCLM ℂ (TemperedDistribution ℝ ℂ))
    (-GapEuler.edge q - (1 / 2 : ℂ) • (ConstantDual.seed : TemperedDistribution ℝ ℂ)) = _
  rw [map_sub, map_neg, map_smul]
  change -(-𝓕 (GapEuler.edge q) - (1 / 2 : ℂ) • 𝓕 (ConstantDual.seed : TemperedDistribution ℝ ℂ)) =
    𝓕 (GapEuler.edge q) + (1 / 2 : ℂ) • 𝓕 (ConstantDual.seed : TemperedDistribution ℝ ℂ)
  module

/-- The original K equation and the complete Psi/dual-Psi source cancel both distribution contacts. -/
theorem original_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (value coordinate : TemperedDistribution ℝ ℂ) = (velocity coordinate : TemperedDistribution ℝ ℂ) := by
  have original := Kernel.original_kernel_euler coordinate
  have solved : GapEuler.euler (K coordinate : BurnolL2) =
      Kernel.A coordinate • Response.Psi + Kernel.beta coordinate • 𝓕 Response.Psi -
        (star coordinate.value - 1 / 2) • (K coordinate : BurnolL2) := eq_sub_of_add_eq original
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (value coordinate)) =
    Lp.toTemperedDistributionCLM ℂ volume 2 (velocity coordinate)
  simp only [value, velocity, map_add, map_sub, map_smul]
  change GapEuler.euler (K coordinate : BurnolL2) -
      Kernel.A coordinate • GapEuler.euler (ConstantDual.seed : TemperedDistribution ℝ ℂ) +
      Kernel.beta coordinate • GapEuler.euler (fourierL2 ConstantDual.seed : TemperedDistribution ℝ ℂ) = _
  have uFourier : 𝓕 (Response.wholeU : TemperedDistribution ℝ ℂ) =
      (fourierL2 Response.wholeU : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq _
  have vFourier : 𝓕 (Response.wholeV : TemperedDistribution ℝ ℂ) =
      (fourierL2 Response.wholeV : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq _
  rw [solved, Response.Psi_fourier, Response.Psi, constant_euler, fourier_constant_euler, uFourier, vFourier]
  simp only [Lp.toTemperedDistributionCLM_apply]
  module

theorem strong_derivative (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift (value coordinate)) (velocity coordinate) 0 :=
  DilationWard.strong_derivative _ _ (original_euler coordinate)

/-- The original K, with both explicit contact corrections, enters the independent position Ward. -/
theorem mixed_position (left right : BurnolCompletedMellinCoordinate) (zero : riemannZeta right.value = 0) :
    inner ℂ (velocity left) (CountedEulerDomain.positionValue right zero) +
      inner ℂ ((K left : BurnolL2) - Kernel.A left • ConstantDual.seed +
        Kernel.beta left • fourierL2 ConstantDual.seed) (CountedEulerDomain.positionVelocity right zero) = 0 :=
  DilationWard.cross_balance _ _ _ _ (original_euler left) (CountedEulerDomain.position_euler right zero)

/-- The independent Fourier source is paired before any original-K contact is discarded. -/
theorem mixed_fourier (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (velocity left) (CountedEulerDomain.fourierValue right) +
      inner ℂ ((K left : BurnolL2) - Kernel.A left • ConstantDual.seed +
        Kernel.beta left • fourierL2 ConstantDual.seed) (CountedEulerDomain.fourierVelocity right) = 0 :=
  DilationWard.cross_balance _ _ _ _ (original_euler left) (CountedEulerDomain.fourier_euler right)

/-- The original K and the complete original joint counting output meet in one complex Ward identity. -/
theorem mixed_joint (left right : BurnolCompletedMellinCoordinate) (zero : riemannZeta right.value = 0) :
    inner ℂ (velocity left) (JointCounting.value right zero) +
      inner ℂ ((K left : BurnolL2) - Kernel.A left • ConstantDual.seed +
        Kernel.beta left • fourierL2 ConstantDual.seed) (CountedEulerDomain.jointVelocity right zero) = 0 :=
  DilationWard.cross_balance _ _ _ _ (original_euler left) (CountedEulerDomain.joint_euler right zero)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.RieszEulerDomain
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
