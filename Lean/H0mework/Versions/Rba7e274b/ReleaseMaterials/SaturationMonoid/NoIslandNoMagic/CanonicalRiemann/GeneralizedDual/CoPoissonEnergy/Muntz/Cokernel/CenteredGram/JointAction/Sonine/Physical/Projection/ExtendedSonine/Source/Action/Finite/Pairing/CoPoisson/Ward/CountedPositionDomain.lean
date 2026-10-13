import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedEulerDomain
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCountedEuler
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.JointCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedEulerDomain

open Complex Filter MeasureTheory
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section

def positionValue (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : BurnolL2 :=
  PositionCounting.value coordinate zero + Kernel.A coordinate • ConstantDual.value

def positionVelocity (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : BurnolL2 :=
  -(star coordinate.value - 1 / 2) • PositionCounting.value coordinate zero +
    Kernel.A coordinate • ResponseCounting.value true -
    Kernel.beta coordinate • ResponseCounting.value false -
    ((1 / 2 : ℂ) * Kernel.A coordinate) • ConstantDual.value

/-- The actual full L¹ source limit and the two independent inverse responses generate the L² Euler value. -/
theorem position_euler (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    GapEuler.euler (positionValue coordinate zero : TemperedDistribution ℝ ℂ) =
      (positionVelocity coordinate zero : TemperedDistribution ℝ ℂ) := by
  ext test
  let reader : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  have u := (reader.continuous.tendsto (ResponseCounting.value false)).comp
    (ResponseCounting.finite_tendsto false)
  have v := (reader.continuous.tendsto (ResponseCounting.value true)).comp
    (ResponseCounting.finite_tendsto true)
  have paired := (v.const_mul (Kernel.A coordinate)).sub (u.const_mul (Kernel.beta coordinate))
  have original := tendsto_nhds_unique (PositionCountedEuler.original_response_limit coordinate zero test) paired
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (positionValue coordinate zero)) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2 (positionVelocity coordinate zero)) test
  simp only [positionValue, positionVelocity, map_add, map_sub, map_smul,
    add_apply, sub_apply, smul_apply, smul_eq_mul, Lp.toTemperedDistributionCLM_apply]
  change GapEuler.euler (PositionCounting.value coordinate zero : TemperedDistribution ℝ ℂ) test +
      Kernel.A coordinate * GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test = _
  change GapEuler.euler (PositionCounting.value coordinate zero : TemperedDistribution ℝ ℂ) test +
      (star coordinate.value - 1 / 2) * (PositionCounting.value coordinate zero : TemperedDistribution ℝ ℂ) test +
      Kernel.A coordinate * (GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test +
        (1 / 2 : ℂ) * (ConstantDual.value : TemperedDistribution ℝ ℂ) test) =
    Kernel.A coordinate * (ResponseCounting.value true : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (ResponseCounting.value false : TemperedDistribution ℝ ℂ) test at original
  linear_combination original

theorem position_strong_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift (positionValue coordinate zero))
      (positionVelocity coordinate zero) 0 :=
  DilationWard.strong_derivative _ _ (position_euler coordinate zero)

theorem mixed_cross_balance (left right : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta left.value = 0) :
    inner ℂ (positionVelocity left zero) (fourierValue right) +
      inner ℂ (positionValue left zero) (fourierVelocity right) = 0 :=
  DilationWard.cross_balance _ _ _ _ (position_euler left zero) (fourier_euler right)

/-- The original joint counting output is unchanged by the two opposite edge corrections. -/
theorem joint_value (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    JointCounting.value coordinate zero =
      Kernel.beta coordinate • positionValue coordinate zero + Kernel.A coordinate • fourierValue coordinate := by
  unfold JointCounting.value positionValue fourierValue
  module

def jointVelocity (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : BurnolL2 :=
  (star coordinate.value - 1 / 2) •
    (Kernel.A coordinate • CountingDual.value coordinate - Kernel.beta coordinate • PositionCounting.value coordinate zero) +
      (Kernel.A coordinate ^ 2 - Kernel.beta coordinate ^ 2) • ResponseCounting.value false

private theorem joint_velocity (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Kernel.beta coordinate • positionVelocity coordinate zero + Kernel.A coordinate • fourierVelocity coordinate =
      jointVelocity coordinate zero := by
  unfold positionVelocity fourierVelocity jointVelocity
  module

/-- Both entire counted source equations generate the actual Euler-domain equation for the original joint. -/
theorem joint_euler (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    GapEuler.euler (JointCounting.value coordinate zero : TemperedDistribution ℝ ℂ) =
      (jointVelocity coordinate zero : TemperedDistribution ℝ ℂ) := by
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (JointCounting.value coordinate zero)) =
    Lp.toTemperedDistributionCLM ℂ volume 2 (jointVelocity coordinate zero)
  rw [joint_value, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
  change Kernel.beta coordinate • GapEuler.euler (positionValue coordinate zero : TemperedDistribution ℝ ℂ) +
    Kernel.A coordinate • GapEuler.euler (fourierValue coordinate : TemperedDistribution ℝ ℂ) = _
  rw [position_euler, fourier_euler]
  simpa only [map_add, map_smul, Lp.toTemperedDistributionCLM_apply] using
    congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) (joint_velocity coordinate zero)

theorem joint_strong_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift (JointCounting.value coordinate zero))
      (jointVelocity coordinate zero) 0 :=
  DilationWard.strong_derivative _ _ (joint_euler coordinate zero)

/-- The complete independent source pair consumes the two actual generated Euler-domain values. -/
theorem joint_cross_balance (left right : BurnolCompletedMellinCoordinate)
    (leftZero : riemannZeta left.value = 0) (rightZero : riemannZeta right.value = 0) :
    inner ℂ (jointVelocity left leftZero) (JointCounting.value right rightZero) +
      inner ℂ (JointCounting.value left leftZero) (jointVelocity right rightZero) = 0 :=
  DilationWard.cross_balance _ _ _ _ (joint_euler left leftZero) (joint_euler right rightZero)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountedEulerDomain
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
