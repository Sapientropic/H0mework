import H0mework.NavierStokes.StressRegeneration.Stress
import H0mework.NavierStokes.StressWeakInput.PhysicalPairing

set_option autoImplicit false
open scoped Topology BigOperators

namespace SaturationMonoid.NavierStokes.NativeWordStressEnergy

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeSourceResolvent NativeFiniteActionResolvent
open NativeSourcePolynomialAction NativePhysicalActionWord NativeWordStressBalance NativeCompleteStressBilinear
open NativeCompleteStressCarrier NativePhysicalPairing NativeEndpointVelocityCarrier

noncomputable section

def kineticRead : Space →L[ℝ] ℝ :=
  -∑ coordinate : Coordinate, Complex.reCLM.comp (readCLM 0 coordinate coordinate)

theorem kineticRead_apply (value : Space) :
    kineticRead value = -(∑ coordinate : Coordinate, (read value 0 coordinate coordinate).re) := by
  simp only [kineticRead, neg_apply, sum_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply, readCLM_apply]

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem source_word_energy (source : StressAt escape) (pointLe : point ≤ 1) (index order : ℕ)
    (time : Icc (0 : ℝ) 1) :
    kineticRead (cross source index order order time.1) =
      ‖coefficients (modes source index) (physicalWord source index order time.1)‖ ^ 2 := by
  let value := includeCLM (modes source index) (modes_closed source index) (physicalWord source index order time.1)
  have whole : wholeVelocity value.1 = sourceWord source index velocity order time.1 := by
    change wholeVelocity
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize
        (physicalWord source index order time.1).1) = _
    rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
      (physical_supported (physicalWord source index order time.1) 0 (modes_zero source index))]
    exact physicalWord_coe source pointLe index order time.1 time.2
  have tensor : read (cross source index order order time.1) = NativeCofinalFluxPairing.bilinearFlux value.1 value.1 := by
    change read (mixed (sourceWord source index velocity order time.1) (sourceWord source index velocity order time.1)) = _
    rw [mixed_read]
    change NativeHigherTimeJets.mixedFlux _ _ = NativeHigherTimeJets.mixedFlux (wholeVelocity value.1) (wholeVelocity value.1)
    rw [whole]
  rw [kineticRead_apply, tensor, NativeCofinalFluxPairing.bilinearFlux_zero_trace value.1 value.2.2, neg_neg]
  change ‖value‖ ^ 2 = _
  rw [include_norm (modes source index) (modes_zero source index) (modes_closed source index)]

theorem balanced_second_energy (source : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    kineticRead (sourceWord source index stress 2 time.1 - cross source index 2 0 time.1 - cross source index 0 2 time.1) =
      2 * ‖coefficients (modes source index) (physicalWord source index 1 time.1)‖ ^ 2 := by
  rw [balanced_second_stress source index time.1 time.2, map_nsmul, source_word_energy source pointLe index 1 time, nsmul_eq_mul, Nat.cast_ofNat]

theorem first_word_bound (source : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    2 * ‖coefficients (modes source index) (physicalWord source index 1 time.1)‖ ^ 2 ≤
      ‖kineticRead‖ * ‖sourceWord source index stress 2 time.1 - cross source index 2 0 time.1 - cross source index 0 2 time.1‖ := by
  have paid := kineticRead.le_opNorm
    (sourceWord source index stress 2 time.1 - cross source index 2 0 time.1 - cross source index 0 2 time.1)
  rw [balanced_second_energy source pointLe index time, Real.norm_of_nonneg (by positivity)] at paid
  exact paid

end
end SaturationMonoid.NavierStokes.NativeWordStressEnergy
