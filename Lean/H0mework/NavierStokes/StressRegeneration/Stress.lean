import H0mework.NavierStokes.StressRegeneration.Physical

set_option autoImplicit false
open scoped Topology BigOperators

namespace SaturationMonoid.NavierStokes.NativeWordStressBalance

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeSourceResolvent NativeFiniteActionResolvent
open NativeSourcePolynomialAction NativePhysicalActionWord NativeCompleteStressBilinear NativeCompleteStressCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def cross (source : StressAt escape) (index left right : ℕ) (time : ℝ) : Space :=
  mixedCLM (sourceWord source index velocity left time) (sourceWord source index velocity right time)

theorem cross_hasDerivAt (source : StressAt escape) (index left right : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (cross source index left right)
      (cross source index (left + 1) right time + cross source index left (right + 1) time) time :=
  (mixedCLM.hasFDerivAt.comp_hasDerivAt time (sourceWord_hasDerivAt source index velocity left time inside)).clm_apply
    (sourceWord_hasDerivAt source index velocity right time inside)

def crossRate (source : StressAt escape) (index left right : ℕ) (time : ℝ) : Space :=
  cross source index (left + 1) right time + cross source index left (right + 1) time

theorem crossRate_hasDerivAt (source : StressAt escape) (index left right : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (crossRate source index left right)
      (cross source index (left + 2) right time +
        2 • cross source index (left + 1) (right + 1) time +
        cross source index left (right + 2) time) time := by
  have actual := (cross_hasDerivAt source index (left + 1) right time inside).add
    (cross_hasDerivAt source index left (right + 1) time inside)
  convert! actual using 1
  simp only [two_smul]
  abel

theorem cross_zero_original (source : StressAt escape) (index : ℕ) (time : ℝ) :
    cross source index 0 0 time = sourceWord source index stress 0 time := rfl

theorem crossRate_zero_original (source : StressAt escape) (index : ℕ) (time : ℝ) :
    crossRate source index 0 0 time = sourceWord source index stress 1 time := by
  rw [sourceWord_stressRate]
  simp only [crossRate, cross, zero_add, sourceWord_velocityRate, sourceWord_velocity]
  rfl

theorem source_stress_second (source : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    sourceWord source index stress 2 time = cross source index 2 0 time +
      2 • cross source index 1 1 time + cross source index 0 2 time := by
  have actual := sourceWord_hasDerivAt source index stress 1 time inside
  have generated := crossRate_hasDerivAt source index 0 0 time inside
  have original : crossRate source index 0 0 = sourceWord source index stress 1 :=
    funext (crossRate_zero_original source index)
  rw [original] at generated
  exact actual.unique generated

theorem balanced_second_stress (source : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    sourceWord source index stress 2 time - cross source index 2 0 time - cross source index 0 2 time =
      2 • cross source index 1 1 time := by
  rw [source_stress_second source index time inside]
  abel

end
end SaturationMonoid.NavierStokes.NativeWordStressBalance
