import H0mework.Versions.X.NavierStokes.StressDynamics.TemporalDifferential

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativePhysicalActionWord

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeSourceResolvent NativeFiniteActionResolvent
open NativeSourcePolynomialAction NativeTemporalResolventReentry

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def physicalWord (source : StressAt escape) (index order : ℕ) (time : ℝ) : physicalSpace (modes source index) :=
  physicalRead (modes source index) (sourceWord source index velocity order time)

theorem physicalWord_zero (source : StressAt escape) (index : ℕ) (time : ℝ) :
    physicalWord source index 0 time = loadCurve source index time := rfl

theorem physicalWord_one (source : StressAt escape) (index : ℕ) (time : ℝ) :
    physicalWord source index 1 time = rateCurve source index time := by
  rw [physicalWord, sourceWord_velocityRate]
  rfl

theorem physicalWord_hasDerivAt (source : StressAt escape) (index order : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (physicalWord source index order) (physicalWord source index (order + 1) time) time :=
  (physicalRead (modes source index)).hasFDerivAt.comp_hasDerivAt time
    (sourceWord_hasDerivAt source index velocity order time inside)

theorem physicalWord_coe (source : StressAt escape) (pointLe : point ≤ 1) (index order : ℕ)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    (physicalWord source index order time).1 = sourceWord source index velocity order time := by
  induction order generalizing time with
  | zero => exact loadCurve_coe source pointLe index ⟨time, inside⟩
  | succ order previous =>
      have original := sourceWord_hasDerivAt source index velocity order time inside
      have projected := (physicalSpace (modes source index)).subtypeL.hasFDerivAt.comp_hasDerivAt time
        (physicalWord_hasDerivAt source index order time inside)
      have matched := projected.hasDerivWithinAt.congr_of_mem (fun sample member => (previous sample member).symm) inside
      exact (matched.derivWithin (uniqueDiffOn_Icc zero_lt_one time inside)).symm.trans
        (original.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one time inside))

end
end SaturationMonoid.NavierStokes.NativePhysicalActionWord
