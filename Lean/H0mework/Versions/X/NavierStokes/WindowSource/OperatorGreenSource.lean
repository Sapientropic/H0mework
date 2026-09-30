import H0mework.Versions.X.NavierStokes.WindowSource.OperatorGreenAlgebra
import H0mework.Versions.X.NavierStokes.StressResolvent.SourceResolvent
import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.Evolution

set_option autoImplicit false
namespace SaturationMonoid.NavierStokes.NativeWindowOperatorGreen
open Set NativeFiniteActionResolvent NativeResolventAdjoint NativeSourceResolvent NativeCommonAdvectorAction
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRawStressAction NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramRaw
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
noncomputable section
variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def sourceRate (source : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    physicalSpace (modes source index) :=
  physicalOperator (modes source index) (modes_zero source index) (modes_closed source index) nu
    (advector source pointLe index node) (advector_reality source pointLe index node) (load source pointLe index node)

theorem sourceRate_original (source : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    (sourceRate source pointLe index node).1 = rawRate source index (sample source pointLe index node).1 := by
  change sourceOperator source index (sample source pointLe index node).1
    (rawField source index (sample source pointLe index node).1) = _
  exact source_diagonal source index _ (sample source pointLe index node).2

theorem sourceRate_derivative (source : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    HasDerivAt (rawField source index) (sourceRate source pointLe index node).1 (sample source pointLe index node).1 := by
  rw [sourceRate_original]
  exact rawField_hasDerivAt source index _ (sample source pointLe index node).2

theorem source_green (source : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (test : Module.End ℝ (physicalSpace (modes source index))) :
    pairing (modes source index) (sourceRate source pointLe index node) (test (load source pointLe index node))+
      pairing (modes source index) (load source pointLe index node) (test (sourceRate source pointLe index node)) =
        pairing (modes source index) (load source pointLe index node)
          (lyapunov (modes source index) (modes_zero source index) (modes_closed source index) nu
            (advector source pointLe index node) (advector_reality source pointLe index node) test
              (load source pointLe index node)) :=
  whole_green _ _ _ _ _ _ test (load source pointLe index node)

theorem source_convection_original (source : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (wave : IntegerWavevector) :
    (convection (modes source index) (modes_zero source index) (modes_closed source index) nu
      (advector source pointLe index node) (advector_reality source pointLe index node)
        (load source pointLe index node)).1 wave =
      NativeUnheatedStressPairEvolution.nonlinear source index (sample source pointLe index node).1 wave := by
  have split := congrArg (fun action : Module.End ℝ (physicalSpace (modes source index)) =>
      (action (load source pointLe index node)).1 wave)
    (operator_split (modes source index) (modes_zero source index) (modes_closed source index) nu
      (advector source pointLe index node) (advector_reality source pointLe index node))
  change (sourceRate source pointLe index node).1 wave =
    -nu.coeff • (laplacian (modes source index) (modes_zero source index) (modes_closed source index) nu
      (load source pointLe index node)).1 wave+_ at split
  rw [sourceRate_original,laplacian_row] at split
  change rawRate source index (sample source pointLe index node).1 wave =
    -nu.coeff • (integerWaveViscousMultiplier wave • rawField source index (sample source pointLe index node).1 wave)+_ at split
  calc
    _ = rawRate source index (sample source pointLe index node).1 wave+
        (nu.coeff*integerWaveViscousMultiplier wave) • rawField source index (sample source pointLe index node).1 wave := by
      rw [split]
      module
    _ = _ := by
      rw [NativeUnheatedStressPairEvolution.rate_split source index _ (sample source pointLe index node).2]
      abel

end
end SaturationMonoid.NavierStokes.NativeWindowOperatorGreen
