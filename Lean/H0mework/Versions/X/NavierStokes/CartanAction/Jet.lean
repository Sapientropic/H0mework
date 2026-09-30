import H0mework.Versions.X.NavierStokes.CartanAction.Compensation

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanSourceJet

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineHolonomicField StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineFullDiracAdjointMaterial StageNineCartanAffineConnectionActualization
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineDiracDualYukawaSpinJurisdiction SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7MotherGaugeConnection
open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativePhysicalFourier NativePhysicalSource NativeSourceMaterialJet
open NativeSourceMaterialAdjoint NativeMaterialMomentumJet NativeMaterialAdjointPrincipal NativeMaterialAdjointAction
open NativePauliCoframeAction NativeMaterialJetAction NativeCartanCompensation

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def gaugeConnection (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) : P286LieBlockData :=
  NativePauliCoframeAction.connection velocity (target velocity derivative) direction + correction velocity direction

def connectionOperator (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift (NativeSourceCartan.connection velocity derivative) direction) +
    diracExteriorMotherLieAction (p286LieBlockEmbed (gaugeConnection velocity derivative direction))

def derivative (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  rawDerivative jet direction + connectionOperator velocity jet direction (NativeCanonicalFluidCoframe.matter velocity)

theorem connectionOperator_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (matter : DiracExteriorMatterCarrier) :
    connectionOperator velocity jet direction matter =
      spinOperator velocity jet direction matter + gaugeOperator velocity jet direction matter +
        (cartanOperator velocity direction matter + correctionOperator velocity direction matter) := by
  simp only [connectionOperator, NativeSourceCartan.connection, cartanAffineSpinConnection,
    diracSpinConnectionLift_add, coframeDiracMatrixMatterAction_add_matrix,
    gaugeConnection, p286LieBlockEmbed_add, diracExteriorMotherLieAction_add, LinearMap.add_apply,
    spinOperator, gaugeOperator, cartanOperator, correctionOperator]
  abel

theorem derivative_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    derivative velocity jet direction =
      covariantDerivative velocity jet direction + compensatedIncrement velocity direction := by
  rw [derivative, connectionOperator_split]
  simp only [covariantDerivative, freeDerivative, rawDerivative, spinOperator, gaugeOperator, gaugeIncrement,
    compensatedIncrement, NativeCartanMaterialResponse.increment, cartanOperator, correctionOperator, correction]
  abel

def dualAction (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (candidate : DiracExteriorMatterCarrier) : ℂ :=
  (volumeFactor velocity : ℂ) * ∑ direction, NativeCanonicalFluidCoframe.dual velocity
    (principal velocity direction (connectionOperator velocity jet direction candidate)) -
      ∑ direction, momentumDerivative velocity jet (NativeCanonicalFluidCoframe.matter velocity)
        (rawDerivative jet) candidate direction

theorem dualAction_eq (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (candidate : DiracExteriorMatterCarrier) :
    dualAction velocity jet candidate =
      dualKinetic velocity jet (NativeCanonicalFluidCoframe.matter velocity) (rawDerivative jet) candidate := by
  simp only [dualAction, connectionOperator_split, map_add, Finset.sum_add_distrib]
  have zero := compensated_dual_zero velocity candidate
  simp only [map_add, Finset.sum_add_distrib] at zero
  unfold dualKinetic
  simp only [map_add, Finset.sum_add_distrib, ← source_dual]
  rw [zero, add_zero]

theorem gaugeConnection_vacuum_zero (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    scalarMotherLieAction (p286LieBlockEmbed (gaugeConnection velocity jet direction))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  simp only [gaugeConnection, p286LieBlockEmbed_add, scalarMotherLieAction_add, correction,
    NativePauliCoframeAction.connection_vacuum_zero, add_zero]

/-- The actual Cartan connection and its generated color correction preserve both original matter equations. -/
theorem receipt_diracDual_cartan_equations {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, ∀ candidate : DiracExteriorMatterCarrier,
      let velocity := receiptField receipt time point
      let jet := receiptJet receipt time point
      let scalar := sourceGeneratedVacuumBase positiveSmoothUnifiedSource
      (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (derivative velocity jet) +
        diracDualRightChiralYukawaAction scalar (NativeCanonicalFluidCoframe.matter velocity) = 0) ∧
      (dualAction velocity jet candidate + (volumeFactor velocity : ℂ) *
        NativeCanonicalFluidCoframe.dual velocity (diracDualRightChiralYukawaAction scalar candidate) = 0) := by
  filter_upwards [receipt_kineticVector_zero receipt time, receipt_dualKinetic_zero receipt time] with point primal dual candidate
  constructor
  · have split : gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
        (derivative (receiptField receipt time point) (receiptJet receipt time point)) =
        gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
          (covariantDerivative (receiptField receipt time point) (receiptJet receipt time point)) +
        gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
          (compensatedIncrement (receiptField receipt time point)) := by
      simp only [gaugeVectorAt, derivative_split, map_add, Finset.sum_add_distrib, smul_add]
    rw [split, primal, compensated_vector_zero, source_yukawa_zero, add_zero, add_zero]
  · rw [dualAction_eq, dual candidate, source_dual_yukawa_zero, mul_zero, add_zero]

end
end SaturationMonoid.NavierStokes.NativeCartanSourceJet
