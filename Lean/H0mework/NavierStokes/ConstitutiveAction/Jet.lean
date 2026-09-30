import H0mework.NavierStokes.ConstitutiveAction.Flux

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeConstitutiveJet

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineHolonomicField StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaSpinJurisdiction SU7MotherLieAlgebra SU7MotherGaugeTheory SU7MotherGaugeConnection
open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativePauliCoframeAction NativeMaterialJetAction NativeMaterialAdjointPrincipal NativeMaterialMomentumJet
open NativeMaterialAdjointAction
open NativePhysicalFourier NativePhysicalSource NativeSourceMaterialJet NativeSourceMaterialAdjoint
open NativeMatterCoframeStress NativeSourceCoframeStress

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def gaugeConnection (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) : P286LieBlockData :=
  NativeCartanSourceJet.gaugeConnection velocity jet direction +
    NativeSourceColorAction.connection velocity (NativeConstitutiveColor.coefficients velocity) direction

def connectionOperator (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift (NativeSourceCartan.connection velocity jet) direction) +
    diracExteriorMotherLieAction (p286LieBlockEmbed (gaugeConnection velocity jet direction))

theorem connectionOperator_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (matter : DiracExteriorMatterCarrier) :
    connectionOperator velocity jet direction matter = NativeCartanSourceJet.connectionOperator velocity jet direction matter +
      NativeSourceColorAction.operator velocity (NativeConstitutiveColor.coefficients velocity) direction matter := by
  simp only [connectionOperator, gaugeConnection, NativeCartanSourceJet.connectionOperator,
    NativeSourceColorAction.operator, p286LieBlockEmbed_add, diracExteriorMotherLieAction_add, LinearMap.add_apply]
  abel

def derivative (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  rawDerivative jet direction + connectionOperator velocity jet direction (NativeCanonicalFluidCoframe.matter velocity)

theorem derivative_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    derivative velocity jet direction = covariantDerivative velocity jet direction +
      NativeConstitutiveFlux.increment velocity direction := by
  rw [derivative, connectionOperator_split]
  have actual := NativeCartanSourceJet.derivative_split velocity jet direction
  simp only [NativeCartanSourceJet.derivative] at actual
  simpa only [NativeConstitutiveFlux.increment, NativeSourceColorAction.increment, ← add_assoc] using
    congrArg (fun matter => matter + NativeSourceColorAction.operator velocity
      (NativeConstitutiveColor.coefficients velocity) direction (NativeCanonicalFluidCoframe.matter velocity)) actual

def dualAction (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (candidate : DiracExteriorMatterCarrier) : ℂ :=
  (volumeFactor velocity : ℂ) * ∑ direction, NativeCanonicalFluidCoframe.dual velocity
    (principal velocity direction (connectionOperator velocity jet direction candidate)) -
      ∑ direction, momentumDerivative velocity jet (NativeCanonicalFluidCoframe.matter velocity)
        (rawDerivative jet) candidate direction

theorem dualAction_eq (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (candidate : DiracExteriorMatterCarrier) :
    dualAction velocity jet candidate = NativeCartanSourceJet.dualAction velocity jet candidate := by
  simp only [dualAction, connectionOperator_split, map_add, Finset.sum_add_distrib,
    NativeConstitutiveColor.source_dual_zero, add_zero]
  rfl

theorem gaugeConnection_vacuum_zero (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    scalarMotherLieAction (p286LieBlockEmbed (gaugeConnection velocity jet direction))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  simp only [gaugeConnection, p286LieBlockEmbed_add, scalarMotherLieAction_add,
    NativeCartanSourceJet.gaugeConnection_vacuum_zero, NativeSourceColorAction.vacuum_zero, add_zero]

theorem receipt_equations {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, ∀ candidate : DiracExteriorMatterCarrier,
      let velocity := receiptField receipt time point
      let jet := receiptJet receipt time point
      let scalar := sourceGeneratedVacuumBase positiveSmoothUnifiedSource
      (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (derivative velocity jet) +
        diracDualRightChiralYukawaAction scalar (NativeCanonicalFluidCoframe.matter velocity) = 0) ∧
      (dualAction velocity jet candidate + (volumeFactor velocity : ℂ) *
        NativeCanonicalFluidCoframe.dual velocity (diracDualRightChiralYukawaAction scalar candidate) = 0) := by
  filter_upwards [receipt_kineticVector_zero receipt time,
    NativeCartanSourceJet.receipt_diracDual_cartan_equations receipt time] with point primal dual candidate
  constructor
  · have split : gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
        (derivative (receiptField receipt time point) (receiptJet receipt time point)) =
        gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
          (covariantDerivative (receiptField receipt time point) (receiptJet receipt time point)) +
        gaugeVectorAt (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point))
          (NativeConstitutiveFlux.increment (receiptField receipt time point)) := by
      simp only [gaugeVectorAt, derivative_split, map_add, Finset.sum_add_distrib, smul_add]
    rw [split, primal, NativeConstitutiveFlux.vector_zero, source_yukawa_zero, add_zero, add_zero]
  · rw [dualAction_eq]
    exact (dual candidate).2

def stress (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (derivative velocity jet))

theorem stress_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    stress velocity jet = NativeSourceCoframeStress.stress velocity jet + NativeConstitutiveFlux.stress velocity := by
  have split : kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (derivative velocity jet) =
      NativeSourceCoframeStress.current velocity jet + NativeConstitutiveFlux.current velocity := by
    ext direction internal
    simp only [kineticCoefficients, derivative_split, NativeSourceCoframeStress.current,
      NativeConstitutiveFlux.current, map_add, smul_add, Complex.add_re, Matrix.add_apply]
  rw [stress, split, responseCovector_add]
  rfl

theorem stress_spatial (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (first second : Fin 3) :
    stress velocity jet (Matrix.single first.succ second.succ 1) =
      NativeSourceCoframeStress.stress velocity jet (Matrix.single first.succ second.succ 1) -
        velocity first * velocity second +
          NativeConstitutiveFlux.isotropicPressure velocity * (if first = second then 1 else 0) := by
  rw [stress_split, add_apply, NativeConstitutiveFlux.stress_spatial]
  ring

theorem receipt_stress_hasFDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus,
      HasFDerivAt (density (kineticCoefficients (NativeCanonicalFluidCoframe.dual (receiptField receipt time point))
        (derivative (receiptField receipt time point) (receiptJet receipt time point))) 0)
        (stress (receiptField receipt time point) (receiptJet receipt time point))
        (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point)) := by
  filter_upwards [receipt_equations receipt time] with point equations
  have actual := (equations 0).1
  rw [source_yukawa_zero, add_zero] at actual
  apply density_hasFDerivAt_of_inner_zero _ _ _ (NativeCanonicalFluidCoframe.coframe_nondegenerate _)
  rw [add_zero, pairing_eq_kinetic]
  change (NativeCanonicalFluidCoframe.dual _ (gaugeVectorAt _ _)).re = 0
  rw [actual, map_zero, Complex.zero_re]

end
end SaturationMonoid.NavierStokes.NativeConstitutiveJet
