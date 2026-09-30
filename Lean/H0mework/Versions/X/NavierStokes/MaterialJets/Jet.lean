import H0mework.Versions.X.NavierStokes.MaterialJets.Receipt

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeBalancedMaterialJet

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineHolonomicField StageNineFullDiracAdjointMaterial StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaSpinJurisdiction SU7MotherLieAlgebra SU7MotherGaugeTheory SU7MotherGaugeConnection
open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativePauliCoframeAction NativeMaterialJetAction NativeMaterialAdjointPrincipal NativeMaterialMomentumJet NativeMaterialAdjointAction
open NativePhysicalFourier NativePhysicalSource NativeSourceMaterialJet NativeSourceMaterialAdjoint
open NativeMatterCoframeStress NativeSourceCoframeStress NativeBalancedJetCoefficients

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def freeCoefficients (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : Fin 4 → Fin 3 → ℝ :=
  coefficients (normalizedVelocity velocity) (normalizedJet jet)

def gaugeConnection (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) : P286LieBlockData :=
  NativeSourceColorAction.connection velocity (freeCoefficients velocity jet) direction +
    NativeCartanCompensation.correction velocity direction +
    NativeSourceColorAction.connection velocity (NativeConstitutiveColor.coefficients velocity) direction

def connectionOperator (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift (NativeSourceCartan.connection velocity jet) direction) +
    diracExteriorMotherLieAction (p286LieBlockEmbed (gaugeConnection velocity jet direction))

theorem gaugeConnection_vacuum_zero (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    scalarMotherLieAction (p286LieBlockEmbed (gaugeConnection velocity jet direction))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  simp only [gaugeConnection, p286LieBlockEmbed_add, scalarMotherLieAction_add,
    NativeSourceColorAction.vacuum_zero, NativeCartanCompensation.correction,
    NativePauliCoframeAction.connection_vacuum_zero, add_zero]

theorem connectionOperator_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (matter : DiracExteriorMatterCarrier) :
    connectionOperator velocity jet direction matter = NativeConstitutiveJet.connectionOperator velocity jet direction matter +
      NativeSourceColorAction.operator velocity (freeCoefficients velocity jet) direction matter - gaugeOperator velocity jet direction matter := by
  simp only [connectionOperator, gaugeConnection, NativeConstitutiveJet.connectionOperator,
    NativeConstitutiveJet.gaugeConnection, NativeCartanSourceJet.gaugeConnection, gaugeOperator,
    NativeSourceColorAction.operator, p286LieBlockEmbed_add, diracExteriorMotherLieAction_add, LinearMap.add_apply]
  abel

def derivative (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  rawDerivative jet direction + connectionOperator velocity jet direction (NativeCanonicalFluidCoframe.matter velocity)

theorem derivative_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    derivative velocity jet direction = NativeConstitutiveJet.derivative velocity jet direction +
      NativeSourceColorAction.increment velocity (freeCoefficients velocity jet) direction -
        gaugeIncrement velocity (target velocity jet) direction := by
  rw [derivative, connectionOperator_split]
  simp only [NativeConstitutiveJet.derivative, NativeSourceColorAction.increment, gaugeOperator, gaugeIncrement]
  abel

theorem primalVector_eq (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (derivative velocity jet) =
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (NativeConstitutiveJet.derivative velocity jet) := by
  have split : gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (derivative velocity jet) =
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (NativeConstitutiveJet.derivative velocity jet) +
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity)
        (NativeSourceColorAction.increment velocity (freeCoefficients velocity jet)) - gaugeVector velocity (target velocity jet) := by
    simp only [gaugeVectorAt, derivative_split, map_add, map_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, smul_add, smul_sub, gaugeVector]
  rw [split, freeCoefficients, NativeBalancedGaugeEnergy.source_vector_eq, add_sub_cancel_right]

theorem free_dual_eq (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (candidate : DiracExteriorMatterCarrier) :
    (∑ direction, NativeCanonicalFluidCoframe.dual velocity (principal velocity direction
      (NativeSourceColorAction.operator velocity (freeCoefficients velocity jet) direction candidate))) =
      ∑ direction, NativeCanonicalFluidCoframe.dual velocity (principal velocity direction (gaugeOperator velocity jet direction candidate)) := by
  rw [NativeSourceColorAction.dual_eq_adjoint, freeCoefficients, NativeBalancedGaugeEnergy.source_vector_eq]
  exact (NativeSourceColorAction.dual_eq_adjoint velocity
    (NativePauliControl.control (normalizedVelocity velocity) (target velocity jet)) candidate).symm

def dualAction (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (candidate : DiracExteriorMatterCarrier) : ℂ :=
  (volumeFactor velocity : ℂ) * ∑ direction, NativeCanonicalFluidCoframe.dual velocity
    (principal velocity direction (connectionOperator velocity jet direction candidate)) -
      ∑ direction, momentumDerivative velocity jet (NativeCanonicalFluidCoframe.matter velocity)
        (rawDerivative jet) candidate direction

theorem dualAction_eq (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (candidate : DiracExteriorMatterCarrier) :
    dualAction velocity jet candidate = NativeConstitutiveJet.dualAction velocity jet candidate := by
  simp only [dualAction, connectionOperator_split, map_add, map_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, free_dual_eq, add_sub_cancel_right]
  rfl

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
  filter_upwards [NativeConstitutiveJet.receipt_equations receipt time] with point equations candidate
  simpa only [primalVector_eq, dualAction_eq] using equations candidate

def jetStress (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity)
    (fun direction => freeDerivative velocity jet direction +
      NativeSourceColorAction.increment velocity (freeCoefficients velocity jet) direction))

def stress (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (derivative velocity jet))

theorem stress_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    stress velocity jet = jetStress velocity jet + NativeConstitutiveFlux.stress velocity := by
  have decomposition : derivative velocity jet = fun direction =>
      (freeDerivative velocity jet direction + NativeSourceColorAction.increment velocity (freeCoefficients velocity jet) direction) +
        NativeConstitutiveFlux.increment velocity direction := by
    funext direction
    rw [derivative_split, NativeConstitutiveJet.derivative_split]
    simp only [covariantDerivative]
    abel
  rw [stress, decomposition]
  have currents : kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity)
      (fun direction => (freeDerivative velocity jet direction +
        NativeSourceColorAction.increment velocity (freeCoefficients velocity jet) direction) + NativeConstitutiveFlux.increment velocity direction) =
      kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity)
        (fun direction => freeDerivative velocity jet direction + NativeSourceColorAction.increment velocity (freeCoefficients velocity jet) direction) +
      NativeConstitutiveFlux.current velocity := by
    ext direction internal
    simp only [kineticCoefficients, NativeConstitutiveFlux.current, map_add, smul_add, Complex.add_re, Matrix.add_apply]
  rw [currents, responseCovector_add]
  rfl

theorem stress_spatial (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (first second : Fin 3) :
    stress velocity jet (Matrix.single first.succ second.succ 1) =
      jetStress velocity jet (Matrix.single first.succ second.succ 1) - velocity first * velocity second +
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
end SaturationMonoid.NavierStokes.NativeBalancedMaterialJet
