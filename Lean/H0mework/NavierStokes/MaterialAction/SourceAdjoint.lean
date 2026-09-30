import H0mework.NavierStokes.MaterialAction.AdjointAction
import H0mework.NavierStokes.SourceReadout.Material

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeSourceMaterialAdjoint

open MeasureTheory Set
open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction StageNineHolonomicField
open StageNineFullDiracAdjointMaterial Stage9C.Material.SpinPair Stage9CU.Fluid
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineDiracDualYukawaSpinJurisdiction SU7ExteriorBreakingYukawa
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeMaterialJetAction
open NativeMaterialAdjointPrincipal NativeMaterialMomentumJet NativeMaterialAdjointAction
open NativePhysicalFourier NativePhysicalSource NativeSourceMaterialJet

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def rawDerivative (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  lowerMatter (NativePauliJet.tangent (normalizedJet derivative direction))

theorem response_paired (tangent : PhysicalSpace) :
    fullCanonicalDiracAdjoint (lowerMatter (NativePauliJet.tangent (normalizedVelocity tangent))) =
      NativeMaterialAction.dualResponse (WithLp.toLp 2 (fun direction => tangent direction)) := by
  apply LinearMap.ext
  intro candidate
  rw [lowerMatter_apply, fullCanonicalDiracAdjoint_evaluate]
  simp only [sourceColorDiracMatter, fullInternalPair_colorLinear]
  simp [NativeMaterialAction.dualResponse, sourceColorDiracDual, NativeMaterialAction.dualCoefficients,
    lowerCoefficients, NativePauliJet.tangent, normalizedVelocity, pauli, Fin.sum_univ_four, Fin.sum_univ_three,
    Fin.sum_univ_two, map_ofNat]
  ring

theorem source_dual (velocity : PhysicalSpace) :
    NativeCanonicalFluidCoframe.dual velocity = fullCanonicalDiracAdjoint (NativeCanonicalFluidCoframe.matter velocity) :=
  NativeCanonicalFluidCoframe.canonical_paired velocity

theorem dual_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (differentiable : HasDerivAt path (derivative direction) time) (candidate : DiracExteriorMatterCarrier) :
    HasDerivAt (fun actual => fullCanonicalDiracAdjoint (NativeCanonicalFluidCoframe.matter (path actual)) candidate)
      (fullCanonicalDiracAdjoint (rawDerivative derivative direction) candidate) time := by
  simpa only [← source_dual, NativeCanonicalFluidCoframe.dual, rawDerivative, normalizedJet,
    response_paired] using NativeMaterialAction.dual_hasDerivAt differentiable candidate

/-- Both product-rule terms are derivatives of the actual canonical matter momentum. -/
theorem momentum_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (differentiable : HasDerivAt path (derivative direction) time) (candidate : DiracExteriorMatterCarrier) :
    HasDerivAt (fun actual => (volumeFactor (path actual) : ℂ) *
      fullCanonicalDiracAdjoint (NativeCanonicalFluidCoframe.matter (path actual))
        (principal (path actual) direction candidate))
      (momentumDerivative (path time) derivative (NativeCanonicalFluidCoframe.matter (path time))
        (rawDerivative derivative) candidate direction) time := by
  simp only [weighted_principal]
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time
    (coefficient_hasDerivAt derivative direction differentiable)).mul
      (dual_hasDerivAt derivative direction differentiable
        (Complex.I • diracMatrixMatterAction (diracGamma direction) candidate))

theorem source_primal (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    primalKinetic velocity derivative (NativeCanonicalFluidCoframe.matter velocity) (rawDerivative derivative) =
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (covariantDerivative velocity derivative) := by
  simp only [primalKinetic, principal, spinOperator, gaugeOperator, rawDerivative,
    covariantDerivative, freeDerivative, gaugeIncrement, gaugeVectorAt, Finset.smul_sum, LinearMap.smul_apply]

/-- The same original receipt supplies the complete canonical-dual kinetic equation for every full-carrier variation. -/
theorem receipt_dualKinetic_zero {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, ∀ candidate : DiracExteriorMatterCarrier,
      dualKinetic (receiptField receipt time point) (receiptJet receipt time point)
        (NativeCanonicalFluidCoframe.matter (receiptField receipt time point))
        (rawDerivative (receiptJet receipt time point)) candidate = 0 := by
  filter_upwards [receipt_kineticVector_zero receipt time] with point source candidate
  rw [dual_eq_primal_adjoint, source_primal, source]
  simp

theorem source_yukawa_zero (velocity : PhysicalSpace) :
    diracDualRightChiralYukawaAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (NativeCanonicalFluidCoframe.matter velocity) = 0 := by
  unfold NativeCanonicalFluidCoframe.matter InitialLift.matter diracDualRightChiralYukawaAction
  rw [LinearMap.comp_apply]
  funext spin
  change exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (∑ other, rightChiralityProjector spin other •
      sourceColorDiracMatter (InitialLift.coefficients (fun direction => velocity direction)) other) = 0
  simp only [sourceColorDiracMatter, map_sum, map_smul,
    sourceColorDoublet_internalYukawa_zero, smul_zero, Finset.sum_const_zero]

theorem source_dual_yukawa_zero (velocity : PhysicalSpace)
    (scalar : ExteriorBreakingScalarCarrier) (candidate : DiracExteriorMatterCarrier) :
    NativeCanonicalFluidCoframe.dual velocity (diracDualRightChiralYukawaAction scalar candidate) = 0 := by
  change (∑ spin, ∑ color, InitialLift.dualCoefficients (fun direction => velocity direction) spin color *
    sourceColorDoubletDual color (diracDualRightChiralYukawaAction scalar candidate spin)) = 0
  unfold sourceColorDoubletDual diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  unfold diracExteriorYukawaInternalAction internalMatterLinearAction exteriorYukawaInternalAction
  simp

/-- Primal and canonical-dual equations are generated together on the original whole physical jet. -/
theorem receipt_diracDual_equations {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus, ∀ candidate : DiracExteriorMatterCarrier,
      let velocity := receiptField receipt time point
      let derivative := receiptJet receipt time point
      let scalar := sourceGeneratedVacuumBase positiveSmoothUnifiedSource
      (primalKinetic velocity derivative (NativeCanonicalFluidCoframe.matter velocity) (rawDerivative derivative) +
        diracDualRightChiralYukawaAction scalar (NativeCanonicalFluidCoframe.matter velocity) = 0) ∧
      (dualKinetic velocity derivative (NativeCanonicalFluidCoframe.matter velocity) (rawDerivative derivative) candidate +
        (volumeFactor velocity : ℂ) * NativeCanonicalFluidCoframe.dual velocity
          (diracDualRightChiralYukawaAction scalar candidate) = 0) := by
  filter_upwards [receipt_kineticVector_zero receipt time, receipt_dualKinetic_zero receipt time] with point primal dual candidate
  constructor
  · rw [source_primal, primal, source_yukawa_zero, add_zero]
  · rw [dual candidate, source_dual_yukawa_zero, mul_zero, add_zero]

end
end SaturationMonoid.NavierStokes.NativeSourceMaterialAdjoint
