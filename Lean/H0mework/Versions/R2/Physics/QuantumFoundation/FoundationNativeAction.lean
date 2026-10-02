import H0mework.Versions.R2.Physics.QuantumFoundation.FoundationDescent
import H0mework.Versions.R2.Physics.SpinPair.Acceptance

/-! All action claims in S9-G use the existing Dirac-dual form-native epoch.
Chart transport, the live constitutive operator and the scalar minimum are
computed on the same accepted actual. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G.Foundation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalBundle StageNineGlobalIntegratedAction StageNineSpinMatterBundle
open StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineBlockwiseConstitutive
open StageNineDiracDualFormNativeMotherAction StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeYangMillsReadout StageNineFormNativeGaugeWedge
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineDiracDualFormNativeJointResidualCarrier StageNineCClassicalWorldAcceptance
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open Stage9C.Material.SpinPair Stage9C.Reduction Stage9C.Dynamics.Homogeneous

noncomputable section

def actualChartField (chart : StageNineChart) : StageNineContinuumFieldSection :=
  transportContinuumFieldSection positiveSmoothUnifiedSource 0 chart (toContinuumFieldSection actual)

theorem actualChartField_matter (chart : StageNineChart) (point : BasePoint) :
    (actualChartField chart point).matter = actualLocalMatter chart point := by
  change _ = spinDiracMatterRepresentation
    (generatedSpinTransition positiveSmoothUnifiedSource 0 chart point)
    (DiracExteriorMatterAction.diracExteriorMatterGaugeRepresentation
      (StageNineEnrichedProofFreeSource.generatedTransition positiveSmoothUnifiedSource 0 chart point)
      (actual.matter point))
  simp only [generatedSpinTransition, map_one, Module.End.one_apply]
  rfl

theorem actualChartField_vacuum (chart : StageNineChart) (point : BasePoint) :
    (actualChartField chart point).scalar =
      generatedLocalVacuumCoordinates positiveSmoothUnifiedSource chart point := by
  change scalarCoordinateAction _ (actual.scalar point) = _
  rw [actual_scalar]
  rfl

theorem actualVacuum_uniqueMinimum (chart : StageNineChart) (point : BasePoint)
    (coordinates : ScalarCoordinateCarrier) :
    generatedScalarPotential positiveSmoothUnifiedSource chart point
        (actualChartField chart point).scalar ≤
      generatedScalarPotential positiveSmoothUnifiedSource chart point coordinates ∧
    (generatedScalarPotential positiveSmoothUnifiedSource chart point coordinates =
        generatedScalarPotential positiveSmoothUnifiedSource chart point
          (actualChartField chart point).scalar ↔
      coordinates = (actualChartField chart point).scalar) := by
  rw [actualChartField_vacuum, generatedScalarPotential_localVacuum]
  exact ⟨generatedScalarPotential_nonneg _ _ _ _, generatedScalarPotential_eq_zero_iff _ _ _ _⟩

theorem actualVacuum_stabilizer (point : BasePoint) (groupElement : SU7MotherGroup) :
    groupElement ∈ generatedVacuumStabilizer positiveSmoothUnifiedSource ↔
      ∀ index : ScalarBasisIndex,
        (su7ExteriorBasis 4).coord index
          (exteriorBreakingScalarRepresentation groupElement
            (scalarCoordinateEquiv.symm (actual.scalar point))) =
        (su7ExteriorBasis 4).coord index (scalarCoordinateEquiv.symm (actual.scalar point)) := by
  rw [actual_scalar]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply]
  exact generatedVacuumStabilizer_mem_iff_coordinates positiveSmoothUnifiedSource groupElement

def actualAction (chart : StageNineChart) : ℝ :=
  sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    positiveSmoothUnifiedSource chart (actualChartField chart)

theorem actualAction_holonomic (chart : StageNineChart) :
    actualAction chart =
      holonomicDiracDualFormNativeIntegratedUnifiedAction positiveSmoothUnifiedSource 0 actual :=
  sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction_chartInvariant
    positiveSmoothUnifiedSource 0 chart (toContinuumFieldSection actual)

theorem actualDensity_descent (chart : StageNineChart) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource chart point
        (actualChartField chart point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField actual point) :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity_overlap
    positiveSmoothUnifiedSource 0 chart point (toContinuumPointField actual point)

theorem actualHodge (point : BasePoint) (form : GaugeTwoForm) :
    coframeGaugeSpacetimeHodgeLinear (actual.coframe point) form =
      ![lapse⁻¹*form 3, lapse⁻¹*form 4, lapse⁻¹*form 5,
        -lapse*form 0, -lapse*form 1, -lapse*form 2] :=
  homogeneousHodge lapse (ne_of_gt lapse_pos) form

theorem actualConstitutive_solves (point : BasePoint) :
    formNativeP286BlockwiseConstitutive (actual.coframe point)
        ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        (actual.gaugeAuxiliary point) = holonomicGaugeCurvature actual point := by
  have auxiliaryZero := congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeAuxiliary
    (actual_classicalWorldAcceptance.pointwiseJointZeroFiber point)
  exact ((formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
    (toContinuumPointField actual point)).1 auxiliaryZero).symm

theorem actualAuxiliary_generated (point : BasePoint) :
    actual.gaugeAuxiliary point = formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (actual.coframe point) (holonomicGaugeCurvature actual point) :=
  (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
    (toContinuumPointField actual point) (actual_nondegenerate point)).1
    (actualConstitutive_solves point).symm

theorem actualGravityIIPlus (point : BasePoint) :
    actual.gravityAuxiliary point = physicalIIPlusBivector (actual.coframe point) := by
  have multiplierZero := congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.gravityMultiplier
    (actual_classicalWorldAcceptance.pointwiseJointZeroFiber point)
  exact formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField actual point) |>.1 multiplierZero

theorem actualResidual_sameAction (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource actual point = 0 :=
  actual_classicalWorldAcceptance.pointwiseJointZeroFiber point

end
end SaturationMonoid.PhysicsCore.Stage9G.Foundation
