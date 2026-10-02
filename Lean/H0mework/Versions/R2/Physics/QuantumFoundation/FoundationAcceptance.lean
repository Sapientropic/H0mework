import H0mework.Versions.R2.Physics.QuantumFoundation.FoundationInvariance

/-! The current actual's geometric and action restrictions form one
foundation for the same-occurrence S9-G consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G.Foundation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalBundle StageNineGlobalConnection StageNineAssociatedBundles
open StageNineSpinMatterBundle StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDynamicBreakingVacuum StageNineBlockwiseConstitutive
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineFormNativeP286GaugeConstitutiveElimination StageNineFormNativeGaugeWedge
open StageNineCClassicalWorldAcceptance StageNineGravityBianchi
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation DiracExteriorMatterAction
open SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa
open Stage9C.Material.SpinPair
open StageNineLocalFrameInvariance StageNineDiracDualFormNativeLocalSpinAction
open StageNineDiracKineticLocalSpinDifferential

noncomputable section

structure ActualFoundation : Prop where
  smooth : actual.Smooth
  nondegenerate : actual.Nondegenerate
  lorentzAdmissible : GravityConnectionLorentzAdmissible actual
  matterInOriginalBundle : ∀ chart point,
    actualGlobalMatter point =
      associatedLocalPoint totalDiracExteriorMatterRepresentation positiveSmoothUnifiedSource
        chart point (actualLocalMatter chart point)
  globalSection : ∀ point,
    associatedBundleProjection totalDiracExteriorMatterRepresentation positiveSmoothUnifiedSource
      (actualGlobalMatter point) = point
  originalMatter : ∀ point, actualLocalMatter 0 point = actual.matter point
  matterDescent : ∀ initial terminal point,
    actualLocalMatter terminal point = totalDiracExteriorMatterRepresentation
      (generatedTotalTransition positiveSmoothUnifiedSource initial terminal point)
      (actualLocalMatter initial point)
  actionMatterIsBundleMatter : ∀ chart point,
    (actualChartField chart point).matter = actualLocalMatter chart point
  originalIndependentDual : ∀ chart point,
    (actualChartField chart point).conjugateMatter = (actual.conjugateMatter point).comp
      (diracExteriorMatterGaugeRepresentation
        (generatedTransition positiveSmoothUnifiedSource 0 chart point)⁻¹)
  fullMotherConnectionDescent : ∀ initial terminal point direction,
    (actualLocalPotential terminal point direction : Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      motherAdjointMatrix (generatedTransition positiveSmoothUnifiedSource initial terminal point)
          (actualLocalPotential initial point direction) -
        (generatedTransitionLogDerivative positiveSmoothUnifiedSource initial terminal direction :
          Matrix SU7MotherIndex SU7MotherIndex ℂ)
  originalConnection : ∀ point direction,
    actualLocalPotential 0 point direction = p286LieBlockEmbed (actual.gaugeConnection point direction)
  generatedJets : ∀ point,
    (toContinuumPointField actual point).gravityCurvature = holonomicGravityCurvature actual point ∧
    (toContinuumPointField actual point).gaugeCurvature = holonomicGaugeCurvature actual point ∧
    (toContinuumPointField actual point).scalarCovariantDerivative =
      holonomicScalarCovariantDerivative actual point ∧
    (toContinuumPointField actual point).matterCovariantDerivative =
      holonomicMatterCovariantDerivative actual point
  dynamicHodge : ∀ point form,
    coframeGaugeSpacetimeHodgeLinear (actual.coframe point) form =
      ![lapse⁻¹*form 3, lapse⁻¹*form 4, lapse⁻¹*form 5,
        -lapse*form 0, -lapse*form 1, -lapse*form 2]
  constitutiveGenerated : ∀ point,
    actual.gaugeAuxiliary point = formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (actual.coframe point) (holonomicGaugeCurvature actual point)
  constitutiveEquation : ∀ point,
    formNativeP286BlockwiseConstitutive (actual.coframe point)
        ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        (actual.gaugeAuxiliary point) = holonomicGaugeCurvature actual point
  gravityIIPlus : ∀ point,
    actual.gravityAuxiliary point = physicalIIPlusBivector (actual.coframe point)
  dynamicVacuum : ∀ chart point,
    (actualChartField chart point).scalar =
      generatedLocalVacuumCoordinates positiveSmoothUnifiedSource chart point
  uniqueVacuumMinimum : ∀ chart point coordinates,
    generatedScalarPotential positiveSmoothUnifiedSource chart point
        (actualChartField chart point).scalar ≤
      generatedScalarPotential positiveSmoothUnifiedSource chart point coordinates ∧
    (generatedScalarPotential positiveSmoothUnifiedSource chart point coordinates =
        generatedScalarPotential positiveSmoothUnifiedSource chart point
          (actualChartField chart point).scalar ↔
      coordinates = (actualChartField chart point).scalar)
  vacuumStabilizer : ∀ point groupElement,
    groupElement ∈ generatedVacuumStabilizer positiveSmoothUnifiedSource ↔
      ∀ index : ScalarBasisIndex,
        (su7ExteriorBasis 4).coord index
          (exteriorBreakingScalarRepresentation groupElement
            (scalarCoordinateEquiv.symm (actual.scalar point))) =
        (su7ExteriorBasis 4).coord index (scalarCoordinateEquiv.symm (actual.scalar point))
  properStabilizer : generatedVacuumStabilizer positiveSmoothUnifiedSource ≠ ⊤
  hyperchargeStabilizer : ∀ phase : Circle,
    embeddedP286HyperchargeElement phase ∈ generatedVacuumStabilizer positiveSmoothUnifiedSource ↔
      phase = 1
  nativeDensityDescent : ∀ chart point,
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource chart point
        (actualChartField chart point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
        (toContinuumPointField actual point)
  nativeHolonomicAction : ∀ chart,
    actualAction chart =
      holonomicDiracDualFormNativeIntegratedUnifiedAction positiveSmoothUnifiedSource 0 actual
  physicalLocalSpin : ∀ chart spinField, LocalSpinFieldSmooth spinField →
    holonomicDiracDualFormNativeIntegratedUnifiedAction positiveSmoothUnifiedSource chart
      (localSpinDiracDualFormNativeAction spinField actual) =
        holonomicDiracDualFormNativeIntegratedUnifiedAction positiveSmoothUnifiedSource chart actual
  fullMovingFrame : ∀ chart change frame field,
    nativeActionInFrame chart (multiplyLocalFrameSections change frame)
        (transformContinuumFieldSection change field) = nativeActionInFrame chart frame field
  movingFrameReadsActual : ∀ chart,
    nativeActionInFrame chart identityLocalTotalFrameSection (actualChartField chart) = actualAction chart
  completeNativeResidual : ∀ point,
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource actual point = 0

theorem actualFoundation : ActualFoundation where
  smooth := actual_classicalWorldAcceptance.smooth
  nondegenerate := actual_classicalWorldAcceptance.nondegenerate
  lorentzAdmissible := actual_classicalWorldAcceptance.gravityConnectionLorentzAdmissible
  matterInOriginalBundle := actualGlobalMatter_in_chart
  globalSection := actualGlobalMatter_section
  originalMatter := actualLocalMatter_zero
  matterDescent := actualLocalMatter_overlap
  actionMatterIsBundleMatter := actualChartField_matter
  originalIndependentDual := fun _ _ => rfl
  fullMotherConnectionDescent := actualLocalPotential_overlap
  originalConnection := actualLocalPotential_zero
  generatedJets := toContinuumPointField_generatedJets actual
  dynamicHodge := actualHodge
  constitutiveGenerated := actualAuxiliary_generated
  constitutiveEquation := actualConstitutive_solves
  gravityIIPlus := actualGravityIIPlus
  dynamicVacuum := actualChartField_vacuum
  uniqueVacuumMinimum := actualVacuum_uniqueMinimum
  vacuumStabilizer := actualVacuum_stabilizer
  properStabilizer := positive_generatedVacuumStabilizer_proper
  hyperchargeStabilizer := positive_hypercharge_mem_vacuumStabilizer_iff
  nativeDensityDescent := actualDensity_descent
  nativeHolonomicAction := actualAction_holonomic
  physicalLocalSpin := actualLocalSpin_invariant
  fullMovingFrame := nativeActionInFrame_change
  movingFrameReadsActual := nativeActionInFrame_actual
  completeNativeResidual := actualResidual_sameAction

end
end SaturationMonoid.PhysicsCore.Stage9G.Foundation
