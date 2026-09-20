import H0mework.Physics.SourceFormation.Material

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineFormNativeMatterSpinThreeForm StageNineFormNativeLorentzGeometricFirstVariation
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation StageNineIIPlusRestriction
open StageNineTopologicalLorentzThreeFormDuality StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open Stage9C.Material.SpinPair Stage9C.Reduction

noncomputable section

theorem coframe_eq (source : SmoothUnifiedSource) :
    (formedField source).coframe = (SourceFamily.fieldAt (index source)).coframe := by
  rw [SourceFamily.field_coframe]
  rfl

theorem gauge_connection_eq (source : SmoothUnifiedSource) :
    (formedField source).gaugeConnection = (SourceFamily.fieldAt (index source)).gaugeConnection := by
  rw [SourceFamily.field_connection]
  rfl

theorem matter_eq (source : SmoothUnifiedSource) :
    (formedField source).matter = (SourceFamily.fieldAt (index source)).matter := by
  rw [SourceFamily.Gauge.field_matter]
  rfl

theorem dual_eq (source : SmoothUnifiedSource) :
    (formedField source).conjugateMatter = (SourceFamily.fieldAt (index source)).conjugateMatter := by
  rw [SourceFamily.Gauge.field_dual]
  rfl

theorem scalar_eq (source : SmoothUnifiedSource) :
    (formedField source).scalar = fun _ => sourceGeneratedVacuumCoordinates source := rfl

private theorem spin_response_source (source target : SmoothUnifiedSource)
    (field : StageNineHolonomicConfiguration) (point : BasePoint) :
    diracDualFormNativeActionSpinResponseAt source field point =
      diracDualFormNativeActionSpinResponseAt target field point := by
  ext internalPair triple
  change -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient source 0 point
      (toContinuumPointField (restrictHolonomicConfigurationToIIPlus field) point)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) internalPair)) =
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient target 0 point
      (toContinuumPointField (restrictHolonomicConfigurationToIIPlus field) point)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) internalPair))
  unfold formNativeLorentzMatterFirstCoefficient matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart]

theorem gravity_connection_eq (source : SmoothUnifiedSource) :
    (formedField source).gravityConnection = (SourceFamily.fieldAt (index source)).gravityConnection := by
  funext point
  have first := sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
    source (StageNineFormNativeP286GaugeYangMillsReadout.formNativeP286GaugeConstitutiveReadout source
      (seed source)) point
  have second := sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
    (SourceFamily.sourceAt (index source))
    (StageNineFormNativeP286GaugeYangMillsReadout.formNativeP286GaugeConstitutiveReadout
      (SourceFamily.sourceAt (index source)) (SourceFamily.seedAt (index source))) point
  change (formedField source).gravityConnection point =
    diracDualFormNativeActionCartanConnectionAt source (formedField source) point at first
  change (SourceFamily.fieldAt (index source)).gravityConnection point =
    diracDualFormNativeActionCartanConnectionAt (SourceFamily.sourceAt (index source))
      (SourceFamily.fieldAt (index source)) point at second
  rw [first, second]
  unfold diracDualFormNativeActionCartanConnectionAt diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [spin_response_source source (SourceFamily.sourceAt (index source)),
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      (SourceFamily.sourceAt (index source)) (formedField source)
      (SourceFamily.fieldAt (index source)) point (congrFun (coframe_eq source) point)
      (congrFun (matter_eq source) point) (congrFun (dual_eq source) point), coframe_eq]

theorem gauge_auxiliary_eq (source : SmoothUnifiedSource) :
    (formedField source).gaugeAuxiliary = (SourceFamily.fieldAt (index source)).gaugeAuxiliary := by
  funext point
  change formNativeP286GaugeEliminatedAuxiliaryAtBoundary (sourceGeneratedUnifiedCouplings source)
    ((seed source).coframe point) (holonomicGaugeCurvature (seed source) point) =
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings (SourceFamily.sourceAt (index source)))
      ((SourceFamily.seedAt (index source)).coframe point)
      (holonomicGaugeCurvature (SourceFamily.seedAt (index source)) point)
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary
  change -formNativeP286BlockScale (source.legacy.sigma)⁻¹ (source.legacy.sigma)⁻¹
      (source.legacy.sigma)⁻¹ _ =
    -formNativeP286BlockScale (SourceFamily.coupling (index source))⁻¹
      (SourceFamily.coupling (index source))⁻¹ (SourceFamily.coupling (index source))⁻¹ _
  rw [source_coupling]
  rfl

theorem gravity_multiplier_eq (source : SmoothUnifiedSource) :
    (formedField source).gravitySimplicityMultiplier =
      (SourceFamily.fieldAt (index source)).gravitySimplicityMultiplier := by
  have first := sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
    source (StageNineFormNativeP286GaugeYangMillsReadout.formNativeP286GaugeConstitutiveReadout source
      (seed source))
  have second := sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
    (SourceFamily.sourceAt (index source))
    (StageNineFormNativeP286GaugeYangMillsReadout.formNativeP286GaugeConstitutiveReadout
      (SourceFamily.sourceAt (index source)) (SourceFamily.seedAt (index source)))
  change (formedField source).gravitySimplicityMultiplier = formNativeGravityReactionField (formedField source) at first
  change (SourceFamily.fieldAt (index source)).gravitySimplicityMultiplier =
    formNativeGravityReactionField (SourceFamily.fieldAt (index source)) at second
  rw [first, second]
  unfold formNativeGravityReactionField holonomicContravariantGravityCurvature
    holonomicGravityCurvature gravityConnectionDerivative
  rw [gravity_connection_eq]
  rfl

theorem gravity_auxiliary_eq (source : SmoothUnifiedSource) :
    (formedField source).gravityAuxiliary = (SourceFamily.fieldAt (index source)).gravityAuxiliary := by
  funext point
  change physicalIIPlusBivector ((seed source).coframe point) =
    physicalIIPlusBivector ((SourceFamily.seedAt (index source)).coframe point)
  congr 1

theorem field_eq_vacuum_update (source : SmoothUnifiedSource) :
    formedField source =
      { SourceFamily.fieldAt (index source) with scalar := fun _ => sourceGeneratedVacuumCoordinates source } := by
  apply StageNineHolonomicConfiguration.ext
  · exact coframe_eq source
  · exact gravity_connection_eq source
  · exact gravity_auxiliary_eq source
  · exact gravity_multiplier_eq source
  · exact gauge_connection_eq source
  · exact gauge_auxiliary_eq source
  · rfl
  · exact matter_eq source
  · exact dual_eq source

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation
