import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeChargeGrade
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginWardRead

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeOriginWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussQuantumMultiplier GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore GaussFockPair
open MixedSpectatorCandidate YukawaResolventDetection GaussCoreLabel
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse FullYSourceResolventGraphSplice
open SourceClockYukawaCubicCurrent GeneralThreeParticleResponse SourceScalarPairedTransport
open PreparationVacuumRawJointFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumSourceActionJets
open PreparationVacuumGaugeSourceInjection PreparationVacuumNonlinearFieldCurve PreparationVacuumOriginalGreenFeedback PreparationVacuumActualFieldQuantization
open PreparationVacuumStaticPoleResponse PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic
open ActualEMExternalRepresentation
open MeasureTheory Filter
open scoped Matrix BigOperators Topology InnerProductSpace Matrix.Norms.Operator
open ActualCompositeFieldCurrent ActualCompositeStaticCurrent
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumFullFieldRiesz
open GaussFockLabel NativeHistoryGrade NamedColorQtNext
open Set
open ActualCompositeGaugeBand PreparationPhysicalPhaseGaugeRealization
open GaussNativeMatter SourceQuantumResidualGaugeSlice GaussYukawaGrade GaussYukawaInteraction PreparationVacuumRestModeCoupling
open ActualCompositeChargeGrade CanonicalGradedCharge CanonicalPhysicalWardCore
open ActualEMOriginWard Stage9C.Material.SpinPair
open PreparationVacuumFullElectricWard PreparationVacuumActionDecomposition CanonicalPhysicalSpatial
open PreparationVacuumFieldConstraintResponse
attribute [local irreducible] compositeChargeCore compositeResponse

/-- The actual full504 matter charge is literally the original source Noether core occurrence. -/
theorem composite_charge_original :
    compositeChargeCore=CanonicalGradedCharge.chargeAction sourcePhaseGaugeLie := by
  unfold compositeChargeCore
  rfl

/-- The finite-frame charge return consumes the original H0 configuration torque and its actual compression defect. -/
theorem composite_frame_charge_original (leg : CompositeLeg) :
    SourceScalarPairedTransport.compressionCore leg.frame (compositeChargeCore (compositeResponse leg))-
      compositeChargeCore (SourceScalarPairedTransport.compressionCore leg.frame (compositeResponse leg))=
    configurationTorque sourcePhaseGaugeLie (compositeResponse leg)-
      (defectAction leg.frame (compositeChargeCore (compositeResponse leg))-
        compositeChargeCore (defectAction leg.frame (compositeResponse leg))) := by
  rw [configurationTorque,←composite_charge_original]
  simp only [defectAction,LinearMap.sub_apply,LinearMap.comp_apply,map_sub]
  abel

/-- Actual fullY matter charge is generated from the original whole H0/Y torque, retaining the same source compression defect and profile action. -/
theorem composite_full_output_original (leg : CompositeLeg) (full : leg.sharp=false) :
    compositeChargeCore (compositeResponse leg)=
      (if leg.dual then (-1:ℂ) else 1) • compositeResponse leg+
        compositeResolvent leg
          (configurationTorque sourcePhaseGaugeLie (compositeResponse leg)+
            GaussYukawaOperator.originalAction (compositeChargeCore (compositeResponse leg))-
            compositeChargeCore (GaussYukawaOperator.originalAction (compositeResponse leg))-
            (defectAction leg.frame (compositeChargeCore (compositeResponse leg))-
              compositeChargeCore (defectAction leg.frame (compositeResponse leg)))) := by
  have mixing:=composite_full_charge_mixing leg full
  rw [composite_frame_charge_original] at mixing
  have identity : compositeChargeMixing leg=
      configurationTorque sourcePhaseGaugeLie (compositeResponse leg)+
        GaussYukawaOperator.originalAction (compositeChargeCore (compositeResponse leg))-
        compositeChargeCore (GaussYukawaOperator.originalAction (compositeResponse leg))-
        (defectAction leg.frame (compositeChargeCore (compositeResponse leg))-
          compositeChargeCore (defectAction leg.frame (compositeResponse leg))) := by
    rw [mixing]
    abel
  have paid:=composite_output_charge_return leg
  rw [identity] at paid
  exact paid

/-- The same actual sharp event eliminates Y while retaining its original configuration/profile torque and finite-frame defect. -/
theorem composite_sharp_output_original (leg : CompositeLeg) (sharp : leg.sharp=true) :
    compositeChargeCore (compositeResponse leg)=
      (if leg.dual then (-1:ℂ) else 1) • compositeResponse leg+
        compositeResolvent leg
          (configurationTorque sourcePhaseGaugeLie (compositeResponse leg)-
            (defectAction leg.frame (compositeChargeCore (compositeResponse leg))-
              compositeChargeCore (defectAction leg.frame (compositeResponse leg)))) := by
  have paid:=composite_sharp_output_charge leg sharp
  rw [composite_frame_charge_original] at paid
  exact paid

private theorem composite_mode_scale : ((gaugeScale/2:ℝ):ℂ)=(3/10:ℂ)*rootTwo := by
  dsimp only [gaugeScale,spinScale,rootTwo]
  push_cast
  ring

/-- The original N3 base current consumes the complete source EM Ward, its scalar countervariation and actual configuration deviation. -/
theorem composite_base_em_ward (p : PhysicalMomentum) (left right : CompositeLeg) :
    compositeBaseWeight p left right=
      -emOriginWardForm p (compositeBase left) (compositeBase right)+
        emOriginScalarForm p (compositeBase left) (compositeBase right)+
        emOriginDeviationForm p (compositeBase left) (compositeBase right) := by
  have paid:=em_origin_form_ward p (compositeBase left) (compositeBase right)
  rw [Complex.real_smul,composite_mode_scale] at paid
  rw [composite_base_weight_source,neg_mul,paid]
  abel

/-- The complete actual current's longrange weight has no free scalar shell: all three original action forms and both complete response norms remain. -/
theorem composite_weight_em_ward (p : PhysicalMomentum) (left right : CompositeLeg)
    (sharp : left.sharp=true ∨ right.sharp=true) :
    compositeMasslessWeight p left right=
      compositeInverseNorm left*compositeInverseNorm right*
        (-emOriginWardForm p (compositeBase left) (compositeBase right)+
          emOriginScalarForm p (compositeBase left) (compositeBase right)+
          emOriginDeviationForm p (compositeBase left) (compositeBase right)) := by
  have reduced : compositeMasslessWeight p left right=
      compositeInverseNorm left*compositeInverseNorm right*compositeBaseWeight p left right := by
    rcases sharp with leftSharp | rightSharp
    · exact composite_weight_sharp_left p left right leftSharp
    · exact composite_weight_sharp_right p left right rightSharp
  rw [reduced,composite_base_em_ward]

/-- The original full-action Noether return acts on this actual N3 base response, retaining configuration/profile, transferred current, pair-current and Yukawa torque. -/
theorem composite_base_original_action (p k : PhysicalMomentum) (leg : CompositeLeg) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (p+k)-retainedCore)
        (compositeChargeCore (compositeBase leg))-
      compositeChargeCore ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore)
        (compositeBase leg))=
    configurationTorque sourcePhaseGaugeLie (compositeBase leg)+
      CanonicalPhysicalWardCore.currentAction k sourcePhaseGaugeLie (compositeBase leg)+
      pairCurrent k sourcePhaseGaugeLie (compositeBase leg)+yukawaTorque sourcePhaseGaugeLie (compositeBase leg) := by
  rw [composite_charge_original]
  exact em_origin_original_action_ward p k (compositeBase leg)

end LowEnergy.GaussComposite.ActualCompositeOriginWard
