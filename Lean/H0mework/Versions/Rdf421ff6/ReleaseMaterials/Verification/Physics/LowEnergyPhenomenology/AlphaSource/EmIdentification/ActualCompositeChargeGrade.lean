import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeGaugeBand

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeChargeGrade
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
attribute [local irreducible] compositeChargeCore compositeResponse compositeBase

/-- Literal full504 matter charge preserves every original Number/grade block. -/
theorem composite_charge_blocks (g : Label) (f : QuantumTest) :
    project g (compositeChargeCore f)=compositeChargeCore (project g f) := by
  have preserve : Preserves PhysicalEMNativeChargeFull.emFullCharge := by
    change Preserves (Complex.I • nativeFull sourcePhaseGaugeLie)
    exact preserves_smul (native_preserves sourcePhaseGaugeLie) Complex.I
  have blocks : Commute (fiberPiece g) (quantized PhysicalEMNativeChargeFull.emFullCharge) := by
    unfold fiberPiece
    exact blockWeight_quantized _ _ preserve
  apply DFunLike.ext
  intro z
  unfold compositeChargeCore
  change fiberPiece g (quantized PhysicalEMNativeChargeFull.emFullCharge (f z))=
    quantized PhysicalEMNativeChargeFull.emFullCharge (fiberPiece g (f z))
  simpa only [mul_apply_eq_comp] using
    congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z)) blocks.eq

private theorem bottom_grade_zero (f : QuantumTest) (bottom : project (3,0) f=f) : gradeCore f=0 := by
  have hp : NativeHistoryGrade.projection (3,0) (embed f)=embed f :=
    (embed_project (3,0) f).symm.trans (congrArg embed bottom)
  apply embed_injective
  rw [←grade_core,map_zero]
  have paid:=congrArg (fun A : H→L[ℂ]H=>A (embed f)) (source_grade_right (3,0))
  simpa only [mul_apply_eq_comp,hp,_root_.smul_apply,Fin.val_zero,Nat.cast_zero,zero_smul] using paid

/-- The actual independent-sharp response and its actual matter-charge image both annihilate the original sharp Y. -/
theorem composite_sharp_Y_charge_zero (leg : CompositeLeg) (sharp : leg.sharp=true) :
    GaussFullHamiltonian.adjointAction (compositeResponse leg)=0 ∧
      GaussFullHamiltonian.adjointAction (compositeChargeCore (compositeResponse leg))=0 := by
  have bottom : project (3,0) (compositeResponse leg)=compositeResponse leg := by
    rw [composite_sharp_bottom leg sharp]
    simpa only [compositeBase] using composite_base_bottom leg
  have chargeBottom : project (3,0) (compositeChargeCore (compositeResponse leg))=
      compositeChargeCore (compositeResponse leg) := by
    rw [composite_charge_blocks,bottom]
  exact ⟨actual_bottom_sharp_action _ (bottom_grade_zero _ bottom),
    actual_bottom_sharp_action _ (bottom_grade_zero _ chargeBottom)⟩

/-- The sharp charge defect is generated entirely by the original finite-frame compression. -/
theorem composite_sharp_charge_frame (leg : CompositeLeg) (sharp : leg.sharp=true) :
    compositeChargeMixing leg=
      SourceScalarPairedTransport.compressionCore leg.frame (compositeChargeCore (compositeResponse leg))-
        compositeChargeCore (SourceScalarPairedTransport.compressionCore leg.frame (compositeResponse leg)) := by
  have vanished:=composite_sharp_Y_charge_zero leg sharp
  rw [composite_sharp_charge_mixing leg sharp,vanished.1,vanished.2,map_zero,add_zero,sub_zero]

/-- Actual sharp output charge retains its generated frame defect and has no hidden Y charge term. -/
theorem composite_sharp_output_charge (leg : CompositeLeg) (sharp : leg.sharp=true) :
    compositeChargeCore (compositeResponse leg)=
      (if leg.dual then (-1:ℂ) else 1) • compositeResponse leg+
        compositeResolvent leg
          (SourceScalarPairedTransport.compressionCore leg.frame (compositeChargeCore (compositeResponse leg))-
            compositeChargeCore (SourceScalarPairedTransport.compressionCore leg.frame (compositeResponse leg))) := by
  have paid:=composite_output_charge_return leg
  rw [composite_sharp_charge_frame leg sharp] at paid
  exact paid

/-- The surviving N3 base numerator is the existing original source mode form, with no free momentum or scalar coupling shell. -/
theorem composite_base_weight_source (p : PhysicalMomentum) (left right : CompositeLeg) :
    compositeBaseWeight p left right=
      -((3/10:ℂ)*rootTwo)*sourceModeForm (compositeBase left) (compositeBase right) := by
  calc
    _=-((3/10:ℂ)*rootTwo)*(rawForm (gaugeField 1 0) p (compositeBase left) (compositeBase right) 0-
      rawForm (gaugeField 2 1) p (compositeBase left) (compositeBase right) 0) := by
      unfold compositeBaseWeight
      ring
    _=_ := by rw [sourceModeForm_generated]

/-- Fourier momentum cancels in the original gauge density before the actual N3 observation. -/
theorem composite_base_weight_momentum (p : PhysicalMomentum) (left right : CompositeLeg) :
    compositeBaseWeight p left right=compositeBaseWeight 0 left right := by
  rw [composite_base_weight_source,composite_base_weight_source]

/-- Any original sharp placement yields the same source-owned N3 numerator, preserving complete response normalizations. -/
theorem composite_weight_source_mode (p : PhysicalMomentum) (left right : CompositeLeg)
    (sharp : left.sharp=true ∨ right.sharp=true) :
    compositeMasslessWeight p left right=
      -((3/10:ℂ)*rootTwo)*compositeInverseNorm left*compositeInverseNorm right*
        sourceModeForm (compositeBase left) (compositeBase right) := by
  have reduced : compositeMasslessWeight p left right=
      compositeInverseNorm left*compositeInverseNorm right*compositeBaseWeight p left right := by
    rcases sharp with leftSharp | rightSharp
    · exact composite_weight_sharp_left p left right leftSharp
    · exact composite_weight_sharp_right p left right rightSharp
  rw [reduced,composite_base_weight_source]
  ring

end LowEnergy.GaussComposite.ActualCompositeChargeGrade
