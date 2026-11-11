import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnitKMaterialConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.PhysicalControls

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_log_source_next_alpha_on_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_born_decoder_next_alpha_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PaCoefficientMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
namespace S
export PaCoefficientActionSource (sourceLogKernel sourceLogCoefficient sourceLogRiesz correction_source_log_action correction_adjoint_r_source actual_next_sourceCoefficient)
end S
namespace M
export OriginalKDirectRCofinalMobiusSourceAction
 (actualQuerySource actualQueryTate actualQueryCorrection actual_query_source actual_query_correction_original source_correction_original actualQReentryPairing actualReentryVector actual_query_source_physical actual_query_Tate_physical)
end M
namespace Ctl
export OriginalKDirectRCofinalMobiusSourceAction.DirectRPhysicalSourceControls (actual_physical_source_same_born_whole)
end Ctl
namespace Face
export OriginalKDirectRCofinalSourceAction (actualFaceImage actual_face_decoder actualPaSource)
namespace Window
export OriginalKDirectRCofinalSourceAction.Window (sourceDecoder inverseSourceDecoder)
end Window
end Face
local instance coefficientMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance coefficientMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "bc" => burnolPaResolventSourceCoefficient c
local notation "p" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth ordinal
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal
local notation "alphaNext" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth ordinal
local notation "nextImage" => Face.actualFaceImage observation nontrivial half depth (ordinal+1)
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- The log functional acts on this query's actual inverse-source decoder. -/
def actualLogPrice : ℂ :=
 inner ℂ (S.sourceLogKernel c) (M.actualQueryTate observation nontrivial half depth ordinal)
def actualUnitFee : ℂ :=
 alpha*bc (OriginalKCombCofinalPaAction.E (OriginalKDirectRCofinalPaUpdate.sourceWholeUnit observation nontrivial half : BurnolL2))
def actualQReentryFee : ℂ :=
 M.actualQReentryPairing observation nontrivial half depth ordinal*bc (M.actualReentryVector observation half)
def generatedNextCoefficient : ℂ :=
 actualLogPrice observation nontrivial half depth ordinal+
 actualUnitFee observation nontrivial half depth ordinal+actualQReentryFee observation nontrivial half depth ordinal

/-- The already-generated full Pa successor pays the log source before its actual born coefficient is read. -/
theorem actual_log_source_next_alpha_on_whole_next :
 type_of% (UnitKMaterialConsumer.actual_unit_free_K_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (Ctl.actual_physical_source_same_born_whole observation nontrivial half depth ordinal) ∧
 type_of% (S.correction_adjoint_r_source c) ∧
 (bc (M.actualQueryCorrection observation nontrivial half depth ordinal)=actualLogPrice observation nontrivial half depth ordinal) ∧
 (alphaNext=generatedNextCoefficient observation nontrivial half depth ordinal) ∧
 (bc (OriginalKCombCofinalPaAction.E bornRaw)=generatedNextCoefficient observation nontrivial half depth ordinal) ∧
 (bc (Face.Window.sourceDecoder nextImage).val=generatedNextCoefficient observation nontrivial half depth ordinal) ∧
 (Face.Window.inverseSourceDecoder nextImage=burnolMobiusSourceL2 (OriginalKCombCofinalPaAction.E bornRaw)) ∧
 type_of% (M.actual_query_source_physical observation nontrivial half depth ordinal) ∧
 type_of% (M.actual_query_Tate_physical observation nontrivial half depth ordinal) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have prior:=Ctl.actual_physical_source_same_born_whole observation nontrivial half depth ordinal
 have physical:=prior.1
 have bornPa:=physical.2.2.2.2.2.1
 have bornFace:=prior.2.2.2.1
 have decodedBorn:=bornFace.2.2.2.2.2.2.2.2.2.2.2.1
 have inverseBorn:=bornFace.2.2.2.2.2.2.2.2.2.2.2.2.1
 have logRead : S.sourceLogCoefficient c p=actualLogPrice observation nontrivial half depth ordinal := by
  change inner ℂ (S.sourceLogKernel c) (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))=_
  unfold actualLogPrice M.actualQueryTate
  rw [M.actual_query_source]
 have actualCorrection:=M.actual_query_correction_original observation nontrivial half depth ordinal
 have correction:=actualCorrection.trans (M.source_correction_original observation nontrivial half depth ordinal)
 have correctionPrice : bc (M.actualQueryCorrection observation nontrivial half depth ordinal)=
   actualLogPrice observation nontrivial half depth ordinal := by
  rw [correction,S.correction_source_log_action]
  exact logRead
 have bornPrice:=congrArg bc bornPa
 rw [map_add,map_add,map_smul,map_smul,correctionPrice] at bornPrice
 change bc (OriginalKCombCofinalPaAction.E bornRaw)=generatedNextCoefficient observation nontrivial half depth ordinal at bornPrice
 have decodedPrice:=(congrArg bc decodedBorn).trans bornPrice
 have nextDecoded:=congrArg (fun point : OriginalKDirectRCofinalSourceAction.Window.PaSourceCarrier=>bc point.val)
  (Face.actual_face_decoder observation nontrivial half depth (ordinal+1))
 change bc (Face.Window.sourceDecoder nextImage).val=alphaNext at nextDecoded
 have nextPrice:=nextDecoded.symm.trans decodedPrice
 exact ⟨UnitKMaterialConsumer.actual_unit_free_K_on_original_whole_next observation nontrivial half depth ordinal,
  prior,S.correction_adjoint_r_source c,correctionPrice,nextPrice,bornPrice,decodedPrice,inverseBorn,
  M.actual_query_source_physical observation nontrivial half depth ordinal,
  M.actual_query_Tate_physical observation nontrivial half depth ordinal,
  physical.2.2.2.2.2.2.2.2.2.1,physical.2.2.2.2.2.2.2.2.2.2.1⟩

/-- This independent consumer reads the next coefficient through its real born and complete two-way source decoder. -/
theorem actual_born_decoder_next_alpha_consumer :
 (alphaNext=generatedNextCoefficient observation nontrivial half depth ordinal) ∧
 (bc (OriginalKCombCofinalPaAction.E bornRaw)=generatedNextCoefficient observation nontrivial half depth ordinal) ∧
 (bc (Face.Window.sourceDecoder nextImage).val=generatedNextCoefficient observation nontrivial half depth ordinal) ∧
 (Face.Window.inverseSourceDecoder nextImage=burnolMobiusSourceL2 (OriginalKCombCofinalPaAction.E bornRaw)) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_log_source_next_alpha_on_whole_next observation nontrivial half depth ordinal
 exact ⟨actual.2.2.2.2.1,actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A zero actual Q driver leaves the full unit fee and generated log source. -/
theorem actual_zero_Q_driver_override (zero : M.actualQReentryPairing observation nontrivial half depth ordinal=0) :
 alphaNext=actualLogPrice observation nontrivial half depth ordinal+actualUnitFee observation nontrivial half depth ordinal := by
 have actual:=(actual_born_decoder_next_alpha_consumer observation nontrivial half depth ordinal).1
 simpa only [generatedNextCoefficient,actualQReentryFee,zero,zero_mul,add_zero] using actual

/-- A zero actual unit coefficient keeps the full physical-Q reentry fee. -/
theorem actual_zero_unit_coefficient_override (zero : alpha=0) :
 alphaNext=actualLogPrice observation nontrivial half depth ordinal+actualQReentryFee observation nontrivial half depth ordinal := by
 have actual:=(actual_born_decoder_next_alpha_consumer observation nontrivial half depth ordinal).1
 simpa only [generatedNextCoefficient,actualUnitFee,zero,zero_mul,add_zero] using actual

/-- Both actual fees may vanish while the complete generated log price remains. -/
theorem actual_zero_fees_override
 (unitZero : actualUnitFee observation nontrivial half depth ordinal=0)
 (reentryZero : actualQReentryFee observation nontrivial half depth ordinal=0) :
 alphaNext=actualLogPrice observation nontrivial half depth ordinal := by
 have actual:=(actual_born_decoder_next_alpha_consumer observation nontrivial half depth ordinal).1
 simpa only [generatedNextCoefficient,unitZero,reentryZero,add_zero] using actual

/-- A nonzero generated log source price cannot be replaced by the two old fees alone. -/
theorem actual_log_source_cannot_be_dropped
 (nonzero : actualLogPrice observation nontrivial half depth ordinal≠0) :
 alphaNext≠actualUnitFee observation nontrivial half depth ordinal+actualQReentryFee observation nontrivial half depth ordinal := by
 intro erased
 have actual:=(actual_born_decoder_next_alpha_consumer observation nontrivial half depth ordinal).1
 change alphaNext=(actualLogPrice observation nontrivial half depth ordinal+_)+_ at actual
 rw [erased] at actual
 have zero : actualLogPrice observation nontrivial half depth ordinal=0 := by linear_combination -actual
 exact nonzero zero

end OriginalKCrossParameterRAdjointSource.PaCoefficientMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
