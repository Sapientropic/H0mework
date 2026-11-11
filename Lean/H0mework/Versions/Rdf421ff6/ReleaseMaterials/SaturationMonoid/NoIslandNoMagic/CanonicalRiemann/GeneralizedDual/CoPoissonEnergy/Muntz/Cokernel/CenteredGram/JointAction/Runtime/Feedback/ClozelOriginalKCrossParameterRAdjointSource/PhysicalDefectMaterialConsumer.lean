import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaCoefficientMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_coupled_source_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_born_decoder_coupled_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PhysicalDefectMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
namespace PA
export OriginalKCombCofinalPaAction (E Q actual_complete_reconstruction)
end PA
namespace Face
export OriginalKDirectRCofinalSourceAction (actualFaceImage)
namespace Window
export OriginalKDirectRCofinalSourceAction.Window (sourceDecoder inverseSourceDecoder)
end Window
end Face
local instance defectMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance defectMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal
local notation "Qunit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth ordinal
local notation "nextOutside" => (D.input observation nontrivial half depth (ordinal+1)).2
local notation "nextImage" => Face.actualFaceImage observation nontrivial half depth (ordinal+1)
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- The complete outside input is read by its actual fixed W source. -/
def outsideAmplitude (value : BurnolL2) : ℂ := -2*inner ℂ (hPowerPhysicalCorrection c) (outside value)
def outsideSource (value : BurnolL2) : BurnolL2 :=
 outsideAmplitude observation half value • OriginalKSourceResolventReconstruction.generatedK (OriginalPrimitiveRankBalance.conjugateCoordinate c)
def wholeQSourceAction (value : BurnolL2) : BurnolL2 :=
 alpha • Qunit+(PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (PA.Q value : BurnolL2)) : BurnolL2)+
 outsideSource observation half value
def physicalOutsideAmplitude (value : BurnolL2) : ℂ :=
 -2*inner ℂ (fourierL2 (OriginalKSourceResolventReconstruction.generatedK c)) (PA.Q value : BurnolL2)
def physicalOutsideResponse (value : BurnolL2) : BurnolL2 :=
 physicalOutsideAmplitude observation half value • PhysicalOutsideSource.physicalOutsideColumn c
def wholeOutsideSourceAction (value : BurnolL2) : BurnolL2 :=
 outside (burnolDirectRightResolvent (observation.coordinate/2) (outside value))+physicalOutsideResponse observation half value
local notation "newQ" => wholeQSourceAction observation nontrivial half depth ordinal raw
local notation "newOutside" => wholeOutsideSourceAction observation half raw

/-- Both computed source blocks enter this original normal, raw, born and complete next inventory. -/
theorem actual_coupled_source_on_original_whole_next :
 type_of% (PaCoefficientMaterialConsumer.actual_log_source_next_alpha_on_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 ((PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (outside raw)) : BurnolL2)=outsideSource observation half raw) ∧
 (((PA.Q targetRaw : BurnolL2),outside targetRaw)=
  (wholeQSourceAction observation nontrivial half depth ordinal inputRaw,wholeOutsideSourceAction observation half inputRaw)) ∧
 (((PA.Q rawNext : BurnolL2),outside rawNext)=(newQ,newOutside)) ∧
 (((PA.Q bornRaw : BurnolL2),outside bornRaw)=(newQ,newOutside)) ∧
 ((Face.Window.sourceDecoder nextImage).val=PA.E bornRaw) ∧
 (Face.Window.inverseSourceDecoder nextImage=burnolMobiusSourceL2 (PA.E bornRaw)) ∧
 (nextOutside=outside bornRaw) ∧
 (nextOutside=newOutside) ∧
 (bornRaw=((Face.Window.sourceDecoder nextImage).val : BurnolL2)+newQ+newOutside) ∧
 type_of% (OriginalKDirectRCofinalResidual.actual_residual_inventory observation nontrivial half depth ordinal) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have inherited:=PaCoefficientMaterialConsumer.actual_log_source_next_alpha_on_whole_next observation nontrivial half depth ordinal
 have prior:=inherited.2.1
 have bornFace:=prior.2.2.2.1
 have decodedBorn:=bornFace.2.2.2.2.2.2.2.2.2.2.2.1
 have inverseBorn:=bornFace.2.2.2.2.2.2.2.2.2.2.2.2.1
 have source:=PhysicalDefectSource.actual_R_outside_Q_source observation nontrivial half raw
 have actual:=PhysicalOutsideSource.actual_Q_outside_coupled_sources observation nontrivial half depth ordinal
 change ((PA.Q rawNext : BurnolL2),outside rawNext)=(newQ,newOutside) at actual
 have actualQ : (PA.Q rawNext : BurnolL2)=newQ := congrArg (fun pair : BurnolL2×BurnolL2=>pair.1) actual
 have target : targetRaw=rawNext := targetAction.2.2.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have normal : ((PA.Q targetRaw : BurnolL2),outside targetRaw)=
   (wholeQSourceAction observation nontrivial half depth ordinal inputRaw,wholeOutsideSourceAction observation half inputRaw) := by
  rw [target,sourceInput]
  exact actual
 have calculated:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have bornR : bornRaw=P.R observation nontrivial half raw := calculated.2.2.1
 have bornToRaw : bornRaw=rawNext := bornR.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have bornPair:=(congrArg (fun value : BurnolL2=>((PA.Q value : BurnolL2),outside value)) bornToRaw).trans actual
 have bornOutside : outside bornRaw=newOutside := congrArg (fun pair : BurnolL2×BurnolL2=>pair.2) bornPair
 have decodedNext:=(decodedBorn.trans (congrArg PA.E bornToRaw))
 have stock : nextOutside=outside bornRaw :=
  (congrArg (fun pair : BurnolL2×BurnolL2=>pair.2) (D.next_pair observation nontrivial half depth ordinal)).trans (congrArg outside bornR.symm)
 have stockComputed : nextOutside=newOutside := stock.trans bornOutside
 have complete:=PA.actual_complete_reconstruction observation nontrivial half depth ordinal
 change (PA.E rawNext : BurnolL2)+(PA.Q rawNext : BurnolL2)+nextOutside=rawNext at complete
 rw [←decodedNext,actualQ,stockComputed] at complete
 have reconstructed:=complete.trans bornToRaw.symm
 exact ⟨inherited,
  OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  source,normal,actual,bornPair,decodedBorn,inverseBorn,stock,stockComputed,reconstructed.symm,
  OriginalKDirectRCofinalResidual.actual_residual_inventory observation nontrivial half depth ordinal,whole,next⟩

/-- The independent reader reconstructs this born from its real Pa decoder and both computed vector sources. -/
theorem actual_born_decoder_coupled_consumer :
 (((PA.Q rawNext : BurnolL2),outside rawNext)=(newQ,newOutside)) ∧
 (((PA.Q bornRaw : BurnolL2),outside bornRaw)=(newQ,newOutside)) ∧
 (bornRaw=((Face.Window.sourceDecoder nextImage).val : BurnolL2)+newQ+newOutside) ∧
 (nextOutside=newOutside) ∧
 (nextOutside=outside bornRaw) ∧
 (Face.Window.inverseSourceDecoder nextImage=burnolMobiusSourceL2 (PA.E bornRaw)) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_coupled_source_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A zero actual outside amplitude removes its response column and keeps both other Q sources. -/
theorem actual_zero_outside_amplitude_override (zero : outsideAmplitude observation half raw=0) :
 (PA.Q rawNext : BurnolL2)=alpha • Qunit+
  (PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (PA.Q raw : BurnolL2)) : BurnolL2) := by
 have actual:=congrArg (fun pair : BurnolL2×BurnolL2=>pair.1)
  (actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal).1
 simpa only [wholeQSourceAction,outsideSource,zero,zero_smul,add_zero] using actual

/-- Zero alpha keeps the full Q action and complete outside source column. -/
theorem actual_zero_unit_coefficient_override (zero : alpha=0) :
 (PA.Q rawNext : BurnolL2)=
  (PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (PA.Q raw : BurnolL2)) : BurnolL2)+outsideSource observation half raw := by
 have actual:=congrArg (fun pair : BurnolL2×BurnolL2=>pair.1)
  (actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal).1
 simpa only [wholeQSourceAction,zero,zero_smul,zero_add] using actual

/-- Zero Fourier-Q source price keeps the complete autonomous outside action. -/
theorem actual_zero_FK_amplitude_override (zero : physicalOutsideAmplitude observation half raw=0) :
 outside rawNext=outside (burnolDirectRightResolvent (observation.coordinate/2) (outside raw)) := by
 have actual:=congrArg (fun pair : BurnolL2×BurnolL2=>pair.2)
  (actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal).1
 simpa only [wholeOutsideSourceAction,physicalOutsideResponse,zero,zero_smul,add_zero] using actual

/-- The already paid Pa return zero cannot erase a nonzero complete Q response. -/
theorem actual_outside_Q_response_cannot_be_erased (nonzero : outsideSource observation half raw≠0) :
 (PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (outside raw)) : BurnolL2)≠0 := by
 have actual:=(actual_coupled_source_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.1
 rw [actual]
 exact nonzero

/-- A nonzero complete outside input response cannot be omitted from Q-next. -/
theorem actual_nonzero_outside_source_cannot_be_dropped (nonzero : outsideSource observation half raw≠0) :
 (PA.Q rawNext : BurnolL2)≠alpha • Qunit+
  (PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (PA.Q raw : BurnolL2)) : BurnolL2) := by
 intro erased
 have actual:=congrArg (fun pair : BurnolL2×BurnolL2=>pair.1)
  (actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal).1
 change _=_+outsideSource observation half raw at actual
 have zero : outsideSource observation half raw=0 := by linear_combination (norm := module) -actual+erased
 exact nonzero zero

/-- A nonzero physical-to-outside source response cannot be omitted from the outside successor. -/
theorem actual_nonzero_physical_outside_response_cannot_be_dropped
 (nonzero : physicalOutsideResponse observation half raw≠0) :
 outside rawNext≠outside (burnolDirectRightResolvent (observation.coordinate/2) (outside raw)) := by
 intro erased
 have actual:=congrArg (fun pair : BurnolL2×BurnolL2=>pair.2)
  (actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal).1
 change _=_+physicalOutsideResponse observation half raw at actual
 have zero : physicalOutsideResponse observation half raw=0 := by linear_combination (norm := module) -actual+erased
 exact nonzero zero

end OriginalKCrossParameterRAdjointSource.PhysicalDefectMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
