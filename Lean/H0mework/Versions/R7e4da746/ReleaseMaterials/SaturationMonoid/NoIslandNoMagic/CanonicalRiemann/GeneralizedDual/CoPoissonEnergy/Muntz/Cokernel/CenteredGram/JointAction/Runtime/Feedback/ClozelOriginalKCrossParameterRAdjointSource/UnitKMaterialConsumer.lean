import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnitKSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLossFreeAdjointMaterial.Consumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_unit_free_K_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_unit_free_K_born_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.UnitKMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local instance unitKMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance unitKMaterialPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "H" => sourceAdjointField c
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalDivision.DirectRDivisionControls.bornRead observation nontrivial half depth ordinal
local notation "nextBornRaw" => OriginalKDirectRCofinalDivision.DirectRDivisionControls.bornRead observation nontrivial half depth (ordinal+1)
local notation "Qunit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "g" => sourceOutsideColumn c raw
local notation "powerPrice" => star (hQuarterAmplitude c)*inner ℂ (SingularCounting.centeredPower c) (burnolMeanZeroTruncatedFourier g)
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- The full K source price keeps the actual outside-physical input after the Pa price is paid. -/
def unitFreeSourcePrice (value : BurnolL2) : ℂ :=
 inner ℂ (hPhysicalField c) value+inner ℂ H (value-(burnolEvenAmbientProjection value : BurnolL2))

/-- Actual original unit source action removes the Pa/unit price, while the fixed B loss remains explicit. -/
theorem actual_unit_free_K_on_original_whole_next :
 type_of% (OriginalKLossFreeAdjointMaterial.actual_lossfree_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (actual_h_projection_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 (wholeUnitSourcePrice c=0 ∧ paAdjointSource c=0 ∧ PA.E H=0 ∧
  qAdjointSource c=hPhysicalField c ∧ hQField c=hPhysicalField c ∧ inner ℂ receiptK Qunit=0) ∧
 (inner ℂ receiptK targetRaw=unitFreeSourcePrice observation nontrivial half inputRaw) ∧
 (inner ℂ receiptK rawNext=unitFreeSourcePrice observation nontrivial half raw) ∧
 (inner ℂ receiptK bornRaw=unitFreeSourcePrice observation nontrivial half raw) ∧
 (inner ℂ receiptK (P.R observation nontrivial half (PA.invisible rawNext))=
   inner ℂ (hPhysicalField c) rawNext-powerPrice ∧
  inner ℂ receiptK nextBornRaw=inner ℂ (hPhysicalField c) rawNext-powerPrice) ∧
 (∀ (physical : BurnolPaAmbientCarrier),physical∈burnolCompactCoPoissonClosedRange →
  inner ℂ H (physical : BurnolL2)=0) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have sourceZero:=UnitKSource.wholeUnitSourcePrice_zero observation nontrivial half
 have disposition:=zero_wholeUnitSourcePrice_override c sourceZero
 have Ezero : PA.E H=0 := (paAdjointSource_actual c orthogonal).trans disposition.1
 have qPhysical : qAdjointSource c=hPhysicalField c := disposition.2.trans (hPhysicalField_formula c)
 have hQPhysical : hQField c=hPhysicalField c := (hQField_eq_paid c).trans qPhysical
 have kernel : receiptK=K := congrArg (fun receipt : OriginalRieszFiniteSource.Receipt=>receipt.kernel) sourceAnchor
 have unitPrice : inner ℂ receiptK Qunit=0 := by
  rw [kernel,actual_Qunit_source_price observation nontrivial half,sourceZero]
 have PaZero (physical : BurnolPaAmbientCarrier) (inside : physical∈burnolCompactCoPoissonClosedRange) :
   inner ℂ H (physical : BurnolL2)=0 := by
  rw [paAdjointSource_tests c orthogonal physical inside,disposition.1,inner_zero_left]
 have price (value : BurnolL2) : inner ℂ H value=unitFreeSourcePrice observation nontrivial half value := by
  have invisible:=full_invisible_source_inventory c value
  rw [original_R_full_input c,qAdjointSource_full_input c orthogonal,qPhysical] at invisible
  have split : value=(PA.E value : BurnolL2)+PA.invisible value := by
   unfold PA.invisible
   module
  calc
   inner ℂ H value=inner ℂ H (PA.E value : BurnolL2)+inner ℂ H (PA.invisible value) := by
    simpa only [inner_add_right] using congrArg (inner ℂ H) split
   _=inner ℂ H (PA.invisible value) := by rw [PaZero (PA.E value) (Submodule.starProjection_apply_mem _ _),zero_add]
   _=unitFreeSourcePrice observation nontrivial half value := invisible
 have read (value : BurnolL2) : inner ℂ receiptK (P.R observation nontrivial half value)=
    unitFreeSourcePrice observation nontrivial half value := by
  rw [kernel,OriginalKCombCofinalRAction.original_R_direct]
  change inner ℂ K (burnolDirectRightResolvent ((c).value/2) value)=_
  rw [original_R_full_input c]
  exact price value
 have target : targetRaw=P.R observation nontrivial half raw := targetAction.2.2
 have normal : inner ℂ receiptK targetRaw=unitFreeSourcePrice observation nontrivial half inputRaw := by
  rw [target,sourceInput]
  exact read raw
 have rawRead : inner ℂ receiptK rawNext=unitFreeSourcePrice observation nontrivial half raw := by
  rw [D.raw_successor]
  exact read raw
 have bornAction:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have born : bornRaw=P.R observation nontrivial half raw := bornAction.2.2.1
 have bornRead : inner ℂ receiptK bornRaw=unitFreeSourcePrice observation nontrivial half raw := by
  rw [born]
  exact read raw
 have projection:=actual_h_projection_on_original_whole_next observation nontrivial half depth ordinal
 have invisibleNext:=projection.2.2.2.2.2.1
 have bornNext:=projection.2.2.2.2.2.2.1
 rw [hQPhysical] at invisibleNext bornNext
 rw [unitPrice,mul_zero,zero_add] at bornNext
 exact ⟨OriginalKLossFreeAdjointMaterial.actual_lossfree_on_original_whole_next observation nontrivial half depth ordinal,
  projection,OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  ⟨sourceZero,disposition.1,Ezero,qPhysical,hQPhysical,unitPrice⟩,normal,rawRead,bornRead,
  ⟨invisibleNext,bornNext⟩,PaZero,whole,next⟩

/-- This independent consumer reads original K on its actual born, not the CP306 combined cotest. -/
theorem actual_unit_free_K_born_consumer :
 (inner ℂ receiptK bornRaw=unitFreeSourcePrice observation nontrivial half raw) ∧
 (inner ℂ receiptK nextBornRaw=inner ℂ (hPhysicalField c) rawNext-powerPrice) ∧
 (PA.E H=0) ∧ (inner ℂ receiptK Qunit=0) ∧
 type_of% (actual_h_projection_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_unit_free_K_on_original_whole_next observation nontrivial half depth ordinal
 have source:=actual.2.2.2.2.1
 have advanced:=actual.2.2.2.2.2.2.2.2.1
 exact ⟨actual.2.2.2.2.2.2.2.1,advanced.2,source.2.2.1,source.2.2.2.2.2,actual.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A zero actual B-power price removes precisely that residual fee. -/
theorem actual_B_power_price_zero_override (zero : powerPrice=0) :
 inner ℂ receiptK nextBornRaw=inner ℂ (hPhysicalField c) rawNext := by
 have actual:=(actual_unit_free_K_born_consumer observation nontrivial half depth ordinal).2.1
 simpa only [zero,sub_zero] using actual

/-- The paid zero unit price does not permit erasing a nonzero B-power source fee. -/
theorem actual_B_power_price_cannot_be_dropped (nonzero : powerPrice≠0) :
 inner ℂ receiptK nextBornRaw≠inner ℂ (hPhysicalField c) rawNext := by
 intro erased
 have actual:=(actual_unit_free_K_born_consumer observation nontrivial half depth ordinal).2.1
 rw [erased] at actual
 exact nonzero (sub_eq_self.mp actual.symm)

end OriginalKCrossParameterRAdjointSource.UnitKMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
