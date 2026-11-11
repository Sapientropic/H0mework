import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitJetSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.MaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_unit_jet_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_unit_jet_born_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitJetMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource SourceOperationScalarInventoryLift
open OriginalKCrossParameterRAdjointSource
open scoped InnerProductSpace
namespace PA
export OriginalKCombCofinalPaAction (E Q)
end PA
local instance unitJetMaterialGroups (grade:Nat) (target:Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance unitJetMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "sourceL" => SharedOutsideSource.sourceL c
local notation "Z" => OriginalKLossFreeAdjointMaterial.installedKernelCombo observation nontrivial half
local notation "newQ" => UnitJetSource.unitJetQSource observation half
local notation "newPa" => UnitJetSource.unitJetPaField observation half
local notation "aH" => OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude c

def actualPaFee (value:BurnolL2) :ℂ :=
 UnitJetSource.unitJetFeedbackCoefficient observation half*burnolPaResolventSourceCoefficient c (PA.E value)
def actualQPrice (value:BurnolL2) :ℂ := inner ℂ newQ (PA.Q value:BurnolL2)
def nextQPrice (value:BurnolL2) :ℂ := actualPaFee observation half value+actualQPrice observation half value

variable (depth ordinal:Nat)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth ordinal
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- The exact source order generates both full fields before the original same-event Q feedback is read. -/
theorem actual_unit_jet_on_original_whole_next :
 type_of% (OriginalKFiniteOrderRelease.MaterialConsumer.actual_release_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 (PaFeedbackSource.fourierWholeUnitSourcePrice c=UnitJetSource.unitJetPrice observation) ∧
 (PaFeedbackSource.sourcePaCoefficient c=UnitJetSource.unitJetPaCoefficient observation half) ∧
 (PA.E sourceL=newPa) ∧
 ((PA.Q sourceL:BurnolL2)=newQ) ∧
 (PaFeedbackSource.sourceQ c=newQ) ∧
 (inner ℂ Z (PA.Q targetRaw:BurnolL2)=nextQPrice observation half inputRaw) ∧
 (inner ℂ Z (PA.Q rawNext:BurnolL2)=nextQPrice observation half raw) ∧
 (inner ℂ Z (PA.Q bornRaw:BurnolL2)=nextQPrice observation half raw) ∧
 (nextQPrice observation half raw=(if m=1 then (-star aH*e)*alpha else 0)+actualQPrice observation half raw) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_Q_successor observation nontrivial half depth ordinal) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have kernel : receiptK=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  congrArg (fun receipt:OriginalRieszFiniteSource.Receipt=>receipt.kernel) sourceAnchor
 have anchor : Z=SharedOutsideSource.sourceKernelCombo c := by
  rw [OriginalKLossFreeAdjointMaterial.installedKernelCombo,kernel]
  exact (SharedOutsideSource.sourceKernelCombo_actual c).symm
 have read (value:BurnolL2) : inner ℂ Z (PA.Q (P.R observation nontrivial half value):BurnolL2)=
   nextQPrice observation half value := by
  rw [anchor,OriginalKCombCofinalRAction.original_R_direct]
  exact UnitJetSource.actual_sourceL_Q_feedback observation nontrivial half value
 have target : targetRaw=P.R observation nontrivial half raw := targetAction.2.2
 have normalPrice : inner ℂ Z (PA.Q targetRaw:BurnolL2)=nextQPrice observation half inputRaw := by
  rw [target,sourceInput]
  exact read raw
 have rawPrice : inner ℂ Z (PA.Q rawNext:BurnolL2)=nextQPrice observation half raw := by
  rw [D.raw_successor]
  exact read raw
 have generated:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have bornAction : bornRaw=P.R observation nontrivial half raw := generated.2.2.1
 have bornPrice : inner ℂ Z (PA.Q bornRaw:BurnolL2)=nextQPrice observation half raw := by
  rw [bornAction]
  exact read raw
 have actualCoefficient : burnolPaResolventSourceCoefficient c (PA.E raw)=alpha := by rfl
 have exactFee : nextQPrice observation half raw=
   (if m=1 then (-star aH*e)*alpha else 0)+actualQPrice observation half raw := by
  unfold nextQPrice actualPaFee UnitJetSource.unitJetFeedbackCoefficient
  rw [actualCoefficient]
  split_ifs <;> simp only [zero_mul]
 have fields:=UnitJetSource.actual_sourceL_E_Q observation nontrivial half
 exact ⟨OriginalKFiniteOrderRelease.MaterialConsumer.actual_release_on_original_whole_next observation nontrivial half depth ordinal,
  OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  UnitJetSource.actual_fourier_whole_unit_source observation nontrivial half,
  UnitJetSource.actual_pa_coefficient_source observation nontrivial half,fields.1,fields.2,
  UnitJetSource.actual_Q_source observation nontrivial half,normalPrice,rawPrice,bornPrice,exactFee,
  OriginalKDirectRCofinalDivision.actual_Q_successor observation nontrivial half depth ordinal,whole,next⟩

/-- The independent born reader consumes the generated fields and the exact Pa/Q prices with the old complete decoder. -/
theorem actual_unit_jet_born_consumer :
 type_of% (OriginalKFiniteOrderRelease.MaterialConsumer.actual_firstborn_release_consumer observation nontrivial half depth ordinal) ∧
 (PA.E sourceL=newPa) ∧
 ((PA.Q sourceL:BurnolL2)=newQ) ∧
 (inner ℂ Z (PA.Q bornRaw:BurnolL2)=nextQPrice observation half raw) ∧
 (nextQPrice observation half raw=(if m=1 then (-star aH*e)*alpha else 0)+actualQPrice observation half raw) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_Q_successor observation nontrivial half depth ordinal) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_unit_jet_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨OriginalKFiniteOrderRelease.MaterialConsumer.actual_firstborn_release_consumer observation nontrivial half depth ordinal,
  actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The simple-order branch retains the complete source Q price beside its true Pa fee. -/
theorem actual_simple_order_feedback (simple:m=1) :
 inner ℂ Z (PA.Q bornRaw:BurnolL2)=(-star aH*e)*alpha+actualQPrice observation half raw := by
 have actual:=actual_unit_jet_born_consumer observation nontrivial half depth ordinal
 exact actual.2.2.2.1.trans (by simpa only [if_pos simple] using actual.2.2.2.2.1)

/-- Higher order removes only the generated Pa field; the full remaining sourceL is still read on Qraw. -/
theorem actual_higher_order_Q_feedback (higher:1<m) :
 newQ=sourceL ∧ inner ℂ Z (PA.Q bornRaw:BurnolL2)=inner ℂ sourceL (PA.Q raw:BurnolL2) := by
 have notSimple:m≠1 := by omega
 have fullQ : newQ=sourceL := by
  simp only [UnitJetSource.unitJetQSource,UnitJetSource.unitJetPaField,UnitJetSource.unitJetPaCoefficient,
   if_neg notSimple,zero_smul,ZeroMemClass.coe_zero,sub_zero]
 have actual:=actual_unit_jet_born_consumer observation nontrivial half depth ordinal
 have price:=actual.2.2.2.1.trans actual.2.2.2.2.1
 rw [if_neg notSimple,zero_add] at price
 exact ⟨fullQ,by simpa only [actualQPrice,fullQ] using price⟩

/-- Vanishing actual source coefficient leaves the complete Q source price in the same born feedback. -/
theorem actual_zero_coefficient_override (zero:alpha=0) :
 inner ℂ Z (PA.Q bornRaw:BurnolL2)=actualQPrice observation half raw := by
 have actual:=actual_unit_jet_born_consumer observation nontrivial half depth ordinal
 have price:=actual.2.2.2.1.trans actual.2.2.2.2.1
 simpa only [zero,mul_zero,ite_self,zero_add] using price

/-- A nonzero complete weighted Pa price cannot be discarded on the strength of either factor alone. -/
theorem actual_nonzero_Pa_fee_cannot_be_dropped (nonzero:actualPaFee observation half raw≠0) :
 inner ℂ Z (PA.Q bornRaw:BurnolL2)≠actualQPrice observation half raw := by
 intro erased
 have actual:=(actual_unit_jet_born_consumer observation nontrivial half depth ordinal).2.2.2.1
 change _=actualPaFee observation half raw+actualQPrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (add_eq_right.mp actual.symm)

theorem actual_nonzero_Q_price_cannot_be_dropped (nonzero:actualQPrice observation half raw≠0) :
 inner ℂ Z (PA.Q bornRaw:BurnolL2)≠actualPaFee observation half raw := by
 intro erased
 have actual:=(actual_unit_jet_born_consumer observation nontrivial half depth ordinal).2.2.2.1
 change _=actualPaFee observation half raw+actualQPrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (add_eq_left.mp actual.symm)

end OriginalKFiniteOrderRelease.UnitJetMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
