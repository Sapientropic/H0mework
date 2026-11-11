import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaFeedbackSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HProjectionReceipt
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.Controls

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_lossfree_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_lossfree_born_consumer"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_lossfree_Q_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKLossFreeAdjointMaterial
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local instance materialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance materialPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalDivision.DirectRDivisionControls.bornRead observation nontrivial half depth ordinal
local notation "Z" => OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c
local notation "V" => OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceL c
local notation "aJ" => OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude c
local notation "aH" => OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude c
local notation "κ" => OriginalKCrossParameterRAdjointSource.PaFeedbackSource.sourcePaCoefficient c
local notation "Vq" => OriginalKCrossParameterRAdjointSource.PaFeedbackSource.sourceQ c
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal
local notation "qraw" => (OriginalKCombCofinalPaAction.Q raw : BurnolL2)
local notation "qnext" => (OriginalKCombCofinalPaAction.Q rawNext : BurnolL2)
local notation "feedback" => star κ*alpha+inner ℂ Vq qraw
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- Only the target cotest uses the installed receipt; the source vector is independently generated. -/
def installedKernelCombo : BurnolL2 := aJ • receiptK-aH • fourierL2 receiptK

private theorem combo_anchor_from
 (sourceAnchor : type_of% (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)) :
 installedKernelCombo observation nontrivial half=Z := by
 have kernel : receiptK=(burnolCompletedMellinRieszVector c : BurnolL2) :=
  congrArg (fun receipt : OriginalRieszFiniteSource.Receipt=>receipt.kernel) sourceAnchor
 rw [installedKernelCombo,kernel]
 exact (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo_actual c).symm

/-- The complete original source action now reads its actual physical input in this combined direction. -/
theorem actual_lossfree_on_original_whole_next :
 type_of% (OriginalKDirectRCofinalOutsideVolterraSource.actual_h_projection_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
   (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
   (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 (inner ℂ (installedKernelCombo observation nontrivial half) targetRaw=
   inner ℂ V (burnolEvenAmbientProjection inputRaw : BurnolL2)) ∧
 (inner ℂ (installedKernelCombo observation nontrivial half) rawNext=
   inner ℂ V (burnolEvenAmbientProjection raw : BurnolL2)) ∧
 (inner ℂ (installedKernelCombo observation nontrivial half) bornRaw=
   inner ℂ V (burnolEvenAmbientProjection raw : BurnolL2)) ∧
 (inner ℂ (installedKernelCombo observation nontrivial half) (OriginalKCombCofinalPaAction.Q targetRaw : BurnolL2)=feedback ∧
  inner ℂ (installedKernelCombo observation nontrivial half) qnext=feedback ∧
  inner ℂ (installedKernelCombo observation nontrivial half) (OriginalKCombCofinalPaAction.Q bornRaw : BurnolL2)=feedback ∧
  type_of% (OriginalKDirectRCofinalDivision.actual_Q_successor observation nontrivial half depth ordinal)) ∧
 (type_of% (sourceAdjoint_original c) ∧
  type_of% (OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal) ∧
  type_of% (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero)) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have anchor:=combo_anchor_from observation nontrivial half sourceAnchor
 have read (value : BurnolL2) :
   inner ℂ (installedKernelCombo observation nontrivial half) (P.R observation nontrivial half value)=
   inner ℂ V (burnolEvenAmbientProjection value : BurnolL2) := by
  rw [anchor,OriginalKCombCofinalRAction.original_R_direct]
  exact OriginalKCrossParameterRAdjointSource.SharedOutsideSource.original_R_sourceL_physical_read c value
 have target : targetRaw=P.R observation nontrivial half raw := targetAction.2.2
 have normal : inner ℂ (installedKernelCombo observation nontrivial half) targetRaw=
    inner ℂ V (burnolEvenAmbientProjection inputRaw : BurnolL2) := by
  rw [target,sourceInput]
  exact read raw
 have rawRead : inner ℂ (installedKernelCombo observation nontrivial half) rawNext=
    inner ℂ V (burnolEvenAmbientProjection raw : BurnolL2) := by
  rw [D.raw_successor]
  exact read raw
 have bornAction:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have born : bornRaw=P.R observation nontrivial half raw := bornAction.2.2.1
 have bornRead : inner ℂ (installedKernelCombo observation nontrivial half) bornRaw=
    inner ℂ V (burnolEvenAmbientProjection raw : BurnolL2) := by
  rw [born]
  exact read raw
 have qRead : inner ℂ (installedKernelCombo observation nontrivial half)
    (OriginalKCombCofinalPaAction.Q (P.R observation nontrivial half raw) : BurnolL2)=feedback := by
  rw [anchor,OriginalKCombCofinalRAction.original_R_direct]
  exact OriginalKCrossParameterRAdjointSource.PaFeedbackSource.original_R_sourceL_Q_feedback c observation.mathlibZero raw
 have normalQ : inner ℂ (installedKernelCombo observation nontrivial half)
    (OriginalKCombCofinalPaAction.Q targetRaw : BurnolL2)=feedback := by
  rw [target]
  exact qRead
 have rawQ : inner ℂ (installedKernelCombo observation nontrivial half) qnext=feedback := by
  rw [D.raw_successor]
  exact qRead
 have bornQ : inner ℂ (installedKernelCombo observation nontrivial half)
    (OriginalKCombCofinalPaAction.Q bornRaw : BurnolL2)=feedback := by
  rw [born]
  exact qRead
 exact ⟨OriginalKDirectRCofinalOutsideVolterraSource.actual_h_projection_on_original_whole_next observation nontrivial half depth ordinal,
  OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  normal,rawRead,bornRead,
  ⟨normalQ,rawQ,bornQ,OriginalKDirectRCofinalDivision.actual_Q_successor observation nontrivial half depth ordinal⟩,
  ⟨adjointSource,divisionRead,orthogonal⟩,whole,next⟩

/-- The independent born consumer keeps the original H projection cost and the actual generated destination. -/
theorem actual_lossfree_born_consumer :
 (inner ℂ (installedKernelCombo observation nontrivial half) bornRaw=
   inner ℂ V (burnolEvenAmbientProjection raw : BurnolL2)) ∧
 type_of% (OriginalKDirectRCofinalOutsideVolterraSource.actual_h_projection_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_lossfree_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨actual.2.2.2.2.2.1,actual.1,actual.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2⟩

/-- The original Q recurrence is read from this same full calculation, unit plus Q return intact. -/
theorem actual_lossfree_Q_consumer :
 (inner ℂ (installedKernelCombo observation nontrivial half) qnext=feedback) ∧
 (inner ℂ (installedKernelCombo observation nontrivial half) (OriginalKCombCofinalPaAction.Q bornRaw : BurnolL2)=feedback) ∧
 type_of% (OriginalKDirectRCofinalDivision.actual_Q_successor observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalOutsideVolterraSource.actual_h_projection_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_lossfree_on_original_whole_next observation nontrivial half depth ordinal
 have qSource:=actual.2.2.2.2.2.2.1
 exact ⟨qSource.2.1,qSource.2.2.1,qSource.2.2.2,actual.1,
  actual.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2⟩

/-- A zero original unit coefficient leaves the complete Q source price in the recurrence. -/
theorem actual_unit_coefficient_zero_override (zero : alpha=0) :
 inner ℂ (installedKernelCombo observation nontrivial half) qnext=inner ℂ Vq qraw := by
 have actual:=(actual_lossfree_Q_consumer observation nontrivial half depth ordinal).1
 simpa only [zero,mul_zero,zero_add] using actual

/-- A nonzero price of the retained Q source cannot be replaced by the unit price alone. -/
theorem actual_Q_source_cannot_be_dropped (nonzero : inner ℂ Vq qraw≠0) :
 inner ℂ (installedKernelCombo observation nontrivial half) qnext≠star κ*alpha := by
 intro erased
 have actual:=(actual_lossfree_Q_consumer observation nontrivial half depth ordinal).1
 rw [erased] at actual
 exact nonzero (add_eq_left.mp actual.symm)

end OriginalKLossFreeAdjointMaterial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
