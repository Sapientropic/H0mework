import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitJetMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_unit_power_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_unit_power_born_consumer"
-- Suggestion indexing would unfold the explicit dependent ledger projections.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "UnitPowerMaterialConsumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitPowerMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource SourceOperationScalarInventoryLift
open OriginalKCrossParameterRAdjointSource
open scoped InnerProductSpace
namespace PA
export OriginalKCombCofinalPaAction (E Q invisible)
end PA
local instance unitPowerMaterialGroups (grade:Nat) (target:Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance unitPowerMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "H" => UnitPowerSource.fulladjointPowerZ observation half
local notation "Z" => OriginalKLossFreeAdjointMaterial.installedKernelCombo observation nontrivial half

def actualPaFee (value:BurnolL2) :ℂ :=
 UnitPowerSource.feedbackCoefficient observation half*burnolPaResolventSourceCoefficient c (PA.E value)
def actualQPrice (value:BurnolL2) :ℂ := inner ℂ H (PA.Q value:BurnolL2)
def actualOutsidePrice (value:BurnolL2) :ℂ :=
 inner ℂ H (value-(burnolEvenAmbientProjection value:BurnolL2))
def actualInvisiblePrice (value:BurnolL2) :ℂ := inner ℂ H (PA.invisible value)
def completePrice (value:BurnolL2) :ℂ :=
 actualPaFee observation half value+actualQPrice observation half value+actualOutsidePrice observation half value

/-- Only the actual cofinal successor is iterated; no unit query is identified with raw. -/
theorem actual_raw_original_power (depth ordinal steps:Nat) :
 D.raw observation nontrivial half depth (ordinal+steps)=
   ((P.R observation nontrivial half)^steps) (D.raw observation nontrivial half depth ordinal) := by
 induction steps with
 | zero => simp only [Nat.add_zero,pow_zero,one_apply_eq_self]
 | succ steps previous =>
  simpa only [Nat.add_succ,pow_succ',mul_apply_eq_comp] using
   (D.raw_successor observation nontrivial half depth (ordinal+steps)).trans
    (congrArg (P.R observation nontrivial half) previous)

private theorem original_action_source : P.R observation nontrivial half=burnolDirectRightResolventCLM c := by
 apply ContinuousLinearMap.ext
 intro v
 exact OriginalKCombCofinalRAction.original_R_direct observation nontrivial half v

private theorem original_power_source (steps:Nat) (value:BurnolL2) :
 ((P.R observation nontrivial half)^steps) value=
   CombSource.Division.rawIterate observation half.down steps value := by
 rw [original_action_source observation nontrivial half]
 rfl

/-- The complete invisible input is Q plus its actual outside-physical component. -/
theorem complete_invisible_inventory (value:BurnolL2) :
 actualInvisiblePrice observation half value=
   actualQPrice observation half value+actualOutsidePrice observation half value := by
 have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
  (burnolEvenAmbientProjection value)
 have inventory := congrArg (fun field:BurnolPaAmbientCarrier=>(field:BurnolL2)) split
 change (PA.E value:BurnolL2)+(PA.Q value:BurnolL2)=(burnolEvenAmbientProjection value:BurnolL2) at inventory
 have actual : PA.invisible value=(PA.Q value:BurnolL2)+(value-(burnolEvenAmbientProjection value:BurnolL2)) := by
  unfold OriginalKCombCofinalPaAction.invisible
  linear_combination (norm := module) -inventory
 unfold actualInvisiblePrice actualQPrice actualOutsidePrice
 rw [actual,inner_add_right]

include nontrivial in
private theorem source_complete_price (value:BurnolL2) :
 inner ℂ (SharedOutsideSource.sourceKernelCombo c)
   (CombSource.Division.rawIterate observation half.down m value)=completePrice observation half value := by
 rw [UnitPowerSource.actual_full_power_read observation half]
 have split : value=(PA.E value:BurnolL2)+PA.invisible value := by
  unfold OriginalKCombCofinalPaAction.invisible
  module
 calc
  inner ℂ H value=inner ℂ H (PA.E value:BurnolL2)+inner ℂ H (PA.invisible value) := by
   nth_rw 1 [split]
   exact inner_add_right _ _ _
  _ = actualPaFee observation half value+actualInvisiblePrice observation half value := by
   rw [UnitPowerSource.actual_adjoint_power_Pa_tests observation nontrivial half (PA.E value)
    (Submodule.starProjection_apply_mem _ _)]
   rfl
  _ = completePrice observation half value := by
   rw [complete_invisible_inventory]
   simp only [completePrice,add_assoc]

variable (depth ordinal:Nat)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawEnd" => D.raw observation nontrivial half depth (ordinal+m)
local notation "lastOrdinal" => ordinal+(m-1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth lastOrdinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth lastOrdinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth lastOrdinal
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- One original terminal step carries the complete old mouth and the new exact-order source price. -/
structure MaterialAt : Prop where
 inherited : type_of% (UnitJetMaterialConsumer.actual_unit_jet_on_original_whole_next observation nontrivial half depth lastOrdinal)
 normalState : type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth lastOrdinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth lastOrdinal))
 normalHistory : type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth lastOrdinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth lastOrdinal))
 sourceField : PA.E H=UnitPowerSource.paPowerField observation half
 lowerSource : ∀ j:Nat,j<m → PA.E ((((P.R observation nontrivial half)^j).adjoint) Z)=0
 feedbackSource : UnitPowerSource.feedbackCoefficient observation half≠0
 sourceFieldNonzero : PA.E H≠0
 rawWord : rawEnd=((P.R observation nontrivial half)^m) raw
 sourceAction : targetRaw=P.R observation nontrivial half inputRaw
 normalGenerated : targetRaw=rawEnd
 bornGenerated : bornRaw=rawEnd
 normalPrice : inner ℂ Z targetRaw=completePrice observation half raw
 rawPrice : inner ℂ Z rawEnd=completePrice observation half raw
 bornPrice : inner ℂ Z bornRaw=completePrice observation half raw
 invisibleInventory : actualInvisiblePrice observation half raw=actualQPrice observation half raw+actualOutsidePrice observation half raw
 generatedIndex : lastOrdinal+1=ordinal+m
 whole : type_of% (RC.original_whole factory initial cfg rfl (lastOrdinal+1))
 next : type_of% (RC.actual_generated_current factory initial cfg rfl (lastOrdinal+1))

/-- The source callback generates the literal final born before its complete m-power price is read. -/
theorem actual_unit_power_on_original_whole_next : MaterialAt observation nontrivial half depth ordinal := by
 have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
 have endIndex : lastOrdinal+1=ordinal+m := by omega
 apply consume_actual_normal_source observation nontrivial half depth lastOrdinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have kernel : (installedOriginalKReceiptAt observation nontrivial half.down).kernel=
   (burnolCompletedMellinRieszVector c:BurnolL2) :=
  congrArg (fun receipt:OriginalRieszFiniteSource.Receipt=>receipt.kernel) sourceAnchor
 have anchor : Z=SharedOutsideSource.sourceKernelCombo c := by
  rw [OriginalKLossFreeAdjointMaterial.installedKernelCombo,kernel]
  exact (SharedOutsideSource.sourceKernelCombo_actual c).symm
 have word := actual_raw_original_power observation nontrivial half depth ordinal m
 have read : inner ℂ Z rawEnd=completePrice observation half raw := by
  rw [anchor,word,original_power_source]
  exact source_complete_price observation nontrivial half raw
 have sourceAction : targetRaw=P.R observation nontrivial half inputRaw := by
  rw [sourceInput]
  exact targetAction.2.2
 have normalGenerated : targetRaw=rawEnd := by
  rw [sourceAction,sourceInput,←D.raw_successor,endIndex]
 have generated := Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have bornAction : bornRaw=P.R observation nontrivial half (D.raw observation nontrivial half depth lastOrdinal) := generated.2.2.1
 have bornGenerated : bornRaw=rawEnd := by
  rw [bornAction,←D.raw_successor,endIndex]
 exact {
  inherited := UnitJetMaterialConsumer.actual_unit_jet_on_original_whole_next observation nontrivial half depth lastOrdinal
  normalState := OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth lastOrdinal state
  normalHistory := OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth lastOrdinal trace
  sourceField := UnitPowerSource.actual_adjoint_power_Pa_source observation nontrivial half
  lowerSource := by
   intro j before
   rw [original_action_source observation nontrivial half,anchor]
   exact UnitPowerSource.actual_adjoint_lower_Pa_zero observation nontrivial half j before
  feedbackSource := UnitPowerSource.feedbackCoefficient_ne_zero observation nontrivial half
  sourceFieldNonzero := UnitPowerSource.actual_adjoint_power_Pa_ne_zero observation nontrivial half
  rawWord := word
  sourceAction := sourceAction
  normalGenerated := normalGenerated
  bornGenerated := bornGenerated
  normalPrice := by rw [normalGenerated];exact read
  rawPrice := read
  bornPrice := by rw [bornGenerated];exact read
  invisibleInventory := complete_invisible_inventory observation half raw
  generatedIndex := endIndex
  whole := whole
  next := next }

/-- This independent reader consumes the same generated born, all three full prices, source field and whole-next. -/
theorem actual_unit_power_born_consumer :
 (PA.E H=UnitPowerSource.paPowerField observation half) ∧
 (∀ j:Nat,j<m → PA.E ((((P.R observation nontrivial half)^j).adjoint) Z)=0) ∧
 (UnitPowerSource.feedbackCoefficient observation half≠0) ∧
 (PA.E H≠0) ∧
 (bornRaw=rawEnd) ∧
 (inner ℂ Z bornRaw=actualPaFee observation half raw+actualQPrice observation half raw+actualOutsidePrice observation half raw) ∧
 (actualInvisiblePrice observation half raw=actualQPrice observation half raw+actualOutsidePrice observation half raw) ∧
 (lastOrdinal+1=ordinal+m) ∧
 type_of% (RC.original_whole factory initial cfg rfl (lastOrdinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (lastOrdinal+1)) := by
 have actual := actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨actual.sourceField,actual.lowerSource,actual.feedbackSource,actual.sourceFieldNonzero,actual.bornGenerated,
  actual.bornPrice,actual.invisibleInventory,actual.generatedIndex,actual.whole,actual.next⟩

/-- The simple-order source computes the exact old coefficient and its complete Q/outside price. -/
theorem actual_simple_order_feedback (simple:m=1) :
 H=SharedOutsideSource.sourceL c ∧
 UnitPowerSource.feedbackCoefficient observation half=UnitJetSource.unitJetFeedbackCoefficient observation half ∧
 completePrice observation half raw=UnitJetMaterialConsumer.nextQPrice observation half raw ∧
 inner ℂ Z bornRaw=UnitJetMaterialConsumer.nextQPrice observation half raw := by
 have generated := UnitPowerSource.simple_order_source observation half simple
 have source := generated.1
 have coefficient := generated.2.2
 have qRead : actualQPrice observation half raw=UnitJetMaterialConsumer.actualQPrice observation half raw := by
  have normal := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_right
   ⟨PA.Q raw,Submodule.starProjection_apply_mem _ _⟩ (burnolEvenAmbientProjection (SharedOutsideSource.sourceL c))
  change inner ℂ (PA.Q (SharedOutsideSource.sourceL c):BurnolL2) (PA.Q raw:BurnolL2)=
   inner ℂ (burnolEvenAmbientProjection (SharedOutsideSource.sourceL c):BurnolL2) (PA.Q raw:BurnolL2) at normal
  rw [(UnitJetSource.actual_sourceL_E_Q observation nontrivial half).2,SharedOutsideSource.sourceL_physical] at normal
  unfold actualQPrice UnitJetMaterialConsumer.actualQPrice
  rw [source]
  exact normal.symm
 have outside : actualOutsidePrice observation half raw=0 := by
  have normal := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
   ⟨SharedOutsideSource.sourceL c,SharedOutsideSource.sourceL_mem c⟩ raw
  change inner ℂ (SharedOutsideSource.sourceL c) (burnolEvenAmbientProjection raw:BurnolL2)=inner ℂ (SharedOutsideSource.sourceL c) raw at normal
  unfold actualOutsidePrice
  rw [source,inner_sub_right,normal,sub_self]
 have price : completePrice observation half raw=UnitJetMaterialConsumer.nextQPrice observation half raw := by
  unfold completePrice UnitJetMaterialConsumer.nextQPrice actualPaFee UnitJetMaterialConsumer.actualPaFee
  rw [coefficient,qRead,outside,add_zero]
 exact ⟨source,coefficient,price,(actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal).bornPrice.trans price⟩

/-- Higher order keeps CP315's first-step zero and recovers the nonzero source coefficient at its exact delay. -/
theorem actual_higher_order_delayed_feedback (higher:1<m) :
 UnitJetSource.unitJetFeedbackCoefficient observation half=0 ∧
 UnitPowerSource.feedbackCoefficient observation half≠0 ∧
 PA.E H≠0 ∧
 inner ℂ Z bornRaw=actualPaFee observation half raw+actualQPrice observation half raw+actualOutsidePrice observation half raw := by
 have notSimple : m≠1 := by omega
 have actual := actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨by simp only [UnitJetSource.unitJetFeedbackCoefficient,if_neg notSimple],
  actual.feedbackSource,actual.sourceFieldNonzero,actual.bornPrice⟩

/-- An explicit zero Q fee retains the actual Pa and complete outside fees. -/
theorem actual_zero_Q_override (zero:actualQPrice observation half raw=0) :
 inner ℂ Z bornRaw=actualPaFee observation half raw+actualOutsidePrice observation half raw := by
 have actual := (actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 simpa only [completePrice,zero,add_zero] using actual

/-- An explicit zero outside fee retains the actual Pa and complete Q fees. -/
theorem actual_zero_outside_override (zero:actualOutsidePrice observation half raw=0) :
 inner ℂ Z bornRaw=actualPaFee observation half raw+actualQPrice observation half raw := by
 have actual := (actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 simpa only [completePrice,zero,add_zero] using actual

theorem actual_zero_coefficient_override
 (zero:burnolPaResolventSourceCoefficient c (PA.E raw)=0) :
 inner ℂ Z bornRaw=actualQPrice observation half raw+actualOutsidePrice observation half raw := by
 have actual := (actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 simpa only [completePrice,actualPaFee,zero,mul_zero,zero_add] using actual

/-- Controls take the complete actual fee, never a factor substituted as a producer premise. -/
theorem actual_nonzero_Pa_fee_cannot_be_dropped (nonzero:actualPaFee observation half raw≠0) :
 inner ℂ Z bornRaw≠actualQPrice observation half raw+actualOutsidePrice observation half raw := by
 intro erased
 have actual := (actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 change _=actualPaFee observation half raw+actualQPrice observation half raw+actualOutsidePrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (by linear_combination -actual)

theorem actual_nonzero_Q_price_cannot_be_dropped (nonzero:actualQPrice observation half raw≠0) :
 inner ℂ Z bornRaw≠actualPaFee observation half raw+actualOutsidePrice observation half raw := by
 intro erased
 have actual := (actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 change _=actualPaFee observation half raw+actualQPrice observation half raw+actualOutsidePrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (by linear_combination -actual)

theorem actual_nonzero_outside_price_cannot_be_dropped (nonzero:actualOutsidePrice observation half raw≠0) :
 inner ℂ Z bornRaw≠actualPaFee observation half raw+actualQPrice observation half raw := by
 intro erased
 have actual := (actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 change _=actualPaFee observation half raw+actualQPrice observation half raw+actualOutsidePrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (by linear_combination -actual)

end OriginalKFiniteOrderRelease.UnitPowerMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
