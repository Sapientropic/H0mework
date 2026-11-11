import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPairedWaveConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRPairedWaveNativeStockConsumer
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace N
export OriginalKPairedWaveNativeStockSource
  (sourceRoot sourceVisit sourceFrame pairedState pairedWords sourceStock bornStock bornFrame
   feedEnvironment settledFrame stockBase sourcePairedOccurrence source_paired_word
   paired_word lastRIndex lastROccurrence last_R_word)
end N
namespace C
export OriginalWholeDebtRPairedWaveConsumer
  (actualInput actualOutput actual_R_equation actual_B_effect actual_complete_B_ne_zero actual_physical_energy_pos)
end C
namespace Feed
export SourceInventoryExecutionFeed
  (Inventory relationSpace affine relation_affine_written receipt receipt_cost request_boundary_written execution_exposure_written history_relation_space)
end Feed
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence sourceRequest source_request_member)
end WR
namespace Gen
export SourceInventoryExecutionFeed.FeedGeneratorOccurrence
  (fromRelationItem fromRelationItem_expression)
end Gen
namespace PT
export SourceOperationPaidRelations (exposure prefixHistory)
end PT

private theorem point_member {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    {source : Feed.Inventory (V := Value) (X := Var) (s := sort)}
    (point : WR.RelationOccurrence source) :
    PresentedRelationEventAt.relation point.word ∈ source.trace := by
  rw [point.trace_eq]
  exact List.mem_append_right _ List.mem_cons_self

private theorem point_history {Sorts Root : Type u} {Value Var : Sorts → Type u}
    [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    (root : RootedAccountedUnfolding Root)
    (source : Feed.Inventory (V := Value) (X := Var) (s := sort))
    (point : WR.RelationOccurrence source) :
    point.word ∈ (PT.prefixHistory root source).relationClosure := by
  rw [Feed.history_relation_space]
  exact Submodule.subset_span (point_member point)

private theorem operation_word_value {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    (environment : Env Value Var) (operation : Value sort →+ Value sort)
    (input output : Value sort) (equation : operation input = output) :
    valueMap (R := ℤ) environment
      (Finsupp.single (.linear operation (.const input)) (1 : ℤ) -
        Finsupp.single (.const output) 1) = 0 := by
  simp only [map_sub, valueMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Expr.eval, equation, sub_self]

private theorem operation_source_item {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    (operation : Value sort →+ Value sort) (input output : Value sort) :
    ((.linear operation (.const input), (1 : ℤ)) : Expr Value Var sort × ℤ) ∈
      Coefficients.sourceItems
        (Finsupp.single (.linear operation (.const input)) (1 : ℤ) -
          Finsupp.single (.const output) 1) := by
  classical
  let expression : Expr Value Var sort := .linear operation (.const input)
  have coefficient : ((Finsupp.single expression (1 : ℤ) -
      Finsupp.single (Expr.const output) 1) : Expr Value Var sort →₀ ℤ) expression = 1 := by
    simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
    have distinct : (Expr.const output : Expr Value Var sort) ≠ expression := by
      change (Expr.const output : Expr Value Var sort) ≠ .linear operation (.const input)
      intro same
      cases same
    simp only [Finsupp.single_eq_of_ne distinct.symm, sub_zero]
  exact List.mem_map.mpr ⟨expression,
    Finset.mem_toList.mpr (Finsupp.mem_support_iff.mpr (by rw [coefficient]; norm_num)),
    congrArg (fun value : ℤ => (expression, value)) coefficient⟩

private theorem right_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    1 / 4 < (coordinate.value / 2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [coordinate.rightHalf]

private theorem original_position_gap (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (gap : value ∈ locallyConstantFace burnolUnscaledCommonGapRadius) :
    burnolDirectRightResolventCLM coordinate value ∈
      locallyConstantFace burnolUnscaledCommonGapRadius :=
  CombSource.Pricing.ambient_R_positionGap (coordinate.value / 2)
    (right_quarter coordinate) value gap

private theorem original_division (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (gap : value ∈ locallyConstantFace burnolUnscaledCommonGapRadius)
    (w : ℂ) (wRight : 1/4 < w.re) (wBelow : w.re < 1/2) :
    burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
      (burnolDirectRightResolventCLM coordinate value) =
      (-(1/(coordinate.value / 2 + w - (1/2 : ℂ)))) *
        burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
          value :=
  CombSource.Pricing.ambient_R_scalar_action (coordinate.value / 2)
    (right_quarter coordinate) value gap w wRight wBelow

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

noncomputable def sourceRPoint := N.sourcePairedOccurrence observation nontrivial half depth ordinal
  (N.lastRIndex observation nontrivial half depth ordinal)

theorem source_R_word : (sourceRPoint observation nontrivial half depth ordinal).word =
    Finsupp.single (.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
      (.const (s := ()) (C.actualInput observation nontrivial half depth ordinal : BurnolL2))) (1 : ℤ) -
      Finsupp.single (.const (s := ()) (C.actualOutput observation nontrivial half depth ordinal)) 1 :=
  (N.source_paired_word observation nontrivial half depth ordinal
    (N.lastRIndex observation nontrivial half depth ordinal)).trans
      ((N.paired_word observation nontrivial half depth ordinal
        (N.lastRIndex observation nontrivial half depth ordinal)).symm.trans
          (N.last_R_word observation nontrivial half depth ordinal))

noncomputable def Support :=
  {item : Expr OriginalKPaNativePortSourceCalculation.Value OriginalKPaNativePortSourceCalculation.Var () × ℤ //
    item ∈ Coefficients.sourceItems (sourceRPoint observation nontrivial half depth ordinal).word}

/-- This generator is the child of the exact Feed request at the original relation slot. -/
noncomputable def supportGenerator (item : Support observation nontrivial half depth ordinal) :=
  Gen.fromRelationItem (N.feedEnvironment observation nontrivial half depth ordinal)
    (N.sourceStock observation nontrivial half depth ordinal)
    (sourceRPoint observation nontrivial half depth ordinal) item

theorem support_generator_expression (item : Support observation nontrivial half depth ordinal) :
    (supportGenerator observation nontrivial half depth ordinal item).expression = item.val.1 :=
  Gen.fromRelationItem_expression _ _ _ _

noncomputable def supportRequest (item : Support observation nontrivial half depth ordinal) :=
  WR.sourceRequest (sourceRPoint observation nontrivial half depth ordinal) item.val

noncomputable def supportReceipt (item : Support observation nontrivial half depth ordinal) :=
  Feed.receipt (N.feedEnvironment observation nontrivial half depth ordinal)
    (supportRequest observation nontrivial half depth ordinal item)

theorem support_cost (item : Support observation nontrivial half depth ordinal) :
    (supportReceipt observation nontrivial half depth ordinal item).length = remaining item.val.1 :=
  Feed.receipt_cost _ _

theorem support_exposure_written (item : Support observation nontrivial half depth ordinal) :
    ∀ event ∈ (PT.exposure (supportReceipt observation nontrivial half depth ordinal item)).trace,
      event ∈ (N.bornStock observation nontrivial half depth ordinal).trace :=
  Feed.execution_exposure_written _ _ _
    (WR.source_request_member (sourceRPoint observation nontrivial half depth ordinal) item.val item.property)

noncomputable def rFeedItem : Support observation nontrivial half depth ordinal :=
  ⟨(.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
      (.const (s := ()) (C.actualInput observation nontrivial half depth ordinal : BurnolL2)), 1),
    Eq.mp (congrArg (fun word =>
      ((.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (.const (s := ()) (C.actualInput observation nontrivial half depth ordinal : BurnolL2)), (1 : ℤ)) :
        Expr OriginalKPaNativePortSourceCalculation.Value OriginalKPaNativePortSourceCalculation.Var () × ℤ) ∈
          Coefficients.sourceItems word)
      (source_R_word observation nontrivial half depth ordinal).symm)
      (operation_source_item
        (Value := OriginalKPaNativePortSourceCalculation.Value)
        (Var := OriginalKPaNativePortSourceCalculation.Var) (sort := ())
        (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (C.actualInput observation nontrivial half depth ordinal : BurnolL2)
        (C.actualOutput observation nontrivial half depth ordinal))⟩

noncomputable def actualRFeedGenerator := supportGenerator observation nontrivial half depth ordinal
  (rFeedItem observation nontrivial half depth ordinal)

noncomputable def actualRFeedReceipt := supportReceipt observation nontrivial half depth ordinal
  (rFeedItem observation nontrivial half depth ordinal)

noncomputable def actualRFeedValue : BurnolL2 :=
  (supportRequest observation nontrivial half depth ordinal
    (rFeedItem observation nontrivial half depth ordinal)).expression.eval
      (N.feedEnvironment observation nontrivial half depth ordinal)

theorem actual_R_feed_paid : (actualRFeedReceipt observation nontrivial half depth ordinal).length = 1 :=
  (support_cost observation nontrivial half depth ordinal
    (rFeedItem observation nontrivial half depth ordinal)).trans rfl

theorem actual_R_feed_equation : actualRFeedValue observation nontrivial half depth ordinal =
    C.actualOutput observation nontrivial half depth ordinal :=
  C.actual_R_equation observation nontrivial half depth ordinal

theorem actual_R_feed_B : OriginalKCombPhysicalAction.physicalRemainder
    (actualRFeedValue observation nontrivial half depth ordinal) ≠ 0 :=
  Eq.mp (congrArg (fun value : BurnolL2 => OriginalKCombPhysicalAction.physicalRemainder value ≠ 0)
    (actual_R_feed_equation observation nontrivial half depth ordinal).symm)
      (C.actual_complete_B_ne_zero observation nontrivial half depth ordinal)

theorem source_R_value_zero : valueMap (R := ℤ)
    (N.feedEnvironment observation nontrivial half depth ordinal)
    (sourceRPoint observation nontrivial half depth ordinal).word = 0 :=
  (congrArg (valueMap (R := ℤ) (N.feedEnvironment observation nontrivial half depth ordinal))
    (source_R_word observation nontrivial half depth ordinal)).trans
      (operation_word_value
        (Value := OriginalKPaNativePortSourceCalculation.Value)
        (Var := OriginalKPaNativePortSourceCalculation.Var) (sort := ())
        _ (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (C.actualInput observation nontrivial half depth ordinal : BurnolL2)
        (C.actualOutput observation nontrivial half depth ordinal)
        (C.actual_R_equation observation nontrivial half depth ordinal))

theorem source_R_affine_written : Feed.affine
    (N.feedEnvironment observation nontrivial half depth ordinal)
    (sourceRPoint observation nontrivial half depth ordinal).word ∈
      Feed.relationSpace (N.bornStock observation nontrivial half depth ordinal) :=
  Feed.relation_affine_written _ _ _ (point_member (sourceRPoint observation nontrivial half depth ordinal))

noncomputable def actualHistory := ActualNativeRelationTransport.bornHistory
  (N.settledFrame observation nontrivial half depth ordinal)
  (N.stockBase observation nontrivial half depth ordinal)

theorem support_boundary_in_actual_history (item : Support observation nontrivial half depth ordinal) :
    Finsupp.single item.val.1 (1 : ℤ) -
      Finsupp.single (.const (item.val.1.eval (N.feedEnvironment observation nontrivial half depth ordinal))) 1 ∈
        (actualHistory observation nontrivial half depth ordinal).relationClosure := by
  have written := Feed.request_boundary_written
    (N.feedEnvironment observation nontrivial half depth ordinal)
    (N.sourceStock observation nontrivial half depth ordinal)
    (supportRequest observation nontrivial half depth ordinal item)
    (WR.source_request_member (sourceRPoint observation nontrivial half depth ordinal) item.val item.property)
  exact Eq.mp (congrArg (fun space =>
    Finsupp.single item.val.1 (1 : ℤ) -
      Finsupp.single (.const (item.val.1.eval (N.feedEnvironment observation nontrivial half depth ordinal))) 1 ∈ space)
      (Feed.history_relation_space _ (N.bornStock observation nontrivial half depth ordinal)).symm) written

noncomputable def actualRNormalization := ActualNativeRelationTransport.normalizeSource
  (N.settledFrame observation nontrivial half depth ordinal)
  (N.stockBase observation nontrivial half depth ordinal)
  ⟨(sourceRPoint observation nontrivial half depth ordinal).word,
    Submodule.subset_span (point_member (sourceRPoint observation nontrivial half depth ordinal))⟩

theorem actual_R_normalization_word : type_of%
    (ActualNativeRelationTransport.normalized_source_word
      (N.settledFrame observation nontrivial half depth ordinal)
      (N.stockBase observation nontrivial half depth ordinal)
      ⟨(sourceRPoint observation nontrivial half depth ordinal).word,
        Submodule.subset_span (point_member (sourceRPoint observation nontrivial half depth ordinal))⟩) :=
  ActualNativeRelationTransport.normalized_source_word
    (N.settledFrame observation nontrivial half depth ordinal)
    (N.stockBase observation nontrivial half depth ordinal)
    ⟨(sourceRPoint observation nontrivial half depth ordinal).word,
      Submodule.subset_span (point_member (sourceRPoint observation nontrivial half depth ordinal))⟩

noncomputable def actualBirthEvent :=
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root
    (N.settledFrame observation nontrivial half depth ordinal)
    (OriginalKPairedWaveNativeStockSource.stockProgramme observation nontrivial half depth ordinal)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit
        (N.settledFrame observation nontrivial half depth ordinal)
        (OriginalKPairedWaveNativeStockSource.stockProgramme observation nontrivial half depth ordinal))

noncomputable def actualBirthTarget := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.targetAt
  (N.settledFrame observation nontrivial half depth ordinal)
  (OriginalKPairedWaveNativeStockSource.stockProgramme observation nontrivial half depth ordinal)
  (actualBirthEvent observation nontrivial half depth ordinal)

theorem actual_whole : type_of% (actualBirthTarget observation nontrivial half depth ordinal).firstDestination_heq :=
  (actualBirthTarget observation nontrivial half depth ordinal).firstDestination_heq

theorem actual_target_next : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.target_next
    (N.settledFrame observation nontrivial half depth ordinal)
    (OriginalKPairedWaveNativeStockSource.stockProgramme observation nontrivial half depth ordinal)
    (actualBirthEvent observation nontrivial half depth ordinal)) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.target_next
    (N.settledFrame observation nontrivial half depth ordinal)
    (OriginalKPairedWaveNativeStockSource.stockProgramme observation nontrivial half depth ordinal)
    (actualBirthEvent observation nontrivial half depth ordinal)

theorem actual_stock_payload : type_of% (ActualNativeRelationTransport.born_payload
    (N.settledFrame observation nontrivial half depth ordinal)
    (N.stockBase observation nontrivial half depth ordinal)
    (actualBirthEvent observation nontrivial half depth ordinal)) :=
  ActualNativeRelationTransport.born_payload
    (N.settledFrame observation nontrivial half depth ordinal)
    (N.stockBase observation nontrivial half depth ordinal)
    (actualBirthEvent observation nontrivial half depth ordinal)

theorem actual_decoded_environment : (N.bornFrame observation nontrivial half depth ordinal).activeEnvironment =
    N.feedEnvironment observation nontrivial half depth ordinal :=
  ActualNativeRelationTransport.decoded_environment
    (N.settledFrame observation nontrivial half depth ordinal)
    (N.stockBase observation nontrivial half depth ordinal)

theorem original_R_in_actual_history : (N.lastROccurrence observation nontrivial half depth ordinal).word ∈
    (actualHistory observation nontrivial half depth ordinal).relationClosure :=
  point_history _ _ (N.lastROccurrence observation nontrivial half depth ordinal)

theorem actual_input_positionGap : (C.actualInput observation nontrivial half depth ordinal : BurnolL2) ∈
    locallyConstantFace burnolUnscaledCommonGapRadius :=
  (C.actualInput observation nontrivial half depth ordinal).property.1.1

theorem actual_output_positionGap : C.actualOutput observation nontrivial half depth ordinal ∈
    locallyConstantFace burnolUnscaledCommonGapRadius :=
  Eq.mp (congrArg (fun value : BurnolL2 =>
    value ∈ locallyConstantFace burnolUnscaledCommonGapRadius)
      (C.actual_R_equation observation nontrivial half depth ordinal))
    (original_position_gap c (C.actualInput observation nontrivial half depth ordinal)
      (actual_input_positionGap observation nontrivial half depth ordinal))

theorem actual_original_Division (w : ℂ) (wRight : 1/4 < w.re) (wBelow : w.re < 1/2) :
    burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
      (C.actualOutput observation nontrivial half depth ordinal) =
      (-(1/((c).value / 2 + w - (1/2 : ℂ)))) *
        burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
          (C.actualInput observation nontrivial half depth ordinal : BurnolL2) :=
  (congrArg (burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow))
    (C.actual_R_equation observation nontrivial half depth ordinal)).symm.trans
      (original_division c (C.actualInput observation nontrivial half depth ordinal)
        (actual_input_positionGap observation nontrivial half depth ordinal) w wRight wBelow)

end OriginalWholeDebtRPairedWaveNativeStockConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeDebtRPairedWaveNativeStockConsumer"
