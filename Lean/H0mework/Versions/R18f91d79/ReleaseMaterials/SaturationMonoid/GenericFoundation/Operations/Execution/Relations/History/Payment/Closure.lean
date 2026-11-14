import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement

open private word_exposure from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed

variable {Sorts Root : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {before after : Expr Value Var sort}

local notation "Word" => Formal ℤ Value Var sort
local notation "Hₚ" "(" root "," trace ")" => prefixHistory root (exposure trace)

private theorem relation_event_word (trace : Trace environment before after) (word : Word)
    (present : PresentedRelationEventAt.relation word ∈ (exposure trace).trace) :
    word ∈ words trace := by
  change PresentedRelationEventAt.relation word ∈ PresentedRelationEventAt.generator before ::
    RootedAccountedUnfolding.traceBranches (events trace) at present
  rw [events_trace] at present
  rcases List.mem_cons.mp present with impossible | belongs
  · cases impossible
  · obtain ⟨item, member, equal⟩ := List.mem_map.mp belongs
    exact (PresentedRelationEventAt.relation.inj equal) ▸ member

theorem payment_relation_closure (root : RootedAccountedUnfolding Root)
    (trace : Trace environment before after) :
    (Hₚ(root, trace)).relationClosure = LinearMap.range (writePayment trace) := by
  have same :
      {word : Word | PresentedRelationEventAt.relation word ∈ (exposure trace).trace} =
        {word : Word | word ∈ words trace} :=
    Set.ext fun word => ⟨relation_event_word trace word, word_exposure trace word⟩
  rw [SourceInventoryExecutionFeed.history_relation_space, write_payment_range,
    SourceInventoryExecutionFeed.relationSpace, same]

/-- The actual paid relation closure has the ordered integer coordinates of its Trace. -/
def relationPaymentEquiv (root : RootedAccountedUnfolding Root)
    (trace : Trace environment before after) :
    (Fin (words trace).length →₀ ℤ) ≃ₗ[ℤ] (Hₚ(root, trace)).relationClosure := by
  let forward := LinearMap.codRestrict (Hₚ(root, trace)).relationClosure (writePayment trace)
    (fun coeff => by rw [payment_relation_closure]; exact ⟨coeff, rfl⟩)
  let back := (readPayment trace).comp (Hₚ(root, trace)).relationClosure.subtype
  refine LinearEquiv.ofLinearMap forward back (LinearMap.ext fun relation => ?_)
    (LinearMap.ext fun coeff => read_write_payment trace coeff)
  have belongs : relation.val ∈ LinearMap.range (writePayment trace) :=
    Eq.mp (congrArg (fun space : Submodule ℤ Word => relation.val ∈ space)
      (payment_relation_closure root trace)) relation.property
  obtain ⟨coeff, written⟩ := belongs
  apply Subtype.ext
  change writePayment trace (readPayment trace relation.val) = relation.val
  rw [← written, read_write_payment trace coeff]

private abbrev paidSpan (trace : Trace environment before after) : Submodule ℤ Word :=
  Submodule.span ℤ {word | word ∈ words trace}

private theorem boundary_span (trace : Trace environment before after) :
    Finsupp.single before 1 - Finsupp.single after 1 ∈ paidSpan trace := by
  rw [← trace.relation_boundary (R := ℤ), ← write_full_payment, paidSpan, ← write_payment_range]
  exact ⟨fullPayment trace, rfl⟩

private theorem edge_support_pays (trace : Trace environment before after) (word : Word)
    (belongs : word ∈ words trace) (atom : Expr Value Var sort) (supported : atom ∈ word.support) :
    Finsupp.single atom 1 - Finsupp.single after 1 ∈ paidSpan trace := by
  obtain ⟨index, written⟩ := List.mem_iff_get.mp belongs
  let cut := paidCut trace index
  let edge : Word := Finsupp.single cut.entry 1 - Finsupp.single cut.exit 1
  have exactEdge : word = edge :=
    written.symm.trans ((stepOccurrence_word trace index).symm.trans (paidCut_word trace index))
  have split : words cut.past ++ edge :: words cut.future = words trace := by
    have whole := congrArg (fun actual : Trace environment before after => words actual) cut.trace_eq
    rw [words_append, words] at whole
    exact whole
  have entry : Finsupp.single cut.entry 1 - Finsupp.single after 1 ∈ paidSpan trace := by
    refine Submodule.span_mono (fun w member => ?_) (boundary_span (.cons cut.step cut.future))
    rw [← split]
    exact List.mem_append_right _ member
  have exit : Finsupp.single cut.exit 1 - Finsupp.single after 1 ∈ paidSpan trace := by
    refine Submodule.span_mono (fun w member => ?_) (boundary_span cut.future)
    rw [← split]
    exact List.mem_append_right _ (List.mem_cons_of_mem edge member)
  by_cases atEntry : atom = cut.entry
  · exact atEntry.symm ▸ entry
  by_cases atExit : atom = cut.exit
  · exact atExit.symm ▸ exit
  have nonzero := Finsupp.mem_support_iff.mp supported
  exfalso
  apply nonzero
  simp only [exactEdge, edge, Finsupp.sub_apply, Finsupp.single_eq_of_ne atEntry,
    Finsupp.single_eq_of_ne atExit, sub_self]

private theorem seed_support_pays (trace : Trace environment before after)
    (event : PresentedRelationEventAt (Expr Value Var sort)) (present : event ∈ (exposure trace).trace)
    (atom : Expr Value Var sort) (supported : atom ∈ event.support) :
    Finsupp.single atom 1 - Finsupp.single after 1 ∈ paidSpan trace := by
  classical
  change event ∈ PresentedRelationEventAt.generator before ::
    RootedAccountedUnfolding.traceBranches (events trace) at present
  rw [events_trace] at present
  rcases List.mem_cons.mp present with rfl | tail
  · have same : atom = before := Finset.mem_singleton.mp supported
    exact same.symm ▸ boundary_span trace
  · obtain ⟨word, belongs, rfl⟩ := List.mem_map.mp tail
    exact edge_support_pays trace word belongs atom supported

def coefficientSum : Word →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ fun _ => 1

private def removeTerminal (terminal : Expr Value Var sort) : Word →ₗ[ℤ] Word :=
  LinearMap.id - (Finsupp.lsingle terminal).comp coefficientSum

/-- Every generator of this fixed paid history reduces to the original terminal syntax. -/
theorem word_sub_terminal_in_relation (root : RootedAccountedUnfolding Root)
    (trace : Trace environment before after) (word : (Hₚ(root, trace)).generatorClosure) :
    word.val - Finsupp.single after (coefficientSum word.val) ∈ (Hₚ(root, trace)).relationClosure := by
  classical
  have reduces : (Hₚ(root, trace)).generatorClosure ≤
      (Hₚ(root, trace)).relationClosure.comap (removeTerminal after) := by
    apply iSup_le
    intro stage
    rw [RootGeneratedCofinalHistoryAt.generatorStage, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨atom, belongs, rfl⟩
    change atom ∈ (Hₚ(root, trace)).generatorSupport stage at belongs
    rw [RootGeneratedCofinalHistoryAt.generatorSupport, List.mem_toFinset, List.mem_flatMap] at belongs
    obtain ⟨event, present, supported⟩ := belongs
    have source := events_seed root (exposure trace) stage event present
    have unit : coefficientSum (Finsupp.single atom 1 : Word) = 1 := by
      simp only [coefficientSum, Finsupp.linearCombination_single, one_smul]
    change Finsupp.single atom 1 - Finsupp.single after (coefficientSum (Finsupp.single atom 1)) ∈
      (Hₚ(root, trace)).relationClosure
    rw [unit, payment_relation_closure, write_payment_range]
    exact seed_support_pays trace event source atom (Finset.mem_toList.mp supported)
  exact reduces word.property

def terminalGenerator (root : RootedAccountedUnfolding Root) (trace : Trace environment before after) :
    (Hₚ(root, trace)).generatorClosure := by
  classical
  have initial : (Finsupp.single before 1 : Word) ∈ (Hₚ(root, trace)).generatorClosure := by
    apply (Hₚ(root, trace)).generatorStage_le_closure 0
    apply Finsupp.single_mem_supported
    change before ∈ (Hₚ(root, trace)).generatorSupport 0
    rw [RootGeneratedCofinalHistoryAt.generatorSupport, List.mem_toFinset, List.mem_flatMap]
    refine ⟨PresentedRelationEventAt.generator before, ?_, Finset.mem_toList.mpr (Finset.mem_singleton_self _)⟩
    simp only [RootGeneratedCofinalHistoryAt.observedEvents, List.range_succ, List.range_zero,
      List.nil_append, List.flatMap_singleton, RootGeneratedCofinalHistoryAt.observation_zero,
      RootGeneratedCofinalHistoryAt.seed]
    exact List.mem_cons_self
  have paid : Finsupp.single before 1 - Finsupp.single after 1 ∈ (Hₚ(root, trace)).relationClosure := by
    rw [payment_relation_closure, write_payment_range]
    exact boundary_span trace
  refine ⟨Finsupp.single after 1, ?_⟩
  simpa only [sub_sub_cancel] using
    Submodule.sub_mem (Hₚ(root, trace)).generatorClosure initial
      ((Hₚ(root, trace)).relationClosure_le_generatorClosure paid)

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
