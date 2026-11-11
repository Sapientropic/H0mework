import H0mework.Realization.Operations.Execution.Run
import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Realization.Operations.Execution.Relations.History.Monotone

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed
open SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
abbrev Event := PresentedRelationEventAt (Expr V X s)
abbrev Inventory := RootedAccountedUnfolding (Event (V := V) (X := X) (s := s))

/-- Source order and repeated occurrences survive; coefficients are not evaluated away. -/
structure Request where
  position : Nat
  sourceEvent : Event (V := V) (X := X) (s := s)
  expression : Expr V X s
  coefficient : ℤ

def eventItems : Event (V := V) (X := X) (s := s) → List (Expr V X s × ℤ)
  | .generator expression => [(expression, 1)]
  | .relation word => Coefficients.sourceItems word

def requestsFrom : Nat → List (Event (V := V) (X := X) (s := s)) →
    List (Request (V := V) (X := X) (s := s))
  | _, [] => []
  | position, event :: rest =>
      ((eventItems event).map fun item => ⟨position, event, item.1, item.2⟩) ++
        requestsFrom (position + 1) rest

def requests (source : Inventory (V := V) (X := X) (s := s)) := requestsFrom 0 source.trace

theorem request_origin_from (position : Nat)
    (events : List (Event (V := V) (X := X) (s := s)))
    (request : Request (V := V) (X := X) (s := s))
    (present : request ∈ requestsFrom position events) :
    ∃ before after, events = before ++ request.sourceEvent :: after ∧
      request.position = position + before.length ∧
      (request.expression, request.coefficient) ∈ eventItems request.sourceEvent := by
  induction events generalizing position with
  | nil => cases present
  | cons event rest previous =>
      rcases List.mem_append.mp present with head | tail
      · obtain ⟨item, belongs, equal⟩ := List.mem_map.mp head
        cases equal
        exact ⟨[], rest, rfl, (Nat.add_zero position).symm, belongs⟩
      · obtain ⟨before, after, equal, index, item⟩ := previous (position + 1) tail
        refine ⟨event :: before, after, congrArg (List.cons event) equal, ?_, item⟩
        simpa only [List.length_cons] using index.trans (by omega)

theorem request_origin (source : Inventory (V := V) (X := X) (s := s))
    (request : Request (V := V) (X := X) (s := s))
    (present : request ∈ requests source) :
    ∃ before after, source.trace = before ++ request.sourceEvent :: after ∧
      request.position = before.length ∧
      (request.expression, request.coefficient) ∈ eventItems request.sourceEvent := by
  simpa only [Nat.zero_add] using request_origin_from 0 source.trace request present

private theorem item_request (events : List (Event (V := V) (X := X) (s := s)))
    (position : Nat) (event : Event (V := V) (X := X) (s := s))
    (item : Expr V X s × ℤ) (present : event ∈ events) (belongs : item ∈ eventItems event) :
    ∃ request ∈ requestsFrom position events,
      request.expression = item.1 ∧ request.coefficient = item.2 := by
  induction events generalizing position with
  | nil => cases present
  | cons head tail previous =>
      rcases List.mem_cons.mp present with equal | rest
      · subst head
        exact ⟨⟨position, event, item.1, item.2⟩,
          List.mem_append_left _ (List.mem_map.mpr ⟨item, belongs, rfl⟩), rfl, rfl⟩
      · obtain ⟨request, member, same, coefficient⟩ := previous (position + 1) rest
        exact ⟨request, List.mem_append_right _ member, same, coefficient⟩

theorem relation_support_request (source : Inventory (V := V) (X := X) (s := s))
    (word : Formal ℤ V X s) (present : PresentedRelationEventAt.relation word ∈ source.trace)
    (expression : Expr V X s) (supported : expression ∈ word.support) :
    ∃ request ∈ requests source,
      request.expression = expression ∧ request.coefficient = word expression := by
  apply item_request source.trace 0 (.relation word) (expression, word expression) present
  exact List.mem_map.mpr ⟨expression, Finset.mem_toList.mpr supported, rfl⟩

def receipt (environment : Env V X) (request : Request (V := V) (X := X) (s := s)) :
    Trace environment request.expression (.const (request.expression.eval environment)) :=
  execution environment request.expression

def sourceCost (source : Inventory (V := V) (X := X) (s := s)) : Nat :=
  ((requests source).map fun request => remaining request.expression).sum

def traceCost (environment : Env V X) (source : Inventory (V := V) (X := X) (s := s)) : Nat :=
  ((requests source).map fun request => (receipt environment request).length).sum

theorem receipt_cost (environment : Env V X) (request : Request (V := V) (X := X) (s := s)) :
    (receipt environment request).length = remaining request.expression := execution_length _ _

/-- This counts generated primitive computation. It is not a Nat debt-payment theorem. -/
theorem complete_source_cost (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s)) :
    traceCost environment source = sourceCost source := by
  simp only [traceCost, sourceCost, receipt_cost]

def executionBranches (environment : Env V X) :
    List (Request (V := V) (X := X) (s := s)) → AccountedBranches (Event (V := V) (X := X) (s := s))
  | [] => .nil
  | request :: rest => .cons (SourceOperationPaidRelations.exposure (receipt environment request))
      (executionBranches environment rest)

private theorem traceBranches_append {A : Type u} (left right : AccountedBranches A) :
    RootedAccountedUnfolding.traceBranches (left.append right) =
      RootedAccountedUnfolding.traceBranches left ++ RootedAccountedUnfolding.traceBranches right := by
  cases left with
  | nil => rfl
  | cons head tail =>
      change head.trace ++ RootedAccountedUnfolding.traceBranches (tail.append right) =
        (head.trace ++ RootedAccountedUnfolding.traceBranches tail) ++ RootedAccountedUnfolding.traceBranches right
      rw [traceBranches_append tail right, List.append_assoc]

/-- Append source-generated execution children to the original occurrence constructor. -/
def written (environment : Env V X) (source : Inventory (V := V) (X := X) (s := s)) :
    Inventory (V := V) (X := X) (s := s) :=
  match source with
  | .occur origin branches => .occur origin (branches.append (executionBranches environment (requests source)))

theorem written_root (environment : Env V X) (source : Inventory (V := V) (X := X) (s := s)) :
    (written environment source).root = source.root := by cases source; rfl

theorem written_trace (environment : Env V X) (source : Inventory (V := V) (X := X) (s := s)) :
    (written environment source).trace = source.trace ++
      RootedAccountedUnfolding.traceBranches (executionBranches environment (requests source)) := by
  cases source with
  | occur origin branches =>
      change origin :: RootedAccountedUnfolding.traceBranches
        (branches.append (executionBranches environment (requests (.occur origin branches)))) = _
      rw [traceBranches_append]
      rfl

theorem original_preserved (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s)) :
    ∀ event ∈ source.trace, event ∈ (written environment source).trace := by
  intro event present
  rw [written_trace]
  exact List.mem_append_left _ present

private theorem request_exposure (environment : Env V X)
    (items : List (Request (V := V) (X := X) (s := s)))
    (request : Request (V := V) (X := X) (s := s)) (present : request ∈ items) :
    ∀ event ∈ (SourceOperationPaidRelations.exposure (receipt environment request)).trace,
      event ∈ RootedAccountedUnfolding.traceBranches (executionBranches environment items) := by
  induction items with
  | nil => cases present
  | cons head tail previous =>
      intro event member
      rcases List.mem_cons.mp present with equal | rest
      · subst head
        exact List.mem_append_left _ member
      · exact List.mem_append_right _ (previous rest event member)

theorem execution_exposure_written (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s))
    (request : Request (V := V) (X := X) (s := s)) (present : request ∈ requests source) :
    ∀ event ∈ (SourceOperationPaidRelations.exposure (receipt environment request)).trace,
      event ∈ (written environment source).trace := by
  intro event member
  rw [written_trace]
  exact List.mem_append_right _ (request_exposure environment _ request present event member)

def relationSpace (source : Inventory (V := V) (X := X) (s := s)) : Submodule ℤ (Formal ℤ V X s) :=
  Submodule.span ℤ {word | PresentedRelationEventAt.relation word ∈ source.trace}

private theorem word_exposure {environment : Env V X} {before after : Expr V X s}
    (trace : Trace environment before after) (word : Formal ℤ V X s)
    (present : word ∈ SourceOperationPaidRelations.words trace) :
    PresentedRelationEventAt.relation word ∈ (SourceOperationPaidRelations.exposure trace).trace := by
  apply List.mem_cons_of_mem
  change PresentedRelationEventAt.relation word ∈
    RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events trace)
  rw [SourceOperationPaidRelations.events_trace]
  exact List.mem_map_of_mem present

private theorem list_sum_mem (space : Submodule ℤ (Formal ℤ V X s)) (words : List (Formal ℤ V X s))
    (all : ∀ word ∈ words, word ∈ space) : words.sum ∈ space := by
  induction words with
  | nil => exact space.zero_mem
  | cons head tail previous =>
      exact space.add_mem (all head List.mem_cons_self)
        (previous fun word member => all word (List.mem_cons_of_mem head member))

theorem request_boundary_written (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s))
    (request : Request (V := V) (X := X) (s := s)) (present : request ∈ requests source) :
    Finsupp.single request.expression 1 - Finsupp.single (.const (request.expression.eval environment)) 1 ∈
      relationSpace (written environment source) := by
  rw [← (receipt environment request).relation_boundary (R := ℤ),
    ← SourceOperationPaidRelations.paid_boundary]
  apply list_sum_mem
  intro word member
  exact Submodule.subset_span (execution_exposure_written environment source request present _
    (word_exposure _ word member))

def affine (environment : Env V X) : Formal ℤ V X s →ₗ[ℤ] Formal ℤ V X s :=
  LinearMap.id - (constantMap (R := ℤ)).comp (valueMap (R := ℤ) environment)

theorem affine_source_sum (environment : Env V X) :
    affine (s := s) environment = Finsupp.linearCombination ℤ
      (fun expression : Expr V X s => Finsupp.single expression 1 -
        Finsupp.single (.const (expression.eval environment)) 1) := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp [affine, constantMap, valueMap, Finsupp.lmapDomain_apply, smul_sub]

theorem relation_affine_written (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s))
    (word : Formal ℤ V X s) (present : PresentedRelationEventAt.relation word ∈ source.trace) :
    affine environment word ∈ relationSpace (written environment source) := by
  rw [affine_source_sum, Finsupp.linearCombination_apply]
  apply Submodule.finsuppSum_mem
  intro expression nonzero
  obtain ⟨request, member, same, _coefficient⟩ := relation_support_request source word present expression
    (Finsupp.mem_support_iff.mpr nonzero)
  exact Submodule.smul_mem _ _ (same ▸ request_boundary_written environment source request member)

theorem relation_span_affine_written (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s))
    (word : Formal ℤ V X s) (present : word ∈ relationSpace source) :
    affine environment word ∈ relationSpace (written environment source) := by
  apply Submodule.span_induction (p := fun word _ => affine environment word ∈ relationSpace (written environment source))
      (fun word member => relation_affine_written environment source word member)
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun _ _ _ _ first second => by rw [map_add]; exact Submodule.add_mem _ first second)
      (fun scalar _ _ member => by rw [map_smul]; exact Submodule.smul_mem _ scalar member) present

theorem history_relation_space {Root : Type u} (root : RootedAccountedUnfolding Root)
    (source : Inventory (V := V) (X := X) (s := s)) :
    (SourceOperationPaidRelations.prefixHistory root source).relationClosure = relationSpace source := by
  apply le_antisymm
  · apply iSup_le
    intro stage
    apply Submodule.span_le.mpr
    intro word present
    apply Submodule.subset_span
    exact SourceOperationPaidRelations.events_seed root source stage _ present
  · apply Submodule.span_le.mpr
    intro word present
    apply (SourceOperationPaidRelations.prefixHistory root source).relationStage_le_closure 0
    apply Submodule.subset_span
    change PresentedRelationEventAt.relation word ∈
      (SourceOperationPaidRelations.prefixHistory root source).observedEvents 0
    simp only [RootGeneratedCofinalHistoryAt.observedEvents, List.range_succ, List.range_zero,
      List.nil_append, List.flatMap_singleton, RootGeneratedCofinalHistoryAt.observation_zero]
    exact present

end SourceInventoryExecutionFeed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
