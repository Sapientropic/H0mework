import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Work
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Signature
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Action
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {input : Input seed} (prepared : Prepared input)

/-- Signature acquisition retains its exact public request and answer. -/
inductive Query where
  | signature (term : Section prepared) (first second : Index prepared)
def Query.Holds : Query prepared → Prop
  | .signature term first second => shape prepared.saved[first].stage (readTerm prepared term first) =
      shape prepared.saved[second].stage (readTerm prepared term second)
instance (query : Query prepared) : Decidable (query.Holds prepared) := by
  cases query; unfold Query.Holds; infer_instance

abbrev SignatureKey := ActionWork.Atom Party Good Port (Mandate.State Party Technology) Instrument

inductive Operation where
  | native (index : Index prepared)
      (scope : Scope (initial input prepared.saved[index].point) input.pricing input.future
        (reference input prepared.saved[index].point) input.actor input.position)
      (event : Whole.Work.Operation scope)
  | query (query : Query prepared) (answer : Bool)
  | signatureStep (query : Query prepared) (event : NativeBenefit.Event (SignatureKey (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
  | presence (answer : Bool)
  | stopped (index : Index prepared)
  | branch (answer : Bool)
  | negate (answer : Bool)
  | retain (accepted : Bool)
  | select (replaced : Bool)

structure Check (P : Prop) where
  private mk ::
  decision : Decidable P
  work : List (Operation prepared)
def Check.value {P : Prop} (made : Check prepared P) : Bool := @decide P made.decision

variable {prepared}
def transport {P Q : Prop} (equivalent : P ↔ Q) (made : Check prepared P) : Check prepared Q :=
  ⟨match made.decision with
    | .isTrue yes => .isTrue (equivalent.mp yes)
    | .isFalse no => .isFalse (fun yes => no (equivalent.mpr yes)),made.work⟩

def conjunction {P Q : Prop} (first : Check prepared P) (later : Unit → Check prepared Q) : Check prepared (P ∧ Q) :=
  match first.decision with
  | .isFalse no => ⟨.isFalse (fun yes => no yes.1),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun both => no both.2)
      | .isTrue other => .isTrue ⟨yes,other⟩,first.work ++ [.branch true] ++ second.work⟩

def negative {P : Prop} (made : Check prepared P) : Check prepared (¬ P) :=
  ⟨match made.decision with
    | .isTrue yes => .isFalse (fun no => no yes)
    | .isFalse no => .isTrue no,made.work ++ [.negate made.value]⟩

def implication {P Q : Prop} (first : Check prepared P) (later : Unit → Check prepared Q) : Check prepared (P → Q) :=
  match first.decision with
  | .isFalse no => ⟨.isTrue (fun yes => False.elim (no yes)),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun accepts => no (accepts yes))
      | .isTrue other => .isTrue (fun _ => other),first.work ++ [.branch true] ++ second.work⟩

def allRows {α : Type} (P : α → Prop) (test : (a : α) → Check prepared (P a)) :
    (items : List α) → Check prepared (∀ a ∈ items,P a)
  | [] => ⟨.isTrue (by simp),[]⟩
  | head::tail => transport (by simp only [List.mem_cons,forall_eq_or_imp])
      (conjunction (test head) (fun _ => allRows P test tail))


variable (prepared)
def localAdmission (index : Index prepared) :
    (stage : Stage input prepared.saved[index].point) → (previous new : Local stage) →
      (row : LocalRow stage) → Check prepared (localHolds stage previous new row)
  | .stopped _,_,_,_ | .blocked _,_,_,_ => ⟨.isFalse (fun h => h),[.stopped index]⟩
  | .ready scope,previous,new,row =>
    let checked := Whole.Work.atom scope input.span (.admission previous new row)
    ⟨checked.decision,checked.work.map (Operation.native index scope)⟩

def localImprovement (index : Index prepared) :
    (stage : Stage input prepared.saved[index].point) → (new previous : Local stage) →
      Check prepared (localBenefit stage new previous)
  | .stopped _,_,_ | .blocked _,_,_ => ⟨.isTrue trivial,[.stopped index]⟩
  | .ready scope,new,previous =>
    let checked := Whole.Work.realBenefit scope input.span new previous
    ⟨checked.decision,checked.work.map (Operation.native index scope)⟩

private theorem paid_header_exact {point : NativePoint input}
    (scope : Scope (initial input point) input.pricing input.future (reference input point) input.actor input.position) :
    scope.paidWord = Prepaid.invoice (initial input point) input.pricing input.future scope.fee := by
  rw [scope.paidWord_exact]
  have listed := Prepaid.a_registered_owner_fee_has_a_source_probe (initial input point) input.actor input.position scope.fee scope.registered
  have valid := of_decide_eq_true (List.mem_filter.mp listed).2
  have physical : ∀ operator target,scope.fee.operation ≠ .revise operator target := by
    intro operator target same
    have kind := valid.2.2.2
    simp only [same] at kind
  have retained := Mandate.Replay.physical_request_is_retained (initial input point).model.scope
    (initial input point).state.current (Prepaid.scaled (initial input point) scope.fee (Prepaid.units (initial input point) input.pricing input.future)) (by
      intro operator target
      unfold Prepaid.scaled
      split
      · intro impossible;cases impossible
      · exact physical operator target)
  change (Mandate.Replay.compile _ _ _ [_]).output = [_]
  simp only [Mandate.Replay.compile,retained]
  split <;> simp only [Mandate.Replay.Path.output,retained]

private def cachedControl {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    (term : List (Option code.Policy)) :=
  term.map (Option.map (fun policy => code.keys.attach.map (fun key => policy key.val key.property)))

/-- The actual fee word has already been generated; signature checking must not rerun its quote. -/
private def unprefixedCachedShape {point : NativePoint input} : (stage : Stage input point) → Local stage → Shape (seed := seed)
  | .stopped header,term => shape (.stopped header) term
  | .blocked failure,_ => Signature.stopped (some failure.retained.paidWord)
  | .ready scope,.keep => .keep scope.paidWord
  | .ready scope,.paid (.control term) => .direct scope.paidWord (cachedControl term.val)
  | .ready scope,.paid (.own own term) => .own scope.paidWord own.val.requested (cachedControl term.val)
  | .ready scope,.paid (.invoiced invoice term) =>
    .invoiced scope.paidWord invoice.val.own.requested
      (invoice.val.quoted.map (fun bill => [Prepaid.scaled _ bill.val.fee bill.val.units])) (cachedControl term.val)

def cachedShape {point : NativePoint input} : (stage : Stage input point) → Local stage → Shape (seed := seed)
  | .ready scope,term => attachPrefix scope.continuation.words (unprefixedCachedShape (.ready scope) term)
  | .stopped header,term => unprefixedCachedShape (.stopped header) term
  | .blocked failure,term => attachPrefix failure.retained.continuation.words (unprefixedCachedShape (.blocked failure) term)

theorem cached_signature_is_the_original_public_request {point : NativePoint input}
    (stage : Stage input point) (term : Local stage) : cachedShape stage term = shape stage term := by
  cases stage with
  | stopped _ => rfl
  | blocked _ => rfl
  | ready scope =>
    apply congrArg (attachPrefix scope.continuation.words)
    cases term with
    | keep => exact congrArg Signature.keep (paid_header_exact scope)
    | paid plan =>
      cases plan <;> simp only [unprefixedCachedShape,cachedControl,paid_header_exact] <;> rfl

def signature (term : Section prepared) (first second : Index prepared) :
    Check prepared ((Query.signature term first second).Holds prepared) :=
  let left := cachedShape prepared.saved[first].stage (readTerm prepared term first)
  let right := cachedShape prepared.saved[second].stage (readTerm prepared term second)
  let checked := SignatureWork.Generic.compare ActionWork.compare left right
  let equivalent : (left = right) ↔ (Query.signature term first second).Holds prepared := by
    dsimp only [left,right,Query.Holds]
    rw [cached_signature_is_the_original_public_request,cached_signature_is_the_original_public_request]
  transport equivalent ⟨checked.decision,.query (.signature term first second) checked.value ::
    checked.work.map (Operation.signatureStep (.signature term first second))⟩

def atom (reference term : Section prepared) : (row : Row prepared) → Check prepared (Holds prepared reference term row)
  | .informed => ⟨inferInstance,[.presence (decide (prepared.saved ≠ []))]⟩
  | .coherence first second => signature prepared term first second
  | .native index row => localAdmission prepared index prepared.saved[index].stage
      (readTerm prepared reference index) (readTerm prepared term index) row

def noWorse (new previous : Section prepared) : Check prepared (NoWorse prepared new previous) :=
  transport (rows_iff prepared previous new)
    (allRows (Holds prepared previous new) (atom prepared previous new) (rows prepared))

def realBenefit (new previous : Section prepared) : Check prepared (Benefit prepared new previous) :=
  transport (show (∀ index ∈ keys prepared, localBenefit prepared.saved[index].stage
      (readTerm prepared new index) (readTerm prepared previous index)) ↔ Benefit prepared new previous from by
                constructor
                · intro h index;exact h index (List.mem_finRange index)
                · intro h index _;exact h index)
    (allRows (fun index => localBenefit prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index))
      (fun index => localImprovement prepared index prepared.saved[index].stage
        (readTerm prepared new index) (readTerm prepared previous index)) (keys prepared))

def Strict (previous new : Section prepared) : Prop := Benefit prepared new previous ∧ ¬ Benefit prepared previous new
private theorem strict_iff (previous new : Section prepared) : Strict prepared previous new ↔
    Improves (axes prepared) (cost prepared) previous new := by
  constructor
  · intro h;exact ⟨(vector_iff prepared _ _).mpr h.1,fun reverse => h.2 ((vector_iff prepared _ _).mp reverse)⟩
  · intro h;exact ⟨(vector_iff prepared _ _).mp h.1,fun reverse => h.2 ((vector_iff prepared _ _).mpr reverse)⟩

def strict (previous new : Section prepared) : Check prepared (Strict prepared previous new) :=
  conjunction (realBenefit prepared new previous) (fun _ => negative (realBenefit prepared previous new))
structure Pool (reference : Section prepared) (items : List (Section prepared)) where
  private mk ::
  accepted : List (Candidate prepared reference)
  exact : accepted = items.filterMap (Policy.check prepared reference)
  work : List (Operation prepared)

def collect (reference : Section prepared) : (items : List (Section prepared)) → Pool prepared reference items
  | [] => ⟨[],rfl,[]⟩
  | head::tail =>
    let checked := noWorse prepared head reference
    let rest := collect reference tail
    match checked.decision with
    | .isTrue accepted =>
      ⟨⟨head,accepted⟩::rest.accepted,by simp only [List.filterMap_cons,Policy.check,dif_pos accepted];rw [rest.exact],
        checked.work ++ [.retain true] ++ rest.work⟩
    | .isFalse rejected =>
      ⟨rest.accepted,by simp only [List.filterMap_cons,Policy.check,dif_neg rejected];exact rest.exact,
        checked.work ++ [.retain false] ++ rest.work⟩

private theorem strict_irrefl (term : Section prepared) : ¬ Strict prepared term term := fun both => both.2 both.1
private theorem strict_trans {first middle last : Section prepared}
    (a : Strict prepared first middle) (b : Strict prepared middle last) :
    Strict prepared first last :=
  ⟨fun index => localBenefit_trans _ (b.1 index) (a.1 index),
    fun reverse => a.2 (fun index => localBenefit_trans _ (reverse index) (b.1 index))⟩

private structure Scan {reference : Section prepared} (first : Candidate prepared reference)
    (remaining : List (Candidate prepared reference)) where
  policy : Candidate prepared reference
  original : policy = first ∨ policy ∈ remaining
  advances : policy = first ∨ Strict prepared first.term policy.term
  maximal : ∀ other ∈ remaining, ¬ Strict prepared policy.term other.term
  work : List (Operation prepared)

variable {prepared}
private theorem no_reverse {reference : Section prepared} {first : Candidate prepared reference}
    {remaining : List (Candidate prepared reference)} (made : Scan prepared first remaining) :
    ¬ Strict prepared made.policy.term first.term := by
  intro backwards
  rcases made.advances with same | forward
  · apply strict_irrefl prepared first.term
    simpa only [same] using backwards
  · exact strict_irrefl prepared first.term (strict_trans prepared forward backwards)

private def scan {reference : Section prepared} (first : Candidate prepared reference) :
    (remaining : List (Candidate prepared reference)) → Scan prepared first remaining
  | [] => ⟨first,.inl rfl,.inl rfl,by simp,[]⟩
  | head::tail =>
    let checked := strict prepared first.term head.term
    match checked.decision with
    | .isTrue better =>
      let rest := scan head tail
      ⟨rest.policy,.inr (by
          rcases rest.original with same | inside
          · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
          · exact List.mem_cons_of_mem _ inside),
        .inr (by
          rcases rest.advances with same | further
          · simpa only [same] using better
          · exact strict_trans prepared better further),by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other;exact no_reverse rest
          · exact rest.maximal other later,checked.work ++ [.select true] ++ rest.work⟩
    | .isFalse notBetter =>
      let rest := scan first tail
      ⟨rest.policy,rest.original.imp_right (List.mem_cons_of_mem _),rest.advances,by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other
            intro backwards
            rcases rest.advances with same | forward
            · apply notBetter
              simpa only [same] using backwards
            · exact notBetter (strict_trans prepared forward backwards)
          · exact rest.maximal other later,checked.work ++ [.select false] ++ rest.work⟩

variable (prepared)
structure Rejected (reference term : Section prepared) where
  private mk ::
  result : Rejection prepared reference term
  work : List (Operation prepared)

private def reject (reference term : Section prepared) :
    (items : List (Row prepared)) → (inside : ∀ row ∈ items,row ∈ rows prepared) →
    (invalid : ¬ ∀ row ∈ items,Holds prepared reference term row) → Rejected prepared reference term
  | [],_,invalid => False.elim (invalid (by simp))
  | head::tail,inside,invalid =>
    let checked := atom prepared reference term head
    match checked.decision with
    | .isFalse broken => ⟨⟨head,inside head List.mem_cons_self,broken⟩,checked.work ++ [.branch false]⟩
    | .isTrue holds =>
      let later := reject reference term tail (fun row member => inside row (List.mem_cons_of_mem _ member))
        (fun all => invalid (by
          intro row member
          rcases List.mem_cons.mp member with same | rest
          · subst row;exact holds
          · exact all row rest))
      ⟨later.result,checked.work ++ [.branch true] ++ later.work⟩

inductive Result (reference : Section prepared) where
  | selected (choice : Choice prepared reference)
  | blocked (rejected : (term : Section prepared) → Rejected prepared reference term)

structure Compilation (reference : Section prepared) where
  private mk ::
  result : Result prepared reference
  work : List (Operation prepared)

def compileOrdered (reference : Section prepared) (order : List (Section prepared))
    (complete : order.Perm (sections prepared)) : Compilation prepared reference :=
  let pool := collect prepared reference order
  have members : pool.accepted.Perm (candidates prepared reference) := by
    rw [pool.exact]
    exact complete.filterMap _
  match same : pool.accepted with
  | [] => ⟨.blocked (fun term => reject prepared reference term (rows prepared) (fun _ member => member)
      (fun all => by
        obtain ⟨candidate,member,_⟩ := every_accepted_section_is_generated prepared reference term
          ((rows_iff prepared reference term).mp all)
        have inside := members.mem_iff.mpr member
        rw [same] at inside
        exact List.not_mem_nil inside)),pool.work⟩
  | head::tail =>
    let found := scan head tail
    ⟨.selected ⟨found.policy,by
      apply members.mem_iff.mp
      rw [same]
      rcases found.original with same | inside
      · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
      · exact List.mem_cons_of_mem _ inside,by
      intro other member improves
      have strict := (strict_iff prepared _ _).mpr improves
      have inside := members.mem_iff.mpr member
      rw [same] at inside
      rcases List.mem_cons.mp inside with same | later
      · subst other;exact no_reverse found strict
      · exact found.maximal other later strict⟩,pool.work ++ found.work⟩


def compile (reference : Section prepared) : Compilation prepared reference :=
  compileOrdered prepared reference (sections prepared) (List.Perm.refl _)

/-- Independent replay uses the same source-native primitives, with its own work. -/
def verify (reference term : Section prepared) : Check prepared
    (NoWorse prepared term reference ∧ ∀ other ∈ sections prepared,
      NoWorse prepared other reference → ¬ Improves (axes prepared) (cost prepared) term other) :=
  conjunction (noWorse prepared term reference) (fun _ =>
    allRows (fun other => NoWorse prepared other reference → ¬ Improves (axes prepared) (cost prepared) term other)
      (fun other => implication (noWorse prepared other reference)
        (fun _ => negative (transport (strict_iff prepared term other) (strict prepared term other)))) (sections prepared))

theorem verify_matches_the_original_independent_verifier (reference term : Section prepared) :
    (verify prepared reference term).value = Policy.verify prepared reference term := by
  unfold Check.value Policy.verify
  exact Subsingleton.elim _ _ |> fun same => congrArg (fun d => @decide _ d) same

def Outcome.checked (reference : Section prepared) : Outcome prepared reference → Bool
  | .selected choice => Policy.verify prepared reference choice.policy.term
  | .blocked _ => false

def Result.outcome {reference : Section prepared} : Result prepared reference → Outcome prepared reference
  | .selected choice => .selected choice
  | .blocked rejected => .blocked (fun term => (rejected term).result)

def Reviewed {reference : Section prepared} : Result prepared reference → Prop
  | .selected choice => NoWorse prepared choice.policy.term reference ∧ ∀ other ∈ sections prepared,
      NoWorse prepared other reference → ¬ Improves (axes prepared) (cost prepared) choice.policy.term other
  | .blocked _ => ∀ term, ¬ NoWorse prepared term reference

def inspect {reference : Section prepared} (made : Compilation prepared reference) :
    Check prepared (Reviewed prepared made.result) := match made.result with
  | .selected choice => verify prepared reference choice.policy.term
  | .blocked rejected => ⟨.isTrue (by
      intro term accepted
      exact (rejected term).result.broken
        ((rows_iff prepared reference term).mpr accepted _ (rejected term).result.original)),
      (sections prepared).flatMap (fun term => (rejected term).work)⟩

structure Receipt {reference : Section prepared} (made : Compilation prepared reference) where
  private mk ::
  review : Check prepared (Reviewed prepared made.result)
  generated : review = inspect prepared made

def certify {reference : Section prepared} (made : Compilation prepared reference) : Receipt prepared made :=
  ⟨inspect prepared made,rfl⟩

namespace Receipt
variable {prepared} {reference : Section prepared} {made : Compilation prepared reference} (receipt : Receipt prepared made)
def work : List (Operation prepared) := made.work ++ receipt.review.work ++ [.branch receipt.review.value]
def authorized : Bool := match made.result with
  | .selected _ => receipt.review.value
  | .blocked _ => false

theorem review_accepts_its_generated_result : receipt.review.value = true := by
  rw [receipt.generated]
  rcases made with ⟨result,work⟩
  cases result with
  | selected choice =>
    change (verify prepared reference choice.policy.term).value = true
    rw [verify_matches_the_original_independent_verifier]
    exact independent_replay_accepts_the_public_selection _ _ _
  | blocked rejected => rfl

theorem authorized_matches_the_original_independent_verifier :
    receipt.authorized = Outcome.checked prepared reference (made.result.outcome prepared) := by
  rcases made with ⟨result,work⟩
  cases result with
  | selected choice =>
    change receipt.review.value = Policy.verify prepared reference choice.policy.term
    rw [receipt.review_accepts_its_generated_result,independent_replay_accepts_the_public_selection]
  | blocked _ => rfl
end Receipt

/-- Each unexpanded call retains its own source, operands and actual answer. -/
inductive Obligation where
  | signature (query : Query prepared) (answer : Bool)
  | signatureLeaf (query : Query prepared) (event : NativeBenefit.Event (SignatureKey (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
  | native (index : Index prepared)
      (scope : Scope (initial input prepared.saved[index].point) input.pricing input.future
        (reference input prepared.saved[index].point) input.actor input.position)
      (query : Whole.Work.Query scope) (answer : Bool)

def Operation.obligation : Operation prepared → Option (Obligation prepared)
  | .query request answer => some (.signature request answer)
  | .signatureStep request event =>
    if SignatureWork.Event.expanded event then none else some (.signatureLeaf request event)
  | .native index scope (.native request answer) => some (.native index scope request answer)
  | _ => none

def Operation.expanded (event : Operation prepared) : Bool := (event.obligation prepared).isNone

def controlSteps (work : List (Operation prepared)) : Nat := (work.filter (Operation.expanded prepared)).length
def pending (work : List (Operation prepared)) : List (Obligation prepared) := work.filterMap (Operation.obligation prepared)

theorem every_operation_is_an_expanded_step_or_a_retained_obligation (work : List (Operation prepared)) :
    work.length = controlSteps prepared work + (pending prepared work).length := by
  induction work with
  | nil => rfl
  | cons head tail ih =>
    cases h : Operation.obligation prepared head <;> simp_all [controlSteps,pending,Operation.expanded] <;> omega

theorem lifted_control_work_is_preserved (index : Index prepared)
    (scope : Scope (initial input prepared.saved[index].point) input.pricing input.future
      (reference input prepared.saved[index].point) input.actor input.position)
    (work : List (Whole.Work.Operation scope)) :
    controlSteps prepared (work.map (Operation.native index scope)) = Whole.Work.controlSteps scope work := by
  induction work with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp_all [controlSteps,Whole.Work.controlSteps,List.filter_cons,Operation.expanded,Operation.obligation]


theorem controlSteps_append (left right : List (Operation prepared)) :
    controlSteps prepared (left++right) = controlSteps prepared left+controlSteps prepared right := by
  simp only [controlSteps,List.filter_append,List.length_append]

private theorem transported_work_exact {P Q : Prop} (equivalent : P ↔ Q) (made : Check prepared P) :
    (transport equivalent made).work = made.work := rfl
private theorem conjunction_cost {P Q : Prop} (first : Check prepared P) (later : Unit → Check prepared Q) :
    controlSteps prepared (conjunction first later).work ≤
      controlSteps prepared first.work+1+controlSteps prepared (later ()).work := by
  cases h : first.decision with
  | isFalse no => simp [conjunction,h,controlSteps,List.filter_cons,Operation.expanded,Operation.obligation]
  | isTrue yes =>
    simp [conjunction,h,controlSteps,List.filter_cons,Operation.expanded,Operation.obligation]
    omega
private theorem implication_cost {P Q : Prop} (first : Check prepared P) (later : Unit → Check prepared Q) :
    controlSteps prepared (implication first later).work ≤
      controlSteps prepared first.work+1+controlSteps prepared (later ()).work := by
  cases h : first.decision with
  | isFalse no => simp [implication,h,controlSteps,List.filter_cons,Operation.expanded,Operation.obligation]
  | isTrue yes =>
    simp [implication,h,controlSteps,List.filter_cons,Operation.expanded,Operation.obligation]
    omega
private theorem negative_cost {P : Prop} (made : Check prepared P) :
    controlSteps prepared (negative made).work = controlSteps prepared made.work+1 := by
  simp [negative,controlSteps,List.filter_cons,Operation.expanded,Operation.obligation]
private theorem allRows_cost {α : Type} (P : α → Prop) (test : (item : α) → Check prepared (P item))
    (budget : α → Nat) (bounded : ∀ item,controlSteps prepared (test item).work ≤ budget item) (items : List α) :
    controlSteps prepared (allRows P test items).work ≤ (items.map (fun item => budget item+1)).sum := by
  induction items with
  | nil => simp [allRows,controlSteps]
  | cons head tail ih =>
    have step := conjunction_cost prepared (test head) (fun _ => allRows P test tail)
    change controlSteps prepared (conjunction (test head) (fun _ => allRows P test tail)).work ≤ _
    simp only [List.map_cons,List.sum_cons]
    have headBound := bounded head
    exact step.trans (by omega)

private theorem native_row_is_original (index : Index prepared) (row : LocalRow prepared.saved[index].stage)
    (inside : Row.native index row ∈ rows prepared) : row ∈ localRows prepared.saved[index].stage := by
  rcases List.mem_append.mp inside with earlier | native
  · rcases List.mem_append.mp earlier with informed | coherence
    · have same := List.mem_singleton.mp informed
      cases same
    · obtain ⟨first,_,mapped⟩ := List.mem_flatMap.mp coherence
      obtain ⟨second,_,same⟩ := List.mem_map.mp mapped
      cases same
  · obtain ⟨other,_,mapped⟩ := List.mem_flatMap.mp native
    obtain ⟨original,listed,same⟩ := List.mem_map.mp mapped
    cases same
    exact listed

def ceiling {α : Type} (budget : α → Nat) : List α → Nat
  | [] => 0
  | head::tail => max (budget head) (ceiling budget tail)
private theorem below_ceiling {α : Type} (budget : α → Nat) (items : List α) (item : α) (inside : item ∈ items) :
    budget item ≤ ceiling budget items := by
  induction items with
  | nil => simp at inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst item;exact Nat.le_max_left _ _
    · exact (ih later).trans (Nat.le_max_right _ _)

def localAdmissionCeiling {point : NativePoint input} : Stage input point → Nat
  | .ready scope => Whole.Work.admissionCeiling scope input.span
  | .stopped _ | .blocked _ => 1

def localBenefitCeiling {point : NativePoint input} : Stage input point → Nat
  | .ready scope => Whole.Work.benefitCeiling scope input.span
  | .stopped _ | .blocked _ => 1

def signatureBudget (term : Section prepared) (first second : Index prepared) :=
  SignatureWork.Generic.budget ActionWork.budget (cachedShape prepared.saved[first].stage (readTerm prepared term first))
    (cachedShape prepared.saved[second].stage (readTerm prepared term second))

/-- The bound covers every generated section and both observation indices before selection. -/
def signatureCeiling := ceiling (fun term : Section prepared =>
  ceiling (fun first : Index prepared => ceiling (signatureBudget prepared term first) (keys prepared))
    (keys prepared)) (sections prepared)
def nativeAdmissionCeiling := max 1 (ceiling (fun index : Index prepared => localAdmissionCeiling prepared.saved[index].stage) (keys prepared))
def admissionCeiling := max (nativeAdmissionCeiling prepared) (signatureCeiling prepared)
def benefitCeiling := ceiling (fun index : Index prepared => localBenefitCeiling prepared.saved[index].stage) (keys prepared)
def admissionWorkBudget := (rows prepared).length*(admissionCeiling prepared+1)
def benefitWorkBudget := (keys prepared).length*(benefitCeiling prepared+1)
def strictWorkBudget := 2*benefitWorkBudget prepared+2

private theorem local_admission_cost (index : Index prepared) (stage : Stage input prepared.saved[index].point)
    (previous new : Local stage) (row : LocalRow stage) (inside : row ∈ localRows stage) :
    controlSteps prepared (localAdmission prepared index stage previous new row).work ≤ localAdmissionCeiling stage := by
  cases stage with
  | stopped _ => exact Nat.le_refl _
  | blocked _ => exact Nat.le_refl _
  | ready scope =>
    dsimp only [localAdmission,localAdmissionCeiling]
    rw [lifted_control_work_is_preserved]
    exact Whole.Work.admission_atom_uniform_bound scope input.span previous new row inside

theorem signature_cost_bound (term : Section prepared) (first second : Index prepared) :
    controlSteps prepared (signature prepared term first second).work ≤ signatureBudget prepared term first second := by
  change controlSteps prepared (.query (.signature term first second) _ ::
    (SignatureWork.Generic.compare ActionWork.compare _ _).work.map (Operation.signatureStep (.signature term first second))) ≤ _
  change controlSteps prepared ((SignatureWork.Generic.compare ActionWork.compare _ _).work.map
    (Operation.signatureStep (.signature term first second))) ≤ _
  exact (List.length_filter_le _ _).trans (by
    rw [List.length_map]
    exact SignatureWork.Generic.work_bound ActionWork.compare ActionWork.budget ActionWork.work_bound _ _)

private theorem signature_below_ceiling (term : Section prepared) (first second : Index prepared) :
    signatureBudget prepared term first second ≤ signatureCeiling prepared := by
  exact (below_ceiling (signatureBudget prepared term first) (keys prepared) second (List.mem_finRange _)).trans
    ((below_ceiling (fun i : Index prepared => ceiling (signatureBudget prepared term i) (keys prepared))
      (keys prepared) first (List.mem_finRange _)).trans
      (below_ceiling (fun t : Section prepared => ceiling (fun i : Index prepared =>
        ceiling (signatureBudget prepared t i) (keys prepared)) (keys prepared))
        (sections prepared) term (Policy.every_section_is_generated prepared term)))

private theorem atom_cost (reference term : Section prepared) (row : Row prepared) (inside : row ∈ rows prepared) :
    controlSteps prepared (atom prepared reference term row).work ≤ admissionCeiling prepared := by
  cases row with
  | informed => exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
  | coherence first second =>
    exact (signature_cost_bound prepared term first second).trans
      ((signature_below_ceiling prepared term first second).trans (Nat.le_max_right _ _))
  | native index row =>
    exact (local_admission_cost prepared index _ _ _ row (native_row_is_original prepared index row inside)).trans
      ((below_ceiling (fun i : Index prepared => localAdmissionCeiling prepared.saved[i].stage) (keys prepared) index (List.mem_finRange _)).trans ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)))

private theorem local_benefit_cost (index : Index prepared) (stage : Stage input prepared.saved[index].point)
    (new previous : Local stage) :
    controlSteps prepared (localImprovement prepared index stage new previous).work ≤ localBenefitCeiling stage := by
  cases stage with
  | stopped _ => exact Nat.le_refl _
  | blocked _ => exact Nat.le_refl _
  | ready scope =>
    dsimp only [localImprovement,localBenefitCeiling]
    rw [lifted_control_work_is_preserved]
    exact Whole.Work.realBenefit_uniform_bound scope input.span new previous

private theorem allRows_cost_on {α : Type} (P : α → Prop) (test : (item : α) → Check prepared (P item))
    (items : List α) (budget : Nat) (bounded : ∀ item ∈ items,controlSteps prepared (test item).work ≤ budget) :
    controlSteps prepared (allRows P test items).work ≤ items.length*(budget+1) := by
  induction items with
  | nil => simp [allRows,controlSteps]
  | cons head tail ih =>
    have step := conjunction_cost prepared (test head) (fun _ => allRows P test tail)
    have a := bounded head List.mem_cons_self
    have b := ih (fun item inside => bounded item (List.mem_cons_of_mem _ inside))
    change controlSteps prepared (conjunction (test head) (fun _ => allRows P test tail)).work ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem noWorse_cost_bound (new previous : Section prepared) :
    controlSteps prepared (noWorse prepared new previous).work ≤ admissionWorkBudget prepared :=
  allRows_cost_on prepared (Holds prepared previous new) (atom prepared previous new) (rows prepared) _
    (fun row inside => atom_cost prepared previous new row inside)

theorem realBenefit_cost_bound (new previous : Section prepared) :
    controlSteps prepared (realBenefit prepared new previous).work ≤ benefitWorkBudget prepared :=
  allRows_cost_on prepared _ _ (keys prepared) _ (fun index inside =>
    (local_benefit_cost prepared index _ _ _).trans (below_ceiling (fun i : Index prepared => localBenefitCeiling prepared.saved[i].stage) (keys prepared) index inside))

private theorem strict_cost_bound (previous new : Section prepared) :
    controlSteps prepared (strict prepared previous new).work ≤ strictWorkBudget prepared := by
  have a := realBenefit_cost_bound prepared new previous
  have b := realBenefit_cost_bound prepared previous new
  have step := conjunction_cost prepared (realBenefit prepared new previous)
    (fun _ => negative (realBenefit prepared previous new))
  rw [negative_cost prepared] at step
  unfold strict strictWorkBudget
  omega
private theorem collect_cost_bound (reference : Section prepared) (items : List (Section prepared)) :
    controlSteps prepared (collect prepared reference items).work ≤ items.length*(admissionWorkBudget prepared+1) := by
  induction items with
  | nil => simp [collect,controlSteps]
  | cons head tail ih =>
    have headBound := noWorse_cost_bound prepared head reference
    cases h : (noWorse prepared head reference).decision <;>
      simp only [collect,h,controlSteps_append,List.length_cons]
    all_goals simp only [controlSteps,Operation.expanded,Operation.obligation,Option.isNone,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *;omega

private theorem scan_cost_bound {reference : Section prepared} (first : Candidate prepared reference)
    (remaining : List (Candidate prepared reference)) :
    controlSteps prepared (scan first remaining).work ≤ remaining.length*(strictWorkBudget prepared+1) := by
  induction remaining generalizing first with
  | nil => simp [scan,controlSteps]
  | cons head tail ih =>
    have bound := strict_cost_bound prepared first.term head.term
    have a := ih head
    have b := ih first
    cases h : (strict prepared first.term head.term).decision <;>
      simp only [scan,h,controlSteps_append,List.length_cons]
    all_goals simp only [controlSteps,Operation.expanded,Operation.obligation,Option.isNone,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *;omega

private theorem reject_cost_bound (reference term : Section prepared) (items : List (Row prepared))
    (inside : ∀ row ∈ items,row ∈ rows prepared)
    (invalid : ¬ ∀ row ∈ items,Holds prepared reference term row) :
    controlSteps prepared (reject prepared reference term items inside invalid).work ≤
      items.length*(admissionCeiling prepared+1) := by
  induction items with
  | nil => exact False.elim (invalid (by simp))
  | cons head tail ih =>
    have bound := atom_cost prepared reference term head (inside head List.mem_cons_self)
    cases h : (atom prepared reference term head).decision with
    | isFalse broken =>
      simp only [reject,h,controlSteps_append]
      change controlSteps prepared (atom prepared reference term head).work+1 ≤ _
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    | isTrue holds =>
      have later := ih (fun row member => inside row (List.mem_cons_of_mem _ member)) (fun all => invalid (by
        intro row member
        rcases List.mem_cons.mp member with equal | rest
        · subst row;exact holds
        · exact all row rest))
      simp only [reject,h,controlSteps_append]
      simp only [controlSteps,Operation.expanded,Operation.obligation,Option.isNone,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *
      omega

def verificationBudget : Nat := admissionWorkBudget prepared+1+
  (sections prepared).length*(admissionWorkBudget prepared+strictWorkBudget prepared+3)

theorem verification_cost_bound (reference term : Section prepared) :
    controlSteps prepared (verify prepared reference term).work ≤ verificationBudget prepared := by
  have initial := noWorse_cost_bound prepared term reference
  have each (other : Section prepared) :
      controlSteps prepared (implication (noWorse prepared other reference)
        (fun _ => negative (transport (strict_iff prepared term other) (strict prepared term other)))).work ≤
          admissionWorkBudget prepared+strictWorkBudget prepared+2 := by
    have entry := noWorse_cost_bound prepared other reference
    have comparison := strict_cost_bound prepared term other
    have step := implication_cost prepared (noWorse prepared other reference)
      (fun _ => negative (transport (strict_iff prepared term other) (strict prepared term other)))
    rw [negative_cost prepared] at step
    rw [transported_work_exact] at step
    omega
  have all := allRows_cost prepared (fun other => NoWorse prepared other reference → ¬ Improves (axes prepared) (cost prepared) term other)
    (fun other => implication (noWorse prepared other reference) (fun _ => negative (transport (strict_iff prepared term other) (strict prepared term other))))
    (fun _ => admissionWorkBudget prepared+strictWorkBudget prepared+2) each (sections prepared)
  have whole := conjunction_cost prepared (noWorse prepared term reference) (fun _ =>
    allRows (fun other => NoWorse prepared other reference → ¬ Improves (axes prepared) (cost prepared) term other)
    (fun other => implication (noWorse prepared other reference) (fun _ => negative (transport (strict_iff prepared term other) (strict prepared term other)))) (sections prepared))
  simp [List.sum_replicate] at all
  have arithmetic : admissionWorkBudget prepared+strictWorkBudget prepared+2+1 =
      admissionWorkBudget prepared+strictWorkBudget prepared+3 := by omega
  rw [arithmetic] at all
  unfold verify verificationBudget
  omega

private theorem flatMap_cost_bound {α : Type} (items : List α) (work : α → List (Operation prepared)) (budget : Nat)
    (bounded : ∀ item ∈ items,controlSteps prepared (work item) ≤ budget) :
    controlSteps prepared (items.flatMap work) ≤ items.length*budget := by
  induction items with
  | nil => simp [controlSteps]
  | cons head tail ih =>
    have a := bounded head List.mem_cons_self
    have b := ih (fun item inside => bounded item (List.mem_cons_of_mem _ inside))
    simp only [List.flatMap_cons,controlSteps_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega


def checkedWork {reference : Section prepared} (made : Compilation prepared reference) := made.work ++ (inspect prepared made).work

/-- Covers the explicit public scan, independent replay, every rejection and cached release. -/
def workBudget : Nat :=
  (sections prepared).length*(admissionWorkBudget prepared+1) +
  (sections prepared).length*(strictWorkBudget prepared+1) + verificationBudget prepared +
  (sections prepared).length*admissionWorkBudget prepared+1

theorem ordered_selection_verification_rejection_and_release_fit_the_generated_budget (reference : Section prepared)
    (order : List (Section prepared)) (complete : order.Perm (sections prepared)) :
    controlSteps prepared (checkedWork prepared (compileOrdered prepared reference order complete)) + 1 ≤ workBudget prepared := by
  have pool := collect_cost_bound prepared reference order
  rw [complete.length_eq] at pool
  have number : (collect prepared reference order).accepted.length ≤ (sections prepared).length := by
    rw [(collect prepared reference order).exact]
    exact (List.length_filterMap_le _ _).trans (Nat.le_of_eq complete.length_eq)
  dsimp only [compileOrdered]
  split
  · rename_i same
    simp only [checkedWork,inspect,controlSteps_append]
    have reports := flatMap_cost_bound (prepared := prepared) (sections prepared) _ (admissionWorkBudget prepared)
      (fun term _ => reject_cost_bound prepared reference term (rows prepared) (fun _ member => member) (fun all => by
        obtain ⟨candidate,member,_⟩ := every_accepted_section_is_generated prepared reference term
          ((rows_iff prepared reference term).mp all)
        have members : (collect prepared reference order).accepted.Perm (candidates prepared reference) := by
          rw [(collect prepared reference order).exact];exact complete.filterMap _
        have inside := members.mem_iff.mpr member
        rw [same] at inside
        exact List.not_mem_nil inside))
    unfold workBudget
    omega
  · rename_i head tail same
    have scanned := scan_cost_bound prepared head tail
    have verified := verification_cost_bound prepared reference (scan head tail).policy.term
    simp only [checkedWork,inspect,controlSteps_append]
    rw [same,List.length_cons] at number
    unfold workBudget
    have size : tail.length*(strictWorkBudget prepared+1) ≤ (sections prepared).length*(strictWorkBudget prepared+1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega


theorem receipt_release_fits_the_generated_budget (reference : Section prepared)
    (order : List (Section prepared)) (complete : order.Perm (sections prepared))
    (receipt : Receipt prepared (compileOrdered prepared reference order complete)) :
    controlSteps prepared receipt.work ≤ workBudget prepared := by
  have bound := ordered_selection_verification_rejection_and_release_fit_the_generated_budget prepared reference order complete
  rw [Receipt.work,receipt.generated]
  change controlSteps prepared (checkedWork prepared (compileOrdered prepared reference order complete) ++ [.branch _]) ≤ _
  rw [controlSteps_append]
  exact bound

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Builders
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {reference : Section prepared}

def collectNil : Pool prepared reference [] := ⟨[],rfl,[]⟩
def collectCons (head : Section prepared) (tail : List (Section prepared))
    (checked : Check prepared (NoWorse prepared head reference)) (later : Pool prepared reference tail) : Pool prepared reference (head::tail) :=
  match checked.decision with
  | .isTrue accepted => ⟨⟨head,accepted⟩::later.accepted,by
      simp only [List.filterMap_cons,Policy.check,dif_pos accepted];rw [later.exact],checked.work++[.retain true]++later.work⟩
  | .isFalse rejected => ⟨later.accepted,by
      simp only [List.filterMap_cons,Policy.check,dif_neg rejected];exact later.exact,checked.work++[.retain false]++later.work⟩
theorem collectCons_exact (head : Section prepared) (tail : List (Section prepared))
    (checked : Check prepared (NoWorse prepared head reference)) (actual : checked = noWorse prepared head reference) :
    collectCons head tail checked (collect prepared reference tail) = collect prepared reference (head::tail) := by
  cases actual
  conv_rhs => dsimp only [collect]
  cases decision : (noWorse prepared head reference).decision <;> simp only [collectCons,decision]
abbrev ScanValue (first : Candidate prepared reference) (remaining : List (Candidate prepared reference)) := Scan prepared first remaining
def scanSpecification (first : Candidate prepared reference) (remaining : List (Candidate prepared reference)) : ScanValue first remaining := scan first remaining
def scanNil (first : Candidate prepared reference) : ScanValue first [] := ⟨first,.inl rfl,.inl rfl,by simp,[]⟩
def scanBetter (first head : Candidate prepared reference) (tail : List (Candidate prepared reference))
    (checked : Check prepared (Strict prepared first.term head.term)) (better : Strict prepared first.term head.term)
    (rest : ScanValue head tail) : ScanValue first (head::tail) :=
  ⟨rest.policy,.inr (by
          rcases rest.original with same | inside
          · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
          · exact List.mem_cons_of_mem _ inside),
        .inr (by
          rcases rest.advances with same | further
          · simpa only [same] using better
          · exact strict_trans prepared better further),by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other;exact no_reverse rest
          · exact rest.maximal other later,checked.work ++ [.select true] ++ rest.work⟩
def scanKept (first head : Candidate prepared reference) (tail : List (Candidate prepared reference))
    (checked : Check prepared (Strict prepared first.term head.term)) (notBetter : ¬Strict prepared first.term head.term)
    (rest : ScanValue first tail) : ScanValue first (head::tail) :=
  ⟨rest.policy,rest.original.imp_right (List.mem_cons_of_mem _),rest.advances,by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other
            intro backwards
            rcases rest.advances with same | forward
            · apply notBetter
              simpa only [same] using backwards
            · exact notBetter (strict_trans prepared forward backwards)
          · exact rest.maximal other later,checked.work ++ [.select false] ++ rest.work⟩
theorem scanBetter_exact (first head : Candidate prepared reference) (tail : List (Candidate prepared reference))
    (checked : Check prepared (Strict prepared first.term head.term)) (actual : checked = strict prepared first.term head.term)
    (better : Strict prepared first.term head.term) (decision : checked.decision = .isTrue better) :
    scanBetter first head tail checked better (scanSpecification head tail) = scanSpecification first (head::tail) := by
  cases actual;simp only [scanSpecification,scan,decision];rfl
theorem scanKept_exact (first head : Candidate prepared reference) (tail : List (Candidate prepared reference))
    (checked : Check prepared (Strict prepared first.term head.term)) (actual : checked = strict prepared first.term head.term)
    (notBetter : ¬Strict prepared first.term head.term) (decision : checked.decision = .isFalse notBetter) :
    scanKept first head tail checked notBetter (scanSpecification first tail) = scanSpecification first (head::tail) := by
  cases actual;simp only [scanSpecification,scan,decision];rfl
private theorem pool_members (pool : Pool prepared reference (sections prepared)) : pool.accepted.Perm (candidates prepared reference) := by
  rw [pool.exact];exact List.Perm.refl _
def compileEmpty (pool : Pool prepared reference (sections prepared)) (same : pool.accepted = []) : Compilation prepared reference :=
  ⟨.blocked (fun term => reject prepared reference term (rows prepared) (fun _ member => member) (fun all => by
      obtain ⟨candidate,member,_⟩ := every_accepted_section_is_generated prepared reference term ((rows_iff prepared reference term).mp all)
      have inside := (pool_members pool).mem_iff.mpr member
      rw [same] at inside;exact List.not_mem_nil inside)),pool.work⟩
def compileSelected (pool : Pool prepared reference (sections prepared)) (head : Candidate prepared reference)
    (tail : List (Candidate prepared reference)) (same : pool.accepted = head::tail) (found : ScanValue head tail) : Compilation prepared reference :=
  ⟨.selected ⟨found.policy,by
      apply (pool_members pool).mem_iff.mp;rw [same]
      rcases found.original with same | inside
      · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
      · exact List.mem_cons_of_mem _ inside,by
      intro other member improves
      have strict := (strict_iff prepared _ _).mpr improves
      have inside := (pool_members pool).mem_iff.mpr member
      rw [same] at inside
      rcases List.mem_cons.mp inside with same | later
      · subst other;exact no_reverse found strict
      · exact found.maximal other later strict⟩,pool.work++found.work⟩
theorem compileEmpty_exact (pool : Pool prepared reference (sections prepared))
    (actual : pool = collect prepared reference (sections prepared)) (same : pool.accepted = []) :
    compileEmpty pool same = compile prepared reference := by
  cases actual;dsimp only [compile,compileOrdered];split
  · rfl
  · rename_i head tail contrary;cases same.symm.trans contrary
theorem compileSelected_exact (pool : Pool prepared reference (sections prepared))
    (actual : pool = collect prepared reference (sections prepared)) (head : Candidate prepared reference)
    (tail : List (Candidate prepared reference)) (same : pool.accepted = head::tail)
    (found : ScanValue head tail) (generated : found = scanSpecification head tail) :
    compileSelected pool head tail same found = compile prepared reference := by
  cases actual;cases generated;dsimp only [compile,compileOrdered];split
  · rename_i contrary;cases same.symm.trans contrary
  · rename_i other rest observed
    rcases List.cons.inj (same.symm.trans observed) with ⟨rfl,rfl⟩;rfl
private def reindex (made : Compilation prepared reference) (result : Result prepared reference) (same : made.result = result)
    (review : Check prepared (Reviewed prepared result)) : Check prepared (Reviewed prepared made.result) := same.symm ▸ review
def selectedReview (made : Compilation prepared reference) (choice : Choice prepared reference) (same : made.result = .selected choice) :
    Check prepared (Reviewed prepared made.result) := reindex made (.selected choice) same (verify prepared reference choice.policy.term)
theorem selectedReview_exact (made : Compilation prepared reference) (choice : Choice prepared reference) (same : made.result = .selected choice) :
    selectedReview made choice same = inspect prepared made := by
  rcases made with ⟨result,work⟩;cases same;rfl
def blockedReview (made : Compilation prepared reference) (rejected : (term : Section prepared) → Rejected prepared reference term)
    (same : made.result = .blocked rejected) (cached : List (Operation prepared)) : Check prepared (Reviewed prepared made.result) :=
  reindex made (.blocked rejected) same ⟨.isTrue (by
    intro term accepted
    exact (rejected term).result.broken ((rows_iff prepared reference term).mpr accepted _ (rejected term).result.original)),cached⟩
theorem blockedReview_exact (made : Compilation prepared reference) (rejected : (term : Section prepared) → Rejected prepared reference term)
    (same : made.result = .blocked rejected) (cached : List (Operation prepared))
    (exact : cached = (sections prepared).flatMap (fun term => (rejected term).work)) : blockedReview made rejected same cached = inspect prepared made := by
  rcases made with ⟨result,work⟩;cases same;cases exact;rfl
def receiptFrom (made : Compilation prepared reference) (review : Check prepared (Reviewed prepared made.result))
    (generated : review = inspect prepared made) : Receipt prepared made := ⟨review,generated⟩
theorem receiptFrom_exact (made : Compilation prepared reference) (review : Check prepared (Reviewed prepared made.result))
    (generated : review = inspect prepared made) : receiptFrom made review generated = certify prepared made := by
  cases generated;rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Builders

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Builders
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {reference : Section prepared}
def trueCheck : Check prepared True := ⟨.isTrue trivial,[]⟩
def andFalse {A B : Prop} (checked : Check prepared A) (broken : ¬A) : Check prepared (A ∧ B) :=
  ⟨.isFalse (fun both => broken both.1),checked.work++[.branch false]⟩
theorem andFalse_exact {A B : Prop} (checked : Check prepared A) (broken : ¬A) (decision : checked.decision = .isFalse broken) (later : Check prepared B) :
    andFalse checked broken = conjunction checked (fun _ => later) := by simp only [conjunction,decision];rfl
def impFalse {A B : Prop} (checked : Check prepared A) (broken : ¬A) : Check prepared (A → B) :=
  ⟨.isTrue (fun yes => False.elim (broken yes)),checked.work++[.branch false]⟩
theorem impFalse_exact {A B : Prop} (checked : Check prepared A) (broken : ¬A) (decision : checked.decision = .isFalse broken) (later : Check prepared B) :
    impFalse checked broken = implication checked (fun _ => later) := by simp only [implication,decision];rfl
theorem strictEquivalence (previous new : Section prepared) : Strict prepared previous new ↔ Improves (axes prepared) (cost prepared) previous new := strict_iff prepared previous new
def selectedFromChecked (made : Compilation prepared reference) (choice : Choice prepared reference) (same : made.result = .selected choice)
    (checked : Check prepared (NoWorse prepared choice.policy.term reference ∧ ∀ other ∈ sections prepared,NoWorse prepared other reference → ¬Improves (axes prepared) (cost prepared) choice.policy.term other)) :
    Check prepared (Reviewed prepared made.result) := reindex made (.selected choice) same checked
theorem selectedFromChecked_exact (made : Compilation prepared reference) (choice : Choice prepared reference) (same : made.result = .selected choice)
    (checked : Check prepared (NoWorse prepared choice.policy.term reference ∧ ∀ other ∈ sections prepared,NoWorse prepared other reference → ¬Improves (axes prepared) (cost prepared) choice.policy.term other))
    (actual : checked = verify prepared reference choice.policy.term) : selectedFromChecked made choice same checked = inspect prepared made := by
  cases actual;exact selectedReview_exact made choice same

def rejectSpecification (term : Section prepared) (items : List (Row prepared))
    (inside : ∀ row ∈ items,row ∈ rows prepared) (invalid : ¬∀ row ∈ items,Holds prepared reference term row) : Rejected prepared reference term := reject prepared reference term items inside invalid
def rejectAt (term : Section prepared) (head : Row prepared) (tail : List (Row prepared))
    (inside : ∀ row ∈ head::tail,row ∈ rows prepared) (checked : Check prepared (Holds prepared reference term head))
    (broken : ¬Holds prepared reference term head) : Rejected prepared reference term :=
  ⟨⟨head,inside head List.mem_cons_self,broken⟩,checked.work++[.branch false]⟩
def rejectAfter (term : Section prepared) (head : Row prepared) (checked : Check prepared (Holds prepared reference term head))
    (later : Rejected prepared reference term) : Rejected prepared reference term := ⟨later.result,checked.work++[.branch true]++later.work⟩
theorem tailInvalid (term : Section prepared) (head : Row prepared) (tail : List (Row prepared))
    (invalid : ¬∀ row ∈ head::tail,Holds prepared reference term row) (holds : Holds prepared reference term head) :
    ¬∀ row ∈ tail,Holds prepared reference term row := fun all => invalid (by
      intro row inside;rcases List.mem_cons.mp inside with same | later
      · subst row;exact holds
      · exact all row later)
theorem rejectAt_exact (term : Section prepared) (head : Row prepared) (tail : List (Row prepared))
    (inside : ∀ row ∈ head::tail,row ∈ rows prepared) (invalid : ¬∀ row ∈ head::tail,Holds prepared reference term row)
    (checked : Check prepared (Holds prepared reference term head)) (actual : checked = atom prepared reference term head)
    (broken : ¬Holds prepared reference term head) (decision : checked.decision = .isFalse broken) :
    rejectAt term head tail inside checked broken = rejectSpecification term (head::tail) inside invalid := by
  cases actual;simp only [rejectSpecification,reject,decision];rfl
theorem rejectAfter_exact (term : Section prepared) (head : Row prepared) (tail : List (Row prepared))
    (inside : ∀ row ∈ head::tail,row ∈ rows prepared) (invalid : ¬∀ row ∈ head::tail,Holds prepared reference term row)
    (checked : Check prepared (Holds prepared reference term head)) (actual : checked = atom prepared reference term head)
    (holds : Holds prepared reference term head) (decision : checked.decision = .isTrue holds) :
    rejectAfter term head checked (rejectSpecification term tail (fun row member => inside row (List.mem_cons_of_mem _ member)) (tailInvalid term head tail invalid holds)) =
      rejectSpecification term (head::tail) inside invalid := by
  cases actual;simp only [rejectSpecification,reject,decision];rfl
theorem rejectedInvalid (rejected : (term : Section prepared) → Rejected prepared reference term) (term : Section prepared) :
    ¬∀ row ∈ rows prepared,Holds prepared reference term row := fun all => (rejected term).result.broken (all _ (rejected term).result.original)
theorem canonicalRejected (made : Compilation prepared reference) (compiled : made = compile prepared reference)
    (rejected : (term : Section prepared) → Rejected prepared reference term) (same : made.result = .blocked rejected)
    (term : Section prepared) : rejected term = rejectSpecification term (rows prepared) (fun _ listed => listed) (rejectedInvalid rejected term) := by
  cases compiled;dsimp only [compile,compileOrdered] at same;split at same
  · cases Result.blocked.inj same;rfl
  · cases same

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Builders
