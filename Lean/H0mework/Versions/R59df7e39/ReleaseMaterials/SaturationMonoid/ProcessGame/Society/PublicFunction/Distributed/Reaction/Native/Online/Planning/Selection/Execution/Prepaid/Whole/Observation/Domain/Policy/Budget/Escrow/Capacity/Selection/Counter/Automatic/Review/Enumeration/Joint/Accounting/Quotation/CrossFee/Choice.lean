import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Pool
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}

namespace Full
variable {driver : Feedback.Input seed.source.code} (cursor : Online.Cursor seed driver)
def EvaluationLe (new previous : Evaluation cursor.source.val.code) : Prop :=
  Planning.evaluationBenefit cursor new previous ∧ new.profile = previous.profile ∧
    (Feedback.Authority.Trace.Lawful.inventory new.native).admitted =
      (Feedback.Authority.Trace.Lawful.inventory previous.native).admitted
instance (new previous : Evaluation cursor.source.val.code) : Decidable (EvaluationLe cursor new previous) := by
  unfold EvaluationLe;infer_instance

theorem evaluation_refl (value : Evaluation cursor.source.val.code) : EvaluationLe cursor value value :=
  ⟨Planning.evaluationBenefit_refl cursor value,rfl,rfl⟩
theorem evaluation_trans {first middle last : Evaluation cursor.source.val.code}
    (left : EvaluationLe cursor first middle) (right : EvaluationLe cursor middle last) : EvaluationLe cursor first last :=
  ⟨Planning.evaluationBenefit_trans cursor left.1 right.1,left.2.1.trans right.2.1,left.2.2.trans right.2.2⟩

def FutureLe : Option (Future.Recovery.Assessment.Report cursor.model) → Option (Future.Recovery.Assessment.Report cursor.model) → Prop
  | some new,some previous => previous.consumed ≤ new.consumed ∧ EvaluationLe cursor new.evaluation previous.evaluation
  | _,none => True
  | none,some _ => False
instance (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) : Decidable (FutureLe cursor new previous) := by
  cases new <;> cases previous <;> unfold FutureLe <;> infer_instance

theorem future_refl (value : Option (Future.Recovery.Assessment.Report cursor.model)) : FutureLe cursor value value := by
  cases value with
  | none => trivial
  | some value => exact ⟨Nat.le_refl _,evaluation_refl cursor _⟩
theorem future_trans {first middle last : Option (Future.Recovery.Assessment.Report cursor.model)}
    (left : FutureLe cursor first middle) (right : FutureLe cursor middle last) : FutureLe cursor first last := by
  cases first <;> cases middle <;> cases last <;> simp only [FutureLe] at *
  all_goals first | trivial | contradiction | exact ⟨right.1.trans left.1,evaluation_trans cursor left.2 right.2⟩

def TensorLe (new previous : Planning.Tensor cursor) : Prop :=
  EvaluationLe cursor new.present previous.present ∧
    (∀ word ∈ Future.Recovery.capabilities cursor.model cursor.depth,FutureLe cursor (new.future cursor word) (previous.future cursor word)) ∧
    ∀ word ∈ Future.Recovery.capabilities cursor.model cursor.depth,
      (previous.funding cursor word).isNone = true → (new.funding cursor word).isNone = true
instance (new previous : Planning.Tensor cursor) : Decidable (TensorLe cursor new previous) := by unfold TensorLe;infer_instance

theorem tensor_refl (value : Planning.Tensor cursor) : TensorLe cursor value value :=
  ⟨evaluation_refl cursor _,fun _ _ => future_refl cursor _,fun _ _ yes => yes⟩
theorem tensor_trans {first middle last : Planning.Tensor cursor}
    (left : TensorLe cursor first middle) (right : TensorLe cursor middle last) : TensorLe cursor first last :=
  ⟨evaluation_trans cursor left.1 right.1,fun word inside => future_trans cursor (left.2.1 word inside) (right.2.1 word inside),
    fun word inside yes => left.2.2 word inside (right.2.2 word inside yes)⟩

theorem full_profile_is_compared (new previous : Planning.Tensor cursor) (valid : TensorLe cursor new previous) :
    new.present.profile = previous.present.profile := valid.1.2.1
end Full

abbrev Offer :=  Pool.Pick prepared position
variable (pool : List (Offer (prepared := prepared) (position := position)))
def scopes (index : Index prepared) := pool.map fun policy => (policy.view index).scope
abbrev Table (index : Index prepared) := QuotaJoint.Table (scopes pool index)
def tables (index : Index prepared) := QuotaJoint.tables (scopes pool index)
def rival (index : Index prepared) (table : Table pool index) := QuotaJoint.opponent (scopes pool index) table

theorem finite_relation_iff_every_same_adaptive_opponent (new previous : Offer (prepared := prepared) (position := position))
    (new_original : new ∈ pool) (previous_original : previous ∈ pool) (index : Index prepared)
    (relation : Planning.Tensor (Policy.initial input prepared.saved[index].point) → Planning.Tensor (Policy.initial input prepared.saved[index].point) → Prop) :
    (∀ table ∈ tables pool index,relation ((new.view index).tensor (rival pool index table))
      ((previous.view index).tensor (rival pool index table))) ↔
    ∀ opponent : Opponent (Policy.initial input prepared.saved[index].point).source.val.code,
      relation ((new.view index).tensor opponent) ((previous.view index).tensor opponent) :=
  QuotaJoint.finite_comparison_iff_every_same_adaptive_opponent (scopes pool index) input.span
    (new.view index).scope (previous.view index).scope
    (List.mem_map.mpr ⟨new,new_original,rfl⟩) (List.mem_map.mpr ⟨previous,previous_original,rfl⟩)
    (new.view index).intent (previous.view index).intent (new.view index).oldBound
    (new.view index).paidBound (previous.view index).paidBound relation

def ResponsibilityLe (new previous : Offer (prepared := prepared) (position := position)) : Prop :=
  (∀ index : Index prepared,∀ table ∈ tables pool index,
    Full.TensorLe (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (rival pool index table))
      ((previous.view index).tensor (rival pool index table))) ∧
  (∀ index : Index prepared,new.work index ≤ previous.work index ∧ previous.credit index ≤ new.credit index) ∧
  new.branch.alternative.1 ≤ previous.branch.alternative.1 ∧
    new.invoiceWork ≤ previous.invoiceWork ∧ previous.invoiceCredit ≤ new.invoiceCredit
instance (new previous : Offer (prepared := prepared) (position := position)) : Decidable (ResponsibilityLe pool new previous) := by
  unfold ResponsibilityLe;infer_instance

theorem responsibility_refl (policy : Offer (prepared := prepared) (position := position)) : ResponsibilityLe pool policy policy :=
  ⟨fun _ _ _ => Full.tensor_refl _ _,fun _ => ⟨Nat.le_refl _,Nat.le_refl _⟩,Nat.le_refl _,Nat.le_refl _,Nat.le_refl _⟩
theorem responsibility_trans {first middle last : Offer (prepared := prepared) (position := position)}
    (left : ResponsibilityLe pool first middle) (right : ResponsibilityLe pool middle last) : ResponsibilityLe pool first last :=
  ⟨fun index table inside => Full.tensor_trans _ (left.1 index table inside) (right.1 index table inside),
    fun index => ⟨(left.2.1 index).1.trans (right.2.1 index).1,(right.2.1 index).2.trans (left.2.1 index).2⟩,
    left.2.2.1.trans right.2.2.1,left.2.2.2.1.trans right.2.2.2.1,right.2.2.2.2.trans left.2.2.2.2⟩

-- Source probes turn the complete preorder into the existing finite vector selector.
def axes := pool

def cost (policy probe : Offer (prepared := prepared) (position := position)) : ℚ :=
  if ResponsibilityLe pool policy probe then 0 else 1

theorem vector_iff (new previous : Offer (prepared := prepared) (position := position)) (original : previous ∈ pool) :
    Distributed.NoWorse (axes pool) (cost pool) new previous ↔ ResponsibilityLe pool new previous := by
  constructor
  · intro vector
    have tested := vector previous original
    by_contra failed
    simp only [cost,if_pos (responsibility_refl pool previous),if_neg failed] at tested
    norm_num at tested
  · intro valid probe _inside
    by_cases old : ResponsibilityLe pool previous probe
    · have now := responsibility_trans pool valid old
      simp only [cost,if_pos old,if_pos now,le_refl]
    · simp only [cost,if_neg old]
      split <;> norm_num

abbrev Selected := Distributed.Selected (axes pool) (cost pool) pool
structure Refined (reference : Offer (prepared := prepared) (position := position)) where
  private mk ::
  selected : Selected pool
  no_worse : ResponsibilityLe pool selected.policy reference

def refine (reference : Offer (prepared := prepared) (position := position)) (listed : reference ∈ pool) : Refined pool reference :=
  let retained := pool.filter fun candidate => decide (ResponsibilityLe pool candidate reference)
  match found : Distributed.choose (axes pool) (cost pool) retained with
  | none => False.elim (by
      have empty := (Distributed.choose_none_iff_empty _ _ _).mp found
      have own : reference ∈ retained := List.mem_filter.mpr ⟨listed,decide_eq_true (responsibility_refl pool reference)⟩
      rw [empty] at own;cases own)
  | some chosen =>
      let accepted := List.mem_filter.mp chosen.original
      let bounded := of_decide_eq_true accepted.2
      ⟨⟨chosen.policy,accepted.1,by
          intro other inside strict
          apply chosen.maximal other (List.mem_filter.mpr ⟨inside,decide_eq_true
            (responsibility_trans pool ((vector_iff pool other chosen.policy accepted.1).mp strict.1) bounded)⟩)
          exact strict⟩,bounded⟩

theorem every_available_improvement_is_selected (reference : Offer (prepared := prepared) (position := position)) (listed : reference ∈ pool)
    (available : ∃ other ∈ pool,ResponsibilityLe pool other reference ∧ ¬ ResponsibilityLe pool reference other) :
    ¬ ResponsibilityLe pool reference (refine pool reference listed).selected.policy := by
  intro backwards
  obtain ⟨other,inside,forward,strict⟩ := available
  apply (refine pool reference listed).selected.maximal other inside
  refine ⟨(vector_iff pool _ _ (refine pool reference listed).selected.original).mpr (responsibility_trans pool forward backwards),?_⟩
  intro reverse
  exact strict (responsibility_trans pool backwards ((vector_iff pool _ _ inside).mp reverse))

def verify (reference candidate : Offer (prepared := prepared) (position := position)) : Bool :=
  decide (ResponsibilityLe pool candidate reference ∧
    ∀ other ∈ pool,¬ (ResponsibilityLe pool other candidate ∧ ¬ResponsibilityLe pool candidate other))
theorem independently_verified (reference : Offer (prepared := prepared) (position := position)) (listed : reference ∈ pool) :
    verify pool reference (refine pool reference listed).selected.policy = true := by
  apply decide_eq_true
  refine ⟨(refine pool reference listed).no_worse,?_⟩
  intro other inside strict
  apply (refine pool reference listed).selected.maximal other inside
  exact ⟨(vector_iff pool _ _ (refine pool reference listed).selected.original).mpr strict.1,
    fun reverse => strict.2 ((vector_iff pool _ _ inside).mp reverse)⟩



inductive Resolution (audit : CrossFee.Result prepared position) (ordinal : Nat) where
  | unlisted (absent : (Pool.collect audit)[ordinal]? = none)
  | refined (reference : Offer (prepared := prepared) (position := position))
      (located : (Pool.collect audit)[ordinal]? = some reference) (answer : Refined (Pool.collect audit) reference)
def resolve (audit : CrossFee.Result prepared position) (ordinal : Nat) : Resolution audit ordinal :=
  match located : (Pool.collect audit)[ordinal]? with
  | none => .unlisted located
  | some reference => .refined reference located (refine (Pool.collect audit) reference (List.mem_of_getElem? located))

inductive Debt where
  | cacheRead | tensorGeneration | fullComparison | selection | verification | installation | storage | announcement
structure Record (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (position ordinal : Nat) where
  private mk ::
  audit : CrossFee.Result prepared position
  generated : audit = CrossFee.generateFor prepared budget position
  resolution : Resolution audit ordinal
  resolved : resolution = resolve audit ordinal

def generateFor (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (position ordinal : Nat) : Record prepared budget position ordinal :=
  let audit := CrossFee.generateFor prepared budget position
  ⟨audit,rfl,resolve audit ordinal,rfl⟩
def generate (prepared : Prepared input) (position ordinal : Nat) :=
  generateFor prepared (CandidateRuntime.budgetFor prepared none) position ordinal

def computationDebts : List Debt :=
  [.cacheRead,.tensorGeneration,.fullComparison,.selection,.verification,.installation,.storage,.announcement]
def Record.pending {budget : CandidateRuntime.BudgetChoice prepared} {ordinal : Nat} (_record : Record prepared budget position ordinal) : List Debt := computationDebts

def afterIndex (audit : CrossFee.Result prepared position) (index : Index prepared) : Index audit.after :=
  match audit with
  | .empty .. => index
  | .unpaid _ funding .. | .zero _ funding .. => Automatic.paidIndex funding index
  | .exploring outer .. => Automatic.paidIndex outer.funding index
def retainedLaw {Audit : Type} (payload : Audit) (audit : CrossFee.Result prepared position) (index : Index audit.after) :
    SourceNativeProjectionLaw (Online.Runtime.root (audit.cursor index)).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Audit
  project := fun _ {_} _ _ => payload
noncomputable def retainedNext {Audit : Type} (payload : Audit) (audit : CrossFee.Result prepared position) (index : Index audit.after) : AuthorityCurrent :=
  originalNext (audit.cursor index) (retainedLaw payload audit index)
noncomputable def Record.next {budget : CandidateRuntime.BudgetChoice prepared} {ordinal : Nat}
    (record : Record prepared budget position ordinal) (index : Index prepared) : AuthorityCurrent :=
  match record.resolution with
  | .unlisted _ => retainedNext record record.audit (afterIndex record.audit index)
  | .refined _ _ answer => answer.selected.policy.next record index

structure Activation (input : Input seed) (override : Option Nat) (position ordinal : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  budget : CandidateRuntime.BudgetChoice preparation
  budget_generated : budget = CandidateRuntime.budgetFor preparation override
  record : Record preparation budget position ordinal
  generated : record = generateFor preparation budget position ordinal
  bound : Binding.Linked preparation point
  bound_generated : Binding.locate preparation point = .linked bound
inductive Invocation (input : Input seed) (override : Option Nat) (position ordinal : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input override position ordinal point)
def invokeWith (input : Input seed) (override : Option Nat) (position ordinal : Nat) (point : NativePoint input) : Invocation input override position ordinal point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let budget := CandidateRuntime.budgetFor preparation override
    let record := generateFor preparation budget position ordinal
    match linked : Binding.locate preparation point with
    | .linked bound => .activated ⟨preparation,rfl,budget,rfl,record,rfl,bound,linked⟩
    | .mismatch broken => False.elim (broken observed)
  else .mismatch observed
def invoke (input : Input seed) (position ordinal : Nat) (point : NativePoint input) : Invocation input none position ordinal point := invokeWith input none position ordinal point
noncomputable def Activation.next {override : Option Nat} {ordinal : Nat} {point : NativePoint input}
    (made : Activation input override position ordinal point) : AuthorityCurrent := made.record.next made.bound.index

theorem every_matching_actual_point_is_activated (input : Input seed) (override : Option Nat) (position ordinal : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input override position ordinal point,invokeWith input override position ordinal point = .activated made := by
  unfold invokeWith;rw [dif_pos observed];dsimp only
  split
  · exact ⟨_,rfl⟩
  · rename_i broken actual;exact False.elim (broken observed)
theorem mismatched_observation_is_rejected (input : Input seed) (override : Option Nat) (position ordinal : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invokeWith input override position ordinal point = .mismatch broken := by
  simp only [invokeWith,dif_neg broken]



def refinementOfVerified (pool : List (Offer (prepared := prepared) (position := position)))
    (reference candidate : Offer (prepared := prepared) (position := position)) (original : candidate ∈ pool)
    (accepted : verify pool reference candidate = true) : Refined pool reference := by
  have checked : ResponsibilityLe pool candidate reference ∧
      ∀ other ∈ pool,¬ (ResponsibilityLe pool other candidate ∧ ¬ResponsibilityLe pool candidate other) := of_decide_eq_true accepted
  refine ⟨⟨candidate,original,?_⟩,checked.1⟩
  intro other inside strict
  exact checked.2 other inside ⟨(vector_iff pool _ _ original).mp strict.1,
    fun reverse => strict.2 ((vector_iff pool _ _ inside).mpr reverse)⟩

inductive ProposalResult (audit : CrossFee.Result prepared position) (ordinal proposed : Nat) where
  | noReference (absent : (Pool.collect audit)[ordinal]? = none)
  | noCandidate (reference : Offer (prepared := prepared) (position := position))
      (located : (Pool.collect audit)[ordinal]? = some reference) (absent : (Pool.collect audit)[proposed]? = none)
  | rejected (reference candidate : Offer (prepared := prepared) (position := position))
      (located : (Pool.collect audit)[ordinal]? = some reference) (proposal : (Pool.collect audit)[proposed]? = some candidate)
      (failed : verify (Pool.collect audit) reference candidate = false)
  | accepted (reference candidate : Offer (prepared := prepared) (position := position))
      (located : (Pool.collect audit)[ordinal]? = some reference) (proposal : (Pool.collect audit)[proposed]? = some candidate)
      (answer : Refined (Pool.collect audit) reference) (same : answer.selected.policy = candidate)
def resolveProposal (audit : CrossFee.Result prepared position) (ordinal proposed : Nat) : ProposalResult audit ordinal proposed :=
  match located : (Pool.collect audit)[ordinal]? with
  | none => .noReference located
  | some reference => match proposal : (Pool.collect audit)[proposed]? with
    | none => .noCandidate reference located proposal
    | some candidate => if accepted : verify (Pool.collect audit) reference candidate = true then
        .accepted reference candidate located proposal (refinementOfVerified (Pool.collect audit) reference candidate (List.mem_of_getElem? proposal) accepted) rfl
      else .rejected reference candidate located proposal (Bool.eq_false_iff.mpr accepted)
structure Proposal (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (position ordinal proposed : Nat) where
  private mk ::
  audit : CrossFee.Result prepared position
  generated : audit = CrossFee.generateFor prepared budget position
  resolution : ProposalResult audit ordinal proposed
  resolved : resolution = resolveProposal audit ordinal proposed

def generateProposalFor (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (position ordinal proposed : Nat) : Proposal prepared budget position ordinal proposed :=
  let audit := CrossFee.generateFor prepared budget position
  ⟨audit,rfl,resolveProposal audit ordinal proposed,rfl⟩
def Proposal.pending {budget : CandidateRuntime.BudgetChoice prepared} {ordinal proposed : Nat}
    (_record : Proposal prepared budget position ordinal proposed) : List Debt := computationDebts
noncomputable def Proposal.next {budget : CandidateRuntime.BudgetChoice prepared} {ordinal proposed : Nat}
    (record : Proposal prepared budget position ordinal proposed) (index : Index prepared) : AuthorityCurrent :=
  match record.resolution with
  | .noReference _ => retainedNext record record.audit (afterIndex record.audit index)
  | .noCandidate reference .. | .rejected reference .. => reference.next record index
  | .accepted _ _ _ _ answer _ => answer.selected.policy.next record index

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice
