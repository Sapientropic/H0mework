import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Work
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)

inductive Query where
  | admission (policy : Section pool) (row : Row pool)
  | present (new previous : Section pool) (index : Index prepared) (table : Comparison.Table pool index)
  | future (new previous : Section pool) (index : Index prepared) (table : Comparison.Table pool index)
      (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model))
  | funding (new previous : Section pool) (index : Index prepared) (table : Comparison.Table pool index)
      (word : List (Future.Recovery.Action (initial input prepared.saved[index].point).model))
def Query.Holds : Query pool → Prop
  | .admission policy row => PublicPolicy.Holds pool policy row
  | .present new previous index table => evaluationBenefit (initial input prepared.saved[index].point)
      ((read pool new index).tensor (Comparison.rival pool index table)).present
      ((read pool previous index).tensor (Comparison.rival pool index table)).present
  | .future new previous index table word => Planning.futureBenefit (initial input prepared.saved[index].point)
      (((read pool new index).tensor (Comparison.rival pool index table)).future _ word)
      (((read pool previous index).tensor (Comparison.rival pool index table)).future _ word)
  | .funding new previous index table word =>
      (((read pool previous index).tensor (Comparison.rival pool index table)).funding _ word).isNone = true →
      (((read pool new index).tensor (Comparison.rival pool index table)).funding _ word).isNone = true
instance (query : Query pool) : Decidable (query.Holds pool) := by
  cases query <;> unfold Query.Holds <;> infer_instance

abbrev BenefitKey := NativeBenefit.WorkKey (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)
abbrev AdmissionKey := NativeAdmission.Key (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)
abbrev SignatureKey := Policy.Work.SignatureKey (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)
inductive Operation where
  | query (query : Query pool) (answer : Bool)
  | source (index : Index prepared) (event : NativeTensor.Event P G O T I)
  | benefit (index : Index prepared) (event : NativeBenefit.Event (BenefitKey (P := P) (G := G) (O := O) (T := T) (I := I)))
  | admission (index : Index prepared) (event : NativeBenefit.Event (AdmissionKey (P := P) (G := G) (O := O) (T := T) (I := I)))
  | signature (policy : Section pool) (first second : Index prepared)
      (event : NativeBenefit.Event (SignatureKey (P := P) (G := G) (O := O) (T := T) (I := I)))
  | branch (answer : Bool)
  | negate (answer : Bool)
  | retain (accepted : Bool)
  | select (replaced : Bool)
structure Check (P : Prop) where
  private mk ::
  decision : Decidable P
  work : List (Operation pool)
def Check.value {P : Prop} (made : Check pool P) : Bool := @decide P made.decision
variable {pool}
def transport {P Q : Prop} (equivalent : P ↔ Q) (made : Check pool P) : Check pool Q :=
  ⟨match made.decision with
    | .isTrue yes => .isTrue (equivalent.mp yes)
    | .isFalse no => .isFalse (fun yes => no (equivalent.mpr yes)),made.work⟩
def conjunction {P Q : Prop} (first : Check pool P) (later : Unit → Check pool Q) : Check pool (P ∧ Q) :=
  match first.decision with
  | .isFalse no => ⟨.isFalse (fun yes => no yes.1),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun both => no both.2)
      | .isTrue other => .isTrue ⟨yes,other⟩,first.work ++ [.branch true] ++ second.work⟩
def negative {P : Prop} (made : Check pool P) : Check pool (¬ P) :=
  ⟨match made.decision with
    | .isTrue yes => .isFalse (fun no => no yes)
    | .isFalse no => .isTrue no,made.work ++ [.negate made.value]⟩
def implication {P Q : Prop} (first : Check pool P) (later : Unit → Check pool Q) : Check pool (P → Q) :=
  match first.decision with
  | .isFalse no => ⟨.isTrue (fun yes => False.elim (no yes)),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun accepts => no (accepts yes))
      | .isTrue other => .isTrue (fun _ => other),first.work ++ [.branch true] ++ second.work⟩
def allRows {α : Type} (P : α → Prop) (test : (a : α) → Check pool (P a)) :
    (items : List α) → Check pool (∀ a ∈ items,P a)
  | [] => ⟨.isTrue (by simp),[]⟩
  | head::tail => transport (by simp only [List.mem_cons,forall_eq_or_imp])
      (conjunction (test head) (fun _ => allRows P test tail))

variable (pool)
def atom (query : Query pool) : Check pool (query.Holds pool) :=
  match query with
  | .admission policy row => match row with
    | .coherence first second =>
      let left := Policy.Work.cachedShape (.ready (read pool policy first).scope) (read pool policy first).intent
      let right := Policy.Work.cachedShape (.ready (read pool policy second).scope) (read pool policy second).intent
      let checked := SignatureWork.Generic.compare ActionWork.compare left right
      let equivalent : left = right ↔ (Query.admission policy (.coherence first second)).Holds pool := by
        dsimp only [left,right,Query.Holds,PublicPolicy.Holds]
        have a := Policy.Work.cached_signature_is_the_original_public_request (.ready (read pool policy first).scope) (read pool policy first).intent
        have b := Policy.Work.cached_signature_is_the_original_public_request (.ready (read pool policy second).scope) (read pool policy second).intent
        exact Iff.of_eq (congrArg₂ Eq a b)
      transport equivalent ⟨checked.decision,.query (Query.admission policy (.coherence first second)) checked.value :: checked.work.map (.signature policy first second)⟩
    | .native index coordinate => match coordinate with
      | .present table =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := Whole.Materialization.present branch.scope input.span branch.intent rival
        let original := Whole.Materialization.present branch.scope input.span .keep rival
        let checked := NativeBenefit.transport (show _ ↔ (Query.admission policy (.native index (.present table))).Holds pool from by
          rw [Whole.Materialization.present_exact,Whole.Materialization.present_exact]
          simp only [Query.Holds,PublicPolicy.Holds,LocalHolds,Comparison.Branch.tensor,oldTensor,
            Whole.keep_is_the_original_unpaid_tensor]
          rfl) (NativeAdmission.present _ current.value original.value)
        ⟨checked.decision,[.query (Query.admission policy (.native index (.present table))) checked.value] ++ (current.work++original.work).map (.source index) ++
          checked.work.map (.admission index)⟩
      | .future table word =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        let current := Whole.Materialization.future branch.scope input.span branch.intent rival word
        let original := Whole.Materialization.future branch.scope input.span .keep rival word
        let checked := NativeBenefit.transport (show _ ↔ (Query.admission policy (.native index (.future table word))).Holds pool from by
          rw [Whole.Materialization.future_exact,Whole.Materialization.future_exact]
          simp only [Query.Holds,PublicPolicy.Holds,LocalHolds,Comparison.Branch.tensor,oldTensor,
            Whole.keep_is_the_original_unpaid_tensor]
          rfl) (NativeAdmission.future _ current.value original.value)
        ⟨checked.decision,[.query (Query.admission policy (.native index (.future table word))) checked.value] ++ (current.work++original.work).map (.source index) ++
          checked.work.map (.admission index)⟩
      | .funding table word =>
        let checked := NativeAdmission.funding
          (((read pool policy index).tensor (Comparison.rival pool index table)).funding _ word)
          ((oldTensor index (Comparison.rival pool index table)).funding _ word)
        ⟨checked.decision,[.query (Query.admission policy (.native index (.funding table word))) checked.value] ++ checked.work.map (.admission index)⟩
      | .release | .coverage | .deployment => ⟨inferInstance,[.query (.admission policy (.native index coordinate)) (decide (LocalHolds pool policy index coordinate))]⟩
    | .informed | .uniform .. => ⟨inferInstance,[.query (.admission policy row) (decide (PublicPolicy.Holds pool policy row))]⟩
  | .present new previous index table =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := Whole.Materialization.present left.scope input.span left.intent rival
    let original := Whole.Materialization.present right.scope input.span right.intent rival
    let checked := NativeBenefit.transport (show _ ↔ (Query.present new previous index table).Holds pool from by
      rw [Whole.Materialization.present_exact,Whole.Materialization.present_exact];rfl)
      (NativeBenefit.present _ current.value original.value)
    ⟨checked.decision,[.query (Query.present new previous index table) checked.value] ++ (current.work++original.work).map (.source index) ++
      checked.work.map (.benefit index)⟩
  | .future new previous index table word =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    let current := Whole.Materialization.future left.scope input.span left.intent rival word
    let original := Whole.Materialization.future right.scope input.span right.intent rival word
    let checked := NativeBenefit.transport (show _ ↔ (Query.future new previous index table word).Holds pool from by
      rw [Whole.Materialization.future_exact,Whole.Materialization.future_exact];rfl)
      (NativeBenefit.future _ current.value original.value)
    ⟨checked.decision,[.query (Query.future new previous index table word) checked.value] ++ (current.work++original.work).map (.source index) ++
      checked.work.map (.benefit index)⟩
  | .funding new previous index table word =>
    let checked := NativeAdmission.funding
      (((read pool new index).tensor (Comparison.rival pool index table)).funding _ word)
      (((read pool previous index).tensor (Comparison.rival pool index table)).funding _ word)
    ⟨checked.decision,[.query (Query.funding new previous index table word) checked.value] ++ checked.work.map (.admission index)⟩

def accepted (policy : Section pool) : Check pool (Accepted pool policy) :=
  transport (rows_iff pool policy) (allRows (PublicPolicy.Holds pool policy)
    (fun row => atom pool (.admission policy row)) (rows pool))

def realBenefit (new previous : Section pool) : Check pool (Benefit pool new previous) :=
  transport (show (∀ index ∈ keys prepared,∀ table ∈ Comparison.tables pool index,
      benefit (initial input prepared.saved[index].point) ((read pool new index).tensor (Comparison.rival pool index table))
        ((read pool previous index).tensor (Comparison.rival pool index table))) ↔ Benefit pool new previous from by
    constructor
    · intro all index;exact all index (List.mem_finRange _)
    · intro all index _;exact all index)
    (allRows _ (fun index => allRows _ (fun table =>
      conjunction (atom pool (.present new previous index table)) (fun _ =>
        conjunction (allRows _ (fun word => atom pool (.future new previous index table word))
          (Future.Recovery.capabilities (initial input prepared.saved[index].point).model (initial input prepared.saved[index].point).depth)) (fun _ =>
          allRows _ (fun word => atom pool (.funding new previous index table word))
          (Future.Recovery.capabilities (initial input prepared.saved[index].point).model (initial input prepared.saved[index].point).depth))))
      (Comparison.tables pool index)) (keys prepared))

def Strict (previous new : Section pool) : Prop := Benefit pool new previous ∧ ¬ Benefit pool previous new
private theorem strict_iff (previous new : Section pool) : Strict pool previous new ↔
    Improves (axes pool) (cost pool) previous new := by
  constructor
  · intro h;exact ⟨(vector_iff pool _ _).mpr h.1,fun reverse => h.2 ((vector_iff pool _ _).mp reverse)⟩
  · intro h;exact ⟨(vector_iff pool _ _).mp h.1,fun reverse => h.2 ((vector_iff pool _ _).mpr reverse)⟩

def strict (previous new : Section pool) : Check pool (Strict pool previous new) :=
  conjunction (realBenefit pool new previous) (fun _ => negative (realBenefit pool previous new))
structure Pool (items : List (Section pool)) where
  private mk ::
  accepted : List (Candidate pool)
  exact : accepted = items.filterMap (PublicPolicy.check pool)
  work : List (Operation pool)

def collect : (items : List (Section pool)) → Pool pool items
  | [] => ⟨[],rfl,[]⟩
  | head::tail =>
    let checked := accepted pool head
    let rest := collect tail
    match checked.decision with
    | .isTrue accepted =>
      ⟨⟨head,accepted⟩::rest.accepted,by simp only [List.filterMap_cons,PublicPolicy.check,dif_pos accepted];rw [rest.exact],
        checked.work ++ [.retain true] ++ rest.work⟩
    | .isFalse rejected =>
      ⟨rest.accepted,by simp only [List.filterMap_cons,PublicPolicy.check,dif_neg rejected];exact rest.exact,
        checked.work ++ [.retain false] ++ rest.work⟩

private theorem strict_irrefl (term : Section pool) : ¬ Strict pool term term := fun both => both.2 both.1
private theorem strict_trans {first middle last : Section pool}
    (a : Strict pool first middle) (b : Strict pool middle last) :
    Strict pool first last :=
  ⟨PublicPolicy.benefit_trans pool b.1 a.1,
    fun reverse => a.2 (PublicPolicy.benefit_trans pool reverse b.1)⟩

private structure Scan (first : Candidate pool)
    (remaining : List (Candidate pool)) where
  policy : Candidate pool
  original : policy = first ∨ policy ∈ remaining
  advances : policy = first ∨ Strict pool first.term policy.term
  maximal : ∀ other ∈ remaining, ¬ Strict pool policy.term other.term
  work : List (Operation pool)

variable {pool}
private theorem no_reverse {first : Candidate pool}
    {remaining : List (Candidate pool)} (made : Scan pool first remaining) :
    ¬ Strict pool made.policy.term first.term := by
  intro backwards
  rcases made.advances with same | forward
  · apply strict_irrefl pool first.term
    simpa only [same] using backwards
  · exact strict_irrefl pool first.term (strict_trans pool forward backwards)

private def scan (first : Candidate pool) :
    (remaining : List (Candidate pool)) → Scan pool first remaining
  | [] => ⟨first,.inl rfl,.inl rfl,by simp,[]⟩
  | head::tail =>
    let checked := strict pool first.term head.term
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
          · exact strict_trans pool better further),by
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
            · exact notBetter (strict_trans pool forward backwards)
          · exact rest.maximal other later,checked.work ++ [.select false] ++ rest.work⟩

variable (pool)
structure Rejected (term : Section pool) where
  private mk ::
  result : Rejection pool term
  work : List (Operation pool)

private def reject (term : Section pool) :
    (items : List (Row pool)) → (inside : ∀ row ∈ items,row ∈ rows pool) →
    (invalid : ¬ ∀ row ∈ items,PublicPolicy.Holds pool term row) → Rejected pool term
  | [],_,invalid => False.elim (invalid (by simp))
  | head::tail,inside,invalid =>
    let checked := atom pool (.admission term head)
    match checked.decision with
    | .isFalse broken => ⟨⟨head,inside head List.mem_cons_self,broken⟩,checked.work ++ [.branch false]⟩
    | .isTrue holds =>
      let later := reject term tail (fun row member => inside row (List.mem_cons_of_mem _ member))
        (fun all => invalid (by
          intro row member
          rcases List.mem_cons.mp member with same | rest
          · subst row;exact holds
          · exact all row rest))
      ⟨later.result,checked.work ++ [.branch true] ++ later.work⟩

inductive Result where
  | selected (choice : Choice pool)
  | blocked (rejected : (term : Section pool) → Rejected pool term)

structure Compilation where
  private mk ::
  result : Result pool
  work : List (Operation pool)

def compileOrdered (order : List (Section pool))
    (complete : order.Perm (sections pool)) : Compilation pool :=
  let collected := collect pool order
  have members : collected.accepted.Perm (candidates pool) := by
    rw [collected.exact]
    exact complete.filterMap _
  match same : collected.accepted with
  | [] => ⟨.blocked (fun term => reject pool term (rows pool) (fun _ member => member)
      (fun all => by
        obtain ⟨candidate,member,_⟩ := every_accepted_section_is_generated pool term
          ((rows_iff pool term).mp all)
        have inside := members.mem_iff.mpr member
        rw [same] at inside
        exact List.not_mem_nil inside)),collected.work⟩
  | head::tail =>
    let found := scan head tail
    ⟨.selected ⟨found.policy,by
      apply members.mem_iff.mp
      rw [same]
      rcases found.original with same | inside
      · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
      · exact List.mem_cons_of_mem _ inside,by
      intro other member improves
      have strict := (strict_iff pool _ _).mpr improves
      have inside := members.mem_iff.mpr member
      rw [same] at inside
      rcases List.mem_cons.mp inside with same | later
      · subst other;exact no_reverse found strict
      · exact found.maximal other later strict⟩,collected.work ++ found.work⟩


def compile : Compilation pool :=
  compileOrdered pool (sections pool) (List.Perm.refl _)

/-- Independent replay uses the same source-native primitives, with its own work. -/
def verify (term : Section pool) : Check pool
    (Accepted pool term ∧ ∀ other ∈ sections pool,
      Accepted pool other → ¬ Improves (axes pool) (cost pool) term other) :=
  conjunction (accepted pool term) (fun _ =>
    allRows (fun other => Accepted pool other → ¬ Improves (axes pool) (cost pool) term other)
      (fun other => implication (accepted pool other)
        (fun _ => negative (transport (strict_iff pool term other) (strict pool term other)))) (sections pool))

theorem verify_matches_the_original_independent_verifier (term : Section pool) :
    (verify pool term).value = PublicPolicy.verify pool term := by
  unfold Check.value PublicPolicy.verify
  exact Subsingleton.elim _ _ |> fun same => congrArg (fun d => @decide _ d) same

def Outcome.checked : Outcome pool → Bool
  | .selected choice => PublicPolicy.verify pool choice.policy.term
  | .blocked _ => false

def Result.outcome : Result pool → Outcome pool
  | .selected choice => .selected choice
  | .blocked rejected => .blocked (fun term => (rejected term).result)

def Reviewed : Result pool → Prop
  | .selected choice => Accepted pool choice.policy.term ∧ ∀ other ∈ sections pool,
      Accepted pool other → ¬ Improves (axes pool) (cost pool) choice.policy.term other
  | .blocked _ => ∀ term, ¬ Accepted pool term

def inspect (made : Compilation pool) :
    Check pool (Reviewed pool made.result) := match made.result with
  | .selected choice => verify pool choice.policy.term
  | .blocked rejected => ⟨.isTrue (by
      intro term accepted
      exact (rejected term).result.broken
        ((rows_iff pool term).mpr accepted _ (rejected term).result.listed)),
      (sections pool).flatMap (fun term => (rejected term).work)⟩

structure Receipt (made : Compilation pool) where
  private mk ::
  review : Check pool (Reviewed pool made.result)
  generated : review = inspect pool made

def certify (made : Compilation pool) : Receipt pool made :=
  ⟨inspect pool made,rfl⟩

namespace Receipt
variable {pool} {made : Compilation pool} (receipt : Receipt pool made)
def work : List (Operation pool) := made.work ++ receipt.review.work ++ [.branch receipt.review.value]
def authorized : Bool := match made.result with
  | .selected _ => receipt.review.value
  | .blocked _ => false

theorem review_accepts_its_generated_result : receipt.review.value = true := by
  rw [receipt.generated]
  rcases made with ⟨result,work⟩
  cases result with
  | selected choice =>
    change (verify pool choice.policy.term).value = true
    rw [verify_matches_the_original_independent_verifier]
    exact independent_verifier_accepts _ _
  | blocked rejected => rfl

theorem authorized_matches_the_original_independent_verifier :
    receipt.authorized = Outcome.checked pool (made.result.outcome pool) := by
  rcases made with ⟨result,work⟩
  cases result with
  | selected choice =>
    change receipt.review.value = PublicPolicy.verify pool choice.policy.term
    rw [receipt.review_accepts_its_generated_result,independent_verifier_accepts]
  | blocked _ => rfl
end Receipt



/-- This bound reads source shapes and primitive bounds, never the selector's completed work. -/
def atomBudget : Query pool → Nat
  | .admission policy row => match row with
    | .coherence first second => 1+SignatureWork.Generic.budget ActionWork.budget
        (Policy.Work.cachedShape (.ready (read pool policy first).scope) (read pool policy first).intent)
        (Policy.Work.cachedShape (.ready (read pool policy second).scope) (read pool policy second).intent)
    | .native index coordinate => match coordinate with
      | .present table =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        1+Whole.Materialization.presentBudget branch.scope input.span branch.intent rival+
          Whole.Materialization.presentBudget branch.scope input.span .keep rival+
          NativeAdmission.presentBudget (initial input prepared.saved[index].point)
            (Whole.Materialization.present branch.scope input.span branch.intent rival).value
            (Whole.Materialization.present branch.scope input.span .keep rival).value
      | .future table word =>
        let branch := read pool policy index
        let rival := Comparison.rival pool index table
        1+Whole.Materialization.futureBudget branch.scope input.span branch.intent rival word+
          Whole.Materialization.futureBudget branch.scope input.span .keep rival word+
          NativeAdmission.futureBudget (initial input prepared.saved[index].point)
            (Whole.Materialization.future branch.scope input.span branch.intent rival word).value
            (Whole.Materialization.future branch.scope input.span .keep rival word).value
      | .funding .. => 4
      | .release | .coverage | .deployment => 1
    | .informed | .uniform .. => 1
  | .present new previous index table =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    1+Whole.Materialization.presentBudget left.scope input.span left.intent rival+
      Whole.Materialization.presentBudget right.scope input.span right.intent rival+
      NativeBenefit.presentBudget (initial input prepared.saved[index].point)
        (Whole.Materialization.present left.scope input.span left.intent rival).value
        (Whole.Materialization.present right.scope input.span right.intent rival).value
  | .future new previous index table word =>
    let left := read pool new index
    let right := read pool previous index
    let rival := Comparison.rival pool index table
    1+Whole.Materialization.futureBudget left.scope input.span left.intent rival word+
      Whole.Materialization.futureBudget right.scope input.span right.intent rival word+
      NativeBenefit.futureBudget (initial input prepared.saved[index].point)
        (Whole.Materialization.future left.scope input.span left.intent rival word).value
        (Whole.Materialization.future right.scope input.span right.intent rival word).value
  | .funding .. => 4

theorem atom_work_bound (query : Query pool) : (atom pool query).work.length ≤ atomBudget pool query := by
  cases query with
  | admission policy row =>
    cases row with
    | informed | uniform => exact Nat.le_refl _
    | coherence first second =>
      have bound := SignatureWork.Generic.work_bound ActionWork.compare ActionWork.budget ActionWork.work_bound
        (Policy.Work.cachedShape (.ready (read pool policy first).scope) (read pool policy first).intent)
        (Policy.Work.cachedShape (.ready (read pool policy second).scope) (read pool policy second).intent)
      simpa only [atom,transport,atomBudget,List.length_cons,List.length_map,Nat.add_comm] using Nat.add_le_add_left bound 1
    | native index coordinate =>
      cases coordinate with
      | release | coverage | deployment => exact Nat.le_refl _
      | present table =>
        have a := Whole.Materialization.present_work_bound (read pool policy index).scope input.span (read pool policy index).intent (Comparison.rival pool index table)
        have b := Whole.Materialization.present_work_bound (read pool policy index).scope input.span .keep (Comparison.rival pool index table)
        have c := NativeAdmission.present_work_bound (initial input prepared.saved[index].point)
          (Whole.Materialization.present (read pool policy index).scope input.span (read pool policy index).intent (Comparison.rival pool index table)).value
          (Whole.Materialization.present (read pool policy index).scope input.span .keep (Comparison.rival pool index table)).value
        simp only [atom,atomBudget,NativeBenefit.transport,List.length_append,List.length_map,List.length_singleton]
        omega
      | future table word =>
        have a := Whole.Materialization.future_work_bound (read pool policy index).scope input.span (read pool policy index).intent (Comparison.rival pool index table) word
        have b := Whole.Materialization.future_work_bound (read pool policy index).scope input.span .keep (Comparison.rival pool index table) word
        have c := NativeAdmission.future_work_bound (initial input prepared.saved[index].point)
          (Whole.Materialization.future (read pool policy index).scope input.span (read pool policy index).intent (Comparison.rival pool index table) word).value
          (Whole.Materialization.future (read pool policy index).scope input.span .keep (Comparison.rival pool index table) word).value
        simp only [atom,atomBudget,NativeBenefit.transport,List.length_append,List.length_map,List.length_singleton]
        omega
      | funding table word =>
        have bound := NativeAdmission.funding_work_bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)
          (((read pool policy index).tensor (Comparison.rival pool index table)).funding _ word)
          ((oldTensor index (Comparison.rival pool index table)).funding _ word)
        simp only [atom,atomBudget,List.length_append,List.length_map,List.length_singleton]
        omega
  | present new previous index table =>
    have a := Whole.Materialization.present_work_bound (read pool new index).scope input.span (read pool new index).intent (Comparison.rival pool index table)
    have b := Whole.Materialization.present_work_bound (read pool previous index).scope input.span (read pool previous index).intent (Comparison.rival pool index table)
    have c := NativeBenefit.present_work_bound (initial input prepared.saved[index].point)
      (Whole.Materialization.present (read pool new index).scope input.span (read pool new index).intent (Comparison.rival pool index table)).value
      (Whole.Materialization.present (read pool previous index).scope input.span (read pool previous index).intent (Comparison.rival pool index table)).value
    simp only [atom,atomBudget,NativeBenefit.transport,List.length_append,List.length_map,List.length_singleton]
    omega
  | future new previous index table word =>
    have a := Whole.Materialization.future_work_bound (read pool new index).scope input.span (read pool new index).intent (Comparison.rival pool index table) word
    have b := Whole.Materialization.future_work_bound (read pool previous index).scope input.span (read pool previous index).intent (Comparison.rival pool index table) word
    have c := NativeBenefit.future_work_bound (initial input prepared.saved[index].point)
      (Whole.Materialization.future (read pool new index).scope input.span (read pool new index).intent (Comparison.rival pool index table) word).value
      (Whole.Materialization.future (read pool previous index).scope input.span (read pool previous index).intent (Comparison.rival pool index table) word).value
    simp only [atom,atomBudget,NativeBenefit.transport,List.length_append,List.length_map,List.length_singleton]
    omega
  | funding new previous index table word =>
    have bound := NativeAdmission.funding_work_bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)
      (((read pool new index).tensor (Comparison.rival pool index table)).funding _ word)
      (((read pool previous index).tensor (Comparison.rival pool index table)).funding _ word)
    simp only [atom,atomBudget,List.length_append,List.length_map,List.length_singleton]
    omega

abbrev capabilityWords (index : Index prepared) := Future.Recovery.capabilities
  (initial input prepared.saved[index].point).model (initial input prepared.saved[index].point).depth

def benefitQueries (new previous : Section pool) : List (Query pool) :=
  (keys prepared).flatMap fun index => (Comparison.tables pool index).flatMap fun table =>
    [.present new previous index table] ++ (capabilityWords index).map (.future new previous index table) ++
      (capabilityWords index).map (.funding new previous index table)

def queries : List (Query pool) :=
  (sections pool).flatMap (fun policy => (rows pool).map (.admission policy)) ++
  (sections pool).flatMap (fun new => (sections pool).flatMap (benefitQueries pool new))

def atomCeiling := Policy.Work.ceiling (atomBudget pool) (queries pool)
def tableCeiling := Policy.Work.ceiling (fun index : Index prepared => (Comparison.tables pool index).length) (keys prepared)
def wordCeiling (_pool : Comparison.Pool catalogue) := Policy.Work.ceiling (fun index : Index prepared => (capabilityWords index).length) (keys prepared)
def admissionWorkBudget := (rows pool).length*(atomCeiling pool+1)
def benefitWorkBudget := (keys prepared).length*(tableCeiling pool*(atomCeiling pool+3+2*wordCeiling pool*(atomCeiling pool+1))+1)
def strictWorkBudget := 2*benefitWorkBudget pool+2

private theorem below_source_ceiling {α : Type} (budget : α → Nat) (items : List α) (item : α) (inside : item ∈ items) :
    budget item ≤ Policy.Work.ceiling budget items := by
  induction items with
  | nil => simp at inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst item;exact Nat.le_max_left _ _
    · exact (ih later).trans (Nat.le_max_right _ _)

private theorem admission_query_generated (policy : Section pool) (row : Row pool) (inside : row ∈ rows pool) :
    Query.admission policy row ∈ queries pool :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨policy,every_section_is_generated pool policy,List.mem_map.mpr ⟨row,inside,rfl⟩⟩)
private theorem benefit_query_generated (new previous : Section pool) (index : Index prepared)
    (table : Comparison.Table pool index) (registered : table ∈ Comparison.tables pool index) (query : Query pool)
    (inside : query ∈ [.present new previous index table] ++ (capabilityWords index).map (.future new previous index table) ++
      (capabilityWords index).map (.funding new previous index table)) : query ∈ queries pool :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨new,every_section_is_generated pool new,
    List.mem_flatMap.mpr ⟨previous,every_section_is_generated pool previous,
      List.mem_flatMap.mpr ⟨index,List.mem_finRange _,List.mem_flatMap.mpr ⟨table,registered,inside⟩⟩⟩⟩)

private theorem atom_uniform (query : Query pool) (inside : query ∈ queries pool) :
    (atom pool query).work.length ≤ atomCeiling pool :=
  (atom_work_bound pool query).trans (below_source_ceiling _ _ _ inside)
private theorem conjunction_work_bound {P Q : Prop} (first : Check pool P) (later : Unit → Check pool Q) :
    (conjunction first later).work.length ≤ first.work.length+1+(later ()).work.length := by
  cases h : first.decision <;> simp [conjunction,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem implication_work_bound {P Q : Prop} (first : Check pool P) (later : Unit → Check pool Q) :
    (implication first later).work.length ≤ first.work.length+1+(later ()).work.length := by
  cases h : first.decision <;> simp [implication,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem negative_work_length {P : Prop} (made : Check pool P) :
    (negative made).work.length = made.work.length+1 := by simp [negative]
private theorem allRows_work_bound {α : Type} (P : α → Prop) (test : (item : α) → Check pool (P item))
    (items : List α) (budget : Nat) (bounded : ∀ item ∈ items,(test item).work.length ≤ budget) :
    (allRows P test items).work.length ≤ items.length*(budget+1) := by
  induction items with
  | nil => simp [allRows]
  | cons head tail ih =>
    have step := conjunction_work_bound pool (test head) (fun _ => allRows P test tail)
    have a := bounded head List.mem_cons_self
    have b := ih (fun item inside => bounded item (List.mem_cons_of_mem _ inside))
    change (conjunction (test head) (fun _ => allRows P test tail)).work.length ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem admission_work_bound (policy : Section pool) :
    (accepted pool policy).work.length ≤ admissionWorkBudget pool :=
  allRows_work_bound pool (PublicPolicy.Holds pool policy) (fun row => atom pool (.admission policy row)) (rows pool) _
    (fun row inside => atom_uniform pool _ (admission_query_generated pool policy row inside))

theorem benefit_work_bound (new previous : Section pool) :
    (realBenefit pool new previous).work.length ≤ benefitWorkBudget pool := by
  have each (index : Index prepared) (table : Comparison.Table pool index) (inside : table ∈ Comparison.tables pool index) :
      (conjunction (atom pool (.present new previous index table)) (fun _ =>
        conjunction (allRows _ (fun word => atom pool (.future new previous index table word)) (capabilityWords index)) (fun _ =>
          allRows _ (fun word => atom pool (.funding new previous index table word)) (capabilityWords index)))).work.length ≤
        atomCeiling pool+2+2*wordCeiling pool*(atomCeiling pool+1) := by
    have a := atom_uniform pool (.present new previous index table)
      (benefit_query_generated pool new previous index table inside _ (by simp))
    have b := allRows_work_bound pool _ (fun word => atom pool (.future new previous index table word)) (capabilityWords index)
      (atomCeiling pool) (fun word registered => atom_uniform pool _
        (benefit_query_generated pool new previous index table inside _ (by simp [registered])))
    have c := allRows_work_bound pool _ (fun word => atom pool (.funding new previous index table word)) (capabilityWords index)
      (atomCeiling pool) (fun word registered => atom_uniform pool _
        (benefit_query_generated pool new previous index table inside _ (by simp [registered])))
    have step := conjunction_work_bound pool (atom pool (.present new previous index table)) (fun _ =>
      conjunction (allRows _ (fun word => atom pool (.future new previous index table word)) (capabilityWords index)) (fun _ =>
        allRows _ (fun word => atom pool (.funding new previous index table word)) (capabilityWords index)))
    have nested := conjunction_work_bound pool
      (allRows _ (fun word => atom pool (.future new previous index table word)) (capabilityWords index)) (fun _ =>
        allRows _ (fun word => atom pool (.funding new previous index table word)) (capabilityWords index))
    have wordsBound := Nat.mul_le_mul_right (atomCeiling pool+1)
      (below_source_ceiling (fun i : Index prepared => (capabilityWords i).length) (keys prepared) index (List.mem_finRange _))
    change (capabilityWords index).length*(atomCeiling pool+1) ≤ wordCeiling pool*(atomCeiling pool+1) at wordsBound
    simp only [Nat.mul_assoc]
    omega
  have tablesBound (index : Index prepared) :
      (allRows _ (fun table => conjunction (atom pool (.present new previous index table)) (fun _ =>
        conjunction (allRows _ (fun word => atom pool (.future new previous index table word)) (capabilityWords index)) (fun _ =>
          allRows _ (fun word => atom pool (.funding new previous index table word)) (capabilityWords index))))
        (Comparison.tables pool index)).work.length ≤
      tableCeiling pool*(atomCeiling pool+3+2*wordCeiling pool*(atomCeiling pool+1)) := by
    have bound := allRows_work_bound pool _ _ (Comparison.tables pool index) _ (each index)
    have size := Nat.mul_le_mul_right (atomCeiling pool+3+2*wordCeiling pool*(atomCeiling pool+1))
      (below_source_ceiling (fun i : Index prepared => (Comparison.tables pool i).length) (keys prepared) index (List.mem_finRange _))
    change (Comparison.tables pool index).length*_ ≤ tableCeiling pool*_ at size
    have arithmetic : atomCeiling pool+2+2*wordCeiling pool*(atomCeiling pool+1)+1 =
        atomCeiling pool+3+2*wordCeiling pool*(atomCeiling pool+1) := by omega
    rw [arithmetic] at bound
    exact bound.trans size
  exact allRows_work_bound pool _ _ (keys prepared) _ (fun index _ => tablesBound index)

private theorem strict_work_bound (previous new : Section pool) :
    (strict pool previous new).work.length ≤ strictWorkBudget pool := by
  have a := benefit_work_bound pool new previous
  have b := benefit_work_bound pool previous new
  have step := conjunction_work_bound pool (realBenefit pool new previous) (fun _ => negative (realBenefit pool previous new))
  rw [negative_work_length] at step
  unfold strict strictWorkBudget
  omega
private theorem collect_work_bound (items : List (Section pool)) :
    (collect pool items).work.length ≤ items.length*(admissionWorkBudget pool+1) := by
  induction items with
  | nil => simp [collect]
  | cons head tail ih =>
    have bound := admission_work_bound pool head
    cases h : (accepted pool head).decision <;>
      simp only [collect,h,List.length_append,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at * <;> omega
private theorem scan_work_bound (first : Candidate pool) (remaining : List (Candidate pool)) :
    (scan first remaining).work.length ≤ remaining.length*(strictWorkBudget pool+1) := by
  induction remaining generalizing first with
  | nil => simp [scan]
  | cons head tail ih =>
    have bound := strict_work_bound pool first.term head.term
    have a := ih head
    have b := ih first
    cases h : (strict pool first.term head.term).decision <;>
      simp only [scan,h,List.length_append,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at * <;> omega
private theorem reject_work_bound (policy : Section pool) (items : List (Row pool))
    (inside : ∀ row ∈ items,row ∈ rows pool) (invalid : ¬ ∀ row ∈ items,PublicPolicy.Holds pool policy row) :
    (reject pool policy items inside invalid).work.length ≤ items.length*(atomCeiling pool+1) := by
  induction items with
  | nil => exact False.elim (invalid (by simp))
  | cons head tail ih =>
    have bound := atom_uniform pool _ (admission_query_generated pool policy head (inside head List.mem_cons_self))
    cases h : (atom pool (.admission policy head)).decision with
    | isFalse broken =>
      simp only [reject,h,List.length_append,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]
      omega
    | isTrue holds =>
      have later := ih (fun row member => inside row (List.mem_cons_of_mem _ member)) (fun all => invalid (by
        intro row member
        rcases List.mem_cons.mp member with equal | rest
        · subst row;exact holds
        · exact all row rest))
      simp only [reject,h,List.length_append,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]
      omega

def verificationBudget := admissionWorkBudget pool+1+
  (sections pool).length*(admissionWorkBudget pool+strictWorkBudget pool+3)
theorem verification_work_bound (policy : Section pool) :
    (verify pool policy).work.length ≤ verificationBudget pool := by
  have initial := admission_work_bound pool policy
  have each (other : Section pool) :
      (implication (accepted pool other) (fun _ => negative (transport (strict_iff pool policy other) (strict pool policy other)))).work.length ≤
        admissionWorkBudget pool+strictWorkBudget pool+2 := by
    have entry := admission_work_bound pool other
    have comparison := strict_work_bound pool policy other
    have step := implication_work_bound pool (accepted pool other)
      (fun _ => negative (transport (strict_iff pool policy other) (strict pool policy other)))
    rw [negative_work_length] at step
    change _ ≤ _+1+((strict pool policy other).work.length+1) at step
    omega
  have all := allRows_work_bound pool _ _ (sections pool) _ (fun other _ => each other)
  have whole := conjunction_work_bound pool (accepted pool policy) (fun _ =>
    allRows _ (fun other => implication (accepted pool other)
      (fun _ => negative (transport (strict_iff pool policy other) (strict pool policy other)))) (sections pool))
  change _ ≤ (sections pool).length*(admissionWorkBudget pool+strictWorkBudget pool+2+1) at all
  have arithmetic : admissionWorkBudget pool+strictWorkBudget pool+2+1 = admissionWorkBudget pool+strictWorkBudget pool+3 := by omega
  rw [arithmetic] at all
  unfold verify verificationBudget
  omega

private theorem flatMap_work_bound {α : Type} (items : List α) (work : α → List (Operation pool)) (budget : Nat)
    (bounded : ∀ item ∈ items,(work item).length ≤ budget) : (items.flatMap work).length ≤ items.length*budget := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    have a := bounded head List.mem_cons_self
    have b := ih (fun item inside => bounded item (List.mem_cons_of_mem _ inside))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def checkedWork (made : Compilation pool) := made.work ++ (inspect pool made).work
def workBudget :=
  (sections pool).length*(admissionWorkBudget pool+1) +
  (sections pool).length*(strictWorkBudget pool+1) + verificationBudget pool +
  (sections pool).length*admissionWorkBudget pool+1

theorem ordered_complete_work_fits_the_source_budget (order : List (Section pool)) (complete : order.Perm (sections pool)) :
    (checkedWork pool (compileOrdered pool order complete)).length+1 ≤ workBudget pool := by
  have collected := collect_work_bound pool order
  rw [complete.length_eq] at collected
  have number : (collect pool order).accepted.length ≤ (sections pool).length := by
    rw [(collect pool order).exact]
    exact (List.length_filterMap_le _ _).trans (Nat.le_of_eq complete.length_eq)
  dsimp only [compileOrdered]
  split
  · rename_i same
    simp only [checkedWork,inspect,List.length_append]
    have reports := flatMap_work_bound (pool := pool) (sections pool) _ (admissionWorkBudget pool)
      (fun policy _ => reject_work_bound pool policy (rows pool) (fun _ member => member) (fun all => by
        obtain ⟨candidate,member,_⟩ := every_accepted_section_is_generated pool policy ((rows_iff pool policy).mp all)
        have members : (collect pool order).accepted.Perm (candidates pool) := by
          rw [(collect pool order).exact];exact complete.filterMap _
        have inside := members.mem_iff.mpr member
        rw [same] at inside
        exact List.not_mem_nil inside))
    unfold workBudget
    omega
  · rename_i head tail same
    have scanned := scan_work_bound pool head tail
    have verified := verification_work_bound pool (scan head tail).policy.term
    simp only [checkedWork,inspect,List.length_append]
    rw [same,List.length_cons] at number
    unfold workBudget
    have size : tail.length*(strictWorkBudget pool+1) ≤ (sections pool).length*(strictWorkBudget pool+1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem receipt_work_fits_the_source_budget (order : List (Section pool)) (complete : order.Perm (sections pool))
    (receipt : Receipt pool (compileOrdered pool order complete)) : receipt.work.length ≤ workBudget pool := by
  have bound := ordered_complete_work_fits_the_source_budget pool order complete
  rw [Receipt.work,receipt.generated]
  simpa only [checkedWork,List.length_append,List.length_singleton] using bound

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Work
