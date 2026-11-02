import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Materialization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Work
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
open Decision
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} {cursor : Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {baseReference : Term cursor} {actor : Party} {position : Nat}
  (scope : Scope cursor pricing n baseReference actor position) (span : Nat)

/-- Native evaluation is an explicit outstanding computation, never a unit-Decision.cost CPU oracle. -/
inductive Query where
  | admission (reference term : Intent scope) (row : Decision.Row scope)
  | presentBenefit (new previous : Intent scope) (table : Table scope)
  | futureBenefit (new previous : Intent scope) (table : Table scope) (word : List (Future.Recovery.Action cursor.model))
  | funding (new previous : Intent scope) (table : Table scope) (word : List (Future.Recovery.Action cursor.model))

def Query.Holds : Query scope → Prop
  | .admission reference term row => Decision.Holds scope span reference term row
  | .presentBenefit new previous table => evaluationBenefit cursor
      (tensor scope span new (opponent scope table)).present
      (tensor scope span previous (opponent scope table)).present
  | .futureBenefit new previous table word => Planning.futureBenefit cursor
      ((tensor scope span new (opponent scope table)).future cursor word)
      ((tensor scope span previous (opponent scope table)).future cursor word)
  | .funding new previous table word =>
      ((tensor scope span previous (opponent scope table)).funding cursor word).isNone = true →
      ((tensor scope span new (opponent scope table)).funding cursor word).isNone = true
instance (query : Query scope) : Decidable (query.Holds scope span) := by
  cases query <;> unfold Query.Holds <;> infer_instance

inductive Operation where
  | frameConstruction (event : NativeSourceFrames.Event)
  | profileConstruction (event : NativeProfile.Event Party Good Port Technology Instrument)
  | manifestConstruction (event : NativeManifest.Event Party Good Port Technology Instrument)
  | native (query : Query scope) (answer : Bool)
  | branch (answer : Bool)
  | negate (answer : Bool)
  | retain (accepted : Bool)
  | select (replaced : Bool)
  | comparison (event : NativeBenefit.Event (NativeBenefit.WorkKey (Party := Party) (Good := Good)
      (Port := Port) (Technology := Technology) (Instrument := Instrument)))

  | admissionComparison (event : NativeBenefit.Event (NativeAdmission.Key (Party := Party) (Good := Good)
      (Port := Port) (Technology := Technology) (Instrument := Instrument)))

def Operation.sourceConstruction : NativeTensor.Event Party Good Port Technology Instrument → Operation scope
  | .source event => .frameConstruction event
  | .profile event => .profileConstruction event
  | .manifest event => .manifestConstruction event

structure Check (P : Prop) where
  private mk ::
  decision : Decidable P
  work : List (Operation scope)

def Check.value {P : Prop} (made : Check scope P) : Bool := @decide P made.decision

def atom (query : Query scope) : Check scope (query.Holds scope span) :=
  match query with
  | .presentBenefit new previous table =>
      let current := Materialization.present scope span new (opponent scope table)
      let original := Materialization.present scope span previous (opponent scope table)
      let compared := NativeBenefit.transport (show _ ↔ Query.Holds scope span (.presentBenefit new previous table) from by
        rw [Materialization.present_exact,Materialization.present_exact];rfl)
        (NativeBenefit.present cursor current.value original.value)
      ⟨compared.decision,[.native (.presentBenefit new previous table) compared.value] ++
        (current.work++original.work).map (Operation.sourceConstruction scope) ++ compared.work.map Operation.comparison⟩
  | .futureBenefit new previous table word =>
      let current := Materialization.future scope span new (opponent scope table) word
      let original := Materialization.future scope span previous (opponent scope table) word
      let compared := NativeBenefit.transport (show _ ↔ Query.Holds scope span (.futureBenefit new previous table word) from by
        rw [Materialization.future_exact,Materialization.future_exact];rfl)
        (NativeBenefit.future cursor current.value original.value)
      ⟨compared.decision,[.native (.futureBenefit new previous table word) compared.value] ++
        (current.work++original.work).map (Operation.sourceConstruction scope) ++ compared.work.map Operation.comparison⟩
  | .admission reference term row => match row with
    | .deployment =>
        ⟨inferInstance,[.native (.admission reference term .deployment) (decide (Deployable scope term)),
          .branch (decide (Deployable scope term))]⟩
    | .present table =>
        let current := Materialization.present scope span term (opponent scope table)
        let original := Materialization.present scope span reference (opponent scope table)
        let compared := NativeBenefit.transport (show _ ↔ Query.Holds scope span (.admission reference term (.present table)) from by
          rw [Materialization.present_exact,Materialization.present_exact];rfl)
          (NativeAdmission.present cursor current.value original.value)
        ⟨compared.decision,[.native (.admission reference term (.present table)) compared.value] ++
          (current.work++original.work).map (Operation.sourceConstruction scope) ++ compared.work.map Operation.admissionComparison⟩
    | .future table word =>
        let current := Materialization.future scope span term (opponent scope table) word
        let original := Materialization.future scope span reference (opponent scope table) word
        let compared := NativeBenefit.transport (show _ ↔ Query.Holds scope span (.admission reference term (.future table word)) from by
          rw [Materialization.future_exact,Materialization.future_exact];rfl)
          (NativeAdmission.future cursor current.value original.value)
        ⟨compared.decision,[.native (.admission reference term (.future table word)) compared.value] ++
          (current.work++original.work).map (Operation.sourceConstruction scope) ++ compared.work.map Operation.admissionComparison⟩
    | .funding table word =>
        let compared := NativeAdmission.funding
          ((tensor scope span term (opponent scope table)).funding cursor word)
          ((tensor scope span reference (opponent scope table)).funding cursor word)
        ⟨compared.decision,[.native (.admission reference term (.funding table word)) compared.value] ++
          compared.work.map Operation.admissionComparison⟩
  | .funding new previous table word =>
      let compared := NativeAdmission.funding
        ((tensor scope span new (opponent scope table)).funding cursor word)
        ((tensor scope span previous (opponent scope table)).funding cursor word)
      ⟨compared.decision,[.native (.funding new previous table word) compared.value] ++
        compared.work.map Operation.admissionComparison⟩

variable {scope span}
def transport {P Q : Prop} (equivalent : P ↔ Q) (made : Check scope P) : Check scope Q :=
  ⟨match made.decision with
    | .isTrue yes => .isTrue (equivalent.mp yes)
    | .isFalse no => .isFalse (fun yes => no (equivalent.mpr yes)),made.work⟩

def conjunction {P Q : Prop} (first : Check scope P) (later : Unit → Check scope Q) : Check scope (P ∧ Q) :=
  match first.decision with
  | .isFalse no => ⟨.isFalse (fun yes => no yes.1),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun both => no both.2)
      | .isTrue other => .isTrue ⟨yes,other⟩,first.work ++ [.branch true] ++ second.work⟩

def negative {P : Prop} (made : Check scope P) : Check scope (¬ P) :=
  ⟨match made.decision with
    | .isTrue yes => .isFalse (fun no => no yes)
    | .isFalse no => .isTrue no,made.work ++ [.negate made.value]⟩

def implication {P Q : Prop} (first : Check scope P) (later : Unit → Check scope Q) : Check scope (P → Q) :=
  match first.decision with
  | .isFalse no => ⟨.isTrue (fun yes => False.elim (no yes)),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun accepts => no (accepts yes))
      | .isTrue other => .isTrue (fun _ => other),first.work ++ [.branch true] ++ second.work⟩

def allRows {α : Type} (P : α → Prop) (test : (a : α) → Check scope (P a)) :
    (items : List α) → Check scope (∀ a ∈ items,P a)
  | [] => ⟨.isTrue (by simp),[]⟩
  | head::tail => transport (by simp only [List.mem_cons,forall_eq_or_imp])
      (conjunction (test head) (fun _ => allRows P test tail))

variable (scope span)
def noWorse (new previous : Intent scope) : Check scope (Decision.NoWorse scope span new previous) :=
  transport (Decision.rows_iff scope span previous new)
    (allRows (Decision.Holds scope span previous new)
      (fun row => atom scope span (.admission previous new row)) (Decision.rows scope))

def realBenefit (new previous : Intent scope) : Check scope (Decision.Benefit scope span new previous) :=
  allRows (fun table => benefit cursor (tensor scope span new (opponent scope table))
      (tensor scope span previous (opponent scope table)))
    (fun table => conjunction (atom scope span (.presentBenefit new previous table)) (fun _ =>
      conjunction (allRows (fun word => Planning.futureBenefit cursor
          ((tensor scope span new (opponent scope table)).future cursor word)
          ((tensor scope span previous (opponent scope table)).future cursor word))
        (fun word => atom scope span (.futureBenefit new previous table word))
        (Future.Recovery.capabilities cursor.model cursor.depth)) (fun _ =>
        allRows (fun word =>
          ((tensor scope span previous (opponent scope table)).funding cursor word).isNone = true →
          ((tensor scope span new (opponent scope table)).funding cursor word).isNone = true)
          (fun word => atom scope span (.funding new previous table word))
          (Future.Recovery.capabilities cursor.model cursor.depth)))) (tables scope)

def strict (previous new : Intent scope) : Check scope (Decision.strictBenefit scope span previous new) :=
  conjunction (realBenefit scope span new previous) (fun _ => negative (realBenefit scope span previous new))

structure Pool (reference : Intent scope) (items : List (Intent scope)) where
  private mk ::
  accepted : List (Decision.Candidate scope span reference)
  exact : accepted = items.filterMap (Decision.check scope span reference)
  work : List (Operation scope)

def collect (reference : Intent scope) : (items : List (Intent scope)) → Pool scope span reference items
  | [] => ⟨[],rfl,[]⟩
  | head::tail =>
    let checked := noWorse scope span head reference
    let rest := collect reference tail
    match checked.decision with
    | .isTrue accepted =>
      ⟨⟨head,accepted⟩::rest.accepted,by simp only [List.filterMap_cons,Decision.check,dif_pos accepted];rw [rest.exact],
        checked.work ++ [.retain true] ++ rest.work⟩
    | .isFalse rejected =>
      ⟨rest.accepted,by simp only [List.filterMap_cons,Decision.check,dif_neg rejected];exact rest.exact,
        checked.work ++ [.retain false] ++ rest.work⟩

private theorem strict_irrefl (term : Intent scope) : ¬ Decision.strictBenefit scope span term term := fun both => both.2 both.1
private theorem strict_trans {first middle last : Intent scope}
    (a : Decision.strictBenefit scope span first middle) (b : Decision.strictBenefit scope span middle last) :
    Decision.strictBenefit scope span first last :=
  ⟨fun table inside => benefit_trans cursor (b.1 table inside) (a.1 table inside),
    fun reverse => a.2 (fun table inside => benefit_trans cursor (reverse table inside) (b.1 table inside))⟩

private structure Scan {reference : Intent scope} (first : Decision.Candidate scope span reference)
    (remaining : List (Decision.Candidate scope span reference)) where
  policy : Decision.Candidate scope span reference
  original : policy = first ∨ policy ∈ remaining
  advances : policy = first ∨ Decision.strictBenefit scope span first.term policy.term
  maximal : ∀ other ∈ remaining, ¬ Decision.strictBenefit scope span policy.term other.term
  work : List (Operation scope)

variable {scope span}
private theorem no_reverse {reference : Intent scope} {first : Decision.Candidate scope span reference}
    {remaining : List (Decision.Candidate scope span reference)} (made : Scan scope span first remaining) :
    ¬ Decision.strictBenefit scope span made.policy.term first.term := by
  intro backwards
  rcases made.advances with same | forward
  · apply strict_irrefl scope span first.term
    simpa only [same] using backwards
  · exact strict_irrefl scope span first.term (strict_trans scope span forward backwards)

private def scan {reference : Intent scope} (first : Decision.Candidate scope span reference) :
    (remaining : List (Decision.Candidate scope span reference)) → Scan scope span first remaining
  | [] => ⟨first,.inl rfl,.inl rfl,by simp,[]⟩
  | head::tail =>
    let checked := strict scope span first.term head.term
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
          · exact strict_trans scope span better further),by
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
            · exact notBetter (strict_trans scope span forward backwards)
          · exact rest.maximal other later,checked.work ++ [.select false] ++ rest.work⟩

variable (scope span)
structure Rejected (reference term : Intent scope) where
  private mk ::
  result : Decision.Rejection scope span reference term
  work : List (Operation scope)

private def reject (reference term : Intent scope) :
    (items : List (Decision.Row scope)) → (inside : ∀ row ∈ items,row ∈ Decision.rows scope) →
    (invalid : ¬ ∀ row ∈ items,Decision.Holds scope span reference term row) → Rejected scope span reference term
  | [],_,invalid => False.elim (invalid (by simp))
  | head::tail,inside,invalid =>
    let checked := atom scope span (.admission reference term head)
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

inductive Result (reference : Intent scope) where
  | selected (choice : Decision.Choice scope span reference)
  | blocked (rejected : (term : Intent scope) → Rejected scope span reference term)

structure Compilation (reference : Intent scope) where
  private mk ::
  result : Result scope span reference
  work : List (Operation scope)

def compileOrdered (reference : Intent scope) (order : List (Intent scope))
    (complete : order.Perm (intents scope)) : Compilation scope span reference :=
  let pool := collect scope span reference order
  have members : pool.accepted.Perm (Decision.candidates scope span reference) := by
    rw [pool.exact]
    exact complete.filterMap _
  match same : pool.accepted with
  | [] => ⟨.blocked (fun term => reject scope span reference term (Decision.rows scope) (fun _ member => member)
      (fun all => by
        obtain ⟨candidate,member,_⟩ := Decision.every_accepted_term_is_generated scope span reference term
          ((Decision.rows_iff scope span reference term).mp all)
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
      have strict := (Decision.strictBenefit_iff scope span _ _).mpr improves
      have inside := members.mem_iff.mpr member
      rw [same] at inside
      rcases List.mem_cons.mp inside with same | later
      · subst other;exact no_reverse found strict
      · exact found.maximal other later strict⟩,pool.work ++ found.work⟩

def compile (reference : Intent scope) : Compilation scope span reference :=
  compileOrdered scope span reference (intents scope) (List.Perm.refl _)

def fundedOrder : List (Intent scope) := (continuations scope).map Intent.paid ++ [.keep]
theorem fundedOrder_complete : (fundedOrder scope).Perm (intents scope) := by
  unfold fundedOrder intents
  exact List.perm_append_comm

def compileFunded : Compilation scope span .keep :=
  compileOrdered scope span .keep (fundedOrder scope) (fundedOrder_complete scope)

theorem a_kept_funded_choice_excludes_every_acceptable_paid_continuation
    (choice : Decision.Choice scope span .keep)
    (selected : (compileFunded scope span).result = .selected choice)
    (kept : choice.policy.term = .keep) (term : Continuation scope) :
    ¬ Decision.NoWorse scope span (.paid term) .keep := by
  intro accepted
  let paidTerms := (continuations scope).map (Intent.paid (scope := scope))
  let paidPool := paidTerms.filterMap (Decision.check scope span .keep)
  have member : (⟨.paid term,accepted⟩ : Decision.Candidate scope span .keep) ∈ paidPool :=
    List.mem_filterMap.mpr ⟨.paid term,List.mem_map.mpr ⟨term,every_continuation_is_generated scope _,rfl⟩,by
      simp only [Decision.check,dif_pos accepted]⟩
  have typed (candidate : Decision.Candidate scope span .keep) (inside : candidate ∈ paidPool) :
      ∃ paid, candidate.term = .paid paid := by
    obtain ⟨intent,generated,checked⟩ := List.mem_filterMap.mp inside
    obtain ⟨paid,_,same⟩ := List.mem_map.mp generated
    cases same
    unfold Decision.check at checked
    split at checked
    · exact ⟨paid,(congrArg (fun candidate : Decision.Candidate scope span .keep => candidate.term)
        (Option.some.inj checked)).symm⟩
    · contradiction
  have pool : (collect scope span .keep (fundedOrder scope)).accepted =
      paidPool ++ [.keep].filterMap (Decision.check scope span .keep) := by
    rw [(collect scope span .keep (fundedOrder scope)).exact]
    exact List.filterMap_append
  cases original : paidPool with
  | nil => rw [original] at member;exact List.not_mem_nil member
  | cons head tail =>
    have inside : head ∈ paidPool := by rw [original];exact List.mem_cons_self
    obtain ⟨paid,headPaid⟩ := typed head inside
    rw [original,List.cons_append] at pool
    unfold compileFunded compileOrdered at selected
    dsimp only at selected
    split at selected
    · rename_i empty
      rw [pool] at empty
      contradiction
    · rename_i first rest found
      have equality := List.cons.inj (found.symm.trans pool)
      have firstEq : first = head := equality.1
      have restEq : rest = tail ++ [.keep].filterMap (Decision.check scope span .keep) := equality.2
      subst first
      subst rest
      have policy := congrArg (fun selected : Decision.Choice scope span .keep => selected.policy.term)
        (Result.selected.inj selected)
      have same : (scan head (tail ++ [.keep].filterMap (Decision.check scope span .keep))).policy.term = .keep :=
        policy.trans kept
      rcases (scan head (tail ++ [.keep].filterMap (Decision.check scope span .keep))).advances with unchanged | forward
      · have impossible : head.term = .keep := by rw [←unchanged];exact same
        rw [headPaid] at impossible
        cases impossible
      · rw [same] at forward
        exact forward.2 (Decision.no_worse_bounds_real_benefit scope span head.no_regression)

/-- A separate executable pass uses the same primitive evaluator and records its own work. -/
def verify (reference term : Intent scope) : Check scope
    (Decision.NoWorse scope span term reference ∧
      ∀ other ∈ intents scope,Decision.NoWorse scope span other reference → ¬ Decision.strictBenefit scope span term other) :=
  conjunction (noWorse scope span term reference) (fun _ =>
    allRows (fun other => Decision.NoWorse scope span other reference → ¬ Decision.strictBenefit scope span term other)
      (fun other => implication (noWorse scope span other reference)
        (fun _ => negative (strict scope span term other))) (intents scope))

theorem verify_matches_the_original_independent_verifier (reference term : Intent scope) :
    (verify scope span reference term).value = Decision.verify scope span reference term := by
  unfold Check.value Decision.verify
  exact Subsingleton.elim _ _ |> fun same => congrArg (fun d => @decide _ d) same

def checkedWork {reference : Intent scope} (made : Compilation scope span reference) : List (Operation scope) :=
  made.work ++ match made.result with
    | .selected choice => (verify scope span reference choice.policy.term).work
    | .blocked rejected => (intents scope).flatMap (fun term => (rejected term).work)

/-- The review checks a selected policy or preserves every generated rejection. -/
def Reviewed {reference : Intent scope} : Result scope span reference → Prop
  | .selected choice => Decision.NoWorse scope span choice.policy.term reference ∧
      ∀ other ∈ intents scope,Decision.NoWorse scope span other reference →
        ¬ Decision.strictBenefit scope span choice.policy.term other
  | .blocked _ => ∀ term, ¬ Decision.NoWorse scope span term reference

def inspect {reference : Intent scope} (made : Compilation scope span reference) :
    Check scope (Reviewed scope span made.result) := match made.result with
  | .selected choice => verify scope span reference choice.policy.term
  | .blocked rejected => ⟨.isTrue (by
      intro term accepted
      exact (rejected term).result.broken
        ((Decision.rows_iff scope span reference term).mpr accepted _ (rejected term).result.original)),
      (intents scope).flatMap (fun term => (rejected term).work)⟩

structure Receipt {reference : Intent scope} (made : Compilation scope span reference) where
  private mk ::
  review : Check scope (Reviewed scope span made.result)
  generated : review = inspect scope span made

def certify {reference : Intent scope} (made : Compilation scope span reference) : Receipt scope span made :=
  ⟨inspect scope span made,rfl⟩

namespace Receipt
variable {scope span} {reference : Intent scope} {made : Compilation scope span reference}
  (receipt : Receipt scope span made)

def comparisonWork : List (Operation scope) := made.work ++ receipt.review.work

/-- The release gate reads the cached check; it never invokes a second solver or verifier. -/
def authorized : Option (Decision.Choice scope span reference) :=
  if receipt.review.value then match made.result with
    | .selected choice => some choice
    | .blocked _ => none
  else none

def work : List (Operation scope) := receipt.comparisonWork ++ [.branch receipt.review.value]

theorem comparisonWork_exact : receipt.comparisonWork = checkedWork scope span made := by
  rw [comparisonWork,receipt.generated]
  rcases made with ⟨result,work⟩
  cases result <;> rfl

theorem review_accepts_its_generated_result : receipt.review.value = true := by
  rw [receipt.generated]
  rcases made with ⟨result,work⟩
  cases result with
  | selected choice =>
      change (verify scope span reference choice.policy.term).value = true
      rw [verify_matches_the_original_independent_verifier]
      exact Decision.independent_replay_accepts_selection _ _ _ _
  | blocked rejected => rfl

theorem authorized_exact : receipt.authorized = match made.result with
    | .selected choice => some choice | .blocked _ => none := by
  simp only [authorized,receipt.review_accepts_its_generated_result,if_true]

end Receipt

def nativeObligations (work : List (Operation scope)) : List (Query scope) := work.filterMap fun operation =>
  match operation with | .native query _ => some query | _ => none

def controlSteps (work : List (Operation scope)) : Nat := (work.filter fun operation =>
  match operation with | .native .. => false | _ => true).length

theorem all_work_is_either_a_primitive_control_or_an_explicit_native_obligation (work : List (Operation scope)) :
    work.length = controlSteps scope work + (nativeObligations scope work).length := by
  induction work with
  | nil => rfl
  | cons head tail ih => cases head <;> simp only [controlSteps,nativeObligations,List.filter_cons,List.filterMap_cons,
      List.length_cons,Bool.false_eq_true,if_false,if_true] at * <;> omega

variable {scope span}
theorem controlSteps_append (left right : List (Operation scope)) :
    controlSteps scope (left++right) = controlSteps scope left+controlSteps scope right := by
  simp only [controlSteps,List.filter_append,List.length_append]
private theorem conjunction_cost {P Q : Prop} (first : Check scope P) (later : Unit → Check scope Q) :
    controlSteps scope (conjunction first later).work ≤
      controlSteps scope first.work+1+controlSteps scope (later ()).work := by
  cases h : first.decision <;> simp [conjunction,h,controlSteps,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem implication_cost {P Q : Prop} (first : Check scope P) (later : Unit → Check scope Q) :
    controlSteps scope (implication first later).work ≤
      controlSteps scope first.work+1+controlSteps scope (later ()).work := by
  cases h : first.decision <;> simp [implication,h,controlSteps,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem negative_cost {P : Prop} (made : Check scope P) :
    controlSteps scope (negative made).work = controlSteps scope made.work+1 := by
  simp [negative,controlSteps]
private theorem allRows_cost {α : Type} (P : α → Prop) (test : (item : α) → Check scope (P item))
    (budget : α → Nat) (bounded : ∀ item,controlSteps scope (test item).work ≤ budget item) (items : List α) :
    controlSteps scope (allRows P test items).work ≤ (items.map (fun item => budget item+1)).sum := by
  induction items with
  | nil => simp [allRows,controlSteps]
  | cons head tail ih =>
    have step := conjunction_cost (test head) (fun _ => allRows P test tail)
    change controlSteps scope (conjunction (test head) (fun _ => allRows P test tail)).work ≤ _
    simp only [List.map_cons,List.sum_cons]
    have headBound := bounded head
    exact step.trans (by omega)
private theorem comparison_cost (events : List (NativeBenefit.Event
    (NativeBenefit.WorkKey (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))) :
    controlSteps scope (events.map Operation.comparison) = events.length := by
  induction events with
  | nil => rfl
  | cons head tail ih => simpa [controlSteps] using congrArg Nat.succ ih

private def ceiling {α : Type} (budget : α → Nat) : List α → Nat
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

variable (scope span)
private theorem admission_comparison_cost (events : List (NativeBenefit.Event
    (NativeAdmission.Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))) :
    controlSteps scope (events.map Operation.admissionComparison) = events.length := by
  induction events with
  | nil => rfl
  | cons head tail ih => simpa [controlSteps] using congrArg Nat.succ ih

private theorem profile_construction_cost (events : List (NativeTensor.Event Party Good Port Technology Instrument)) :
    controlSteps scope (events.map (Operation.sourceConstruction scope)) = events.length := by
  induction events with
  | nil => rfl
  | cons head tail ih => cases head <;> simpa [controlSteps,Operation.sourceConstruction] using congrArg Nat.succ ih

def sourcePresentBudget (new previous : Intent scope) (table : Table scope) :=
  Materialization.presentBudget scope span new (opponent scope table) + Materialization.presentBudget scope span previous (opponent scope table)
def sourceFutureBudget (new previous : Intent scope) (table : Table scope) (word : List (Future.Recovery.Action cursor.model)) :=
  Materialization.futureBudget scope span new (opponent scope table) word + Materialization.futureBudget scope span previous (opponent scope table) word

def presentAtomBudget (new previous : Intent scope) (table : Table scope) :=
  sourcePresentBudget scope span new previous table + NativeBenefit.presentBudget cursor
    (tensor scope span new (opponent scope table)).present (tensor scope span previous (opponent scope table)).present

def futureAtomBudget (new previous : Intent scope) (table : Table scope) (word : List (Future.Recovery.Action cursor.model)) :=
  sourceFutureBudget scope span new previous table word + NativeBenefit.futureBudget cursor
    ((tensor scope span new (opponent scope table)).future cursor word) ((tensor scope span previous (opponent scope table)).future cursor word)

def admissionBudget (reference term : Intent scope) : Decision.Row scope → Nat
  | .deployment => 1
  | .present table => sourcePresentBudget scope span term reference table + NativeAdmission.presentBudget cursor
      (tensor scope span term (opponent scope table)).present (tensor scope span reference (opponent scope table)).present
  | .future table word => sourceFutureBudget scope span term reference table word + NativeAdmission.futureBudget cursor
      ((tensor scope span term (opponent scope table)).future cursor word) ((tensor scope span reference (opponent scope table)).future cursor word)
  | .funding _ _ => 3

private theorem admission_cost (reference term : Intent scope) (row : Decision.Row scope) :
    controlSteps scope (atom scope span (.admission reference term row)).work ≤ admissionBudget scope span reference term row := by
  cases row with
  | deployment => simp [atom,controlSteps,admissionBudget]
  | present table =>
    have a := Materialization.present_work_bound scope span term (opponent scope table)
    have b := Materialization.present_work_bound scope span reference (opponent scope table)
    have c := NativeAdmission.present_work_bound cursor
      (Materialization.present scope span term (opponent scope table)).value (Materialization.present scope span reference (opponent scope table)).value
    simp only [Materialization.present_exact] at c
    simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,admission_comparison_cost,List.length_append]
    change 0+_+_ ≤ _
    unfold admissionBudget sourcePresentBudget
    exact Nat.add_le_add (by omega) (by simpa only [Materialization.present_exact,tensor] using c)
  | future table word =>
    have a := Materialization.future_work_bound scope span term (opponent scope table) word
    have b := Materialization.future_work_bound scope span reference (opponent scope table) word
    have c := NativeAdmission.future_work_bound cursor
      (Materialization.future scope span term (opponent scope table) word).value (Materialization.future scope span reference (opponent scope table) word).value
    simp only [Materialization.future_exact] at c
    simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,admission_comparison_cost,List.length_append]
    change 0+_+_ ≤ _
    unfold admissionBudget sourceFutureBudget
    exact Nat.add_le_add (by omega) (by simpa only [Materialization.future_exact,tensor,Tensor.future] using c)
  | funding table word =>
    change controlSteps scope ([Operation.native _ _] ++ _) ≤ _
    rw [controlSteps_append,admission_comparison_cost]
    change 0+_ ≤ _
    simp only [Nat.zero_add]
    exact NativeAdmission.funding_work_bound _ _

private theorem funding_cost (new previous : Intent scope) (table : Table scope) (word) :
    controlSteps scope (atom scope span (.funding new previous table word)).work ≤ 3 := by
  change controlSteps scope ([Operation.native _ _] ++ _) ≤ _
  rw [controlSteps_append,admission_comparison_cost]
  change 0+_ ≤ _
  simp only [Nat.zero_add]
  exact NativeAdmission.funding_work_bound _ _

def admissionCeiling := ceiling (fun reference : Intent scope => ceiling (fun term : Intent scope =>
  ceiling (admissionBudget scope span reference term) (Decision.rows scope)) (intents scope)) (intents scope)
def admissionWorkBudget := (Decision.rows scope).length*(admissionCeiling scope span+1)

private theorem admission_uniform (reference term : Intent scope) (row : Decision.Row scope) (inside : row ∈ Decision.rows scope) :
    controlSteps scope (atom scope span (.admission reference term row)).work ≤ admissionCeiling scope span :=
  (admission_cost scope span reference term row).trans
    ((below_ceiling _ (Decision.rows scope) row inside).trans
      ((below_ceiling (fun candidate : Intent scope => ceiling (admissionBudget scope span reference candidate) (Decision.rows scope))
        (intents scope) term (every_intent_is_generated scope _)).trans
        (below_ceiling (fun origin : Intent scope => ceiling (fun candidate : Intent scope =>
          ceiling (admissionBudget scope span origin candidate) (Decision.rows scope)) (intents scope))
          (intents scope) reference (every_intent_is_generated scope _))))


private theorem allRows_cost_on {α : Type} (P : α → Prop) (test : (item : α) → Check scope (P item))
    (items : List α) (budget : Nat) (bounded : ∀ item ∈ items,controlSteps scope (test item).work ≤ budget) :
    controlSteps scope (allRows P test items).work ≤ items.length*(budget+1) := by
  induction items with
  | nil => simp [allRows,controlSteps]
  | cons head tail ih =>
    have step := conjunction_cost (test head) (fun _ => allRows P test tail)
    have a := bounded head List.mem_cons_self
    have b := ih (fun item inside => bounded item (List.mem_cons_of_mem _ inside))
    change controlSteps scope (conjunction (test head) (fun _ => allRows P test tail)).work ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem present_cost (new previous : Intent scope) (table : Table scope) :
    controlSteps scope (atom scope span (.presentBenefit new previous table)).work ≤ presentAtomBudget scope span new previous table := by
  have a := Materialization.present_work_bound scope span new (opponent scope table)
  have b := Materialization.present_work_bound scope span previous (opponent scope table)
  have c := NativeBenefit.present_work_bound cursor
    (Materialization.present scope span new (opponent scope table)).value (Materialization.present scope span previous (opponent scope table)).value
  simp only [Materialization.present_exact] at c
  simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,comparison_cost,List.length_append]
  change 0+_+_ ≤ _
  unfold presentAtomBudget sourcePresentBudget
  exact Nat.add_le_add (by omega) (by simpa only [Materialization.present_exact,tensor] using c)
private theorem future_cost (new previous : Intent scope) (table : Table scope) (word) :
    controlSteps scope (atom scope span (.futureBenefit new previous table word)).work ≤ futureAtomBudget scope span new previous table word := by
  have a := Materialization.future_work_bound scope span new (opponent scope table) word
  have b := Materialization.future_work_bound scope span previous (opponent scope table) word
  have c := NativeBenefit.future_work_bound cursor
    (Materialization.future scope span new (opponent scope table) word).value (Materialization.future scope span previous (opponent scope table) word).value
  simp only [Materialization.future_exact] at c
  simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,comparison_cost,List.length_append]
  change 0+_+_ ≤ _
  unfold futureAtomBudget sourceFutureBudget
  exact Nat.add_le_add (by omega) (by simpa only [Materialization.future_exact,tensor,Tensor.future] using c)

theorem noWorse_cost_bound (new previous : Intent scope) :
    controlSteps scope (noWorse scope span new previous).work ≤ admissionWorkBudget scope span := by
  exact allRows_cost_on scope (Decision.Holds scope span previous new)
    (fun row => atom scope span (.admission previous new row)) (Decision.rows scope) _
    (fun row inside => admission_uniform scope span previous new row inside)

def benefitTableBudget (new previous : Intent scope) (table : Table scope) : Nat :=
  presentAtomBudget scope span new previous table +
  ((Future.Recovery.capabilities cursor.model cursor.depth).map (fun word =>
    futureAtomBudget scope span new previous table word+1)).sum +
  4*(Future.Recovery.capabilities cursor.model cursor.depth).length+3

def benefitBudget (new previous : Intent scope) : Nat :=
  ((tables scope).map (fun table => benefitTableBudget scope span new previous table+1)).sum

theorem realBenefit_cost_bound (new previous : Intent scope) :
    controlSteps scope (realBenefit scope span new previous).work ≤ benefitBudget scope span new previous := by
  unfold realBenefit benefitBudget
  apply allRows_cost
  intro table
  have present := present_cost scope span new previous table
  have future := allRows_cost (fun word => Planning.futureBenefit cursor
      ((tensor scope span new (opponent scope table)).future cursor word)
      ((tensor scope span previous (opponent scope table)).future cursor word))
    (fun word => atom scope span (.futureBenefit new previous table word))
    (fun word => futureAtomBudget scope span new previous table word)
    (fun word => future_cost scope span new previous table word) (Future.Recovery.capabilities cursor.model cursor.depth)
  have funding := allRows_cost (fun word =>
      ((tensor scope span previous (opponent scope table)).funding cursor word).isNone = true →
      ((tensor scope span new (opponent scope table)).funding cursor word).isNone = true)
    (fun word => atom scope span (.funding new previous table word)) (fun _ => 3)
    (fun word => funding_cost scope span new previous table word) (Future.Recovery.capabilities cursor.model cursor.depth)
  have inside := conjunction_cost
    (allRows (fun word => Planning.futureBenefit cursor
      ((tensor scope span new (opponent scope table)).future cursor word)
      ((tensor scope span previous (opponent scope table)).future cursor word))
      (fun word => atom scope span (.futureBenefit new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth))
    (fun _ => allRows (fun word =>
      ((tensor scope span previous (opponent scope table)).funding cursor word).isNone = true →
      ((tensor scope span new (opponent scope table)).funding cursor word).isNone = true)
      (fun word => atom scope span (.funding new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth))
  have outside := conjunction_cost (atom scope span (.presentBenefit new previous table)) (fun _ =>
    conjunction (allRows (fun word => Planning.futureBenefit cursor
      ((tensor scope span new (opponent scope table)).future cursor word)
      ((tensor scope span previous (opponent scope table)).future cursor word))
      (fun word => atom scope span (.futureBenefit new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth)) (fun _ =>
      allRows (fun word =>
      ((tensor scope span previous (opponent scope table)).funding cursor word).isNone = true →
      ((tensor scope span new (opponent scope table)).funding cursor word).isNone = true)
      (fun word => atom scope span (.funding new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth)))
  simp [List.sum_replicate] at funding
  unfold benefitTableBudget
  exact outside.trans (by omega)


def benefitCeiling := ceiling (fun new : Intent scope => ceiling (benefitBudget scope span new) (intents scope)) (intents scope)
def strictBudget := 2*benefitCeiling scope span+2
private theorem realBenefit_uniform (new previous : Intent scope) :
    controlSteps scope (realBenefit scope span new previous).work ≤ benefitCeiling scope span :=
  (realBenefit_cost_bound scope span new previous).trans
    ((below_ceiling _ (intents scope) previous (every_intent_is_generated scope _)).trans
      (below_ceiling (fun candidate : Intent scope => ceiling (benefitBudget scope span candidate) (intents scope))
        (intents scope) new (every_intent_is_generated scope _)))
private theorem strict_cost_bound (previous new : Intent scope) :
    controlSteps scope (strict scope span previous new).work ≤ strictBudget scope span := by
  have a := realBenefit_uniform scope span new previous
  have b := realBenefit_uniform scope span previous new
  have step := conjunction_cost (realBenefit scope span new previous)
    (fun _ => negative (realBenefit scope span previous new))
  rw [negative_cost] at step
  unfold strict strictBudget
  omega

private theorem collect_cost_bound (reference : Intent scope) (items : List (Intent scope)) :
    controlSteps scope (collect scope span reference items).work ≤ items.length*(admissionWorkBudget scope span+1) := by
  induction items with
  | nil => simp [collect,controlSteps]
  | cons head tail ih =>
    have headBound := noWorse_cost_bound scope span head reference
    cases h : (noWorse scope span head reference).decision <;>
      simp only [collect,h,controlSteps_append,List.length_cons]
    all_goals simp only [controlSteps,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *;omega

private theorem scan_cost_bound {reference : Intent scope} (first : Decision.Candidate scope span reference)
    (remaining : List (Decision.Candidate scope span reference)) :
    controlSteps scope (scan first remaining).work ≤ remaining.length*(strictBudget scope span+1) := by
  induction remaining generalizing first with
  | nil => simp [scan,controlSteps]
  | cons head tail ih =>
    have bound := strict_cost_bound scope span first.term head.term
    have a := ih head
    have b := ih first
    cases h : (strict scope span first.term head.term).decision <;>
      simp only [scan,h,controlSteps_append,List.length_cons]
    all_goals simp only [controlSteps,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *;omega

private theorem reject_cost_bound (reference term : Intent scope) (items : List (Decision.Row scope))
    (inside : ∀ row ∈ items,row ∈ Decision.rows scope)
    (invalid : ¬ ∀ row ∈ items,Decision.Holds scope span reference term row) :
    controlSteps scope (reject scope span reference term items inside invalid).work ≤
      items.length*(admissionCeiling scope span+1) := by
  induction items with
  | nil => exact False.elim (invalid (by simp))
  | cons head tail ih =>
    have bound := admission_uniform scope span reference term head (inside head List.mem_cons_self)
    cases h : (atom scope span (.admission reference term head)).decision with
    | isFalse broken =>
      simp only [reject,h,controlSteps_append]
      change controlSteps scope (atom scope span (.admission reference term head)).work+1 ≤ _
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    | isTrue holds =>
      have later := ih (fun row member => inside row (List.mem_cons_of_mem _ member)) (fun all => invalid (by
        intro row member
        rcases List.mem_cons.mp member with equal | rest
        · subst row;exact holds
        · exact all row rest))
      simp only [reject,h,controlSteps_append]
      simp only [controlSteps,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *
      omega

def verificationBudget : Nat := admissionWorkBudget scope span+1+
  (intents scope).length*(admissionWorkBudget scope span+strictBudget scope span+3)

theorem verification_cost_bound (reference term : Intent scope) :
    controlSteps scope (verify scope span reference term).work ≤ verificationBudget scope span := by
  have initial := noWorse_cost_bound scope span term reference
  have each (other : Intent scope) :
      controlSteps scope (implication (noWorse scope span other reference)
        (fun _ => negative (strict scope span term other))).work ≤
          admissionWorkBudget scope span+strictBudget scope span+2 := by
    have entry := noWorse_cost_bound scope span other reference
    have comparison := strict_cost_bound scope span term other
    have step := implication_cost (noWorse scope span other reference)
      (fun _ => negative (strict scope span term other))
    rw [negative_cost] at step
    omega
  have all := allRows_cost (fun other => Decision.NoWorse scope span other reference → ¬ Decision.strictBenefit scope span term other)
    (fun other => implication (noWorse scope span other reference) (fun _ => negative (strict scope span term other)))
    (fun _ => admissionWorkBudget scope span+strictBudget scope span+2) each (intents scope)
  have whole := conjunction_cost (noWorse scope span term reference) (fun _ =>
    allRows (fun other => Decision.NoWorse scope span other reference → ¬ Decision.strictBenefit scope span term other)
    (fun other => implication (noWorse scope span other reference) (fun _ => negative (strict scope span term other))) (intents scope))
  simp [List.sum_replicate] at all
  have arithmetic : admissionWorkBudget scope span+strictBudget scope span+2+1 =
      admissionWorkBudget scope span+strictBudget scope span+3 := by omega
  rw [arithmetic] at all
  unfold verify verificationBudget
  omega

private theorem flatMap_cost_bound {α : Type} (items : List α) (work : α → List (Operation scope)) (budget : Nat)
    (bounded : ∀ item ∈ items,controlSteps scope (work item) ≤ budget) :
    controlSteps scope (items.flatMap work) ≤ items.length*budget := by
  induction items with
  | nil => simp [controlSteps]
  | cons head tail ih =>
    have a := bounded head List.mem_cons_self
    have b := ih (fun item inside => bounded item (List.mem_cons_of_mem _ inside))
    simp only [List.flatMap_cons,controlSteps_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- A result-independent bound for precisely the explicit semantic instructions.
    Native snapshot/primitive internals remain outside this declared work language. -/
def workBudget : Nat :=
  (intents scope).length*(admissionWorkBudget scope span+1) +
  (intents scope).length*(strictBudget scope span+1) +
  verificationBudget scope span + (intents scope).length*admissionWorkBudget scope span + 1

theorem ordered_selection_verification_rejection_and_release_fit_the_generated_budget (reference : Intent scope)
    (order : List (Intent scope)) (complete : order.Perm (intents scope)) :
    controlSteps scope (checkedWork scope span (compileOrdered scope span reference order complete)) + 1 ≤ workBudget scope span := by
  have pool := collect_cost_bound scope span reference order
  rw [complete.length_eq] at pool
  have number : (collect scope span reference order).accepted.length ≤ (intents scope).length := by
    rw [(collect scope span reference order).exact]
    exact (List.length_filterMap_le _ _).trans (Nat.le_of_eq complete.length_eq)
  dsimp only [compileOrdered]
  split
  · rename_i same
    simp only [checkedWork,controlSteps_append]
    have reports := flatMap_cost_bound (scope := scope) (intents scope) _ (admissionWorkBudget scope span)
      (fun term _ => reject_cost_bound scope span reference term (Decision.rows scope) (fun _ member => member) (fun all => by
        obtain ⟨candidate,member,_⟩ := Decision.every_accepted_term_is_generated scope span reference term
          ((Decision.rows_iff scope span reference term).mp all)
        have members : (collect scope span reference order).accepted.Perm (Decision.candidates scope span reference) := by
          rw [(collect scope span reference order).exact];exact complete.filterMap _
        have inside := members.mem_iff.mpr member
        rw [same] at inside
        exact List.not_mem_nil inside))
    unfold workBudget
    omega
  · rename_i head tail same
    have scanned := scan_cost_bound scope span head tail
    have verified := verification_cost_bound scope span reference (scan head tail).policy.term
    simp only [checkedWork,controlSteps_append]
    rw [same,List.length_cons] at number
    unfold workBudget
    have size : tail.length*(strictBudget scope span+1) ≤ (intents scope).length*(strictBudget scope span+1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem ordered_selection_verification_and_rejection_fit_the_generated_budget (reference : Intent scope)
    (order : List (Intent scope)) (complete : order.Perm (intents scope)) :
    controlSteps scope (checkedWork scope span (compileOrdered scope span reference order complete)) ≤ workBudget scope span :=
  (Nat.le_add_right _ 1).trans
    (ordered_selection_verification_rejection_and_release_fit_the_generated_budget _ _ _ _ complete)

theorem complete_selection_verification_and_rejection_fit_the_generated_budget (reference : Intent scope) :
    controlSteps scope (checkedWork scope span (compile scope span reference)) ≤ workBudget scope span :=
  ordered_selection_verification_and_rejection_fit_the_generated_budget _ _ _ _ (List.Perm.refl _)

theorem funded_selection_verification_and_rejection_fit_the_generated_budget :
    controlSteps scope (checkedWork scope span (compileFunded scope span)) ≤ workBudget scope span :=
  ordered_selection_verification_and_rejection_fit_the_generated_budget _ _ _ _ (fundedOrder_complete scope)


theorem receipt_release_fits_the_same_generated_budget (reference : Intent scope)
    (order : List (Intent scope)) (complete : order.Perm (intents scope))
    (receipt : Receipt scope span (compileOrdered scope span reference order complete)) :
    controlSteps scope receipt.work ≤ workBudget scope span := by
  rw [Receipt.work,controlSteps_append,receipt.comparisonWork_exact]
  have gate : controlSteps scope [.branch receipt.review.value] = 1 := rfl
  rw [gate]
  exact ordered_selection_verification_rejection_and_release_fit_the_generated_budget scope span reference order complete

/-- Source-shape bounds consumed by the public multi-source interpreter. -/
theorem admission_atom_uniform_bound (reference term : Intent scope) (row : Decision.Row scope)
    (inside : row ∈ Decision.rows scope) :
    controlSteps scope (atom scope span (.admission reference term row)).work ≤ admissionCeiling scope span :=
  admission_uniform scope span reference term row inside

theorem realBenefit_uniform_bound (new previous : Intent scope) :
    controlSteps scope (realBenefit scope span new previous).work ≤ benefitCeiling scope span :=
  realBenefit_uniform scope span new previous

theorem admission_atom_cost_bound (reference term : Intent scope) (row : Decision.Row scope) :
    controlSteps scope (atom scope span (.admission reference term row)).work ≤ admissionBudget scope span reference term row :=
  admission_cost scope span reference term row


theorem ceiling_eq_foldr {α : Type} (cost : α → Nat) (items : List α) :
    ceiling cost items = items.foldr (fun item total => max (cost item) total) 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [ceiling,List.foldr_cons,ih]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Work
