import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeTensor
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeAdmission
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
  (cursor : Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)) (n : Nat)

/-- Native evaluation is an explicit outstanding computation, never a unit-cost CPU oracle. -/
inductive Query where
  | admission (reference term : Term cursor) (row : Row cursor)
  | presentBenefit (new previous : Term cursor) (table : Table cursor)
  | futureBenefit (new previous : Term cursor) (table : Table cursor) (word : List (Future.Recovery.Action cursor.model))
  | funding (new previous : Term cursor) (table : Table cursor) (word : List (Future.Recovery.Action cursor.model))

def Query.Holds : Query cursor → Prop
  | .admission reference term row => Selection.Holds cursor pricing n reference term row
  | .presentBenefit new previous table => evaluationBenefit cursor
      (tensor cursor pricing new (opponent cursor table) n).present
      (tensor cursor pricing previous (opponent cursor table) n).present
  | .futureBenefit new previous table word => Planning.futureBenefit cursor
      ((tensor cursor pricing new (opponent cursor table) n).future cursor word)
      ((tensor cursor pricing previous (opponent cursor table) n).future cursor word)
  | .funding new previous table word =>
      ((tensor cursor pricing previous (opponent cursor table) n).funding cursor word).isNone = true →
      ((tensor cursor pricing new (opponent cursor table) n).funding cursor word).isNone = true
instance (query : Query cursor) : Decidable (query.Holds cursor pricing n) := by
  cases query <;> unfold Query.Holds <;> infer_instance

inductive Operation where
  | frameConstruction (event : NativeSourceFrames.Event)
  | profileConstruction (event : NativeProfile.Event Party Good Port Technology Instrument)
  | manifestConstruction (event : NativeManifest.Event Party Good Port Technology Instrument)
  | native (query : Query cursor) (answer : Bool)
  | branch (answer : Bool)
  | negate (answer : Bool)
  | retain (accepted : Bool)
  | select (replaced : Bool)
  | comparison (event : NativeBenefit.Event (NativeBenefit.WorkKey (Party := Party) (Good := Good)
      (Port := Port) (Technology := Technology) (Instrument := Instrument)))

  | admissionComparison (event : NativeBenefit.Event (NativeAdmission.Key (Party := Party) (Good := Good)
      (Port := Port) (Technology := Technology) (Instrument := Instrument)))

def Operation.sourceConstruction : NativeTensor.Event Party Good Port Technology Instrument → Operation cursor
  | .source event => .frameConstruction event
  | .profile event => .profileConstruction event
  | .manifest event => .manifestConstruction event

structure Check (P : Prop) where
  private mk ::
  decision : Decidable P
  work : List (Operation cursor)

def Check.value {P : Prop} (made : Check cursor P) : Bool := @decide P made.decision

def atom (query : Query cursor) : Check cursor (query.Holds cursor pricing n) :=
  match query with
  | .presentBenefit new previous table =>
      let current := NativeTensor.present cursor new (opponent cursor table) n
      let original := NativeTensor.present cursor previous (opponent cursor table) n
      let compared := NativeBenefit.transport (show _ ↔ Query.Holds cursor pricing n (.presentBenefit new previous table) from by
        rw [NativeTensor.present_exact,NativeTensor.present_exact];rfl)
        (NativeBenefit.present cursor current.value original.value)
      ⟨compared.decision,[.native (.presentBenefit new previous table) compared.value] ++
        (current.work++original.work).map (Operation.sourceConstruction cursor) ++ compared.work.map Operation.comparison⟩
  | .futureBenefit new previous table word =>
      let current := NativeTensor.future cursor pricing new (opponent cursor table) n word
      let original := NativeTensor.future cursor pricing previous (opponent cursor table) n word
      let compared := NativeBenefit.transport (show _ ↔ Query.Holds cursor pricing n (.futureBenefit new previous table word) from by
        rw [NativeTensor.future_exact,NativeTensor.future_exact];rfl)
        (NativeBenefit.future cursor current.value original.value)
      ⟨compared.decision,[.native (.futureBenefit new previous table word) compared.value] ++
        (current.work++original.work).map (Operation.sourceConstruction cursor) ++ compared.work.map Operation.comparison⟩
  | .admission reference term row => match row with
    | .present table =>
        let current := NativeTensor.present cursor term (opponent cursor table) n
        let original := NativeTensor.present cursor reference (opponent cursor table) n
        let compared := NativeBenefit.transport (show _ ↔ Query.Holds cursor pricing n (.admission reference term (.present table)) from by
          rw [NativeTensor.present_exact,NativeTensor.present_exact];rfl)
          (NativeAdmission.present cursor current.value original.value)
        ⟨compared.decision,[.native (.admission reference term (.present table)) compared.value] ++
          (current.work++original.work).map (Operation.sourceConstruction cursor) ++ compared.work.map Operation.admissionComparison⟩
    | .future table word =>
        let current := NativeTensor.future cursor pricing term (opponent cursor table) n word
        let original := NativeTensor.future cursor pricing reference (opponent cursor table) n word
        let compared := NativeBenefit.transport (show _ ↔ Query.Holds cursor pricing n (.admission reference term (.future table word)) from by
          rw [NativeTensor.future_exact,NativeTensor.future_exact];rfl)
          (NativeAdmission.future cursor current.value original.value)
        ⟨compared.decision,[.native (.admission reference term (.future table word)) compared.value] ++
          (current.work++original.work).map (Operation.sourceConstruction cursor) ++ compared.work.map Operation.admissionComparison⟩
    | .funding table word =>
        let compared := NativeAdmission.funding
          ((tensor cursor pricing term (opponent cursor table) n).funding cursor word)
          ((tensor cursor pricing reference (opponent cursor table) n).funding cursor word)
        ⟨compared.decision,[.native (.admission reference term (.funding table word)) compared.value] ++
          compared.work.map Operation.admissionComparison⟩
  | .funding new previous table word =>
      let compared := NativeAdmission.funding
        ((tensor cursor pricing new (opponent cursor table) n).funding cursor word)
        ((tensor cursor pricing previous (opponent cursor table) n).funding cursor word)
      ⟨compared.decision,[.native (.funding new previous table word) compared.value] ++
        compared.work.map Operation.admissionComparison⟩

variable {cursor pricing n}
def transport {P Q : Prop} (equivalent : P ↔ Q) (made : Check cursor P) : Check cursor Q :=
  ⟨match made.decision with
    | .isTrue yes => .isTrue (equivalent.mp yes)
    | .isFalse no => .isFalse (fun yes => no (equivalent.mpr yes)),made.work⟩

def conjunction {P Q : Prop} (first : Check cursor P) (later : Unit → Check cursor Q) : Check cursor (P ∧ Q) :=
  match first.decision with
  | .isFalse no => ⟨.isFalse (fun yes => no yes.1),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun both => no both.2)
      | .isTrue other => .isTrue ⟨yes,other⟩,first.work ++ [.branch true] ++ second.work⟩

def negative {P : Prop} (made : Check cursor P) : Check cursor (¬ P) :=
  ⟨match made.decision with
    | .isTrue yes => .isFalse (fun no => no yes)
    | .isFalse no => .isTrue no,made.work ++ [.negate made.value]⟩

def implication {P Q : Prop} (first : Check cursor P) (later : Unit → Check cursor Q) : Check cursor (P → Q) :=
  match first.decision with
  | .isFalse no => ⟨.isTrue (fun yes => False.elim (no yes)),first.work ++ [.branch false]⟩
  | .isTrue yes =>
    let second := later ()
    ⟨match second.decision with
      | .isFalse no => .isFalse (fun accepts => no (accepts yes))
      | .isTrue other => .isTrue (fun _ => other),first.work ++ [.branch true] ++ second.work⟩

def allRows {α : Type} (P : α → Prop) (test : (a : α) → Check cursor (P a)) :
    (items : List α) → Check cursor (∀ a ∈ items,P a)
  | [] => ⟨.isTrue (by simp),[]⟩
  | head::tail => transport (by simp only [List.mem_cons,forall_eq_or_imp])
      (conjunction (test head) (fun _ => allRows P test tail))

variable (cursor pricing n)
def noWorse (new previous : Term cursor) : Check cursor (NoWorse cursor pricing n new previous) :=
  transport (rows_iff cursor pricing n previous new)
    (allRows (Selection.Holds cursor pricing n previous new)
      (fun row => atom cursor pricing n (.admission previous new row)) (rows cursor))

def realBenefit (new previous : Term cursor) : Check cursor (Benefit cursor pricing n new previous) :=
  allRows (fun table => benefit cursor (tensor cursor pricing new (opponent cursor table) n)
      (tensor cursor pricing previous (opponent cursor table) n))
    (fun table => conjunction (atom cursor pricing n (.presentBenefit new previous table)) (fun _ =>
      conjunction (allRows (fun word => Planning.futureBenefit cursor
          ((tensor cursor pricing new (opponent cursor table) n).future cursor word)
          ((tensor cursor pricing previous (opponent cursor table) n).future cursor word))
        (fun word => atom cursor pricing n (.futureBenefit new previous table word))
        (Future.Recovery.capabilities cursor.model cursor.depth)) (fun _ =>
        allRows (fun word =>
          ((tensor cursor pricing previous (opponent cursor table) n).funding cursor word).isNone = true →
          ((tensor cursor pricing new (opponent cursor table) n).funding cursor word).isNone = true)
          (fun word => atom cursor pricing n (.funding new previous table word))
          (Future.Recovery.capabilities cursor.model cursor.depth)))) (tables cursor)

def strict (previous new : Term cursor) : Check cursor (strictBenefit cursor pricing n previous new) :=
  conjunction (realBenefit cursor pricing n new previous) (fun _ => negative (realBenefit cursor pricing n previous new))

structure Pool (reference : Term cursor) (items : List (Term cursor)) where
  private mk ::
  accepted : List (Candidate cursor pricing n reference)
  exact : accepted = items.filterMap (Selection.check cursor pricing n reference)
  work : List (Operation cursor)

def collect (reference : Term cursor) : (items : List (Term cursor)) → Pool cursor pricing n reference items
  | [] => ⟨[],rfl,[]⟩
  | head::tail =>
    let checked := noWorse cursor pricing n head reference
    let rest := collect reference tail
    match checked.decision with
    | .isTrue accepted =>
      ⟨⟨head,accepted⟩::rest.accepted,by simp only [List.filterMap_cons,Selection.check,dif_pos accepted];rw [rest.exact],
        checked.work ++ [.retain true] ++ rest.work⟩
    | .isFalse rejected =>
      ⟨rest.accepted,by simp only [List.filterMap_cons,Selection.check,dif_neg rejected];exact rest.exact,
        checked.work ++ [.retain false] ++ rest.work⟩

private theorem strict_irrefl (term : Term cursor) : ¬ strictBenefit cursor pricing n term term := fun both => both.2 both.1
private theorem strict_trans {first middle last : Term cursor}
    (a : strictBenefit cursor pricing n first middle) (b : strictBenefit cursor pricing n middle last) :
    strictBenefit cursor pricing n first last :=
  ⟨fun table inside => benefit_trans cursor (b.1 table inside) (a.1 table inside),
    fun reverse => a.2 (fun table inside => benefit_trans cursor (reverse table inside) (b.1 table inside))⟩

private structure Scan {reference : Term cursor} (first : Candidate cursor pricing n reference)
    (remaining : List (Candidate cursor pricing n reference)) where
  policy : Candidate cursor pricing n reference
  original : policy = first ∨ policy ∈ remaining
  advances : policy = first ∨ strictBenefit cursor pricing n first.term policy.term
  maximal : ∀ other ∈ remaining, ¬ strictBenefit cursor pricing n policy.term other.term
  work : List (Operation cursor)

variable {cursor pricing n}
private theorem no_reverse {reference : Term cursor} {first : Candidate cursor pricing n reference}
    {remaining : List (Candidate cursor pricing n reference)} (made : Scan cursor pricing n first remaining) :
    ¬ strictBenefit cursor pricing n made.policy.term first.term := by
  intro backwards
  rcases made.advances with same | forward
  · apply strict_irrefl cursor pricing n first.term
    simpa only [same] using backwards
  · exact strict_irrefl cursor pricing n first.term (strict_trans cursor pricing n forward backwards)

private def scan {reference : Term cursor} (first : Candidate cursor pricing n reference) :
    (remaining : List (Candidate cursor pricing n reference)) → Scan cursor pricing n first remaining
  | [] => ⟨first,.inl rfl,.inl rfl,by simp,[]⟩
  | head::tail =>
    let checked := strict cursor pricing n first.term head.term
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
          · exact strict_trans cursor pricing n better further),by
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
            · exact notBetter (strict_trans cursor pricing n forward backwards)
          · exact rest.maximal other later,checked.work ++ [.select false] ++ rest.work⟩

variable (cursor pricing n)
structure Rejected (reference term : Term cursor) where
  private mk ::
  result : Rejection cursor pricing n reference term
  work : List (Operation cursor)

private def reject (reference term : Term cursor) :
    (items : List (Row cursor)) → (inside : ∀ row ∈ items,row ∈ rows cursor) →
    (invalid : ¬ ∀ row ∈ items,Selection.Holds cursor pricing n reference term row) → Rejected cursor pricing n reference term
  | [],_,invalid => False.elim (invalid (by simp))
  | head::tail,inside,invalid =>
    let checked := atom cursor pricing n (.admission reference term head)
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

inductive Result (reference : Term cursor) where
  | selected (choice : Choice cursor pricing n reference)
  | blocked (rejected : (term : Term cursor) → Rejected cursor pricing n reference term)

structure Compilation (reference : Term cursor) where
  private mk ::
  result : Result cursor pricing n reference
  work : List (Operation cursor)

def compile (reference : Term cursor) : Compilation cursor pricing n reference :=
  let pool := collect cursor pricing n reference (terms cursor)
  match same : pool.accepted with
  | [] => ⟨.blocked (fun term => reject cursor pricing n reference term (rows cursor) (fun _ member => member)
      (fun all => by
        obtain ⟨candidate,member,_⟩ := every_accepted_term_is_generated cursor pricing n reference term
          ((rows_iff cursor pricing n reference term).mp all)
        change candidate ∈ (terms cursor).filterMap (Selection.check cursor pricing n reference) at member
        rw [←pool.exact,same] at member
        exact List.not_mem_nil member)),pool.work⟩
  | head::tail =>
    let found := scan head tail
    ⟨.selected ⟨found.policy,by
      rw [show candidates cursor pricing n reference = pool.accepted from pool.exact.symm,same]
      rcases found.original with same | inside
      · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
      · exact List.mem_cons_of_mem _ inside,by
      intro other member improves
      have strict := (strictBenefit_iff cursor pricing n _ _).mpr improves
      change other ∈ candidates cursor pricing n reference at member
      rw [show candidates cursor pricing n reference = pool.accepted from pool.exact.symm,same] at member
      rcases List.mem_cons.mp member with same | later
      · subst other;exact no_reverse found strict
      · exact found.maximal other later strict⟩,pool.work ++ found.work⟩

/-- A separate executable pass uses the same primitive evaluator and records its own work. -/
def verify (reference term : Term cursor) : Check cursor
    (NoWorse cursor pricing n term reference ∧
      ∀ other ∈ terms cursor,NoWorse cursor pricing n other reference → ¬ strictBenefit cursor pricing n term other) :=
  conjunction (noWorse cursor pricing n term reference) (fun _ =>
    allRows (fun other => NoWorse cursor pricing n other reference → ¬ strictBenefit cursor pricing n term other)
      (fun other => implication (noWorse cursor pricing n other reference)
        (fun _ => negative (strict cursor pricing n term other))) (terms cursor))

theorem verify_matches_the_original_independent_verifier (reference term : Term cursor) :
    (verify cursor pricing n reference term).value = Selection.verify cursor pricing n reference term := by
  unfold Check.value Selection.verify
  exact Subsingleton.elim _ _ |> fun same => congrArg (fun d => @decide _ d) same

def checkedWork {reference : Term cursor} (made : Compilation cursor pricing n reference) : List (Operation cursor) :=
  made.work ++ match made.result with
    | .selected choice => (verify cursor pricing n reference choice.policy.term).work
    | .blocked rejected => (terms cursor).flatMap (fun term => (rejected term).work)

def nativeObligations (work : List (Operation cursor)) : List (Query cursor) := work.filterMap fun operation =>
  match operation with | .native query _ => some query | _ => none

def controlSteps (work : List (Operation cursor)) : Nat := (work.filter fun operation =>
  match operation with | .native .. => false | _ => true).length

theorem all_work_is_either_a_primitive_control_or_an_explicit_native_obligation (work : List (Operation cursor)) :
    work.length = controlSteps cursor work + (nativeObligations cursor work).length := by
  induction work with
  | nil => rfl
  | cons head tail ih => cases head <;> simp only [controlSteps,nativeObligations,List.filter_cons,List.filterMap_cons,
      List.length_cons,Bool.false_eq_true,if_false,if_true] at * <;> omega

variable {cursor pricing n}
theorem controlSteps_append (left right : List (Operation cursor)) :
    controlSteps cursor (left++right) = controlSteps cursor left+controlSteps cursor right := by
  simp only [controlSteps,List.filter_append,List.length_append]
private theorem conjunction_cost {P Q : Prop} (first : Check cursor P) (later : Unit → Check cursor Q) :
    controlSteps cursor (conjunction first later).work ≤
      controlSteps cursor first.work+1+controlSteps cursor (later ()).work := by
  cases h : first.decision <;> simp [conjunction,h,controlSteps,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem implication_cost {P Q : Prop} (first : Check cursor P) (later : Unit → Check cursor Q) :
    controlSteps cursor (implication first later).work ≤
      controlSteps cursor first.work+1+controlSteps cursor (later ()).work := by
  cases h : first.decision <;> simp [implication,h,controlSteps,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
private theorem negative_cost {P : Prop} (made : Check cursor P) :
    controlSteps cursor (negative made).work = controlSteps cursor made.work+1 := by
  simp [negative,controlSteps]
private theorem allRows_cost {α : Type} (P : α → Prop) (test : (item : α) → Check cursor (P item))
    (budget : α → Nat) (bounded : ∀ item,controlSteps cursor (test item).work ≤ budget item) (items : List α) :
    controlSteps cursor (allRows P test items).work ≤ (items.map (fun item => budget item+1)).sum := by
  induction items with
  | nil => simp [allRows,controlSteps]
  | cons head tail ih =>
    have step := conjunction_cost (test head) (fun _ => allRows P test tail)
    change controlSteps cursor (conjunction (test head) (fun _ => allRows P test tail)).work ≤ _
    simp only [List.map_cons,List.sum_cons]
    have headBound := bounded head
    exact step.trans (by omega)
private theorem comparison_cost (events : List (NativeBenefit.Event
    (NativeBenefit.WorkKey (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))) :
    controlSteps cursor (events.map Operation.comparison) = events.length := by
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

variable (cursor pricing n)
private theorem admission_comparison_cost (events : List (NativeBenefit.Event
    (NativeAdmission.Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))) :
    controlSteps cursor (events.map Operation.admissionComparison) = events.length := by
  induction events with
  | nil => rfl
  | cons head tail ih => simpa [controlSteps] using congrArg Nat.succ ih

private theorem profile_construction_cost (events : List (NativeTensor.Event Party Good Port Technology Instrument)) :
    controlSteps cursor (events.map (Operation.sourceConstruction cursor)) = events.length := by
  induction events with
  | nil => rfl
  | cons head tail ih => cases head <;> simpa [controlSteps,Operation.sourceConstruction] using congrArg Nat.succ ih

def sourcePresentBudget (new previous : Term cursor) (table : Table cursor) :=
  NativeTensor.presentBudget cursor new (opponent cursor table) n + NativeTensor.presentBudget cursor previous (opponent cursor table) n
def sourceFutureBudget (new previous : Term cursor) (table : Table cursor) (word : List (Future.Recovery.Action cursor.model)) :=
  NativeTensor.futureBudget cursor pricing new (opponent cursor table) n word + NativeTensor.futureBudget cursor pricing previous (opponent cursor table) n word

def presentAtomBudget (new previous : Term cursor) (table : Table cursor) :=
  sourcePresentBudget cursor n new previous table + NativeBenefit.presentBudget cursor
    (tensor cursor pricing new (opponent cursor table) n).present (tensor cursor pricing previous (opponent cursor table) n).present

def futureAtomBudget (new previous : Term cursor) (table : Table cursor) (word : List (Future.Recovery.Action cursor.model)) :=
  sourceFutureBudget cursor pricing n new previous table word + NativeBenefit.futureBudget cursor
    ((tensor cursor pricing new (opponent cursor table) n).future cursor word) ((tensor cursor pricing previous (opponent cursor table) n).future cursor word)

def admissionBudget (reference term : Term cursor) : Row cursor → Nat
  | .present table => sourcePresentBudget cursor n term reference table + NativeAdmission.presentBudget cursor
      (tensor cursor pricing term (opponent cursor table) n).present (tensor cursor pricing reference (opponent cursor table) n).present
  | .future table word => sourceFutureBudget cursor pricing n term reference table word + NativeAdmission.futureBudget cursor
      ((tensor cursor pricing term (opponent cursor table) n).future cursor word) ((tensor cursor pricing reference (opponent cursor table) n).future cursor word)
  | .funding _ _ => 3

private theorem admission_cost (reference term : Term cursor) (row : Row cursor) :
    controlSteps cursor (atom cursor pricing n (.admission reference term row)).work ≤ admissionBudget cursor pricing n reference term row := by
  cases row with
  | present table =>
    have a := NativeTensor.present_work_bound cursor term (opponent cursor table) n
    have b := NativeTensor.present_work_bound cursor reference (opponent cursor table) n
    have c := NativeAdmission.present_work_bound cursor
      (NativeTensor.present cursor term (opponent cursor table) n).value (NativeTensor.present cursor reference (opponent cursor table) n).value
    simp only [NativeTensor.present_exact] at c
    simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,admission_comparison_cost,List.length_append]
    change 0+_+_ ≤ _
    unfold admissionBudget sourcePresentBudget
    exact Nat.add_le_add (by omega) (by simpa only [NativeTensor.present_exact,tensor] using c)
  | future table word =>
    have a := NativeTensor.future_work_bound cursor pricing term (opponent cursor table) n word
    have b := NativeTensor.future_work_bound cursor pricing reference (opponent cursor table) n word
    have c := NativeAdmission.future_work_bound cursor
      (NativeTensor.future cursor pricing term (opponent cursor table) n word).value (NativeTensor.future cursor pricing reference (opponent cursor table) n word).value
    simp only [NativeTensor.future_exact] at c
    simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,admission_comparison_cost,List.length_append]
    change 0+_+_ ≤ _
    unfold admissionBudget sourceFutureBudget
    exact Nat.add_le_add (by omega) (by simpa only [NativeTensor.future_exact,tensor,Tensor.future] using c)
  | funding table word =>
    change controlSteps cursor ([Operation.native _ _] ++ _) ≤ _
    rw [controlSteps_append,admission_comparison_cost]
    change 0+_ ≤ _
    simp only [Nat.zero_add]
    exact NativeAdmission.funding_work_bound _ _

private theorem funding_cost (new previous : Term cursor) (table : Table cursor) (word) :
    controlSteps cursor (atom cursor pricing n (.funding new previous table word)).work ≤ 3 := by
  change controlSteps cursor ([Operation.native _ _] ++ _) ≤ _
  rw [controlSteps_append,admission_comparison_cost]
  change 0+_ ≤ _
  simp only [Nat.zero_add]
  exact NativeAdmission.funding_work_bound _ _

def admissionCeiling := ceiling (fun reference : Term cursor => ceiling (fun term : Term cursor =>
  ceiling (admissionBudget cursor pricing n reference term) (rows cursor)) (terms cursor)) (terms cursor)
def admissionWorkBudget := (rows cursor).length*(admissionCeiling cursor pricing n+1)

private theorem admission_uniform (reference term : Term cursor) (row : Row cursor) (inside : row ∈ rows cursor) :
    controlSteps cursor (atom cursor pricing n (.admission reference term row)).work ≤ admissionCeiling cursor pricing n :=
  (admission_cost cursor pricing n reference term row).trans
    ((below_ceiling _ (rows cursor) row inside).trans
      ((below_ceiling (fun candidate : Term cursor => ceiling (admissionBudget cursor pricing n reference candidate) (rows cursor))
        (terms cursor) term (List.mem_attach _ _)).trans
        (below_ceiling (fun origin : Term cursor => ceiling (fun candidate : Term cursor =>
          ceiling (admissionBudget cursor pricing n origin candidate) (rows cursor)) (terms cursor))
          (terms cursor) reference (List.mem_attach _ _))))


private theorem allRows_cost_on {α : Type} (P : α → Prop) (test : (item : α) → Check cursor (P item))
    (items : List α) (budget : Nat) (bounded : ∀ item ∈ items,controlSteps cursor (test item).work ≤ budget) :
    controlSteps cursor (allRows P test items).work ≤ items.length*(budget+1) := by
  induction items with
  | nil => simp [allRows,controlSteps]
  | cons head tail ih =>
    have step := conjunction_cost (test head) (fun _ => allRows P test tail)
    have a := bounded head List.mem_cons_self
    have b := ih (fun item inside => bounded item (List.mem_cons_of_mem _ inside))
    change controlSteps cursor (conjunction (test head) (fun _ => allRows P test tail)).work ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem present_cost (new previous : Term cursor) (table : Table cursor) :
    controlSteps cursor (atom cursor pricing n (.presentBenefit new previous table)).work ≤ presentAtomBudget cursor pricing n new previous table := by
  have a := NativeTensor.present_work_bound cursor new (opponent cursor table) n
  have b := NativeTensor.present_work_bound cursor previous (opponent cursor table) n
  have c := NativeBenefit.present_work_bound cursor
    (NativeTensor.present cursor new (opponent cursor table) n).value (NativeTensor.present cursor previous (opponent cursor table) n).value
  simp only [NativeTensor.present_exact] at c
  simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,comparison_cost,List.length_append]
  change 0+_+_ ≤ _
  unfold presentAtomBudget sourcePresentBudget
  exact Nat.add_le_add (by omega) (by simpa only [NativeTensor.present_exact,tensor] using c)
private theorem future_cost (new previous : Term cursor) (table : Table cursor) (word) :
    controlSteps cursor (atom cursor pricing n (.futureBenefit new previous table word)).work ≤ futureAtomBudget cursor pricing n new previous table word := by
  have a := NativeTensor.future_work_bound cursor pricing new (opponent cursor table) n word
  have b := NativeTensor.future_work_bound cursor pricing previous (opponent cursor table) n word
  have c := NativeBenefit.future_work_bound cursor
    (NativeTensor.future cursor pricing new (opponent cursor table) n word).value (NativeTensor.future cursor pricing previous (opponent cursor table) n word).value
  simp only [NativeTensor.future_exact] at c
  simp only [atom,NativeBenefit.transport,controlSteps_append,profile_construction_cost,comparison_cost,List.length_append]
  change 0+_+_ ≤ _
  unfold futureAtomBudget sourceFutureBudget
  exact Nat.add_le_add (by omega) (by simpa only [NativeTensor.future_exact,tensor,Tensor.future] using c)

theorem noWorse_cost_bound (new previous : Term cursor) :
    controlSteps cursor (noWorse cursor pricing n new previous).work ≤ admissionWorkBudget cursor pricing n := by
  exact allRows_cost_on cursor (Selection.Holds cursor pricing n previous new)
    (fun row => atom cursor pricing n (.admission previous new row)) (rows cursor) _
    (fun row inside => admission_uniform cursor pricing n previous new row inside)

def benefitTableBudget (new previous : Term cursor) (table : Table cursor) : Nat :=
  presentAtomBudget cursor pricing n new previous table +
  ((Future.Recovery.capabilities cursor.model cursor.depth).map (fun word =>
    futureAtomBudget cursor pricing n new previous table word+1)).sum +
  4*(Future.Recovery.capabilities cursor.model cursor.depth).length+3

def benefitBudget (new previous : Term cursor) : Nat :=
  ((tables cursor).map (fun table => benefitTableBudget cursor pricing n new previous table+1)).sum

theorem realBenefit_cost_bound (new previous : Term cursor) :
    controlSteps cursor (realBenefit cursor pricing n new previous).work ≤ benefitBudget cursor pricing n new previous := by
  unfold realBenefit benefitBudget
  apply allRows_cost
  intro table
  have present := present_cost cursor pricing n new previous table
  have future := allRows_cost (fun word => Planning.futureBenefit cursor
      ((tensor cursor pricing new (opponent cursor table) n).future cursor word)
      ((tensor cursor pricing previous (opponent cursor table) n).future cursor word))
    (fun word => atom cursor pricing n (.futureBenefit new previous table word))
    (fun word => futureAtomBudget cursor pricing n new previous table word)
    (fun word => future_cost cursor pricing n new previous table word) (Future.Recovery.capabilities cursor.model cursor.depth)
  have funding := allRows_cost (fun word =>
      ((tensor cursor pricing previous (opponent cursor table) n).funding cursor word).isNone = true →
      ((tensor cursor pricing new (opponent cursor table) n).funding cursor word).isNone = true)
    (fun word => atom cursor pricing n (.funding new previous table word)) (fun _ => 3)
    (fun word => funding_cost cursor pricing n new previous table word) (Future.Recovery.capabilities cursor.model cursor.depth)
  have inside := conjunction_cost
    (allRows (fun word => Planning.futureBenefit cursor
      ((tensor cursor pricing new (opponent cursor table) n).future cursor word)
      ((tensor cursor pricing previous (opponent cursor table) n).future cursor word))
      (fun word => atom cursor pricing n (.futureBenefit new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth))
    (fun _ => allRows (fun word =>
      ((tensor cursor pricing previous (opponent cursor table) n).funding cursor word).isNone = true →
      ((tensor cursor pricing new (opponent cursor table) n).funding cursor word).isNone = true)
      (fun word => atom cursor pricing n (.funding new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth))
  have outside := conjunction_cost (atom cursor pricing n (.presentBenefit new previous table)) (fun _ =>
    conjunction (allRows (fun word => Planning.futureBenefit cursor
      ((tensor cursor pricing new (opponent cursor table) n).future cursor word)
      ((tensor cursor pricing previous (opponent cursor table) n).future cursor word))
      (fun word => atom cursor pricing n (.futureBenefit new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth)) (fun _ =>
      allRows (fun word =>
      ((tensor cursor pricing previous (opponent cursor table) n).funding cursor word).isNone = true →
      ((tensor cursor pricing new (opponent cursor table) n).funding cursor word).isNone = true)
      (fun word => atom cursor pricing n (.funding new previous table word)) (Future.Recovery.capabilities cursor.model cursor.depth)))
  simp [List.sum_replicate] at funding
  unfold benefitTableBudget
  exact outside.trans (by omega)


def benefitCeiling := ceiling (fun new : Term cursor => ceiling (benefitBudget cursor pricing n new) (terms cursor)) (terms cursor)
def strictBudget := 2*benefitCeiling cursor pricing n+2
private theorem realBenefit_uniform (new previous : Term cursor) :
    controlSteps cursor (realBenefit cursor pricing n new previous).work ≤ benefitCeiling cursor pricing n :=
  (realBenefit_cost_bound cursor pricing n new previous).trans
    ((below_ceiling _ (terms cursor) previous (List.mem_attach _ _)).trans
      (below_ceiling (fun candidate : Term cursor => ceiling (benefitBudget cursor pricing n candidate) (terms cursor))
        (terms cursor) new (List.mem_attach _ _)))
private theorem strict_cost_bound (previous new : Term cursor) :
    controlSteps cursor (strict cursor pricing n previous new).work ≤ strictBudget cursor pricing n := by
  have a := realBenefit_uniform cursor pricing n new previous
  have b := realBenefit_uniform cursor pricing n previous new
  have step := conjunction_cost (realBenefit cursor pricing n new previous)
    (fun _ => negative (realBenefit cursor pricing n previous new))
  rw [negative_cost] at step
  unfold strict strictBudget
  omega

private theorem collect_cost_bound (reference : Term cursor) (items : List (Term cursor)) :
    controlSteps cursor (collect cursor pricing n reference items).work ≤ items.length*(admissionWorkBudget cursor pricing n+1) := by
  induction items with
  | nil => simp [collect,controlSteps]
  | cons head tail ih =>
    have headBound := noWorse_cost_bound cursor pricing n head reference
    cases h : (noWorse cursor pricing n head reference).decision <;>
      simp only [collect,h,controlSteps_append,List.length_cons]
    all_goals simp only [controlSteps,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *;omega

private theorem scan_cost_bound {reference : Term cursor} (first : Candidate cursor pricing n reference)
    (remaining : List (Candidate cursor pricing n reference)) :
    controlSteps cursor (scan first remaining).work ≤ remaining.length*(strictBudget cursor pricing n+1) := by
  induction remaining generalizing first with
  | nil => simp [scan,controlSteps]
  | cons head tail ih =>
    have bound := strict_cost_bound cursor pricing n first.term head.term
    have a := ih head
    have b := ih first
    cases h : (strict cursor pricing n first.term head.term).decision <;>
      simp only [scan,h,controlSteps_append,List.length_cons]
    all_goals simp only [controlSteps,List.filter_cons,List.filter_nil,if_true,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul] at *;omega

private theorem reject_cost_bound (reference term : Term cursor) (items : List (Row cursor))
    (inside : ∀ row ∈ items,row ∈ rows cursor)
    (invalid : ¬ ∀ row ∈ items,Selection.Holds cursor pricing n reference term row) :
    controlSteps cursor (reject cursor pricing n reference term items inside invalid).work ≤
      items.length*(admissionCeiling cursor pricing n+1) := by
  induction items with
  | nil => exact False.elim (invalid (by simp))
  | cons head tail ih =>
    have bound := admission_uniform cursor pricing n reference term head (inside head List.mem_cons_self)
    cases h : (atom cursor pricing n (.admission reference term head)).decision with
    | isFalse broken =>
      simp only [reject,h,controlSteps_append]
      change controlSteps cursor (atom cursor pricing n (.admission reference term head)).work+1 ≤ _
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

def verificationBudget : Nat := admissionWorkBudget cursor pricing n+1+
  (terms cursor).length*(admissionWorkBudget cursor pricing n+strictBudget cursor pricing n+3)

theorem verification_cost_bound (reference term : Term cursor) :
    controlSteps cursor (verify cursor pricing n reference term).work ≤ verificationBudget cursor pricing n := by
  have initial := noWorse_cost_bound cursor pricing n term reference
  have each (other : Term cursor) :
      controlSteps cursor (implication (noWorse cursor pricing n other reference)
        (fun _ => negative (strict cursor pricing n term other))).work ≤
          admissionWorkBudget cursor pricing n+strictBudget cursor pricing n+2 := by
    have entry := noWorse_cost_bound cursor pricing n other reference
    have comparison := strict_cost_bound cursor pricing n term other
    have step := implication_cost (noWorse cursor pricing n other reference)
      (fun _ => negative (strict cursor pricing n term other))
    rw [negative_cost] at step
    omega
  have all := allRows_cost (fun other => NoWorse cursor pricing n other reference → ¬ strictBenefit cursor pricing n term other)
    (fun other => implication (noWorse cursor pricing n other reference) (fun _ => negative (strict cursor pricing n term other)))
    (fun _ => admissionWorkBudget cursor pricing n+strictBudget cursor pricing n+2) each (terms cursor)
  have whole := conjunction_cost (noWorse cursor pricing n term reference) (fun _ =>
    allRows (fun other => NoWorse cursor pricing n other reference → ¬ strictBenefit cursor pricing n term other)
    (fun other => implication (noWorse cursor pricing n other reference) (fun _ => negative (strict cursor pricing n term other))) (terms cursor))
  simp [List.sum_replicate,Nat.mul_comm] at all
  simp only [Nat.mul_comm (admissionWorkBudget cursor pricing n+strictBudget cursor pricing n+3) (terms cursor).length] at all
  unfold verify verificationBudget
  omega

private theorem flatMap_cost_bound {α : Type} (items : List α) (work : α → List (Operation cursor)) (budget : Nat)
    (bounded : ∀ item ∈ items,controlSteps cursor (work item) ≤ budget) :
    controlSteps cursor (items.flatMap work) ≤ items.length*budget := by
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
  (terms cursor).length*(admissionWorkBudget cursor pricing n+1) +
  (terms cursor).length*(strictBudget cursor pricing n+1) +
  verificationBudget cursor pricing n + (terms cursor).length*admissionWorkBudget cursor pricing n

theorem complete_selection_verification_and_rejection_fit_the_generated_budget (reference : Term cursor) :
    controlSteps cursor (checkedWork cursor pricing n (compile cursor pricing n reference)) ≤ workBudget cursor pricing n := by
  have pool := collect_cost_bound cursor pricing n reference (terms cursor)
  have number : (collect cursor pricing n reference (terms cursor)).accepted.length ≤ (terms cursor).length := by
    rw [(collect cursor pricing n reference (terms cursor)).exact]
    exact List.length_filterMap_le _ _
  dsimp only [compile]
  split
  · rename_i same
    simp only [checkedWork,controlSteps_append]
    have reports := flatMap_cost_bound (cursor := cursor) (terms cursor) _ (admissionWorkBudget cursor pricing n)
      (fun term _ => reject_cost_bound cursor pricing n reference term (rows cursor) (fun _ member => member) (fun all => by
        obtain ⟨candidate,member,_⟩ := every_accepted_term_is_generated cursor pricing n reference term
          ((rows_iff cursor pricing n reference term).mp all)
        change candidate ∈ (terms cursor).filterMap (Selection.check cursor pricing n reference) at member
        rw [←(collect cursor pricing n reference (terms cursor)).exact,same] at member
        exact List.not_mem_nil member))
    unfold workBudget
    omega
  · rename_i head tail same
    have scanned := scan_cost_bound cursor pricing n head tail
    have verified := verification_cost_bound cursor pricing n reference (scan head tail).policy.term
    simp only [checkedWork,controlSteps_append]
    rw [same,List.length_cons] at number
    unfold workBudget
    have size : tail.length*(strictBudget cursor pricing n+1) ≤ (terms cursor).length*(strictBudget cursor pricing n+1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution
