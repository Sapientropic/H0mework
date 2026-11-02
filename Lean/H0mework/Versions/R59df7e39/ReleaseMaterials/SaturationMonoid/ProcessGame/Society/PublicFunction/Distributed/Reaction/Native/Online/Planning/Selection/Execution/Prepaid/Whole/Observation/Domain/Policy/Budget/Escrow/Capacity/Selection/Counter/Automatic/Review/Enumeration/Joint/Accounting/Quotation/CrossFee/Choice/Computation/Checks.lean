import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeAdmission
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Checks
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
open NativeBenefit

structure Bounded (Key : Type) (P : Prop) (limit : Nat) where
  check : NativeBenefit.Check Key P
  bound : check.work.length ≤ limit
namespace Bounded
variable {Key : Type} {P Q : Prop} {a b : Nat}
def cast (made : Bounded Key P a) (same : P ↔ Q) : Bounded Key Q a := ⟨NativeBenefit.transport same made.check,made.bound⟩
def resize (made : Bounded Key P a) (limit : Nat) (enough : a ≤ limit) : Bounded Key P limit := ⟨made.check,made.bound.trans enough⟩
def conjoin (first : Bounded Key P a) (later : Unit → Bounded Key Q b) : Bounded Key (P ∧ Q) (a+1+b) :=
  ⟨NativeBenefit.conjunction first.check (fun _ => (later ()).check),
    (NativeBenefit.conjunction_work_bound first.check (fun _ => (later ()).check)).trans (by have := first.bound;have := (later ()).bound;omega)⟩
def imply (first : Bounded Key P a) (later : Unit → Bounded Key Q b) : Bounded Key (P → Q) (a+1+b) :=
  ⟨NativeBenefit.implication first.check (fun _ => (later ()).check),
    (NativeBenefit.implication_work_bound first.check (fun _ => (later ()).check)).trans (by have := first.bound;have := (later ()).bound;omega)⟩
def boolean (value : Bool) : Bounded Key (value = true) 1 := ⟨NativeBenefit.boolean value,Nat.le_refl _⟩
def natural (left right : Nat) : Bounded Key (left ≤ right) 1 := ⟨NativeBenefit.naturalLe left right,Nat.le_refl _⟩
def rational (left right : ℚ) : Bounded Key (left ≤ right) 1 := ⟨NativeBenefit.rationalLe left right,Nat.le_refl _⟩
def negative (made : Bounded Key P a) : Bounded Key (¬P) (a+2) :=
  ((imply made (fun _ => (boolean false).cast (by simp))).cast Iff.rfl).resize _ (by omega)
def rows {α : Type} (P : α → Prop) (budget : α → Nat) (make : (item : α) → Bounded Key (P item) (budget item))
    (items : List α) : Bounded Key (∀ item ∈ items,P item) ((items.map (fun item => budget item+1)).sum) :=
  ⟨NativeBenefit.allRows P (fun item => (make item).check) items,NativeBenefit.allRows_work_bound P _ budget (fun item => (make item).bound) items⟩
def record (prelude : List (NativeBenefit.Event Key)) (made : Bounded Key P a) : Bounded Key P (prelude.length+a) :=
  ⟨NativeBenefit.record prelude made.check,by simpa only [NativeBenefit.record,List.length_append] using Nat.add_le_add_left made.bound prelude.length⟩
end Bounded

variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
abbrev Key := NativeAdmission.Key (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)
local notation "Produced" => Bounded (Key (P := P) (G := G) (O := O) (T := T) (I := I))

def nativeEqual (left right : NativeBenefit.NativeKey (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) :
    NativeBenefit.Check (Key (P := P) (G := G) (O := O) (T := T) (I := I)) (left = right) :=
  NativeAdmission.encodedEqual NativeAdmission.Atom.native (by intro a b same;cases same;rfl) left right

theorem lists_budget_bound {α : Type} (left right : List α) : NativeAdmission.listsBudget (fun _ _ => 1) left right ≤ 2*left.length+1 := by
  induction left generalizing right with
  | nil => cases right <;> simp [NativeAdmission.listsBudget]
  | cons head tail ih =>
      cases right with
      | nil => simp only [NativeAdmission.listsBudget,List.length_cons];omega
      | cons other rest =>
          have later := ih rest
          simp only [NativeAdmission.listsBudget,List.length_cons]
          omega

def inventoryBudget (new previous : Feedback.Authority.Trace.Manifest P G O T I) : Nat :=
  NativeInventory.budget new+NativeInventory.budget previous+
    NativeBenefit.subpermBudget (NativeInventory.rowCount new) (NativeInventory.rowCount previous)+2*NativeInventory.rowCount new+2

def inventory (new previous : Feedback.Authority.Trace.Manifest P G O T I) : Produced
    ((Feedback.Authority.Trace.Lawful.inventory new).due.Subperm (Feedback.Authority.Trace.Lawful.inventory previous).due ∧
      (Feedback.Authority.Trace.Lawful.inventory new).admitted = (Feedback.Authority.Trace.Lawful.inventory previous).admitted) (inventoryBudget new previous) := by
  let current := NativeInventory.compile new
  let original := NativeInventory.compile previous
  let tested := NativeBenefit.conjunction
    (NativeBenefit.rekey NativeAdmission.Atom.native (by intro a b same;cases same;rfl) (NativeBenefit.subperm current.inventory.due original.inventory.due))
    (fun _ => NativeAdmission.listsEqual nativeEqual current.inventory.admitted original.inventory.admitted)
  let checked := NativeBenefit.record ((current.work++original.work).map (fun event => NativeBenefit.Event.source (NativeAdmission.Atom.construction event)))
    (NativeBenefit.transport (by rw [current.exact,original.exact]) tested)
  refine ⟨checked,?_⟩
  have due := NativeBenefit.subperm_work_bound current.inventory.due original.inventory.due
  have admitted := NativeAdmission.lists_work_bound nativeEqual (fun _ _ => 1) (fun _ _ => Nat.le_refl _) current.inventory.admitted original.inventory.admitted
  have pairs := lists_budget_bound current.inventory.admitted original.inventory.admitted
  have combined := NativeBenefit.conjunction_work_bound
    (NativeBenefit.rekey NativeAdmission.Atom.native (by intro a b same;cases same;rfl) (NativeBenefit.subperm current.inventory.due original.inventory.due))
    (fun _ => NativeAdmission.listsEqual nativeEqual current.inventory.admitted original.inventory.admitted)
  dsimp only [NativeBenefit.rekey] at combined
  simp only [List.length_map] at combined
  rw [current.exact,original.exact] at due admitted pairs combined
  have size := NativeInventory.admitted_length new
  have dueSize := NativeBenefit.subpermBudget_mono (NativeInventory.due_length_bound new) (NativeInventory.due_length_bound previous)
  dsimp only [checked,NativeBenefit.record,NativeBenefit.transport,tested,NativeBenefit.rekey]
  simp only [List.length_append,List.length_map]
  rw [NativeInventory.work_exact,NativeInventory.work_exact,current.exact,original.exact]
  unfold inventoryBudget
  rw [size] at pairs
  have admittedTotal := admitted.trans pairs
  have dueTotal := due.trans dueSize
  have total := combined.trans (Nat.add_le_add (Nat.add_le_add_right dueTotal 1) admittedTotal)
  omega

variable {driver : Feedback.Input seed.source.code} (cursor : Online.Cursor seed driver)
def evaluationBudget (new previous : Evaluation cursor.source.val.code) : Nat :=
  12+inventoryBudget new.native previous.native+NativeAdmission.profileBudget new.profile previous.profile+2*(Window.axes cursor.model cursor.depth).length

def evaluation (new previous : Evaluation cursor.source.val.code) : Produced (Full.EvaluationLe cursor new previous) (evaluationBudget cursor new previous) := by
  let legal : Produced (previous.legal = true → new.legal = true) 3 := Bounded.imply (Bounded.boolean previous.legal) (fun _ => Bounded.boolean new.legal)
  let complete : Produced (previous.complete = true → new.complete = true) 3 := Bounded.imply (Bounded.boolean previous.complete) (fun _ => Bounded.boolean new.complete)
  let values := Bounded.rows (Key := Key (P := P) (G := G) (O := O) (T := T) (I := I)) (fun axis => new.value axis ≤ previous.value axis) (fun _ => 1)
    (fun axis => Bounded.rational (new.value axis) (previous.value axis)) (Window.axes cursor.model cursor.depth)
  let profile : Produced (new.profile = previous.profile) (NativeAdmission.profileBudget new.profile previous.profile) :=
    ⟨NativeAdmission.profile new.profile previous.profile,NativeAdmission.profile_work_bound new.profile previous.profile⟩
  let body := Bounded.conjoin legal (fun _ => Bounded.conjoin complete (fun _ =>
    Bounded.conjoin (inventory new.native previous.native) (fun _ => Bounded.conjoin profile (fun _ => values))))
  exact (body.cast (by unfold Full.EvaluationLe Planning.evaluationBenefit;tauto)).resize _ (by
    simp [evaluationBudget,List.sum_replicate,Nat.mul_comm];omega)

def futureBudget (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) : Nat :=
  match new,previous with | some current,some original => evaluationBudget cursor current.evaluation original.evaluation+3 | _,_ => 1

def future (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) : Produced (Full.FutureLe cursor new previous) (futureBudget cursor new previous) := by
  cases new with
  | none => cases previous with
    | none => exact (Bounded.boolean true).cast (by simp [Full.FutureLe])
    | some original => exact (Bounded.boolean false).cast (by simp [Full.FutureLe])
  | some current => cases previous with
    | none => exact (Bounded.boolean true).cast (by simp [Full.FutureLe])
    | some original =>
      let body := (Bounded.conjoin (Bounded.natural original.consumed current.consumed)
        (fun _ => evaluation cursor current.evaluation original.evaluation)).record [.branch true]
      exact body.resize _ (by dsimp only [futureBudget];simp only [List.length_cons,List.length_nil];omega)

def tensorBudget (new previous : Planning.Tensor cursor) : Nat :=
  evaluationBudget cursor new.present previous.present+2+
    ((Future.Recovery.capabilities cursor.model cursor.depth).map (fun word => futureBudget cursor (new.future cursor word) (previous.future cursor word)+1)).sum+
    4*(Future.Recovery.capabilities cursor.model cursor.depth).length

def tensor (new previous : Planning.Tensor cursor) : Produced (Full.TensorLe cursor new previous) (tensorBudget cursor new previous) := by
  let futures := Bounded.rows (fun word => Full.FutureLe cursor (new.future cursor word) (previous.future cursor word))
    (fun word => futureBudget cursor (new.future cursor word) (previous.future cursor word))
    (fun word => future cursor (new.future cursor word) (previous.future cursor word)) (Future.Recovery.capabilities cursor.model cursor.depth)
  let funding := Bounded.rows (Key := Key (P := P) (G := G) (O := O) (T := T) (I := I)) (fun word => (previous.funding cursor word).isNone = true → (new.funding cursor word).isNone = true)
    (fun _ => 3) (fun word => Bounded.imply (Bounded.boolean (previous.funding cursor word).isNone)
      (fun _ => Bounded.boolean (new.funding cursor word).isNone)) (Future.Recovery.capabilities cursor.model cursor.depth)
  exact (Bounded.conjoin (evaluation cursor new.present previous.present) (fun _ => Bounded.conjoin futures (fun _ => funding))).resize _ (by
    simp [tensorBudget,List.sum_replicate,Nat.mul_comm];omega)

variable (pool : List (Offer (prepared := prepared) (position := position)))
def responsibilityBudget (new previous : Offer (prepared := prepared) (position := position)) : Nat :=
  ((keys prepared).map (fun index => ((Choice.tables pool index).map (fun table =>
    tensorBudget (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
      ((previous.view index).tensor (Choice.rival pool index table))+1)).sum+1)).sum+4*(keys prepared).length+10

def responsibility (new previous : Offer (prepared := prepared) (position := position)) :
    Produced (ResponsibilityLe pool new previous) (responsibilityBudget pool new previous) := by
  let rows := Bounded.rows (fun index => ∀ table ∈ Choice.tables pool index,
      Full.TensorLe (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
        ((previous.view index).tensor (Choice.rival pool index table)))
    (fun index => ((Choice.tables pool index).map (fun table => tensorBudget (Policy.initial input prepared.saved[index].point)
      ((new.view index).tensor (Choice.rival pool index table)) ((previous.view index).tensor (Choice.rival pool index table))+1)).sum)
    (fun index => Bounded.rows _ _ (fun table => tensor (Policy.initial input prepared.saved[index].point)
      ((new.view index).tensor (Choice.rival pool index table)) ((previous.view index).tensor (Choice.rival pool index table))) (Choice.tables pool index)) (keys prepared)
  let costs := Bounded.rows (Key := Key (P := P) (G := G) (O := O) (T := T) (I := I)) (fun index : Index prepared => new.work index ≤ previous.work index ∧ previous.credit index ≤ new.credit index)
    (fun _ => 3) (fun index => Bounded.conjoin (Bounded.natural (new.work index) (previous.work index))
      (fun _ => Bounded.natural (previous.credit index) (new.credit index))) (keys prepared)
  let invoices := Bounded.conjoin (Key := Key (P := P) (G := G) (O := O) (T := T) (I := I)) (Bounded.natural new.branch.alternative.1 previous.branch.alternative.1) (fun _ =>
    Bounded.conjoin (Bounded.natural new.invoiceWork previous.invoiceWork) (fun _ => Bounded.natural previous.invoiceCredit new.invoiceCredit))
  exact ((Bounded.conjoin rows (fun _ => Bounded.conjoin costs (fun _ => invoices))).cast (by
    unfold ResponsibilityLe
    simp only [keys,List.mem_finRange,forall_const])).resize _ (by
      simp [responsibilityBudget,List.sum_replicate,Nat.mul_comm];omega)

def strictBudget (previous new : Offer (prepared := prepared) (position := position)) := responsibilityBudget pool new previous+responsibilityBudget pool previous new+3

def strict (previous new : Offer (prepared := prepared) (position := position)) :
    Produced (ResponsibilityLe pool new previous ∧ ¬ResponsibilityLe pool previous new) (strictBudget pool previous new) :=
  (Bounded.conjoin (responsibility pool new previous) (fun _ => (responsibility pool previous new).negative)).resize _ (by dsimp only [strictBudget];omega)

def verifyBudget (reference candidate : Offer (prepared := prepared) (position := position)) := responsibilityBudget pool candidate reference+1+
  (pool.map (fun other => strictBudget pool candidate other+3)).sum

def verify (reference candidate : Offer (prepared := prepared) (position := position)) :
    Produced (ResponsibilityLe pool candidate reference ∧ ∀ other ∈ pool,¬(ResponsibilityLe pool other candidate ∧ ¬ResponsibilityLe pool candidate other))
      (verifyBudget pool reference candidate) :=
  Bounded.conjoin (responsibility pool candidate reference) (fun _ =>
    Bounded.rows _ _ (fun other => (strict pool candidate other).negative) pool)

theorem responsibility_is_the_original_complete_relation (new previous : Offer (prepared := prepared) (position := position)) :
    (responsibility pool new previous).check.value = decide (ResponsibilityLe pool new previous) := by
  unfold NativeBenefit.Check.value
  exact congrArg (fun decision => @decide _ decision) (Subsingleton.elim _ _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Checks
