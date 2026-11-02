import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Source
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol

namespace Generic
variable {Key : Type} [DecidableEq Key]
def equal {α : Type} (encode : α → Key) (faithful : Function.Injective encode) (left right : α) : Code Key (.truth (left = right)) :=
  Code.transport ⟨fun same => faithful same,fun same => congrArg encode same⟩ (.atom (.equal (encode left) (encode right)))

def lists {α : Type} (test : (left right : α) → Code Key (.truth (left = right))) :
    (left right : List α) → Code Key (.truth (left = right))
  | [],[] => .pure (.isTrue rfl)
  | [],_::_ | _::_,[] => .pure (.isFalse (by intro impossible;cases impossible))
  | left::ls,right::rs => Code.transport (by simp only [List.cons.injEq])
      (Code.conjunction (test left right) (fun _ => lists test ls rs))

def rows {α : Type} (claim : α → Prop) (make : (item : α) → Code Key (.truth (claim item))) :
    (items : List α) → Code Key (.truth (∀ item ∈ items,claim item))
  | [] => .pure (.isTrue (by simp))
  | head::tail => Code.transport (by simp only [List.mem_cons,forall_eq_or_imp])
      (Code.conjunction (make head) (fun _ => rows claim make tail))

def count {α : Type} [DecidableEq α] (test : (left right : α) → Code Key (.truth (left = right))) (key : α) :
    (items : List α) → Code Key (.number (fun amount => amount = items.count key))
  | [] => .pure ⟨0,rfl⟩
  | head::tail => .bind (test head key) fun answer => match answer with
    | .isFalse different => .bind (count test key tail) fun later =>
        .pure ⟨later.val,by rw [later.property];simp [different]⟩
    | .isTrue same => .bind (count test key tail) fun later =>
        .bind (.atom (.increment later.val)) fun next =>
          .pure ⟨next.val,by rw [next.property,later.property];simp [same]⟩

def countLe {α : Type} [DecidableEq α] (test : (left right : α) → Code Key (.truth (left = right))) (key : α) (left right : List α) :
    Code Key (.truth (left.count key ≤ right.count key)) :=
  .bind (count test key left) fun first => .bind (count test key right) fun second =>
    Code.transport (by rw [first.property,second.property]) (.atom (.natural first.val second.val))

def subperm {α : Type} [DecidableEq α] (test : (left right : α) → Code Key (.truth (left = right))) (left right : List α) : Code Key (.truth (left.Subperm right)) :=
  Code.transport List.subperm_ext_iff.symm (rows (fun key => left.count key ≤ right.count key) (fun key => countLe test key left right) left)
end Generic

variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
local notation "Program" => Code (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))

def nativeEqual (left right : NativeBenefit.NativeKey (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) : Program (.truth (left = right)) :=
  Generic.equal NativeAdmission.Atom.native (by intro a b same;cases same;rfl) left right

def inventory (new previous : Feedback.Authority.Trace.Manifest P G O T I) : Program (.truth
    ((Feedback.Authority.Trace.Lawful.inventory new).due.Subperm (Feedback.Authority.Trace.Lawful.inventory previous).due ∧
      (Feedback.Authority.Trace.Lawful.inventory new).admitted = (Feedback.Authority.Trace.Lawful.inventory previous).admitted)) :=
  let current := Feedback.Authority.Trace.Lawful.inventory new
  let original := Feedback.Authority.Trace.Lawful.inventory previous
  Code.conjunction (Generic.subperm nativeEqual current.due original.due)
    (fun _ => Generic.lists nativeEqual current.admitted original.admitted)

def profile (new previous : Settlement.Profile P G O (Mandate.State P T) I) : Program (.truth (new = previous)) :=
  let debt := Generic.equal (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) NativeAdmission.Atom.debt (by intro a b same;cases same;rfl)
  let quantity := Generic.equal (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) NativeAdmission.Atom.quantity (by intro a b same;cases same;rfl)
  let service := Generic.equal (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) NativeAdmission.Atom.service (by intro a b same;cases same;rfl)
  let control := Generic.equal (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) NativeAdmission.Atom.control (by intro a b same;cases same;rfl)
  Code.transport (by cases new;cases previous;simp only [Settlement.Profile.mk.injEq])
    (Code.conjunction (Generic.lists debt new.originalDebts previous.originalDebts) (fun _ =>
      Code.conjunction (Generic.lists debt new.newbornDebts previous.newbornDebts) (fun _ =>
        Code.conjunction (Generic.lists (Generic.lists quantity) new.rights previous.rights) (fun _ =>
          Code.conjunction (Generic.lists quantity new.uncoveredClaims previous.uncoveredClaims) (fun _ =>
            Code.conjunction (Generic.lists service new.firstServices previous.firstServices) (fun _ => control new.control previous.control))))))

variable {driver : Feedback.Input seed.source.code} (cursor : Online.Cursor seed driver)
def evaluation (new previous : Evaluation cursor.source.val.code) : Program (.truth (Full.EvaluationLe cursor new previous)) :=
  Code.transport (by unfold Full.EvaluationLe Planning.evaluationBenefit;tauto)
    (Code.conjunction (Code.implication (.atom (.boolean previous.legal)) (fun _ => .atom (.boolean new.legal))) (fun _ =>
      Code.conjunction (Code.implication (.atom (.boolean previous.complete)) (fun _ => .atom (.boolean new.complete))) (fun _ =>
        Code.conjunction (inventory new.native previous.native) (fun _ =>
          Code.conjunction (profile new.profile previous.profile) (fun _ =>
            Generic.rows (fun axis => new.value axis ≤ previous.value axis) (fun axis => .atom (.rational (new.value axis) (previous.value axis)))
              (Window.axes cursor.model cursor.depth))))))

def future : (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) → Program (.truth (Full.FutureLe cursor new previous))
  | none,none => .pure (.isTrue trivial)
  | some _,none => .pure (.isTrue trivial)
  | none,some _ => .pure (.isFalse id)
  | some current,some original => Code.conjunction (.atom (.natural original.consumed current.consumed))
      (fun _ => evaluation cursor current.evaluation original.evaluation)

def tensor (new previous : Planning.Tensor cursor) : Program (.truth (Full.TensorLe cursor new previous)) :=
  Code.conjunction (evaluation cursor new.present previous.present) (fun _ =>
    Code.conjunction (Generic.rows (fun word => Full.FutureLe cursor (new.future cursor word) (previous.future cursor word))
      (fun word => future cursor (new.future cursor word) (previous.future cursor word)) (Future.Recovery.capabilities cursor.model cursor.depth)) (fun _ =>
        Generic.rows (fun word => (previous.funding cursor word).isNone = true → (new.funding cursor word).isNone = true)
          (fun word => Code.implication (.atom (.boolean (previous.funding cursor word).isNone)) (fun _ => .atom (.boolean (new.funding cursor word).isNone)))
          (Future.Recovery.capabilities cursor.model cursor.depth)))

variable (pool : List (Offer (prepared := prepared) (position := position)))
def responsibility (new previous : Offer (prepared := prepared) (position := position)) : Program (.truth (ResponsibilityLe pool new previous)) :=
  let tensors := Generic.rows (fun index => ∀ table ∈ Choice.tables pool index,
      Full.TensorLe (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
        ((previous.view index).tensor (Choice.rival pool index table)))
    (fun index => Generic.rows _ (fun table => tensor (Policy.initial input prepared.saved[index].point)
      ((new.view index).tensor (Choice.rival pool index table)) ((previous.view index).tensor (Choice.rival pool index table))) (Choice.tables pool index)) (keys prepared)
  let costs := Generic.rows (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))
    (fun index : Index prepared => new.work index ≤ previous.work index ∧ previous.credit index ≤ new.credit index)
    (fun index => Code.conjunction (.atom (.natural (new.work index) (previous.work index))) (fun _ => .atom (.natural (previous.credit index) (new.credit index)))) (keys prepared)
  let invoices := Code.conjunction (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))
    (.atom (.natural new.branch.alternative.1 previous.branch.alternative.1)) (fun _ =>
      Code.conjunction (.atom (.natural new.invoiceWork previous.invoiceWork)) (fun _ => .atom (.natural previous.invoiceCredit new.invoiceCredit)))
  Code.transport (by unfold ResponsibilityLe;simp only [keys,List.mem_finRange,forall_const])
    (Code.conjunction tensors (fun _ => Code.conjunction costs (fun _ => invoices)))

def strict (previous new : Offer (prepared := prepared) (position := position)) :
    Program (.truth (ResponsibilityLe pool new previous ∧ ¬ResponsibilityLe pool previous new)) :=
  Code.conjunction (responsibility pool new previous) (fun _ => Code.negative (responsibility pool previous new))

def verify (reference candidate : Offer (prepared := prepared) (position := position)) : Program (.truth
    (ResponsibilityLe pool candidate reference ∧ ∀ other ∈ pool,¬(ResponsibilityLe pool other candidate ∧ ¬ResponsibilityLe pool candidate other))) :=
  Code.conjunction (responsibility pool candidate reference) (fun _ =>
    Generic.rows _ (fun other => Code.negative (strict pool candidate other)) pool)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Source
