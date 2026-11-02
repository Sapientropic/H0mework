import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeAdmission
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SignatureWork
variable {Key : Type}

def optional {α : Type} (test : (left right : α) → NativeBenefit.Check Key (left = right)) :
    (left right : Option α) → NativeBenefit.Check Key (left = right)
  | none,none => NativeBenefit.transport (by simp) (NativeBenefit.boolean true)
  | some left,some right => NativeBenefit.record [.boolean true] (NativeBenefit.transport (by simp) (test left right))
  | none,some _ | some _,none => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
def optionalBudget {α : Type} (budget : α → α → Nat) : Option α → Option α → Nat
  | some left,some right => 1+budget left right
  | _,_ => 1
theorem optional_work_bound {α : Type} (test : (left right : α) → NativeBenefit.Check Key (left = right))
    (budget : α → α → Nat) (bounded : ∀ left right,(test left right).work.length ≤ budget left right)
    (left right : Option α) : (optional test left right).work.length ≤ optionalBudget budget left right := by
  cases left <;> cases right <;> simp only [optional,optionalBudget,NativeBenefit.transport,NativeBenefit.record,NativeBenefit.boolean,List.length_append,List.length_singleton]
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.add_le_add_left (bounded _ _) 1
private def tag {P : Prop} (made : NativeBenefit.Check Key P) := NativeBenefit.record [.boolean true] made
private theorem tag_bound {P : Prop} (made : NativeBenefit.Check Key P) (budget : Nat) (bounded : made.work.length ≤ budget) :
    (tag made).work.length ≤ 1+budget := by
  simpa only [tag,NativeBenefit.record,List.length_append,List.length_singleton] using Nat.add_le_add_left bounded 1
private theorem pair_bound {P Q : Prop} (first : NativeBenefit.Check Key P) (later : Unit → NativeBenefit.Check Key Q)
    (a b : Nat) (left : first.work.length ≤ a) (right : (later ()).work.length ≤ b) :
    (NativeBenefit.conjunction first later).work.length ≤ a+1+b :=
  (NativeBenefit.conjunction_work_bound first later).trans (by omega)

namespace Generic
variable {Action : Type}
variable (test : (left right : Action) → NativeBenefit.Check Key (left = right))
  (cost : Action → Action → Nat) (bounded : ∀ left right,(test left right).work.length ≤ cost left right)

def word (left right : List Action) := NativeAdmission.listsEqual test left right
def wordBudget (left right : List Action) := NativeAdmission.listsBudget cost left right
include bounded in
theorem word_work_bound (left right : List Action) : (word test left right).work.length ≤ wordBudget cost left right :=
  NativeAdmission.lists_work_bound test cost bounded left right

def words (left right : List (List Action)) := NativeAdmission.listsEqual (word test) left right
def wordsBudget (left right : List (List Action)) := NativeAdmission.listsBudget (wordBudget cost) left right
include bounded in
theorem words_work_bound (left right : List (List Action)) : (words test left right).work.length ≤ wordsBudget cost left right :=
  NativeAdmission.lists_work_bound (word test) (wordBudget cost) (word_work_bound test cost bounded) left right

def invoice (left right : Option (List Action)) := optional (word test) left right
def invoiceBudget (left right : Option (List Action)) := optionalBudget (wordBudget cost) left right
include bounded in
theorem invoice_work_bound (left right : Option (List Action)) : (invoice test left right).work.length ≤ invoiceBudget cost left right :=
  optional_work_bound (word test) (wordBudget cost) (word_work_bound test cost bounded) left right

def control (left right : List (Option (List (List Action)))) := NativeAdmission.listsEqual (optional (words test)) left right
def controlBudget (left right : List (Option (List (List Action)))) := NativeAdmission.listsBudget (optionalBudget (wordsBudget cost)) left right
include bounded in
theorem control_work_bound (left right : List (Option (List (List Action)))) :
    (control test left right).work.length ≤ controlBudget cost left right :=
  NativeAdmission.lists_work_bound (optional (words test)) (optionalBudget (wordsBudget cost))
    (optional_work_bound (words test) (wordsBudget cost) (words_work_bound test cost bounded)) left right

def compare : (left right : Signature Action) → NativeBenefit.Check Key (left = right)
  | .keep headerL,.keep headerR => tag (NativeBenefit.transport (by simp only [Signature.keep.injEq]) (word test headerL headerR))
  | .direct headerL controlL,.direct headerR controlR => tag (NativeBenefit.transport (by simp only [Signature.direct.injEq]) (NativeBenefit.conjunction (word test headerL headerR) (fun _ => control test controlL controlR)))
  | .own headerL requestedL controlL,.own headerR requestedR controlR => tag (NativeBenefit.transport (by simp only [Signature.own.injEq]) (NativeBenefit.conjunction (word test headerL headerR) (fun _ => NativeBenefit.conjunction (word test requestedL requestedR) (fun _ => control test controlL controlR))))
  | .invoiced headerL requestedL invoiceL controlL,.invoiced headerR requestedR invoiceR controlR => tag (NativeBenefit.transport (by simp only [Signature.invoiced.injEq]) (NativeBenefit.conjunction (word test headerL headerR) (fun _ => NativeBenefit.conjunction (word test requestedL requestedR) (fun _ => NativeBenefit.conjunction (invoice test invoiceL invoiceR) (fun _ => control test controlL controlR)))))
  | .stopped invoiceL,.stopped invoiceR => tag (NativeBenefit.transport (by simp only [Signature.stopped.injEq]) (invoice test invoiceL invoiceR))
  | .prefix committedL nextL,.prefix committedR nextR => tag (NativeBenefit.transport (by simp only [Signature.prefix.injEq]) (NativeBenefit.conjunction (words test committedL committedR) (fun _ => compare nextL nextR)))
  | .keep _,.direct _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .keep _,.own _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .keep _,.invoiced _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .keep _,.stopped _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .keep _,.prefix _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .direct _ _,.keep _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .direct _ _,.own _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .direct _ _,.invoiced _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .direct _ _,.stopped _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .direct _ _,.prefix _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .own _ _ _,.keep _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .own _ _ _,.direct _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .own _ _ _,.invoiced _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .own _ _ _,.stopped _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .own _ _ _,.prefix _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .invoiced _ _ _ _,.keep _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .invoiced _ _ _ _,.direct _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .invoiced _ _ _ _,.own _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .invoiced _ _ _ _,.stopped _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .invoiced _ _ _ _,.prefix _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .stopped _,.keep _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .stopped _,.direct _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .stopped _,.own _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .stopped _,.invoiced _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .stopped _,.prefix _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .prefix _ _,.keep _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .prefix _ _,.direct _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .prefix _ _,.own _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .prefix _ _,.invoiced _ _ _ _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)
  | .prefix _ _,.stopped _ => NativeBenefit.transport (by simp) (NativeBenefit.boolean false)

def budget : Signature Action → Signature Action → Nat
  | .keep headerL,.keep headerR => 1+wordBudget cost headerL headerR
  | .direct headerL controlL,.direct headerR controlR => 1+(wordBudget cost headerL headerR+1+controlBudget cost controlL controlR)
  | .own headerL requestedL controlL,.own headerR requestedR controlR => 1+(wordBudget cost headerL headerR+1+(wordBudget cost requestedL requestedR+1+controlBudget cost controlL controlR))
  | .invoiced headerL requestedL invoiceL controlL,.invoiced headerR requestedR invoiceR controlR => 1+(wordBudget cost headerL headerR+1+(wordBudget cost requestedL requestedR+1+(invoiceBudget cost invoiceL invoiceR+1+controlBudget cost controlL controlR)))
  | .stopped invoiceL,.stopped invoiceR => 1+invoiceBudget cost invoiceL invoiceR
  | .prefix committedL nextL,.prefix committedR nextR => 1+(wordsBudget cost committedL committedR+1+budget nextL nextR)
  | _,_ => 1

include bounded in
theorem work_bound (left right : Signature Action) : (compare test left right).work.length ≤ budget cost left right := by
  induction left generalizing right with
  | keep headerL =>
    cases right with
    | keep headerR =>
      change (tag (word test headerL headerR)).work.length ≤ 1+wordBudget cost headerL headerR
      exact tag_bound _ _ (word_work_bound test cost bounded headerL headerR)
    | direct headerR controlR =>
      exact Nat.le_refl 1
    | own headerR requestedR controlR =>
      exact Nat.le_refl 1
    | invoiced headerR requestedR invoiceR controlR =>
      exact Nat.le_refl 1
    | stopped invoiceR =>
      exact Nat.le_refl 1
    | «prefix» committedR nextR =>
      exact Nat.le_refl 1
  | direct headerL controlL =>
    cases right with
    | keep headerR =>
      exact Nat.le_refl 1
    | direct headerR controlR =>
      change (tag (NativeBenefit.conjunction (word test headerL headerR) (fun _ => control test controlL controlR))).work.length ≤ 1+(wordBudget cost headerL headerR+1+controlBudget cost controlL controlR)
      exact tag_bound _ _ (pair_bound (word test headerL headerR) (fun _ => control test controlL controlR) (wordBudget cost headerL headerR) (controlBudget cost controlL controlR) (word_work_bound test cost bounded headerL headerR) (control_work_bound test cost bounded controlL controlR))
    | own headerR requestedR controlR =>
      exact Nat.le_refl 1
    | invoiced headerR requestedR invoiceR controlR =>
      exact Nat.le_refl 1
    | stopped invoiceR =>
      exact Nat.le_refl 1
    | «prefix» committedR nextR =>
      exact Nat.le_refl 1
  | own headerL requestedL controlL =>
    cases right with
    | keep headerR =>
      exact Nat.le_refl 1
    | direct headerR controlR =>
      exact Nat.le_refl 1
    | own headerR requestedR controlR =>
      change (tag (NativeBenefit.conjunction (word test headerL headerR) (fun _ => NativeBenefit.conjunction (word test requestedL requestedR) (fun _ => control test controlL controlR)))).work.length ≤ 1+(wordBudget cost headerL headerR+1+(wordBudget cost requestedL requestedR+1+controlBudget cost controlL controlR))
      exact tag_bound _ _ (pair_bound (word test headerL headerR) (fun _ => NativeBenefit.conjunction (word test requestedL requestedR) (fun _ => control test controlL controlR)) (wordBudget cost headerL headerR) ((wordBudget cost requestedL requestedR+1+controlBudget cost controlL controlR)) (word_work_bound test cost bounded headerL headerR) (pair_bound (word test requestedL requestedR) (fun _ => control test controlL controlR) (wordBudget cost requestedL requestedR) (controlBudget cost controlL controlR) (word_work_bound test cost bounded requestedL requestedR) (control_work_bound test cost bounded controlL controlR)))
    | invoiced headerR requestedR invoiceR controlR =>
      exact Nat.le_refl 1
    | stopped invoiceR =>
      exact Nat.le_refl 1
    | «prefix» committedR nextR =>
      exact Nat.le_refl 1
  | invoiced headerL requestedL invoiceL controlL =>
    cases right with
    | keep headerR =>
      exact Nat.le_refl 1
    | direct headerR controlR =>
      exact Nat.le_refl 1
    | own headerR requestedR controlR =>
      exact Nat.le_refl 1
    | invoiced headerR requestedR invoiceR controlR =>
      change (tag (NativeBenefit.conjunction (word test headerL headerR) (fun _ => NativeBenefit.conjunction (word test requestedL requestedR) (fun _ => NativeBenefit.conjunction (invoice test invoiceL invoiceR) (fun _ => control test controlL controlR))))).work.length ≤ 1+(wordBudget cost headerL headerR+1+(wordBudget cost requestedL requestedR+1+(invoiceBudget cost invoiceL invoiceR+1+controlBudget cost controlL controlR)))
      exact tag_bound _ _ (pair_bound (word test headerL headerR) (fun _ => NativeBenefit.conjunction (word test requestedL requestedR) (fun _ => NativeBenefit.conjunction (invoice test invoiceL invoiceR) (fun _ => control test controlL controlR))) (wordBudget cost headerL headerR) ((wordBudget cost requestedL requestedR+1+(invoiceBudget cost invoiceL invoiceR+1+controlBudget cost controlL controlR))) (word_work_bound test cost bounded headerL headerR) (pair_bound (word test requestedL requestedR) (fun _ => NativeBenefit.conjunction (invoice test invoiceL invoiceR) (fun _ => control test controlL controlR)) (wordBudget cost requestedL requestedR) ((invoiceBudget cost invoiceL invoiceR+1+controlBudget cost controlL controlR)) (word_work_bound test cost bounded requestedL requestedR) (pair_bound (invoice test invoiceL invoiceR) (fun _ => control test controlL controlR) (invoiceBudget cost invoiceL invoiceR) (controlBudget cost controlL controlR) (invoice_work_bound test cost bounded invoiceL invoiceR) (control_work_bound test cost bounded controlL controlR))))
    | stopped invoiceR =>
      exact Nat.le_refl 1
    | «prefix» committedR nextR =>
      exact Nat.le_refl 1
  | stopped invoiceL =>
    cases right with
    | keep headerR =>
      exact Nat.le_refl 1
    | direct headerR controlR =>
      exact Nat.le_refl 1
    | own headerR requestedR controlR =>
      exact Nat.le_refl 1
    | invoiced headerR requestedR invoiceR controlR =>
      exact Nat.le_refl 1
    | stopped invoiceR =>
      change (tag (invoice test invoiceL invoiceR)).work.length ≤ 1+invoiceBudget cost invoiceL invoiceR
      exact tag_bound _ _ (invoice_work_bound test cost bounded invoiceL invoiceR)
    | «prefix» committedR nextR =>
      exact Nat.le_refl 1
  | «prefix» committedL nextL ih =>
    cases right with
    | keep headerR =>
      exact Nat.le_refl 1
    | direct headerR controlR =>
      exact Nat.le_refl 1
    | own headerR requestedR controlR =>
      exact Nat.le_refl 1
    | invoiced headerR requestedR invoiceR controlR =>
      exact Nat.le_refl 1
    | stopped invoiceR =>
      exact Nat.le_refl 1
    | «prefix» committedR nextR =>
      change (tag (NativeBenefit.conjunction (words test committedL committedR) (fun _ => compare test nextL nextR))).work.length ≤ 1+(wordsBudget cost committedL committedR+1+budget cost nextL nextR)
      exact tag_bound _ _ (pair_bound (words test committedL committedR) (fun _ => compare test nextL nextR) (wordsBudget cost committedL committedR) (budget cost nextL nextR) (words_work_bound test cost bounded committedL committedR) (ih nextR))

end Generic

variable {Action : Type} [DecidableEq Action]
def word := Generic.word (Action := Action) NativeBenefit.equal
def wordBudget := Generic.wordBudget (Action := Action) (fun _ _ => 1)
theorem word_work_bound (left right : List Action) : (word left right).work.length ≤ wordBudget left right :=
  Generic.word_work_bound NativeBenefit.equal (fun _ _ => 1) (fun _ _ => Nat.le_refl _) left right
def words := Generic.words (Action := Action) NativeBenefit.equal
def wordsBudget := Generic.wordsBudget (Action := Action) (fun _ _ => 1)
theorem words_work_bound (left right : List (List Action)) : (words left right).work.length ≤ wordsBudget left right :=
  Generic.words_work_bound NativeBenefit.equal (fun _ _ => 1) (fun _ _ => Nat.le_refl _) left right
def invoice := Generic.invoice (Action := Action) NativeBenefit.equal
def invoiceBudget := Generic.invoiceBudget (Action := Action) (fun _ _ => 1)
theorem invoice_work_bound (left right : Option (List Action)) : (invoice left right).work.length ≤ invoiceBudget left right :=
  Generic.invoice_work_bound NativeBenefit.equal (fun _ _ => 1) (fun _ _ => Nat.le_refl _) left right
def control := Generic.control (Action := Action) NativeBenefit.equal
def controlBudget := Generic.controlBudget (Action := Action) (fun _ _ => 1)
theorem control_work_bound (left right : List (Option (List (List Action)))) : (control left right).work.length ≤ controlBudget left right :=
  Generic.control_work_bound NativeBenefit.equal (fun _ _ => 1) (fun _ _ => Nat.le_refl _) left right

def compare (left right : Signature Action) := Generic.compare NativeBenefit.equal left right
def budget (left right : Signature Action) := Generic.budget (fun _ _ => 1) left right
theorem work_bound (left right : Signature Action) : (compare left right).work.length ≤ budget left right :=
  Generic.work_bound NativeBenefit.equal (fun _ _ => 1) (fun _ _ => Nat.le_refl _) left right

def Event.expanded : NativeBenefit.Event Key → Bool
  | .boolean _ | .branch _ => true
  | _ => false
def expanded (work : List (NativeBenefit.Event Key)) := (work.filter Event.expanded).length
theorem expanded_work_bound (left right : Signature Action) : expanded (compare left right).work ≤ budget left right :=
  (List.length_filter_le _ _).trans (work_bound left right)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SignatureWork
