import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding.Order
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Selection

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family

/-- Each actual candidate keeps its own dependent report and refusal types.
The comparison does not identify different source occurrences. -/
structure Tensor (Present Query : Type) (Report Refusal : Present → Query → Type) where
  present : Present
  restoration : (query : Query) → Option (Report present query × Option (Refusal present query))

variable {Present Query : Type} {Report Refusal : Present → Query → Type}

namespace Tensor
variable (tensor : Tensor Present Query Report Refusal) (query : Query)
def future := (tensor.restoration query).map Prod.fst
def funding := (tensor.restoration query).bind Prod.snd
end Tensor

variable (presentNoWorse : Present → Present → Prop)
  (reportNoWorse : (new previous : Present) → (query : Query) → Report new query → Report previous query → Prop)

def ReportsNoWorse {New Previous : Type} (relation : New → Previous → Prop) : Option New → Option Previous → Prop
  | some current,some old => relation current old
  | _,_ => False

def futureNoWorse (new previous : Tensor Present Query Report Refusal) (query : Query) : Prop :=
  ReportsNoWorse (reportNoWorse new.present previous.present query) (new.future query) (previous.future query)

def Accepts (required : List Query) (new previous : Tensor Present Query Report Refusal) : Prop :=
  presentNoWorse new.present previous.present ∧
    (∀ query ∈ required,futureNoWorse reportNoWorse new previous query) ∧
    ∀ query ∈ required,Distributed.Reaction.Native.Future.Recovery.Funding.NoWorse
      (new.funding query) (previous.funding query)

variable [DecidableRel presentNoWorse]
  [∀ new previous query (left : Report new query) (right : Report previous query),
    Decidable (reportNoWorse new previous query left right)]

instance (new previous : Tensor Present Query Report Refusal) (query : Query) :
    Decidable (futureNoWorse reportNoWorse new previous query) := by
  unfold futureNoWorse ReportsNoWorse
  split <;> infer_instance

instance (required : List Query) (new previous : Tensor Present Query Report Refusal) :
    Decidable (Accepts presentNoWorse reportNoWorse required new previous) := by
  unfold Accepts
  infer_instance

inductive Failure (required : List Query) (new previous : Tensor Present Query Report Refusal) where
  | present (broken : ¬ presentNoWorse new.present previous.present)
  | future (query : Query) (required : query ∈ required)
      (broken : ¬ futureNoWorse reportNoWorse new previous query)
  | funding (query : Query) (required : query ∈ required)
      (previousPaid : (previous.funding query).isNone = true)
      (nowRefused : (new.funding query).isNone ≠ true)

def explain (required : List Query) (new previous : Tensor Present Query Report Refusal)
    (denied : ¬ Accepts presentNoWorse reportNoWorse required new previous) :
    Failure presentNoWorse reportNoWorse required new previous :=
  if present : presentNoWorse new.present previous.present then
    match Distributed.inspect (futureNoWorse reportNoWorse new previous) required with
    | .rejected query inside broken => .future query inside broken
    | .accepted futures =>
      match Distributed.inspect (fun query => Distributed.Reaction.Native.Future.Recovery.Funding.NoWorse
          (new.funding query) (previous.funding query)) required with
      | .rejected query inside broken =>
          have previousPaid : (previous.funding query).isNone = true := by
            by_contra absent
            exact broken (fun yes => (absent yes).elim)
          .funding query inside previousPaid (fun paid => broken (fun _ => paid))
      | .accepted funding => False.elim (denied ⟨present,futures,funding⟩)
  else .present present

inductive Inspection (required : List Query) (new previous : Tensor Present Query Report Refusal) where
  | accepted (checked : Accepts presentNoWorse reportNoWorse required new previous)
  | rejected (failure : Failure presentNoWorse reportNoWorse required new previous)

def inspect (required : List Query) (new previous : Tensor Present Query Report Refusal) :
    Inspection presentNoWorse reportNoWorse required new previous :=
  if checked : Accepts presentNoWorse reportNoWorse required new previous then .accepted checked
  else .rejected (explain presentNoWorse reportNoWorse required new previous checked)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family
