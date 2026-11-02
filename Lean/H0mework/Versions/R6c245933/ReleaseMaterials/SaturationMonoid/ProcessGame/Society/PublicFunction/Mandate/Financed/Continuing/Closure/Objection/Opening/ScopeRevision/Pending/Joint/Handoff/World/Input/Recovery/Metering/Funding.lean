import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Projection
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Funding
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} {inventory : Inventory epoch} {word : List Action}

/-- Every refusal keeps the actual old request and its own source invoice. -/
inductive Failure (cursor : Recovery.Cursor inventory word) where
  | unpriced (head : Action) (tail : List Action) (pending : cursor.residual = head::tail)
      (absent : quote cursor head.signer = none)
  | construction (head : Action) (tail : List Action) (pending : cursor.residual = head::tail)
      (fee : Fee cursor head.signer) (quoted : quote cursor head.signer = some fee)
      (refused : (attempt fee.request 1 cursor).succeeded = false)
  | comparison (head : Action) (tail : List Action) (pending : cursor.residual = head::tail)
      (fee : Fee cursor head.signer) (quoted : quote cursor head.signer = some fee)
      (paid : (attempt fee.request 1 cursor).succeeded = true)
      (refused : (attempt fee.request (units cursor head.signer fee.request)
        (construction cursor fee.request)).succeeded = false)

def ofResult {cursor : Recovery.Cursor inventory word} : Result cursor → Option (Failure cursor)
  | .finished .. | .searched .. => none
  | .unpriced head tail pending absent => some (.unpriced head tail pending absent)
  | .constructionRefused head tail pending fee quoted refused => some (.construction head tail pending fee quoted refused)
  | .comparisonRefused head tail pending fee quoted paid refused => some (.comparison head tail pending fee quoted paid refused)

variable {cursor : Recovery.Cursor inventory word}

def isFunded : Metering.Projection.Kind → Bool
  | .finished | .searched => true
  | .unpriced | .constructionRefused | .comparisonRefused => false

theorem status_is_the_actual_result (made : Result cursor) :
    (ofResult made).isNone = isFunded (Metering.Projection.read made).kind := by
  cases made <;> rfl

theorem every_failed_bill_retains_its_actual_raw_item (failed : Failure cursor) :
    (∃ head tail, cursor.residual = head::tail ∧ quote cursor head.signer = none) ∨
    ∃ (saved : Recovery.Cursor inventory word) (fee : Action) (count : Nat),
      ∃ item ∈ (Mandate.law base epoch.scope).rawItems saved.before (attempt fee count saved).output,
        item.index = (attempt fee count saved).consumed.length ∧
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request := by
  cases failed with
  | unpriced head tail pending absent => exact Or.inl ⟨head,tail,pending,absent⟩
  | construction head tail pending fee quoted refused =>
      exact Or.inr ⟨cursor,fee.request,1,refused_invoice_has_its_actual_failure _ _ _ refused⟩
  | comparison head tail pending fee quoted paid refused =>
      exact Or.inr ⟨Metering.construction cursor fee.request,fee.request,units cursor head.signer fee.request,
        refused_invoice_has_its_actual_failure _ _ _ refused⟩

theorem failed_funding_never_credits_an_original_request (made : Result cursor)
    (failed : (ofResult made).isSome = true) :
    made.finish.consumed = cursor.consumed ∧ made.finish.residual = cursor.residual := by
  cases made <;> try exact ⟨rfl,rfl⟩
  all_goals cases failed
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Funding
