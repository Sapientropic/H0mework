import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.ScheduledAuthority
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Revision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open Reparation.Actual (First)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (prior : Installation.Live.Ledger seed community cut)
  (grammar : Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument))
  (observed : Set (Effect Party Good Port Technology Instrument))
  (lane : LocalU7 prior.world) (novel : ¬ observed ⊆ grammar.covered)

local notation "Audit" => auditResident prior grammar observed lane novel
local notation "FirstAudit" => auditFirst prior grammar observed lane
local notation "Failure" => rootedFailure prior grammar observed lane novel
local notation "AuditNext" => CausalEntrySuccessorAt.targetVisit (RootedActualExpressibilityFailureAt.oldSuccessor (Failure))
local notation "Revised" => generatedNext prior grammar observed lane novel
local notation "OldFinite" => targetFinite prior grammar observed lane novel
local notation "OldFibres" => First.openFibres (FirstAudit)
local notation "Repair" => grammar.repair observed

private theorem auditCurrent_eq :
    (Audit).visit.current = (AuditNext).current := by
  change (Audit).visit.current = (Failure).oldSuccessor.next
  let generated := Compiler.successor (FirstAudit).flow (Audit).visit.current
  have target_eq : (Failure).oldSuccessor.next = generated.targetCurrent :=
    Option.some.inj ((Failure).oldSuccessor.next_eq.symm.trans generated.next_eq)
  have target_true : generated.targetCurrent = true :=
    Compiler.successor_current (FirstAudit).flow (Audit).visit.current
  exact (audit_lands_at_first_write prior grammar observed lane novel).trans (target_eq.trans target_true).symm

variable {Payload : Type}

private def onAudit (input : ReadOn prior.resident Payload) : ReadOn (Audit) Payload :=
  input.freezeWrite (auditBase prior grammar observed lane)
    (auditProjection prior grammar observed lane novel) (Audit).visit

private def atAuditSuccessor (input : ReadOn prior.resident Payload) :
    ReadAt (Audit).root (AuditNext) Payload :=
  (onAudit prior grammar observed lane novel input).atSameCurrent
    (auditCurrent_eq prior grammar observed lane novel)

private def onRevision (input : ReadOn prior.resident Payload) : ReadOn (Revised) Payload :=
  (atAuditSuccessor prior grammar observed lane novel input).freezeWrite
    (Compiler.livingRoot (revisedFirst (Failure) (OldFinite) (OldFibres)).flow)
    (newRead (Failure) (OldFinite) (OldFibres) (Repair))
    (Revised).visit

/-- The signed faces of the original resident pass through the actual U7
audit and U8 first write to the generated dispatch resident. -/
def revisedReads : ReadPath prior.resident (Revised) where
  carry := onRevision prior grammar observed lane novel
  keeps := fun input =>
    (onAudit prior grammar observed lane novel input).atSameCurrent_read
      (auditCurrent_eq prior grammar observed lane novel)


end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
