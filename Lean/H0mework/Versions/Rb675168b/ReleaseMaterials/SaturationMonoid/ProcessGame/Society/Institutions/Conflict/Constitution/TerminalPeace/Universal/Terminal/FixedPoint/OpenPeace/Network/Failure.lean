import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Install

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open Reparation.Actual (First)

noncomputable section

private theorem cast_row_heq {N : WorldRelationNetwork} {s t : N.Support}
    (same : s = t) (entry : OpenResponsibilityAt N s) :
    HEq ((ConstructivePresentation.cast (F := OpenResponsibilityAt N) same).forward entry) entry := by
  cases same
  rfl

private theorem carried_heq {N : WorldRelationNetwork} {s t : N.Support}
    (same : s = t) {left : OpenResponsibilityAt N s} {right : OpenResponsibilityAt N t}
    (entry : HEq left right) :
    HEq (LedgerEntryDispositionAt.evolved (.carried rfl HEq.rfl) : LedgerEntryDispositionAt N left)
      (LedgerEntryDispositionAt.evolved (.carried rfl HEq.rfl) : LedgerEntryDispositionAt N right) := by
  cases same
  cases eq_of_heq entry
  rfl

private theorem row_is_carried_at_landing {N : WorldRelationNetwork}
    (first : First N) {current : Bool} (arrived : current = true)
    (entry : OpenResponsibilityAt N (first.support current)) :
    ((Compiler.ledgerCompiler first.flow).compile (Compiler.emitted first.flow current)).entryDisposition entry =
      .evolved (.carried rfl HEq.rfl) := by
  cases arrived
  exact after_first_write_keeps_row first entry

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (prior : Installation.Live.Ledger seed community cut)
  (grammar : Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument))
  (observed : Set (Effect Party Good Port Technology Instrument))
  (lane : LocalU7 prior.world)
  (novel : ¬ observed ⊆ grammar.covered)

local notation "N₀" => LocalU7.asWorld lane
local notation "Focus" => prior.resident.support
local notation "Bearer" => prior.resident.entry
local notation "OldTheory" => LocalU7.restrictTheory lane prior.resident.root.source.base.lawSurface
local notation "OldRow" => inheritedBearer N₀ Focus Bearer grammar observed
local notation "Obstruction" => obstruction N₀ Focus Bearer grammar observed novel
local notation "Failure" => failure N₀ Focus Bearer grammar observed OldTheory novel
local notation "ExtendedU7" => u7 N₀ Focus Bearer grammar observed (LocalU7.producer lane)
local notation "Calculus" => calculus N₀ Focus Bearer grammar observed (LocalU7.producer lane) (LocalU7.calculus lane)
local notation "AuditEvent" => U7ActualSuccessorSource.emit (U7ObstructionEvolutionCalculus.source Calculus) Obstruction
local notation "Resident" => auditResident prior grammar observed lane novel
local notation "TokenFace" => installedToken prior grammar observed lane novel

/-- The installed failure and the U7 compiler both read the same bearer
and its whole-ledger carry at the restricted epoch's actual successor. -/
def failureFace :
    SourceNativeRootExpressibilityFailureFaceAt (Resident).root.toAuthoritativeRoot
      (Resident).visit (U7 := ExtendedU7) Failure where
  lawSurface_eq := rfl
  projection := (TokenFace).projection
  active := (TokenFace).active
  classifier_eq := (TokenFace).classifier_eq
  calculus := Calculus
  u7Event := AuditEvent
  u7Event_eq_emit := rfl
  theoryAudit := audit N₀ Focus Bearer grammar observed (LocalU7.producer lane) (LocalU7.calculus lane) novel
  support_eq := audit_support prior grammar observed lane novel
  rootEntry := (Resident).entry
  rootEntryAtFailure_eq := by
    apply eq_of_heq
    exact (cast_row_heq (audit_support prior grammar observed lane novel) (Resident).entry).trans
      ((audit_bearer_kept prior grammar observed lane novel).trans
        (heq_of_eq (audit_demand_entry N₀ Focus Bearer grammar observed (LocalU7.producer lane) (LocalU7.calculus lane) novel).symm))
  rootDispositionCommutes := by
    have same := audit_support prior grammar observed lane novel
    have entry := audit_bearer_kept prior grammar observed lane novel
    have carried := row_is_carried_at_landing (auditFirst prior grammar observed lane)
      (audit_lands_at_first_write prior grammar observed lane novel) (Resident).entry
    exact ⟨entry.trans (heq_of_eq (audit_demand_entry N₀ Focus Bearer grammar observed (LocalU7.producer lane) (LocalU7.calculus lane) novel).symm),
      (heq_of_eq carried).trans ((carried_heq same entry).trans
        (audit_entry_disposition N₀ Focus Bearer grammar observed (LocalU7.producer lane) (LocalU7.calculus lane) novel).symm)⟩
  project_heq := installed_token_is_exact prior grammar observed lane novel

def rootedFailure :
    RootedActualExpressibilityFailureAt (Resident).root.toAuthoritativeRoot (Resident).visit ExtendedU7 Failure :=
  RootedActualExpressibilityFailureAt.ofRootFailureFace
    (failureFace prior grammar observed lane novel)
    (Resident).authority.toAuthoritativeAuthority
    (CausalEntrySuccessorAt.ofNonterminal
      (Compiler.successor (auditFirst prior grammar observed lane).flow (Resident).visit.current).next_eq)

theorem rooted_failure_retains_the_bearer :
    HEq (rootedFailure prior grammar observed lane novel).rootEntry OldRow :=
  audit_bearer_kept prior grammar observed lane novel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
