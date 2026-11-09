import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core.ResidentWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Live

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (Resident StateAt Stack identityWhole Occurrence Balance)
open Reparation.Transport (sourceSupport)

noncomputable section

/-- A faithful restriction of the live ledger. -/
structure RowRestriction (A B : WorldRelationNetwork) (s : A.Support) (t : B.Support) where
  rows : OpenResponsibilityAt A s ↪ OpenResponsibilityAt B t
  responsibility : A.Responsibility ↪ B.Responsibility
  claim : A.Claim ↪ B.Claim
  responsibility_eq : ∀ row, (rows row).1 = responsibility row.1
  claim_eq : ∀ row, (rows row).claim = claim row.claim
  budget_eq : ∀ row, (rows row).progressBudget = row.progressBudget

namespace RowRestriction

variable {A B D : WorldRelationNetwork} {s : A.Support} {t : B.Support} {v : D.Support}

def atSameSupport {u : A.Support} (same : s = u) : RowRestriction A A s u := by
  cases same
  exact ⟨Function.Embedding.refl _, Function.Embedding.refl _, Function.Embedding.refl _,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def trans (left : RowRestriction A B s t) (right : RowRestriction B D t v) :
    RowRestriction A D s v where
  rows := left.rows.trans right.rows
  responsibility := left.responsibility.trans right.responsibility
  claim := left.claim.trans right.claim
  responsibility_eq row :=
    (right.responsibility_eq _).trans (congrArg right.responsibility (left.responsibility_eq row))
  claim_eq row := (right.claim_eq _).trans (congrArg right.claim (left.claim_eq row))
  budget_eq row := (right.budget_eq _).trans (left.budget_eq row)

end RowRestriction

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

structure Ledger (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community) (cut : Root.Cut Party Good Port Technology Instrument) where
  private mk ::
  originalWorld : WorldRelationNetwork
  stack : Stack seed community cut.native.frame.N originalWorld
  world : WorldRelationNetwork
  resident : Resident world
  restriction : RowRestriction originalWorld world (stack.support (sourceSupport cut.native)) resident.support
  ready : Core.ResidentWrite.Ready resident

variable {seed cut : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

namespace Ledger

def ofState (prior : StateAt seed community cut) : Ledger seed community cut :=
  ⟨prior.world, prior.stack, prior.world, prior.resident,
    RowRestriction.atSameSupport prior.exactSupport.symm, Core.ready prior⟩

instance : Coe (StateAt seed community cut) (Ledger seed community cut) := ⟨ofState⟩

variable (prior : Ledger seed community cut)

def move {N : WorldRelationNetwork} (next : Resident N)
    (extension : RowRestriction prior.world N prior.resident.support next.support)
    (ready : Core.ResidentWrite.Ready next) : Ledger seed community cut :=
  ⟨prior.originalWorld, prior.stack, N, next, prior.restriction.trans extension, ready⟩

def originalRow (row : OpenResponsibilityAt prior.originalWorld (prior.stack.support (sourceSupport cut.native))) :
    OpenResponsibilityAt prior.world prior.resident.support :=
  prior.restriction.rows row

theorem originalRow_injective : Function.Injective prior.originalRow :=
  prior.restriction.rows.injective

theorem every_balance_has_a_live_row (balance : Occurrence seed community × Balance)
    (present : balance ∈ prior.stack.balances) :
    ∃ original, prior.stack.read (sourceSupport cut.native) original = .inr balance ∧
      ∃ live : OpenResponsibilityAt prior.world prior.resident.support,
        live = prior.originalRow original ∧ live.progressBudget = original.progressBudget := by
  obtain ⟨original, read⟩ := prior.stack.every_balance_has_an_actual_open_row _ balance present
  exact ⟨original, read, prior.originalRow original, rfl, prior.restriction.budget_eq original⟩

end Ledger

structure Landed (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community) (cut : Root.Cut Party Good Port Technology Instrument) (Payload : Type) where
  state : Ledger seed community cut
  material : SourceNativeRootSemanticFaceAt state.resident.root state.resident.visit
  materialType : material.Restriction = Payload

variable {Payload : Type}

def Landed.read (visit : Landed seed community cut Payload) : Payload :=
  cast visit.materialType visit.material.rootRead

variable (prior : Ledger seed community cut) (emission : Payload) (writes : Bool)

def action := Core.ResidentWrite.action prior.resident prior.ready emission writes

def publish : Landed seed community cut Payload where
  state := prior.move (Core.ResidentWrite.landing prior.resident prior.ready emission writes)
    (RowRestriction.atSameSupport (Core.ResidentWrite.support_eq prior.resident prior.ready emission writes).symm)
    ⟨(Core.ResidentWrite.support_eq prior.resident prior.ready emission writes).symm ▸ prior.ready.finite,
      prior.ready.fibres⟩
  material := Core.ResidentWrite.face prior.resident prior.ready emission writes
  materialType := rfl

theorem the_canonical_write_is_the_published_whole_state :
    (⟨prior.world, (action prior emission writes).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (publish prior emission writes).state.resident.erase :=
  Core.ResidentWrite.canonical_next prior.resident prior.ready emission writes

theorem original_rows_are_the_whole_first_write :
    let written := (action prior emission writes).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole prior.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  Core.ResidentWrite.whole_first_write prior.resident prior.ready emission writes

theorem earlier_reads_are_kept_at_the_landing
    (projection : prior.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (publish prior emission writes).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (prior.resident.root.source.base.projectionLaw.outcomeAt projection
        (prior.resident.root.emitted prior.resident.visit.current)) :=
  Core.ResidentWrite.earlier_reads prior.resident prior.ready emission writes projection

theorem publish_reads_the_exact_payload : (publish prior emission writes).read = emission := rfl

theorem publish_preserves_the_entire_stack : (publish prior emission writes).state.stack = prior.stack := rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Live
