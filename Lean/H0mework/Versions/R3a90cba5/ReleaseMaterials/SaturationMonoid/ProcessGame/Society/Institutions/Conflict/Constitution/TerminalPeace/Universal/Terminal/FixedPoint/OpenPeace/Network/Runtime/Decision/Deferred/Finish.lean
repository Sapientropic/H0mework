import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Start

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open private Runtime.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance
open private OpenPeace.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
open private AdaptivePeace.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "St" => Runtime.State (seed := seed) (cut := cut) (community := community)
  origin people quantum (reserveBase := reserveBase)
local notation "Effects" => Set (Effect Party Good Port Technology Instrument)
local notation "Grammar" => Language (RawEvent Party Good Port Technology Instrument)
  (Effect Party Good Port Technology Instrument)

structure Completion (reached : St) (observed : Effects) where
  private mk ::
  next : St
  write : Option (Installation.Live.Landed seed community cut Grammar)
  samePhysical : next.current.physical = reached.current.physical
  sameStack : HEq next.current.ledger.stack reached.current.ledger.stack
  coverage : next.base.language.covered = reached.base.language.covered ∪ observed
  reads : ReadPath reached.current.ledger.resident next.current.ledger.resident

private def completeScope (reached : St) (observed : Effects)
    (checked : Decidable (observed ⊆ reached.base.language.covered)) : Completion reached observed :=
  match checked with
  | .isTrue covered =>
    ⟨reached, none, rfl, HEq.rfl, (Set.union_eq_left.mpr covered).symm, ⟨id, fun _ => rfl⟩⟩
  | .isFalse novel => by
    let prior := reached.current.ledger
    let grammar := reached.base.language
    let write := revisedLanguageWrite prior grammar observed reached.u7 novel
    let retained := revisedReads prior grammar observed reached.u7 novel
    let after := Runtime.State.mk
      (OpenPeace.State.mk (AdaptivePeace.State.mk { reached.current with ledger := write.state }
        reached.base.adaptive.amendment) (some write))
      (reached.lanes.map retained.carry)
      (LocalU7.afterCoface (rootedFailure prior grammar observed reached.u7 novel))
    refine ⟨after, some write, rfl, HEq.rfl, ?_, retained⟩
    change write.read.covered = _
    rw [revisedLanguageWrite_read, Language.covered_repair]

variable {home : AnyAuthoritativeRootCurrent.{0}} {replies : Replies Party Good Port Technology Instrument}
  {before : Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase)}
  {input : OpenPeace.Input Party Good Port Technology Instrument}
  (job : Deferred home replies before input) (policy : Policy Party Good Port Technology Instrument) (n : Nat)

local notation "Reached" => Prod.fst (job.run policy n)
local notation "Observed" => ReadAt.read (Deferred.readAt job policy n)

/-- The checked scope is read from the later resident. The original
charge, waiting rounds and any intervening amendments remain in its history. -/
def Deferred.completeAt (checked : Decidable (Observed ⊆ (Reached).base.language.covered)) :
    Completion (Reached) Observed :=
  completeScope (Reached) Observed checked

def Deferred.completeAtWitness (point : Effect Party Good Port Technology Instrument)
    (observed : point ∈ Observed) (fresh : point ∉ (Reached).base.language.covered) :
    Completion (Reached) Observed :=
  job.completeAt policy n (.isFalse fun included => fresh (included observed))

theorem Deferred.completion_reads_the_original_request
    (checked : Decidable (Observed ⊆ (Reached).base.language.covered)) :
    let done := job.completeAt policy n checked
    ((done.reads.carry (job.readAt policy n)).read = Runtime.scope home replies before input) ∧
      Runtime.scope home replies before input ⊆ done.next.base.language.covered := by
  intro done
  have exactScope := job.readAt_is_the_original_paid_scope policy n
  refine ⟨(done.reads.keeps (job.readAt policy n)).trans exactScope, ?_⟩
  rw [← exactScope, done.coverage]
  exact Set.subset_union_right

theorem Deferred.a_later_new_scope_writes_at_the_reached_resident
    (novel : ¬ Observed ⊆ (Reached).base.language.covered) :
    let done := job.completeAt policy n (.isFalse novel)
    let prior := (Reached).current.ledger
    let generated := (revised prior (Reached).base.language Observed (Reached).u7 novel).generate
    (⟨generated.NewN, generated.newLivingRoot.generatedNextCurrentAt
      (.finite generated.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      done.next.current.ledger.resident.erase :=
  revisedLedger_is_the_generated_first_write _ _ _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
