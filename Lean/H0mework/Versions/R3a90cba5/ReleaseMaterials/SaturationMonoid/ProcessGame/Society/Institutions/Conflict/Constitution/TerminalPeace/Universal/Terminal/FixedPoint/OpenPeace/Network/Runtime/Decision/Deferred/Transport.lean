import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Finish
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open private completeScope from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Finish

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin reserveBase newBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {home : AnyAuthoritativeRootCurrent.{0}} {replies : Replies Party Good Port Technology Instrument}
  {before : Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := reserveBase)}
  {input : OpenPeace.Input Party Good Port Technology Instrument}

variable (job : Deferred home replies before input)
  (reached : Runtime.State (seed := seed) (cut := cut) (community := community)
    origin people quantum (reserveBase := newBase))
  (path : ReadPath job.live.current.ledger.resident reached.current.ledger.resident)

local notation "Observed" => ReadAt.read (ReadPath.carry path (Deferred.pending job))

/-- A checked pending effect is consumed even after the material
dispatcher has changed the reserve index. The original scope follows
the actual resident's dependent read path. -/
def Deferred.completeAlong (test : Decidable (Observed ⊆ reached.base.language.covered)) :
    Completion reached Observed :=
  completeScope reached Observed test

theorem Deferred.covered_paid_scope_does_not_write_twice (covered : Observed ⊆ reached.base.language.covered) :
    let done := job.completeAlong reached path (.isTrue covered)
    done.write = none ∧ done.next = reached :=
  ⟨rfl, rfl⟩

theorem Deferred.completion_along_reads_the_same_original_scope
    (test : Decidable (Observed ⊆ reached.base.language.covered)) :
    let done := job.completeAlong reached path test
    (done.reads.carry (path.carry job.pending)).read = Runtime.scope home replies before input ∧
      Runtime.scope home replies before input ⊆ done.next.base.language.covered := by
  intro done
  have exactScope := (path.keeps job.pending).trans job.exactScope
  refine ⟨(done.reads.keeps _).trans exactScope, ?_⟩
  rw [← exactScope, done.coverage]
  exact Set.subset_union_right

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (catalogue : RebaseHistory.Catalogue Party Good Port Technology Instrument)
  (policy : Nat → RebaseHistory.Resident seed cut community origin people quantum →
    RebaseHistory.Command Party Good Port Technology Instrument)
  (n : Nat)

local notation "Start" => Sigma.mk reserveBase (Deferred.live job)
local notation "Reached" => RebaseHistory.history home replies catalogue Start policy n
local notation "Path" => RebaseHistory.historyReads home replies catalogue Start policy n
local notation "ObservedAt" => ReadAt.read (ReadPath.carry (Path) (Deferred.pending job))

def Deferred.completeAfterRebases
    (test : Decidable (ObservedAt ⊆ (Reached).2.base.language.covered)) :
    Completion (Reached).2 ObservedAt :=
  job.completeAlong (Reached).2 (Path) test

theorem Deferred.the_mixed_schedule_retains_the_original_paid_scope
    (test : Decidable (ObservedAt ⊆ (Reached).2.base.language.covered)) :
    let done := job.completeAfterRebases catalogue policy n test
    (done.reads.carry ((Path).carry job.pending)).read = Runtime.scope home replies before input ∧
      Runtime.scope home replies before input ⊆ done.next.base.language.covered :=
  job.completion_along_reads_the_same_original_scope (Reached).2 (Path) test

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
