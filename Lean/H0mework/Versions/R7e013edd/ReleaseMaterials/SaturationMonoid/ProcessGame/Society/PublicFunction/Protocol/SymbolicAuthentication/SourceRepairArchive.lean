import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairArchive
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code) (genesis : Cursor bound.source.code)
 (parent : RecursiveSigningSource.State bound genesis) (scope : Scope) (value : Bool)

def fromOriginal (origin : Segment bound) (depth : Nat) :=
 SourceRepairRun.produce contract (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages
  scope value depth (JointReceptionSource.initial bound genesis parent)

def produce (slot depth : Nat) : Option (SourceRepairRun.Report bound.source.code) :=
 match parent.archive[slot]? with
 | none => none
 | some origin => some (fromOriginal bound contract base law genesis parent scope value origin depth)

-- A failed repair does not erase an already sufficient actual received quorum.
def decision (slot depth : Nat) (recipient : Fin bound.source.code.sites) (threshold : Nat) : ProspectiveQuorum.Result :=
 match parent.archive[slot]? with
 | none => .blocked .missingQuorum
 | some origin => JointReceptionConsumer.produce (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages
  (fromOriginal bound contract base law genesis parent scope value origin depth).final recipient scope threshold

theorem every_original_report_replays_its_actual_commands_and_retains_all_history
 (origin : Segment bound) (depth : Nat) :
 let report := fromOriginal bound contract base law genesis parent scope value origin depth
 let start := JointReceptionSource.initial bound genesis parent
 SourceRepairSearch.execute contract start report.commands=report.final ∧
 SourceRepairSearch.Path contract start report.commands ∧
 report.commands.length≤(SourceRepairSearch.debt (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages scope value start+1)*depth ∧
 start.actual.archive <+: report.final.actual.archive ∧
 start.actual.windows <+: report.final.actual.windows ∧ start.rows <+: report.final.rows := by
 have replay := SourceRepairRun.every_report_replays_only_its_selected_actual_source_commands contract
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value depth
  (SourceRepairSearch.debt (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value
    (JointReceptionSource.initial bound genesis parent)+1) (JointReceptionSource.initial bound genesis parent)
 have retained := SourceRepairRun.every_final_report_retains_its_original_source_history contract
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value depth
  (JointReceptionSource.initial bound genesis parent)
 exact ⟨replay.1,replay.2.1,replay.2.2,retained⟩

theorem the_public_source_producer_returns_completion_or_an_actual_bounded_obstruction
 (slot depth : Nat) (origin : Segment bound) (located : parent.archive[slot]?=some origin) :
 ∃ report, produce bound contract base law genesis parent scope value slot depth=some report ∧
 (report.status=.complete ∨ report.status=.blocked) ∧
 ArchivedDeliveryConsumer.NativeContinuation report.final.actual.model report.final.actual.point := by
 refine ⟨fromOriginal bound contract base law genesis parent scope value origin depth,?_,?_,?_⟩
 · simp only [produce,located]
 · exact SourceRepairRun.the_producer_always_completes_or_returns_its_exact_bounded_obstruction contract
    (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value depth
    (JointReceptionSource.initial bound genesis parent)
 · exact JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _

theorem a_public_blocked_report_excludes_every_source_repair_at_its_actual_endpoint
 (slot depth : Nat) (origin : Segment bound) (located : parent.archive[slot]?=some origin)
 (report : SourceRepairRun.Report bound.source.code)
 (actual : produce bound contract base law genesis parent scope value slot depth=some report)
 (blocked : report.status=.blocked) :
 0<SourceRepairSearch.debt (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value report.final ∧
 ∀ commands, SourceRepairSearch.Path contract report.final commands → commands.length≤depth →
 SourceRepairSearch.debt (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value report.final ≤
 SourceRepairSearch.debt (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value
  (SourceRepairSearch.execute contract report.final commands) := by
 simp only [produce,located,Option.some.injEq] at actual
 subst report
 exact SourceRepairRun.every_blocked_report_has_the_actual_unresolved_bounded_obstruction contract
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value depth
  (SourceRepairSearch.debt (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value
    (JointReceptionSource.initial bound genesis parent)+1) (JointReceptionSource.initial bound genesis parent) blocked

theorem a_completed_actual_repair_generates_joint_decisions_and_its_own_next
 (slot depth : Nat) (origin : Segment bound) (located : parent.archive[slot]?=some origin)
 (report : SourceRepairRun.Report bound.source.code)
 (actual : produce bound contract base law genesis parent scope value slot depth=some report)
 (complete : report.status=.complete) (threshold : Nat) (positive : 0<threshold)
 (safe : (ActorEnvelope.roster origin.origin.source).card+
  ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope<threshold+threshold)
 (reference : Fin bound.source.code.sites)
 (enough : threshold≤(JointReceptionConsumer.addressedActors (origin.vocabulary bound base) origin.origin origin.stages scope value reference).card) :
 ∃ answer,
 (∀ recipient, threshold≤(JointReceptionConsumer.addressedActors (origin.vocabulary bound base) origin.origin origin.stages scope value recipient).card →
  decision bound contract base law genesis parent scope value slot depth recipient threshold=.decided answer) ∧
 ArchivedDeliveryConsumer.NativeContinuation report.final.actual.model report.final.actual.point := by
 have same := actual
 simp only [produce,located,Option.some.injEq] at same
 have originalComplete := complete
 rw [← same] at originalComplete
 simp only [fromOriginal,SourceRepairRun.produce] at originalComplete
 have cleared := SourceRepairRun.every_completed_report_has_no_unreceived_original_target contract
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value depth
  (SourceRepairSearch.debt (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value
    (JointReceptionSource.initial bound genesis parent)+1) (JointReceptionSource.initial bound genesis parent)
  originalComplete
 have empty := Finset.card_eq_zero.mp cleared
 obtain ⟨answer,first⟩ := JointReceptionConsumer.actual_joint_completion_generates_source_budget_decisions
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value _ empty threshold positive safe reference enough
 refine ⟨answer,?_,JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩
 intro recipient supported
 obtain ⟨other,second⟩ := JointReceptionConsumer.actual_joint_completion_generates_source_budget_decisions
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value _ empty threshold positive safe recipient supported
 have agree := JointReceptionConsumer.all_generated_endpoint_decisions_agree
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages _ _ reference recipient scope threshold answer other first second
 simp only [decision,located]
 simpa only [fromOriginal,SourceRepairRun.produce,agree] using second

theorem actual_decisions_agree_even_when_repair_horizons_differ
 (slot leftDepth rightDepth : Nat) (left right : Fin bound.source.code.sites) (threshold : Nat) (a b : Bool)
 (first : decision bound contract base law genesis parent scope value slot leftDepth left threshold=.decided a)
 (second : decision bound contract base law genesis parent scope value slot rightDepth right threshold=.decided b) : a=b := by
 cases located : parent.archive[slot]? with
 | none => simp only [decision,located] at first;contradiction
 | some origin =>
   simp only [decision,located] at first second
   exact JointReceptionConsumer.all_generated_endpoint_decisions_agree (origin.vocabulary bound base) (origin.law bound law)
    origin.origin origin.stages _ _ left right scope threshold a b first second

theorem removing_the_original_archive_removes_the_report_and_blocks_decision
 (slot depth : Nat) (absent : parent.archive[slot]?=none) (recipient : Fin bound.source.code.sites) (threshold : Nat) :
 produce bound contract base law genesis parent scope value slot depth=none ∧
 decision bound contract base law genesis parent scope value slot depth recipient threshold=.blocked .missingQuorum := by
 simp only [produce,decision,absent,and_self]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairArchive
