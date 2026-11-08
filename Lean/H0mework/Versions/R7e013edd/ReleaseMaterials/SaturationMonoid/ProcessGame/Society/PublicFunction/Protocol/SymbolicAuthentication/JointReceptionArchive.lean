import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionArchive
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
 (parent : RecursiveSigningSource.State bound genesis)
 (scope : Scope) (value : Bool)
 (external : Nat → JointReceptionSource.State bound.source.code → RenewableArchiveSource.Command)

private def execute (origin : Segment bound) :=
 JointReceptionSource.run (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value
  contract (JointReceptionSource.initial bound genesis parent) external

-- The public runner admits a slot, never a caller-selected signing history or endpoint.
def run (slot count : Nat) : Option (JointReceptionSource.State bound.source.code) :=
 match parent.archive[slot]? with
 | none => none
 | some origin => some (execute bound contract base law genesis parent scope value external origin count)

def produce (slot count : Nat) (recipient : Fin bound.source.code.sites) (threshold : Nat) : ProspectiveQuorum.Result :=
 match parent.archive[slot]? with
 | none => .blocked .missingQuorum
 | some origin => JointReceptionConsumer.produce (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages
   (execute bound contract base law genesis parent scope value external origin count) recipient scope threshold

def recurrentOpportunities (slot : Nat) : Prop :=
 match parent.archive[slot]? with
 | none => False
 | some origin => ∀ index,
   (JointReceptionSource.pending (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value
    (execute bound contract base law genesis parent scope value external origin index)).Nonempty →
   ∃ delay task,
    task∈JointReceptionSource.menu (execute bound contract base law genesis parent scope value external origin (index+delay)) ∧
    JointReceptionSource.offer (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value
     (execute bound contract base law genesis parent scope value external origin (index+delay)) task=true

theorem original_archived_opportunities_generate_one_joint_decision_and_own_next
 (slot : Nat) (origin : Segment bound) (located : parent.archive[slot]?=some origin)
 (opportunities : recurrentOpportunities bound contract base law genesis parent scope value external slot)
 (threshold : Nat) (positive : 0<threshold)
 (safe : (ActorEnvelope.roster origin.origin.source).card+
  ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope<threshold+threshold)
 (reference : Fin bound.source.code.sites)
 (enough : threshold≤(JointReceptionConsumer.addressedActors (origin.vocabulary bound base) origin.origin origin.stages scope value reference).card) :
 ∃ count answer state,
 run bound contract base law genesis parent scope value external slot count=some state ∧
 (∀ recipient, threshold≤(JointReceptionConsumer.addressedActors (origin.vocabulary bound base) origin.origin origin.stages scope value recipient).card →
  produce bound contract base law genesis parent scope value external slot count recipient threshold=.decided answer) ∧
 ArchivedDeliveryConsumer.NativeContinuation state.actual.model state.actual.point := by
 have actualOpportunities := opportunities
 simp only [recurrentOpportunities,located] at actualOpportunities
 obtain ⟨count,answer,common,native⟩ := JointReceptionConsumer.recurrent_opportunities_generate_a_common_decision_and_actual_continuation
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages scope value contract
  (JointReceptionSource.initial bound genesis parent) external actualOpportunities threshold positive safe reference enough
 refine ⟨count,answer,execute bound contract base law genesis parent scope value external origin count,?_,?_,native⟩
 · simp only [run,located]
 · intro recipient supported
   simp only [produce,located]
   exact common recipient supported

theorem deleting_the_original_archive_blocks_both_execution_and_decision
 (slot count : Nat) (missing : parent.archive[slot]?=none)
 (recipient : Fin bound.source.code.sites) (threshold : Nat) :
 run bound contract base law genesis parent scope value external slot count=none ∧
 produce bound contract base law genesis parent scope value external slot count recipient threshold=.blocked .missingQuorum := by
 simp only [run,produce,missing,and_self]

theorem each_public_decision_consumes_its_original_paid_source_and_actual_quorum
 (slot count : Nat) (recipient : Fin bound.source.code.sites) (threshold : Nat) (answer : Bool)
 (done : produce bound contract base law genesis parent scope value external slot count recipient threshold=.decided answer) :
 ∃ origin state, parent.archive[slot]?=some origin ∧
 run bound contract base law genesis parent scope value external slot count=some state ∧
 (ActorEnvelope.roster origin.origin.source).card+
  ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope<threshold+threshold ∧
 0<threshold ∧ threshold≤(ActorQuorum.support
  (JointReceptionSource.observed (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages state recipient)
   scope answer).card := by
 cases located : parent.archive[slot]? with
 | none => simp only [produce,located] at done;contradiction
 | some origin =>
   simp only [produce,located] at done
   refine ⟨origin,execute bound contract base law genesis parent scope value external origin count,rfl,?_,?_⟩
   · simp only [run,located]
   · exact JointReceptionConsumer.generated_decision_requires_positive_actual_quorum_and_source_budget
      (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages _ recipient scope threshold answer done

theorem public_decisions_agree_under_independent_dynamic_controls
 (other : Nat → JointReceptionSource.State bound.source.code → RenewableArchiveSource.Command)
 (slot leftCount rightCount : Nat) (left right : Fin bound.source.code.sites) (threshold : Nat) (a b : Bool)
 (first : produce bound contract base law genesis parent scope value external slot leftCount left threshold=.decided a)
 (second : produce bound contract base law genesis parent scope value other slot rightCount right threshold=.decided b) : a=b := by
 cases located : parent.archive[slot]? with
 | none => simp only [produce,located] at first;contradiction
 | some origin =>
   simp only [produce,located] at first second
   exact JointReceptionConsumer.all_generated_endpoint_decisions_agree
    (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages _ _ left right scope threshold a b first second

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionArchive
