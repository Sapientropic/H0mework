import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Result
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Capability
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Reconstruction
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Input.Recovery.Metering.Assessment.Relation
noncomputable section

variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) {epoch : Epoch} (inventory : Inventory epoch)
  (past : List (Rule prior.model.source.code))

abbrev Program := Whole.Program prior.model.source.code (horizon prior.domain)

def controls (program : Program prior) :=
  past ++ Prefix.Runtime.suffix (original := prior.original) (past := past) prior.point.point program

def full (program : Program prior) :=
  Splice.install prior.point.point prior.rival (controls prior past program)

def next (program : Program prior) :=
  Writeback.next (full prior past program).source inventory
    (depth prior.point.point) (controls prior past program).length prior.worldPending

def native (program : Program prior) : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet)
    (next prior inventory past program).saved :=
  Writeback.native (full prior past program).source inventory
    (depth prior.point.point) (controls prior past program).length prior.worldPending

def rebuilt (program : Program prior) :=
  Communication.result (next prior inventory past program).saved
    (next prior inventory past program).pending prior (full prior past program)

def snapshot (program : Program prior) :=
  Communication.Capability.generate prior (next prior inventory past program).saved.2
    (next prior inventory past program).pending (full prior past program)

def origin (program : Program prior) (position : Fin (prior.domain.length+1)) :=
  (full prior past program :: prior.domain)[position]

private def extendWindow {first : Packet} (seed : Window first)
    (old : Continuation.Cursor prior.model.source.code) : Window first :=
  ⟨⟨seed.packet.1,Communication.Source.saved seed.packet.2 old⟩,
    .append seed.native (Communication.Source.native seed.packet.2 old)⟩

def window (program : Program prior) (position : Fin (prior.domain.length+1)) :
    Window (⟨epoch,inventory⟩ : Packet) :=
  extendWindow prior ⟨(next prior inventory past program).saved,native prior inventory past program⟩
    (origin prior past program position)

inductive Test where
  | window (position : Fin (prior.domain.length+1))
  | admission
  | programme (index : Fin (Communication.Capability.catalogue prior).length)

def tests : List (Test prior) :=
  .admission :: ((List.finRange (prior.domain.length+1)).map Test.window ++
    (List.finRange (Communication.Capability.catalogue prior).length).map Test.programme)

theorem every_test_is_generated (test : Test prior) : test ∈ tests prior := by
  cases test with
  | admission => exact List.mem_cons_self
  | window position => exact List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map.mpr ⟨position,List.mem_finRange _,rfl⟩))
  | programme index => exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩))

def Holds (reference program : Program prior) : Test prior → Prop
  | .window position => Window.NoWorse (window prior inventory past program position)
      (window prior inventory past reference position)
  | .admission => (snapshot prior inventory past reference).passed = true →
      (snapshot prior inventory past program).passed = true
  | .programme index => (snapshot prior inventory past reference).read index = true →
      (snapshot prior inventory past program).read index = true

instance (reference program : Program prior) (test : Test prior) :
    Decidable (Holds prior inventory past reference program test) := by
  cases test <;> unfold Holds <;> infer_instance

def NoWorse (reference program : Program prior) : Prop :=
  ∀ test ∈ tests prior,Holds prior inventory past reference program test

instance (reference program : Program prior) : Decidable (NoWorse prior inventory past reference program) := by
  unfold NoWorse
  infer_instance

structure Rejection (reference program : Program prior) where
  test : Test prior
  generated : test ∈ tests prior
  broken : ¬ Holds prior inventory past reference program test

def rejectionFrom (reference program : Program prior)
    (failed : ¬ NoWorse prior inventory past reference program) : Rejection prior inventory past reference program :=
  match Distributed.inspect (Holds prior inventory past reference program) (tests prior) with
  | .rejected test generated broken => ⟨test,generated,broken⟩
  | .accepted kept => False.elim (failed kept)

theorem noWorse_refl (program : Program prior) : NoWorse prior inventory past program program := by
  intro test _
  cases test with
  | window position => exact Window.noWorse_refl _
  | admission => exact fun yes => yes
  | programme index => exact fun yes => yes

theorem keeps_the_complete_original_catalogue (reference program : Program prior)
    (kept : NoWorse prior inventory past reference program) :
    Communication.Capability.NoWorse (snapshot prior inventory past program)
      (snapshot prior inventory past reference) := by
  refine ⟨kept .admission (every_test_is_generated prior _),?_⟩
  intro index inside
  exact kept (.programme ⟨index,List.mem_range.mp inside⟩) (every_test_is_generated prior _)

/-- Both sides include the actual raw-word inspection, Requests response, full
reconstruction and original programme assessment. Units are declared services. -/
def units : Nat :=
  1 + (Whole.programs prior.model.source.code (horizon prior.domain)).length *
    (2 * (horizon prior.domain + Prefix.Runtime.actualHorizon prior.point.point + 2 +
      Input.Recovery.Metering.Assessment.Relation.Feed.Work.Reconstruction.snapshotServices prior) +
      (tests prior).length)


theorem every_actual_control_inspection_is_reserved (program : Program prior)
    (within : past.length ≤ horizon prior.domain) :
    (controls prior past program).length ≤ horizon prior.domain + Prefix.Runtime.actualHorizon prior.point.point := by
  have padded : (Prefix.Runtime.completeControls (original := prior.original) prior.point.point program).length =
      Prefix.Runtime.actualHorizon prior.point.point := Prefix.Padding.length _ _
  change (past ++ (Prefix.Runtime.completeControls (original := prior.original) prior.point.point program).drop past.length).length ≤ _
  rw [List.length_append,List.length_drop,padded]
  omega

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment
