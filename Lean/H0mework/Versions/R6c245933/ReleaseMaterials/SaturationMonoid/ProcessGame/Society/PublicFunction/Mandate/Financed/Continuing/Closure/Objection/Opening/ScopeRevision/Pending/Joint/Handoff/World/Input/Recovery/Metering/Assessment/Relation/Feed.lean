import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
noncomputable section

variable (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) (point : Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor model.source.code)
  {fuel : Nat} (reference : Rule model.source.code) (program : Whole.Program model.source.code fuel)
  (rival : Opponent model.source.code)

def source := Future.target point.source point.entry point.cut
  (Future.jointOpponent point.source point.entry point.cut (Whole.controller point reference program rival))
  (Whole.schedule point reference program).val

def words : List (List Action) :=
  (List.range (Cut.horizon point.source point.entry point.cut)).map fun offset =>
    (source model point reference program rival).actualExecution (Budget.Programme.Debt.depth point+offset) |>.submitted

variable {epoch : Epoch} (inventory : Inventory epoch)
def window : Window (⟨epoch,inventory⟩ : Packet) :=
  ⟨Event.run ⟨epoch,inventory⟩ (words model point reference program rival),
    Event.runEvolution ⟨epoch,inventory⟩ (words model point reference program rival)⟩

abbrev Present := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tensor model point × Window (⟨epoch,inventory⟩ : Packet)

def present (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
    (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) := .unpriced) :
    Present model point inventory :=
  ⟨Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.actualTensor (tariff := tariff) model point reference program rival,
    window model point reference program rival inventory⟩

abbrev Reports := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family.Tensor (Present model point inventory) (List Action)
  (fun actual word => Report actual.2.packet.2 word)
  (fun actual word => Funding.Failure (Recovery.begin actual.2.packet.2 word))

def tensor (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
    (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) := .unpriced) :
    Reports model point inventory :=
  let actual := present model point reference program rival inventory tariff
  ⟨actual,fun word => let report := Runtime.read actual.2.packet.2 word
    some (report,report.funding)⟩

def PresentNoWorse (requested : List (List Action))
    (new previous : Present model point inventory) : Prop :=
  Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.accepts (requested := requested) model point new.1 previous.1 ∧
    Window.NoWorse new.2 previous.2

instance (requested : List (List Action)) (new previous : Present model point inventory) :
    Decidable (PresentNoWorse model point inventory requested new previous) := by
  unfold PresentNoWorse;infer_instance

def FutureNoWorse (new previous : Present model point inventory) (word : List Action)
    (current : Report new.2.packet.2 word) (old : Report previous.2.packet.2 word) : Prop :=
  ReportNoWorse new.2 previous.2 word current old ∧
    JointNoWorse new.2 previous.2 word current old ∧ ScopeNoWorse new.2 previous.2 word current old

instance (new previous : Present model point inventory) (word : List Action)
    (current : Report new.2.packet.2 word) (old : Report previous.2.packet.2 word) :
    Decidable (FutureNoWorse model point inventory new previous word current old) := by
  unfold FutureNoWorse;infer_instance

variable {program rival}
def Accepts (requested : List (List Action)) (new previous : Whole.Program model.source.code fuel)
    (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) := .unpriced) : Prop :=
  Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family.Accepts (PresentNoWorse model point inventory requested)
    (FutureNoWorse model point inventory) (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.required model point requested)
    (tensor model point reference new opponent inventory tariff)
    (tensor model point reference previous opponent inventory tariff)

instance (requested : List (List Action)) (new previous : Whole.Program model.source.code fuel)
    (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit)) :
    Decidable (Accepts model point reference inventory requested new previous opponent tariff) := by
  unfold Accepts;infer_instance

def inspect (requested : List (List Action)) (new previous : Whole.Program model.source.code fuel)
    (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) := .unpriced) :=
  Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family.inspect (PresentNoWorse model point inventory requested)
    (FutureNoWorse model point inventory) (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.required model point requested)
    (tensor model point reference new opponent inventory tariff)
    (tensor model point reference previous opponent inventory tariff)

theorem accepted_retains_the_entire_original_tensor (requested : List (List Action))
    (new previous : Whole.Program model.source.code fuel) (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (accepted : Accepts model point reference inventory requested new previous opponent tariff) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.accepts (requested := requested) model point
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.actualTensor (tariff := tariff) model point reference new opponent)
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.actualTensor (tariff := tariff) model point reference previous opponent) :=
  accepted.1.1

theorem accepted_retains_the_complete_history_relation (requested : List (List Action))
    (new previous : Whole.Program model.source.code fuel) (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (accepted : Accepts model point reference inventory requested new previous opponent tariff) :
    Relation.Accepts (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.required model point requested)
      (window model point reference new opponent inventory)
      (window model point reference previous opponent inventory) :=
  ⟨accepted.1.2,fun word member => (accepted.2.1 word member).1,accepted.2.2⟩

theorem accepted_consumes_the_original_joint_next (requested : List (List Action))
    (new previous : Whole.Program model.source.code fuel) (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (accepted : Accepts model point reference inventory requested new previous opponent tariff)
    (word : List Action)
    (member : word ∈ Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.required model point requested) :
    JointNoWorse (window model point reference new opponent inventory)
      (window model point reference previous opponent inventory) word
      (Runtime.read (window model point reference new opponent inventory).packet.2 word)
      (Runtime.read (window model point reference previous opponent inventory).packet.2 word) :=
  (accepted.2.1 word member).2.1

theorem accepted_reenters_every_port_at_each_actual_scope (requested : List (List Action))
    (new previous : Whole.Program model.source.code fuel) (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (accepted : Accepts model point reference inventory requested new previous opponent tariff)
    (word : List Action)
    (member : word ∈ Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.required model point requested)
    (intent : Input.Intent) :
    ScopeForecast.PortNoWorse
      ((scopeForecast (window model point reference new opponent inventory) word
        (Runtime.read (window model point reference new opponent inventory).packet.2 word)).read intent)
      ((scopeForecast (window model point reference previous opponent inventory) word
        (Runtime.read (window model point reference previous opponent inventory).packet.2 word)).read intent) :=
  ((accepted.2.1 word member).2.2 intent (ScopeForecast.every_native_port_is_included intent)).1


theorem accepted_preserves_original_task_admission_at_each_actual_scope (requested : List (List Action))
    (new previous : Whole.Program model.source.code fuel) (opponent : Opponent model.source.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff (Party := Bool) (Good := Good)
      (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (accepted : Accepts model point reference inventory requested new previous opponent tariff)
    (word : List Action)
    (member : word ∈ Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.required model point requested)
    (intent : Input.Intent) :
    TaskSource.Admission.NoWorse
      ((scopeForecast (window model point reference new opponent inventory) word
        (Runtime.read (window model point reference new opponent inventory).packet.2 word)).taskAdmission intent)
      ((scopeForecast (window model point reference previous opponent inventory) word
        (Runtime.read (window model point reference previous opponent inventory).packet.2 word)).taskAdmission intent) :=
  ((accepted.2.1 word member).2.2 intent (ScopeForecast.every_native_port_is_included intent)).2.2


theorem every_word_has_its_original_candidate_visit (offset : Nat)
    (inside : offset < Cut.horizon point.source point.entry point.cut) :
    (words model point reference program rival)[offset]? =
      some ((source model point reference program rival).actualExecution
        (Budget.Programme.Debt.depth point+offset)).submitted := by
  simp only [words,List.getElem?_map,List.getElem?_range inside,Option.map_some]

theorem the_common_table_keeps_the_same_candidate_source :
    source model point reference program (Cut.opponent point.source point.entry point.cut (externalTable point rival)) =
      source model point reference program rival := by
  have same := Whole.one_external_restriction_controls_the_entire_program model point reference program rival
  change Future.jointOpponent point.source point.entry point.cut
      (Whole.controller point reference program (Cut.opponent point.source point.entry point.cut (externalTable point rival))) =
    Future.jointOpponent point.source point.entry point.cut (Whole.controller point reference program rival) at same
  unfold source
  rw [same]

theorem the_common_table_keeps_the_same_actual_history :
    window model point reference program (Cut.opponent point.source point.entry point.cut (externalTable point rival)) inventory =
      window model point reference program rival inventory := by
  unfold window words
  rw [the_common_table_keeps_the_same_candidate_source]

theorem the_common_table_keeps_the_complete_joint_tensor
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff
      (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit)) :
    tensor model point reference program (Cut.opponent point.source point.entry point.cut (externalTable point rival)) inventory tariff =
      tensor model point reference program rival inventory tariff := by
  have legacy := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.one_common_external_table_generates_the_same_complete_restoration_tensor
    (tariff := tariff) model point reference program rival
  change Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.actualTensor
      (tariff := tariff) model point reference program (Cut.opponent point.source point.entry point.cut (externalTable point rival)) = _ at legacy
  have actual := the_common_table_keeps_the_same_actual_history model point reference inventory (program := program) (rival := rival)
  unfold tensor present
  rw [legacy,actual]

namespace Source
variable {epoch : Epoch}
    (machine : Native.Authority.Sources base epoch.scope)

/-- The native machine is supplied by its original source; the complete World
inventory remains a separate source input and is never rebuilt from that machine. -/
def boundSource : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨base,epoch.scope,machine.val,machine.property.1,machine.property.2⟩

theorem source_task_homology_is_literal : (boundSource machine).source.code.task = epoch.source.seed.task :=
  machine.property.2

def produce (inventory : Inventory epoch)
    (point : Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor machine.val.code)
    (reference : Rule machine.val.code) (program : Whole.Program machine.val.code fuel)
    (rival : Opponent machine.val.code)
    (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff
      (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) := .unpriced) :=
  tensor (boundSource machine) point reference program rival inventory tariff
end Source


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
