import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

inductive EconomicAxis where
  | material (metric : Settlement.Material Party Good)
  | unpaid (index : Nat) (holder : Party)
  | service (index : Fin code.task.slots.length)

def economicAxes (source : Machine Party Good Port (Mandate.State Party Technology) Instrument) (cut : Nat) : List (EconomicAxis source.code) :=
  (Settlement.materials source.code).map .material ++
    (List.range (Cut.originalSlots source cut)).flatMap (fun index => source.code.parties.map (.unpaid index)) ++
    (List.finRange source.code.task.slots.length).map .service

structure Evaluation where
  legal : Bool
  complete : Bool
  profile : Settlement.Profile Party Good Port (Mandate.State Party Technology) Instrument
  native : Authority.Trace.Manifest Party Good Port Technology Instrument
  value : EconomicAxis code → ℚ

variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (entry : Input bound.source.code) (cut : Nat) (active : bound.source.feedback? = some entry)

@[inline] def evaluate (rival : Opponent bound.source.code) (programme : Cut.Term bound.source entry cut) : Evaluation bound.source.code where
  legal := (Residual.run bound.source.code (Residual.scheduleAt bound.source cut programme.val) ⟨rival,entry.budget⟩
    (Residual.seed bound.source entry cut) (Cut.horizon bound.source entry cut)).frame.localLegal
  complete := (List.finRange bound.source.code.task.slots.length).all fun index =>
    (Identity.firstService (Cut.machine bound.source entry cut rival programme) (Cut.finish bound.source entry cut - 1) index).isSome
  profile := Cut.profile bound.source entry cut rival programme
  native := Authority.Trace.generate bound entry cut rival programme active
  value := fun axis => match axis with
    | .material metric => Cut.material bound.source entry cut rival programme metric
    | .unpaid index holder => Cut.remaining bound.source entry cut rival programme index holder
    | .service index => Cut.serviceTime bound.source entry cut rival programme index

variable (empty : bound.source.continuation = [])

include empty in
theorem evaluate_joint (rival : Opponent bound.source.code) (programme : Cut.Term bound.source entry cut) :
    evaluate bound entry cut active (Future.jointOpponent bound.source entry cut rival) programme =
      evaluate bound entry cut active rival programme := by
  apply (Evaluation.mk.injEq ..).mpr
  refine ⟨?_,?_,Cut.joint_profile bound.source entry cut rival programme active empty,
    Authority.Trace.joint_complete_manifest bound entry cut rival programme active empty,?_⟩
  · exact congrArg (fun state : State bound.source.code => state.frame.localLegal)
      (Residual.one_restriction_preserves_the_whole_remaining_run bound.source.code (Residual.seed bound.source entry cut)
        (Residual.schedules bound.source entry cut) _ (List.mem_map.mpr ⟨programme.val,programme.property,rfl⟩)
        ⟨rival,entry.budget⟩ (Cut.horizon bound.source entry cut) (Nat.le_refl _))
  · apply List.all_congr rfl
    intro index
    exact congrArg Option.isSome (Cut.joint_first_service bound.source entry cut rival programme active empty
      (Cut.finish bound.source entry cut-1) (by dsimp only [Cut.finish,Cut.start];omega) index)
  · funext axis
    cases axis with
    | material metric => exact Cut.joint_material bound.source entry cut rival programme active empty metric
    | unpaid index holder =>
      exact congrArg (fun holdings => (Settlement.holdingAt holdings index (bound.source.code.parties.idxOf holder)).1)
        (Cut.joint_holdings bound.source entry cut rival programme active empty)
    | service index =>
      exact congrArg (fun first : Option Nat => (first.getD (Cut.finish bound.source entry cut) : ℚ))
        (Cut.joint_first_service bound.source entry cut rival programme active empty (Cut.finish bound.source entry cut-1)
          (by dsimp only [Cut.finish,Cut.start];omega) index)

abbrev actualEvaluation (protocol : Rule bound.source.code) (rival : Opponent bound.source.code) :=
  evaluate bound entry cut active (controller bound.source cut protocol rival) (term bound.source entry cut protocol)

abbrev tableEvaluation (protocol : Rule bound.source.code) (table : Cut.Table bound.source entry cut) :=
  evaluate bound entry cut active (tableController bound.source entry cut protocol table) (term bound.source entry cut protocol)

include empty in
theorem table_evaluation_is_its_own_actual_protocol (protocol : Rule bound.source.code)
    (table : Cut.Table bound.source entry cut) :
    tableEvaluation bound entry cut active protocol table =
      actualEvaluation bound entry cut active protocol (Cut.opponent bound.source entry cut table) :=
  evaluate_joint bound entry cut active empty _ _

include empty in
theorem one_external_table_preserves_every_protocol_full_responsibility
    (protocol : Rule bound.source.code) (rival : Opponent bound.source.code) :
    tableEvaluation bound entry cut active protocol
        (Residual.restrict bound.source.code (Residual.seed bound.source entry cut) (Residual.schedules bound.source entry cut) rival) =
      actualEvaluation bound entry cut active protocol rival := by
  unfold tableEvaluation
  rw [one_external_restriction_controls_every_own_rule]
  exact evaluate_joint bound entry cut active empty _ _

include empty in
theorem finite_relation_iff_same_external_adaptive_opponent
    (relation : Evaluation bound.source.code → Evaluation bound.source.code → Prop)
    (new old : Rule bound.source.code) :
    (∀ table ∈ Cut.tables bound.source entry cut,
      relation (tableEvaluation bound entry cut active new table) (tableEvaluation bound entry cut active old table)) ↔
      ∀ rival : Opponent bound.source.code,
        relation (actualEvaluation bound entry cut active new rival) (actualEvaluation bound entry cut active old rival) := by
  constructor
  · intro finite rival
    have checked := finite
      (Residual.restrict bound.source.code (Residual.seed bound.source entry cut) (Residual.schedules bound.source entry cut) rival)
      (Residual.restriction_is_generated bound.source.code (Residual.seed bound.source entry cut) (Residual.schedules bound.source entry cut) rival)
    rw [one_external_table_preserves_every_protocol_full_responsibility bound entry cut active empty new rival,
      one_external_table_preserves_every_protocol_full_responsibility bound entry cut active empty old rival] at checked
    exact checked
  · intro all table _
    rw [table_evaluation_is_its_own_actual_protocol bound entry cut active empty new table,
      table_evaluation_is_its_own_actual_protocol bound entry cut active empty old table]
    exact all _



end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol
