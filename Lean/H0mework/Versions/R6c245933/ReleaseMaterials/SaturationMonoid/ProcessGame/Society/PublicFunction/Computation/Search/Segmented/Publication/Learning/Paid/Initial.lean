import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Round

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Rule model.source.code)
  (baseline : Whole.Program model.source.code fuel)

/-- The diagonal needs actual legality and service completion. Its other original
coordinates follow by reflexivity, without allocating either complete manifest. -/
def scalar (point : Cursor model.source.code) (rival : Opponent model.source.code) : Bool × Bool :=
  let driver := controller point original baseline rival
  let term := schedule point original baseline
  ⟨rawLegal point driver term,
    (List.finRange model.source.code.task.slots.length).all fun index =>
      (Identity.firstService (Cut.machine point.source point.entry point.cut driver term)
        (Cut.finish point.source point.entry point.cut - 1) index).isSome⟩

theorem scalar_is_original (point : Cursor model.source.code) (rival : Opponent model.source.code) :
    scalar model original baseline point rival =
      ⟨(actualEvaluation model point original baseline rival).legal,
        (actualEvaluation model point original baseline rival).complete⟩ := rfl

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem diagonal (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
    (coordinates : List (EconomicAxis code)) (evaluation : Evaluation code) :
    Synthesis.accepts code coordinates evaluation evaluation ↔
      evaluation.legal = true ∧ evaluation.complete = true := by
  constructor
  · intro kept
    exact ⟨kept.1,kept.2.1⟩
  · intro checked
    exact ⟨checked.1,checked.2,rfl,Authority.Trace.Lawful.refl evaluation.native,fun _ _ => le_rfl⟩

theorem scalar_iff_accepts (point : Cursor model.source.code) (rival : Opponent model.source.code) :
    ((scalar model original baseline point rival).1 = true ∧
      (scalar model original baseline point rival).2 = true) ↔
      Synthesis.accepts model.source.code (economicAxes point.source point.cut)
        (actualEvaluation model point original baseline rival) (actualEvaluation model point original baseline rival) := by
  rw [diagonal,scalar_is_original]

def compact : Prop :=
  if PublicDomain.quiet (code := model.source.code) then
    ∀ point ∈ Replanning.points model domain,
      (scalar model original baseline point.val PublicDomain.silent).1 = true ∧
      (scalar model original baseline point.val PublicDomain.silent).2 = true
  else
    ∀ point ∈ Replanning.points model domain,
      ∀ table ∈ Cut.tables point.val.source point.val.entry point.val.cut,
        (scalar model original baseline point.val (Cut.opponent point.val.source point.val.entry point.val.cut table)).1 = true ∧
        (scalar model original baseline point.val (Cut.opponent point.val.source point.val.entry point.val.cut table)).2 = true

theorem compact_iff : compact model domain original baseline ↔
    Selection.acceptable model domain original baseline baseline := by
  rw [← Selection.compactPacked_iff]
  unfold compact Selection.compactPacked
  split
  · constructor
    · intro checked point member
      exact (scalar_iff_accepts model original baseline point.val PublicDomain.silent).mp (checked point member)
    · intro checked point member
      exact (scalar_iff_accepts model original baseline point.val PublicDomain.silent).mpr (checked point member)
  · unfold Selection.packed
    constructor
    · intro checked point member table generated
      exact (scalar_iff_accepts model original baseline point.val _).mp (checked point member table generated)
    · intro checked point member table generated
      exact (scalar_iff_accepts model original baseline point.val _).mpr (checked point member table generated)

def decider : Decidable (Selection.acceptable model domain original baseline baseline) := by
  letI : Decidable (compact model domain original baseline) := by
    unfold compact
    split <;> infer_instance
  exact decidable_of_iff (compact model domain original baseline) (compact_iff model domain original baseline)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Initial
