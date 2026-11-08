import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Acceptance
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Compiled

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement

open Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
  (reserved : (script : List (Option (Compile.RawInput Party Good Port Technology Instrument))) → Finset (Service.Ordinal source script))

inductive Rejection (script : Script)
  | malformed (bad : ¬ Service.OriginalDemands ordered.toFinset task)
  | native (issue : Obstruction source script)
  | overdue (problem : Problem source script ordered task (reserved script) (fun _ => 0))
      (first : firstProblem source script ordered task (reserved script) (fun _ => 0) = some problem)
      (reached : problemTime problem ≤ finish source script)

def rejection (script : Script) : Option (Rejection source ordered task reserved script) :=
  match inspect source script ordered task (reserved script) with
  | .paid _ => none
  | .malformed bad => some (.malformed bad)
  | .native issue => some (.native issue)
  | .overdue problem first reached => some (.overdue problem first reached)

theorem a_programme_has_no_due_rejection_exactly_when_it_pays
    (script : Script) :
    rejection source ordered task reserved script = none ↔
      ∃ paid, inspect source script ordered task (reserved script) = .paid paid := by
  unfold rejection
  cases inspect source script ordered task (reserved script) with
  | paid actual => exact ⟨fun _ => ⟨actual, rfl⟩, fun _ => rfl⟩
  | malformed _ | native _ | overdue _ _ _ => simp

/-- Optimize across the actual programmes that pass the joint due check.
All candidates share the original source and keep their own accounting. -/
theorem the_due_programme_domain_has_an_actual_minimum_or_approach_or_named_rejection
    {Value : Type*} [CompleteLinearOrder Value] (read : Script → Value) :
    let values := Bounds.Compiled.values source id (rejection source ordered task reserved) read
    (∃ (script : Script) (paid : PaidAt source script ordered task (reserved script)),
      inspect source script ordered task (reserved script) = .paid paid ∧ read script = sInf values) ∨
    (values.Nonempty ∧ sInf values ∉ values ∧
      ∀ limit, sInf values < limit →
        ∃ (script : Script) (paid : PaidAt source script ordered task (reserved script)),
          inspect source script ordered task (reserved script) = .paid paid ∧ read script < limit) ∨
    (∀ script, Recorded source script ∧ Nonempty (Rejection source ordered task reserved script)) := by
  let reject := rejection source ordered task reserved
  cases Bounds.Compiled.resolve source id reject read with
  | attained script _ checked least =>
    obtain ⟨paid, same⟩ :=
      (a_programme_has_no_due_rejection_exactly_when_it_pays source ordered task reserved script).mp checked
    exact .inl ⟨script, paid, same, least⟩
  | approached existsValue noExact near =>
    refine .inr (.inl ⟨existsValue, noExact, fun limit closer => ?_⟩)
    obtain ⟨script, _, checked, below⟩ := near limit closer
    obtain ⟨paid, same⟩ :=
      (a_programme_has_no_due_rejection_exactly_when_it_pays source ordered task reserved script).mp checked
    exact ⟨script, paid, same, below⟩
  | obstructed issues =>
    refine .inr (.inr fun script => ⟨record source script, ?_⟩)
    cases seen : reject script with
    | some issue => exact ⟨issue⟩
    | none =>
      obtain ⟨paid, _⟩ :=
        (a_programme_has_no_due_rejection_exactly_when_it_pays source ordered task reserved script).mp seen
      rcases (issues script).2 with bad | ⟨issue, blocked⟩
      · obtain ⟨native⟩ := bad
        exact (native.refutes paid.settlement.toFeasible).elim
      · rw [seen] at blocked
        cases blocked

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
