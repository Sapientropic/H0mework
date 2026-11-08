import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Horizon
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Guard

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
open PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)

/-- An extended label would authorize a proposal that the actual expired
law refuses at this very cut. It therefore cannot be the installed law. -/
theorem moving_the_deadline_requires_a_different_original_law
    {cut : C} {base : Base} {scope : J} (original : Installed cut base scope)
    (expired : scope.task.deadline < cut.raw.clock)
    {replacement : ℚ} (reopened : cut.raw.clock ≤ replacement) :
    ¬ Installed cut base (withCutoff scope replacement) := by
  intro relabelled
  obtain ⟨slot, member, _⟩ := scope.task.demand
  have standing : slot.bearer ∈ PublicFunction.Delegation.members scope.task :=
    List.mem_map.mpr ⟨slot, member, rfl⟩
  let probe := request scope cut.raw slot.bearer (.propose slot.bearer)
  have same : request (withCutoff scope replacement) cut.raw slot.bearer (.propose slot.bearer) = probe := rfl
  have offered : (law base (withCutoff scope replacement)).operationAllowed cut.raw probe = true := by
    rw [← same]
    apply (command_policy base (withCutoff scope replacement) cut.raw slot.bearer (.propose slot.bearer)).mpr
    exact ⟨standing, reopened⟩
  unfold Installed at original relabelled
  rw [← relabelled, original] at offered
  exact (not_le_of_gt expired) ((command_policy base scope cut.raw slot.bearer (.propose slot.bearer)).mp offered).2

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
