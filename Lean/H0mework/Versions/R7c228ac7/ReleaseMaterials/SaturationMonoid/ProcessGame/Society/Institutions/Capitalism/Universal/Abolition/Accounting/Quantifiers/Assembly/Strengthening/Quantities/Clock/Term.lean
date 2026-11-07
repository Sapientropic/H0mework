import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Service
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Restriction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock

open Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def completionClock (source : C) (script : Script) : EReal :=
  (((Execution.endAt source script).raw.clock : ℝ) : EReal)

abbrev deadlineCut (source : C) (task : PublicTaskSpec Party Good) :=
  Bounds.Restriction.cutoff source (inspectService source task) (completionClock source)

def PaidBy (source : C) (task : PublicTaskSpec Party Good) (deadline : EReal) : Prop :=
  ∃ script, Settled source script ∧ FullyServed source task script ∧ completionClock source script ≤ deadline

theorem attained_completion_times_are_exactly_the_root_service_image
    (source : C) (task : PublicTaskSpec Party Good) (time : EReal) :
    (time : WithTop EReal) ∈ Bounds.values source
      (Bounds.Restriction.restrict (inspectService source task) (completionClock source)) ↔
    ∃ script, Settled source script ∧ FullyServed source task script ∧ completionClock source script = time := by
  rw [Bounds.Restriction.exact_qualified_image]
  simp only [service_pass_iff_fully_paid]

/-- A proposed cutoff is feasible precisely above the tight cut, or at a
cut reached by a literal paid programme. The source's real clock is used. -/
theorem deadline_iff_above_tight_cut_or_attained
    (source : C) (task : PublicTaskSpec Party Good) (deadline : EReal) :
    PaidBy source task deadline ↔
      deadlineCut source task < (deadline : WithTop EReal) ∨
        deadlineCut source task = (deadline : WithTop EReal) ∧
        ∃ script, Settled source script ∧ FullyServed source task script ∧ completionClock source script = deadline := by
  constructor
  · rintro ⟨script, paid, served, timely⟩
    have passed := (service_pass_iff_fully_paid source task script).mpr served
    have least := Bounds.lower_le source
      (Bounds.Restriction.restrict (inspectService source task) (completionClock source)) script paid.toFeasible
    rw [Bounds.Restriction.restrict, passed] at least
    have within : (completionClock source script : WithTop EReal) ≤ (deadline : WithTop EReal) :=
      WithTop.coe_le_coe.mpr timely
    rcases lt_or_eq_of_le (least.trans within) with earlier | exactTime
    · exact .inl earlier
    · exact .inr ⟨exactTime, script, paid, served,
        WithTop.coe_injective (le_antisymm within (exactTime ▸ least))⟩
  · rintro (earlier | ⟨_, script, paid, served, same⟩)
    · obtain ⟨script, paid, passed, timely⟩ :=
        Bounds.Restriction.a_strict_limit_produces_a_paid_qualified_script source
          (inspectService source task) (completionClock source) _ earlier
      exact ⟨script, paid, (service_pass_iff_fully_paid source task script).mp passed,
        (WithTop.coe_lt_coe.mp timely).le⟩
    · exact ⟨script, paid, served, same.le⟩

theorem the_original_root_resolves_the_tight_service_completion_cut
    (source : C) (task : PublicTaskSpec Party Good) :
    Bounds.Restriction.Minimum source (inspectService source task) (completionClock source) :=
  Bounds.Restriction.resolve _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock
