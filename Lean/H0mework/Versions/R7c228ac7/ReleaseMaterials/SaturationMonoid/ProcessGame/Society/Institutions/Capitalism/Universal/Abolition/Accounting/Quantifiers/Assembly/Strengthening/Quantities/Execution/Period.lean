import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument

abbrev PeriodChecks (source : C) (word : Word) :=
  Public.Scope.Checks source.native.input source.native.depth source.native.count
    source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.actual.snapshot
    (normalise word)

private theorem permitted_review_selects_the_period (source : C) (word : Word)
    (review : ReviewAvailable source) :
    (query source (some (.execute word))).executionRaw = .execute word := by
  have same : (query source (some (.execute word))).control = source.control :=
    (source.requery_keeps_control_and_complete_account (fun _ _ => .execute word)).1
  unfold Evolving.Epoch.Current.executionRaw Evolving.Epoch.Current.choice
  rw [same, submitted_is_original]
  unfold Evolving.Epoch.select
  split
  · rfl
  · rename_i cursor observed
    have available : cursor.recourse = true := by
      simpa only [ReviewAvailable, observed] using review
    rw [if_pos available]
    rfl

private theorem checked_period_is_the_effective_word (source : C) (word : Word)
    (ready : Ready source) (review : ReviewAvailable source) (checked : PeriodChecks source word) :
    Optimality.Programme.Epoch.effective (query source (some (.execute word))) = [.execute word] := by
  have readyAt : Ready (query source (some (.execute word))) := ready
  have original := (Public.Scope.every_checked_period_executes_the_original_proposal source.native.input
    source.native.depth source.native.count source.native.prefixLimit source.native.renewalLimit
    source.native.oldPast source.native.actual.snapshot (.execute word) (normalise word) rfl checked).1
  unfold Optimality.Programme.Epoch.effective
  rw [if_neg readyAt, permitted_review_selects_the_period source word review]
  exact congrArg (fun body => [body]) original

private theorem checked_period_has_the_literal_physical_result (source : C) (word : Word)
    (checked : PeriodChecks source word) :
    let initial := Evolving.Epoch.Source.originalState source.native
    let law := Physical.Public.interpreter source.native.input
    let result := Physical.Public.compile source.native.input initial (.execute word)
    result.next.raw = law.next source.raw (normalise word) ∧
      result.execution.items = law.rawItems source.raw (normalise word) := by
  intro initial law result
  have items : ∀ item ∈ law.rawItems initial.raw (normalise word),
      (Physical.Public.interpreter source.native.input).Valid item.before item.request :=
    fun item present => (checked.2.2.1 item present).1
  change (Physical.Public.compile source.native.input initial (.execute word)).next.raw = _ ∧
    (Physical.Public.compile source.native.input initial (.execute word)).execution.items = _
  cases Physical.Public.compile source.native.input initial (.execute word) with
  | accepted actual selection paid =>
      have same : normalise word = actual := Option.some.inj selection
      subst actual
      exact ⟨rfl, rfl⟩
  | refused actual selection item listed failed =>
      have same : normalise word = actual := Option.some.inj selection
      subst actual
      exact (failed (items item listed)).elim
  | metadata selection => cases selection

/-- The exact guarded period advances the literal real clock. Its native
accounting can be consumed afterwards without repeating its material body. -/
theorem a_checked_period_has_the_original_real_effect (source : C) (word : Word)
    (ready : Ready source) (review : ReviewAvailable source) (checked : PeriodChecks source word) :
    (next source (some (.execute word))).raw =
      (Physical.Public.interpreter source.native.input).next source.raw (normalise word) := by
  have literal := effective_step source (some (.execute word))
  rw [checked_period_is_the_effective_word source word ready review checked] at literal
  exact (congrArg (fun value => value.raw) literal).symm.trans
    (checked_period_has_the_literal_physical_result source word checked).1

theorem a_checked_period_has_the_original_paid_inventory (source : C) (word : Word)
    (ready : Ready source) (review : ReviewAvailable source) (checked : PeriodChecks source word) :
    inventory source [some (.execute word)] =
      (Physical.Public.interpreter source.native.input).rawItems source.raw (normalise word) := by
  have literal := effective_inventory source (some (.execute word))
  rw [checked_period_is_the_effective_word source word ready review checked] at literal
  simp only [inventory, List.append_nil]
  rw [← literal, Optimality.Programme.items, Optimality.Programme.items, List.append_nil]
  exact (checked_period_has_the_literal_physical_result source word checked).2

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
