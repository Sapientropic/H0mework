import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Tight
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Clock
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PaidPeriod

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal

open Source.Program Abolition.Root Abolition.Root.Registered Execution
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable normalise)

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Policy" => Nat → C → Script

def producing (chooseWord : Nat → C → Word) : Policy :=
  fun stage current => periodAndAccounting current (chooseWord stage current)

/-- A local physical and institutional invariant suffices to generate
the paid stages. The original interpreter and native drain compute them. -/
theorem production_and_native_accounting_generate_a_cofinal_paid_policy
    (source : C) (chooseWord : Nat → C → Word) (live : Nat → C → Prop) (initial : live 0 source)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (quantum : ℚ) (positive : 0 < quantum)
    (localLaw : ∀ stage current, live stage current →
      Ready current ∧ ReviewAvailable current ∧ PeriodChecks current (chooseWord stage current) ∧
      quantum ≤ max 0 ((Physical.Public.interpreter current.native.input).duration current.raw) ∧
      inspect stage current (producing chooseWord stage current) = none ∧
      live (stage + 1) (endAt current (producing chooseWord stage current))) :
    Paid source (producing chooseWord) Issue inspect := by
  let policy := producing chooseWord
  have active (stage : Nat) : live stage (stageAt source policy stage) := by
    induction stage with
    | zero => exact initial
    | succ n inherited =>
      rw [next_stage_is_the_literal_original_next]
      exact (localLaw n _ inherited).2.2.2.2.2
  have step (stage : Nat) := localLaw stage _ (active stage)
  have native (stage : Nat) := the_original_paid_period_retains_all_native_rows
    (stageAt source policy stage) (chooseWord stage (stageAt source policy stage))
    (step stage).1 (step stage).2.1 (step stage).2.2.1
  refine ⟨fun stage => (native stage).1, fun stage => (step stage).2.2.2.2.1,
    a_positive_paid_clock_quantum_crosses_every_physical_horizon source policy quantum positive ?_⟩
  intro stage
  unfold elapsed
  change quantum ≤ (endAt (stageAt source policy stage)
    (periodAndAccounting (stageAt source policy stage) (chooseWord stage (stageAt source policy stage)))).raw.clock - _
  rw [(native stage).2]
  have duration := (step stage).2.2.2.1
  change quantum ≤ _ + max 0 _ - _
  linarith only [duration]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal
