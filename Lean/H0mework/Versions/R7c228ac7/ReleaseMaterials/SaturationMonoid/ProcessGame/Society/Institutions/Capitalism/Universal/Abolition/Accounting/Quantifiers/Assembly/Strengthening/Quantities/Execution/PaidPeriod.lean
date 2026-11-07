import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Drain
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Primitive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable normalise)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def periodAndAccounting (source : C) (word : Word) : Script :=
  [some (.execute word)] ++ drain (next source (some (.execute word)))

theorem inventory_of_the_original_period_and_accounting
    (source : C) (word : Word) (ready : Ready source) (review : ReviewAvailable source)
    (checked : PeriodChecks source word) :
    inventory source (periodAndAccounting source word) =
      (Physical.Public.interpreter source.native.input).rawItems source.raw (normalise word) := by
  let paid := next source (some (.execute word))
  have empty := (the_first_exhausted_native_cut_is_the_original_paid_drain paid).2.2.1
  unfold periodAndAccounting
  rw [inventory_append, show endAt source [some (.execute word)] = paid from rfl, empty, List.append_nil]
  exact a_checked_period_has_the_original_paid_inventory source word ready review checked

theorem the_original_paid_period_retains_all_native_rows
    (source : C) (word : Word) (ready : Ready source) (review : ReviewAvailable source)
    (checked : PeriodChecks source word) :
    Settled source (periodAndAccounting source word) ∧
      (endAt source (periodAndAccounting source word)).raw =
        (Physical.Public.interpreter source.native.input).next source.raw (normalise word) := by
  let paid := next source (some (.execute word))
  have terminal : endAt source (periodAndAccounting source word) = endAt paid (drain paid) := rfl
  obtain ⟨finished, sameMaterial, _, _, _⟩ := the_first_exhausted_native_cut_is_the_original_paid_drain paid
  refine ⟨settle source _ ⟨?_, terminal.symm ▸ finished⟩,
    (congrArg (fun current : C => current.raw) terminal).trans
      (sameMaterial.trans (a_checked_period_has_the_original_real_effect source word ready review checked))⟩
  have actual := inventory_of_the_original_period_and_accounting source word ready review checked
  apply (Demand.covers_iff_original_floor_of_paid_inventory _ _ ExecutionItem.index (by simpa using actual)).mpr
  intro cell required
  obtain ⟨bearer, listed, actualCell⟩ := List.mem_flatMap.mp required
  apply checked.2.1 cell
  apply List.mem_flatMap.mpr
  refine ⟨bearer, ?_, actualCell⟩
  exact Public.Scope.every_current_standing_is_checked source.native.input source.native.depth source.native.count
    source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.actual.snapshot
    (normalise word) bearer listed

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
