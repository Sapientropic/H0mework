import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Drain
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Source.Program Abolition.Root Abolition.Root.Registered
open Quantities

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Only instructions are proposed. The handoff date and the new root
current are read from the first actually paid renewal. -/
structure Proposal (Party Good Port Technology Instrument : Type) where
  preparation : List (Option (Compile.RawInput Party Good Port Technology Instrument))
  pair : Material.Migration.CodePair Party Good Port Technology Instrument

def preparedScript (source : C) (proposal : Proposal Party Good Port Technology Instrument) : Script :=
  Proposal.preparation proposal ++ Execution.drain (Execution.endAt source (Proposal.preparation proposal))

def prepared (source : C) (proposal : Proposal Party Good Port Technology Instrument) : C := Execution.endAt source (preparedScript source proposal)

def migrationQuery (source : C) (proposal : Proposal Party Good Port Technology Instrument) : C :=
  Execution.query (prepared source proposal) (some (.migrate proposal.pair))

def migrated (source : C) (proposal : Proposal Party Good Port Technology Instrument) : C := (migrationQuery source proposal).advance

def renewalStart (source : C) (proposal : Proposal Party Good Port Technology Instrument) : C :=
  Execution.endAt (migrated source proposal) (Execution.drain (migrated source proposal))

def renewalQuery (source : C) (proposal : Proposal Party Good Port Technology Instrument) : C := Execution.query (renewalStart source proposal) (some .advance)

def renewed (source : C) (proposal : Proposal Party Good Port Technology Instrument) : C := (renewalQuery source proposal).advance

def script (source : C) (proposal : Proposal Party Good Port Technology Instrument) : Script :=
  preparedScript source proposal ++
    (some (.migrate proposal.pair) :: Execution.drain (migrated source proposal)) ++
    (some .advance :: Execution.drain (renewed source proposal))

def completed (source : C) (proposal : Proposal Party Good Port Technology Instrument) : C := Execution.endAt source (script source proposal)

def handoffTime (source : C) (proposal : Proposal Party Good Port Technology Instrument) : ℚ := (renewed source proposal).raw.clock

theorem end_is_the_original_renewal_and_its_accounting (source : C) (proposal : Proposal Party Good Port Technology Instrument) :
    completed source proposal =
      Execution.endAt (renewed source proposal) (Execution.drain (renewed source proposal)) := by
  simp only [completed, script, Execution.endAt_append]
  rfl

theorem preparation_is_ready (source : C) (proposal : Proposal Party Good Port Technology Instrument) : ¬ Pending (prepared source proposal) := by
  unfold prepared preparedScript
  rw [Execution.endAt_append]
  exact (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain _).1

theorem renewal_is_ready (source : C) (proposal : Proposal Party Good Port Technology Instrument) : ¬ Pending (renewalStart source proposal) :=
  (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain _).1

theorem the_handoff_time_is_the_completed_root_clock (source : C) (proposal : Proposal Party Good Port Technology Instrument) :
    (completed source proposal).raw.clock = handoffTime source proposal := by
  rw [end_is_the_original_renewal_and_its_accounting,
    (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain _).2.1]
  rfl

theorem the_handoff_uses_one_original_ledger (source : C) (proposal : Proposal Party Good Port Technology Instrument) :
    Recorded source (script source proposal) :=
  record source _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
