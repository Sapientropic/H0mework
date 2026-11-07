import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.History

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

/-- Nat indexes observations of the actual recursively generated source.
No future inputs, endpoints or per-step laws are parameters. -/
def currentAt : Nat → Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | 0 => source
  | n+1 => (currentAt n).advance

theorem every_actual_epoch_reads_its_live_control_and_closes_its_whole_ledger (n : Nat) :
    Current.ClosedAt (currentAt source n) :=
  (currentAt source n).the_source_generates_its_whole_ledger_actual_epoch

theorem every_next_is_the_same_root_resolver (n : Nat) :
    (currentAt source (n+1)).inquiry.erase =
      (RootInquiryProcessNode.answered (currentAt source n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (currentAt source n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (currentAt source (n+1)).inquiry) :=
  (currentAt source n).advance_is_the_actual_root_successor

theorem no_native_birth_or_epoch_resets_either_original_paid_row (n : Nat) :
    (currentAt source n).native.rows.productive.progressBudget = 0 ∧
      (currentAt source n).native.rows.gross.progressBudget = 0 :=
  ⟨(currentAt source n).native.rows.productive_zero,(currentAt source n).native.rows.gross_zero⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.History
