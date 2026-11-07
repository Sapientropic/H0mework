import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open Source.Program Innovation Quantifiers.Joint Evolution Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

attribute [local irreducible] Execution.Selected.items Planning.selected Planning.actualNext Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))

variable (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

attribute [local irreducible] initial


/-- The already paid original root generates the type-changing actual chain;
only source data, its primitive resource condition and current query code
are inputs. All original responsibility rows are carried by actual writes. -/
theorem the_original_source_generates_its_whole_ledger_actual_evolution (n : Nat) :
    History.ClosedAt (initial seed claim enough reader) n :=
  History.the_source_generates_its_whole_ledger_evolving_closure (initial seed claim enough reader) n


theorem the_completed_source_has_no_pending_native_work :
    ¬ Public.Inquiry.HasWork (initial seed claim enough reader).frame
      (initial seed claim enough reader).actual.actual :=
  initial_has_no_pending_native_work seed claim enough reader


theorem the_first_actual_next_is_the_current_source_raw_action :
    (initial seed claim enough reader).advance =
      (initial seed claim enough reader).raw (the_completed_source_has_no_pending_native_work seed claim enough reader) := by
  exact NativeCurrent.advance_eq_raw (initial seed claim enough reader)
    (the_completed_source_has_no_pending_native_work seed claim enough reader)



end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source
