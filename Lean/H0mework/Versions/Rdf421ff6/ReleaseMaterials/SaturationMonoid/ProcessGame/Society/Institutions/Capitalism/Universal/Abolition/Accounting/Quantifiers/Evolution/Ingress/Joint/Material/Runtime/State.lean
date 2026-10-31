import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Transport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

abbrev FinancialCurrent := Public.Accounting.Current seed.input seed.depth seed.count (Background.nativeAccount seed)

def cursor := Physical.receive (Execution.Prefix.sharedCursor seed) (.execute (Material.word seed claim))

def initial : FinancialCurrent seed := Public.Accounting.initial seed.input seed.depth seed.count (Background.nativeAccount seed)

def next : FinancialCurrent seed → FinancialCurrent seed :=
  Public.Accounting.next seed.input seed.depth seed.count 0 0 [] (cursor seed claim)

def sharedAt (actual : FinancialCurrent seed) : Current seed claim :=
  if actual.bodyPaid then Planning.actualNext seed claim (Material.shared seed claim) else Material.shared seed claim

def support (actual : FinancialCurrent seed) : (Admission.N seed claim).Support :=
  Material.support seed claim (Public.Accounting.support seed.input seed.depth seed.count (Background.family seed) actual)
    (sharedAt seed claim actual)

omit [DecidableEq Technology] in
theorem the_initial_financial_account_is_the_actual_background :
    (initial seed).account = Background.nativeAccount seed ∧ (initial seed).bodyPaid = false := ⟨rfl,rfl⟩

theorem the_body_is_paid_once_before_any_native_item :
    (next seed claim (initial seed)).bodyPaid = true ∧
      (next seed claim (initial seed)).account = Background.nativeAccount seed := ⟨rfl,rfl⟩

theorem the_first_material_next_is_the_source_selected_actual_next :
    sharedAt seed claim (next seed claim (initial seed)) =
      Planning.actualNext seed claim (Material.shared seed claim) := by
  simp only [sharedAt,(the_body_is_paid_once_before_any_native_item seed claim).1,if_true]

theorem native_bookkeeping_keeps_the_already_executed_material_state
    (actual : FinancialCurrent seed) (paid : actual.bodyPaid = true) :
    sharedAt seed claim (next seed claim actual) = sharedAt seed claim actual := by
  have later : (next seed claim actual).bodyPaid = true := by
    unfold next Public.Accounting.next
    rw [dif_pos paid]
    split
    · exact paid
    · split
      · exact paid
      · exact (Public.Accounting.Current.after_item_reads_the_source_generated_native_account actual paid _).2.2
  simp only [sharedAt,paid,later,if_true]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
