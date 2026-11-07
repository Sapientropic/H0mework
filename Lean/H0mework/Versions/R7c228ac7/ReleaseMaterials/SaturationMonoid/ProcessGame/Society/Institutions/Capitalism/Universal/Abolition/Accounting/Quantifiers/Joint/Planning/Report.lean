import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Selection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Needs

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning

open Source.Program Innovation Priority.Adequacy.Capacity.Inspection

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)

inductive DebtDisposition : Type
  | paid (productive : Current.productivePaid seed claim (actualNext seed claim current))
      (gross : Current.grossPaid seed claim (actualNext seed claim current))
  | productive (key : Party × Good)
      (original : key ∈ Responsibility.Family.positiveScope mechanism past nature response)
      (unpaid : 0 < (actualNext seed claim current).productive key)
  | gross (key : Entitlement.Duty.Key (Party := Party) (Good := Good))
      (original : key ∈ Entitlement.Duty.scope (window seed))
      (unpaid : 0 < (actualNext seed claim current).gross key)

def inspectDebt : DebtDisposition seed claim current :=
  match inspectAll (fun key => (actualNext seed claim current).productive key = 0)
    (Responsibility.Family.positiveScope mechanism past nature response) with
  | .blocked key original failed => .productive key original
      (lt_of_le_of_ne ((actualNext seed claim current).productive_nonnegative key) (Ne.symm failed))
  | .ready productive =>
    match inspectAll (fun key => (actualNext seed claim current).gross key = 0) (Entitlement.Duty.scope (window seed)) with
    | .blocked key original failed => .gross key original
        (lt_of_le_of_ne ((actualNext seed claim current).gross_nonnegative key) (Ne.symm failed))
    | .ready gross => .paid productive gross

structure Report : Type where
  originalAttempt : Entitlement.Execution.InspectionAt (actualLaw seed) current.raw (chosen seed claim current)
  originalDebt : DebtDisposition seed claim current
  independentNeeds : Responsibility.Family.NeedDisposition (actualLaw seed) current.raw (selected seed claim current) seed.current.members

def report : Report seed claim current :=
  ⟨actualInspection seed claim current,inspectDebt seed claim current,
    Responsibility.Family.inspectNeeds (actualLaw seed) current.raw (selected seed claim current) seed.current.members⟩

theorem a_stopped_programme_retains_its_original_first_failure
    (stopped : selected seed claim current ≠ chosen seed claim current) :
    ∃ request rest, chosen seed claim current = selected seed claim current ++ request :: rest ∧
      ¬ (actualLaw seed).Valid ((actualLaw seed).execute current.raw 0 (selected seed claim current)).final request :=
  Entitlement.Execution.a_truncated_source_keeps_its_original_first_failure _ _ _ stopped

theorem every_selected_original_inventory_item_is_actual :
    ∀ item ∈ (actualLaw seed).rawItems current.raw (selected seed claim current),
      (actualLaw seed).Valid item.before item.request :=
  Entitlement.Execution.validity_reaches_every_original_inventory_item _ _ _
    (Entitlement.Execution.the_source_prefix_is_valid _ _ _) 0

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning
