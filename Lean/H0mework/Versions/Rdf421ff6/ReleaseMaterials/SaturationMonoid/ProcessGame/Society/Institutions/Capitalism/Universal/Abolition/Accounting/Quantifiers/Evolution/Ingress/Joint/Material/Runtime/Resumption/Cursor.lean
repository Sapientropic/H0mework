import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Family
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.NativeEvolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
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

def stageCursor (actual : FinancialCurrent seed) : Option (FinancialCurrent seed) :=
  if actual.bodyPaid then some actual else none

omit [DecidableEq Technology] in
theorem a_present_native_cursor_is_the_same_paid_current
    (current actual : FinancialCurrent seed) (aligned : stageCursor seed current = some actual) :
    current.bodyPaid = true ∧ current = actual := by
  by_cases paid : current.bodyPaid = true
  · exact ⟨paid,Option.some.inj (by simpa only [stageCursor,paid,if_true] using aligned)⟩
  · simp [stageCursor,paid] at aligned

theorem the_actual_root_next_is_the_original_native_next_without_new_admission
    (actual : FinancialCurrent seed) :
    Runtime.next seed claim actual = Public.Accounting.nativeNext seed.input seed.depth seed.count 0 0 []
      (Runtime.cursor seed claim) actual := by
  unfold Runtime.next Public.Accounting.next Public.Accounting.nativeNext
  by_cases paid : actual.bodyPaid = true
  · rw [dif_pos paid,dif_pos paid]
    cases found : Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) actual with
    | none => rfl
    | some item =>
        have original : item ∈ Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) :=
          List.mem_of_getElem? (by simpa only [Public.Accounting.item?,paid,if_true] using found)
        dsimp only
        rw [Drain.no_original_position_requests_another_loan seed claim item original]
  · rw [dif_neg paid,dif_neg paid]

theorem a_native_successor_keeps_the_existing_paid_body
    (actual : FinancialCurrent seed) (paid : actual.bodyPaid = true) :
    (Runtime.next seed claim actual).bodyPaid = true := by
  rw [the_actual_root_next_is_the_original_native_next_without_new_admission]
  unfold Public.Accounting.nativeNext
  rw [dif_pos paid]
  split
  · exact paid
  · exact (Public.Accounting.Current.after_item_reads_the_source_generated_native_account actual paid _).2.2

theorem the_source_support_at_a_paid_cursor_is_the_same_lifted_whole_account
    (enough : Planning.Enough seed claim (Material.shared seed claim))
    (current actual : FinancialCurrent seed) (aligned : stageCursor seed current = some actual) :
    Runtime.support seed claim current = Public.Accounting.support seed.input seed.depth seed.count
      (family seed claim enough) actual := by
  obtain ⟨paid,same⟩ := a_present_native_cursor_is_the_same_paid_current seed current actual aligned
  subst actual
  change Material.support seed claim _ (Runtime.sharedAt seed claim current) =
    Material.support seed claim _ (paidState seed claim)
  unfold Runtime.sharedAt
  rw [paid,if_pos rfl]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
