import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain

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

theorem no_ordinary_step_bypasses_a_required_new_claim_admission (actual : FinancialCurrent seed) :
    Public.Accounting.registration? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) actual = none := by
  unfold Public.Accounting.registration?
  split
  · rename_i paid
    split
    · rfl
    · rename_i item found
      have member : item ∈ Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) :=
        List.mem_of_getElem? (by simpa only [Public.Accounting.item?,paid,if_true] using found)
      split
      · rfl
      · rename_i fresh issued
        cases (no_original_position_requests_another_loan seed claim item member).symm.trans issued
  · rfl

private theorem a_native_step_retains_the_paid_body
    (actual : FinancialCurrent seed) (paid : actual.bodyPaid = true) :
    (Runtime.next seed claim actual).bodyPaid = true := by
  unfold Runtime.next Public.Accounting.next
  rw [dif_pos paid]
  split
  · exact paid
  · split
    · exact paid
    · exact (Public.Accounting.Current.after_item_reads_the_source_generated_native_account _ paid _).2.2

theorem every_positive_native_stage_has_already_paid_the_single_body (stages : Nat) :
    (stateAt seed claim (stages + 1)).bodyPaid = true := by
  induction stages with
  | zero => exact (Runtime.the_body_is_paid_once_before_any_native_item seed claim).1
  | succ stages earlier =>
      change ((Runtime.next seed claim)^[(stages + 1) + 1] (Runtime.initial seed)).bodyPaid = true
      rw [Function.iterate_succ_apply']
      exact a_native_step_retains_the_paid_body seed claim _ earlier

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain
