import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Occurrence
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Consent
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation.Stock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Quantities.Execution
open Reparation Reparation.Actual
open private located from
  H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation.Stock

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

omit [DecidableEq Port] [DecidableEq Community] in
private theorem programme_requests_have_no_controller_consent
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (before : Capitalism.Universal.Abolition.Root.Actual.Current
      (Party := Party) (Good := Good) (Port := Port) (Technology := Technology)
      (Instrument := Instrument))
    (code : List (Compile.RawInput Party Good Port Technology Instrument))
    (item : ExecutionItem Party Good Port Technology Instrument)
    (actual : item ∈ Optimality.Programme.items input before code) :
    item.request.consents = [] := by
  induction code generalizing before with
  | nil => cases actual
  | cons raw tail ih =>
      rcases List.mem_append.mp actual with direct | later
      · exact Physical.Public.every_actual_public_instruction_has_no_controller_consent input before raw item direct
      · exact ih _ later

omit [DecidableEq Community] in
theorem the_original_material_inventory_has_no_controller_consent
    (cut : Conflict.Root.Cut Party Good Port Technology Instrument)
    (input : Input Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (actual : item ∈ Boundary.Actual.items cut input) :
    item.request.consents = [] := by
  change item ∈ inventory cut [input] at actual
  rw [← material_is_the_folded_actual_inventory cut [input]] at actual
  exact programme_requests_have_no_controller_consent _ _ _ _ actual

/-- The existing public material interpreter sees one signer on a receipt.
The two actual parties remain distinct on the original damage addresses. -/
theorem every_cross_community_receipt_opens_its_equal_reverse_damage
    {seed : Conflict.Root.Cut Party Good Port Technology Instrument}
    {community : Party → Community} {key : Key Party Good}
    (receipt : SignedReceipt seed key)
    (foreign : community key.1 ≠ community key.2.1) :
    ∃ damage : Boundary.Actual.DamageAt (endAt seed receipt.past) receipt.input community,
      damage.position = receipt.position ∧ damage.key = (key.2.1, key.1, key.2.2) ∧
      damage.quantity = receipt.quantity := by
  let cut := endAt seed receipt.past
  let item := receipt.item
  let law := Boundary.Actual.materialLaw cut
  let reverse : Key Party Good := (key.2.1, key.1, key.2.2)
  obtain ⟨signed, valid, goods, form, quantity⟩ :=
    positive_receipt_has_the_original_signature_and_delivery _ item key receipt.positive
  have different : key.1 ≠ key.2.1 := fun equal => foreign (congrArg community equal)
  have consent : item.request.consents = [] :=
    the_original_material_inventory_has_no_controller_consent cut receipt.input item receipt.is_original_receipt.1
  have rawLaw : cut.native.input = seed.native.input := endAt_input seed receipt.past
  have accepted : law.Valid item.before item.request := by
    change (Physical.Public.interpreter cut.native.input).Valid item.before item.request
    rw [rawLaw]
    exact PublicFunction.valid_physical _ _ _ valid
  have reverseLoss : loss law community item reverse = receipt.quantity := by
    have coerced : Coercive community item reverse :=
      ⟨foreign.symm, signed, by simp [consent]⟩
    have actualQuantity : amount Good goods key.2.2 = receipt.quantity := by
      rw [RawLaw.actualCredit, if_pos valid, RawLaw.credit, form, located, if_pos rfl] at quantity
      exact quantity
    have debits : flowAt (law.actualDebit item.before item.request) key.2.1 key.2.2 =
        receipt.quantity := by
      rw [RawLaw.actualDebit, if_pos accepted, RawLaw.debit, form, located, if_pos rfl, actualQuantity]
    have credits : flowAt (law.actualCredit item.before item.request) key.2.1 key.2.2 = 0 := by
      rw [RawLaw.actualCredit, if_pos accepted, RawLaw.credit, form, located, if_neg different]
    have measured : loss law community item reverse =
        max 0 (flowAt (law.actualDebit item.before item.request) key.2.1 key.2.2 -
          flowAt (law.actualCredit item.before item.request) key.2.1 key.2.2) :=
      if_pos coerced
    rw [measured, debits, credits, sub_zero, max_eq_right receipt.positive.le]
  let damage : Boundary.Actual.DamageAt cut receipt.input community :=
    ⟨(receipt.position, reverse), reverseLoss ▸ receipt.positive⟩
  exact ⟨damage, rfl, rfl, reverseLoss⟩

#print axioms every_cross_community_receipt_opens_its_equal_reverse_damage

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
