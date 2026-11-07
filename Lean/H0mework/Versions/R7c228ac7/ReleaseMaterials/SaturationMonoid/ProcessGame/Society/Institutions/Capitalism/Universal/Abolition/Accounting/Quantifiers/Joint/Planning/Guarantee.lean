import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Resources
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Realization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

structure ActualSuccess (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) : Prop where
  originalAccepted : ∀ item ∈ (actualLaw seed).rawItems current.raw word,
    (actualLaw seed).Valid item.before item.request
  productivePaid : Current.productivePaid seed claim (Current.advance seed claim current word)
  grossPaid : Current.grossPaid seed claim (Current.advance seed claim current word)
  needsPaid : Exit.Necessity.AllNeedsPaid (actualLaw seed) current.raw seed.current.members word
  originalFinancialEffect : (Current.advance seed claim current word).raw.claims =
    (Primitive.execute (actualLaw seed) current.raw 0 word).final.claims

theorem primitive_resources_generate_one_actual_payment_of_both_original_obligations
    (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (resources : Resources seed claim current word) : ActualSuccess seed claim current word := by
  have conditions := resource_conditions seed claim current word resources
  have same := primitive_resources_generate_the_same_single_actual_allocation seed claim current word conditions
  have valid := Priority.Adequacy.Capacity.original_inventory_is_valid (actualLaw seed) current.raw word conditions
  refine ⟨valid,?_,?_,?_,?_⟩
  · intro key original
    change max 0 (current.productive key - max 0 ((Current.analysis seed claim current word).netProductive key)) = 0
    rw [same]
    apply max_eq_left
    exact sub_nonpos.mpr (resources.productive key original)
  · intro key original
    change (Current.analysis seed claim current word).gross key = 0
    rw [same]
    have conservation := primitive_gross_account_is_exact seed claim current word key
    have capacity := resources.gross key original
    exact le_antisymm (by linarith) ((primitiveAnalysis seed claim current word).gross_nonnegative key)
  · intro actor original
    have bills := resources.needs actor original
    have actual := Priority.Adequacy.Capacity.raw_bill_becomes_actual_paid_service (actualLaw seed) current.raw word valid actor
    exact ⟨(actual _ .necessity).mpr bills.1,(actual _ .maintenance).mpr bills.2⟩
  · change ((actualLaw seed).execute current.raw 0 word).final.claims = _
    rw [Primitive.all_primitive_effects_become_the_same_actual_execution (actualLaw seed) current.raw 0 word conditions]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning
