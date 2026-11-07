import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def requiredStock (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (actor : Party) (good : Good) : ℚ :=
  match items with
  | [] => 0
  | item :: rest => max
      (flowAt (law.debit item.before item.request) actor good - (item.before.stock actor good - initial.stock actor good))
      (requiredStock law initial rest actor good)

omit [DecidableEq Instrument] in
theorem each_primitive_prefix_requirement_is_in_the_source_envelope
    (law : RawLaw Party Good Port Technology Instrument) (initial : RawCurrent Party Good Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (item : ExecutionItem Party Good Port Technology Instrument)
    (inside : item ∈ items) (actor : Party) (good : Good) :
    flowAt (law.debit item.before item.request) actor good - (item.before.stock actor good - initial.stock actor good) ≤
      requiredStock law initial items actor good := by
  induction items with
  | nil => cases inside
  | cons head rest inherited =>
    rcases List.mem_cons.mp inside with same | later
    · subst item
      exact le_max_left _ _
    · exact (inherited later).trans (le_max_right _ _)

/-- A pointwise primitive material inequality. No actual-debit, successful
execution, target next, payment or gate certificate occurs in this condition. -/
def StockDominates (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ actor good, requiredStock law initial (execute law initial 0 word).items actor good ≤ initial.stock actor good

theorem source_stock_domination_makes_every_unrejected_debit_affordable
    (law : RawLaw Party Good Port Technology Instrument) (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (resources : StockDominates law initial word)
    (item : ExecutionItem Party Good Port Technology Instrument) (inside : item ∈ (execute law initial 0 word).items)
    (entry : (Party × Good) × ℚ) (_debited : entry ∈ law.debit item.before item.request) :
    flowAt (law.debit item.before item.request) entry.1.1 entry.1.2 ≤ item.before.stock entry.1.1 entry.1.2 := by
  have prefixBound := each_primitive_prefix_requirement_is_in_the_source_envelope
    law initial _ item inside entry.1.1 entry.1.2
  have sourceBound := resources entry.1.1 entry.1.2
  linarith

/-- The source facts that money cannot supply: actual policy/permission,
primitive sign/recipe nonnegativity, and the original time-local need guard. -/
structure NonMaterialConditions (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : Prop where
  signer : ∀ item ∈ items, RawLaw.SignerMatches item.request
  policy : ∀ item ∈ items, law.operationAllowed item.before item.request = true
  permission : ∀ item ∈ items, ∀ port ∈ law.requiredPorts item.before item.request,
    law.allowed item.before.technology port item.request.signer = true ∨
      law.controller item.before.technology port ∈ item.request.consents
  demand : ∀ item ∈ items, law.ClaimGuard item.before item.request
  debitNonnegative : ∀ item ∈ items, NonnegativeBundle (Party × Good) (law.debit item.before item.request)
  creditNonnegative : ∀ item ∈ items, NonnegativeBundle (Party × Good) (law.credit item.before item.request)

theorem primitive_resources_and_source_conditions_generate_actual_execution
    (law : RawLaw Party Good Port Technology Instrument) (initial : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (resources : StockDominates law initial word)
    (source : NonMaterialConditions law (execute law initial 0 word).items) :
    law.execute initial 0 word = execute law initial 0 word := by
  apply all_primitive_effects_become_the_same_actual_execution
  exact ⟨source.signer,source.policy,source.permission,source.demand,source.debitNonnegative,
    source.creditNonnegative,source_stock_domination_makes_every_unrejected_debit_affordable law initial word resources⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive
