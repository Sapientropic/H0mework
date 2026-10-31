import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu.Routing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw primitiveAnalysis dose Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology] in
private theorem append_material (front : RawEvent Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (before : ∀ old ∈ front, Responsibility.NonFinancialOperation old.operation)
    (material : Responsibility.NonFinancialOperation request.operation) :
    ∀ old ∈ front ++ [request], Responsibility.NonFinancialOperation old.operation := by
  intro old member
  rcases List.mem_append.mp member with original | added
  · exact before old original
  · cases List.mem_singleton.mp added
    exact material

omit [DecidableEq Technology] in
theorem funding_preserves_the_original_nonfinancial_prefix (operator : Party)
    (front : RawEvent Party Good Port Technology Instrument) (keys : List (Party × Good))
    (before : ∀ old ∈ front, Responsibility.NonFinancialOperation old.operation) :
    ∀ request ∈ fundNeedsFrom seed claim current operator front keys, Responsibility.NonFinancialOperation request.operation := by
  induction keys generalizing front with
  | nil => exact before
  | cons key rest inherited =>
      dsimp only [fundNeedsFrom]
      split
      · exact inherited _ (append_material _ _ before trivial)
      · exact inherited _ before

omit [DecidableEq Technology] in
theorem gross_refunds_preserve_the_original_nonfinancial_prefix
    (front : RawEvent Party Good Port Technology Instrument)
    (keys : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
    (before : ∀ old ∈ front, Responsibility.NonFinancialOperation old.operation) :
    ∀ request ∈ grossFrom seed claim current front keys, Responsibility.NonFinancialOperation request.operation := by
  induction keys generalizing front with
  | nil => exact before
  | cons key rest inherited =>
      dsimp only [grossFrom]
      split_ifs <;> first
      | exact inherited _ before
      | apply inherited; exact append_material _ _ before trivial

omit [DecidableEq Technology] in
theorem productive_repairs_preserve_the_original_nonfinancial_prefix (operator : Party)
    (front : RawEvent Party Good Port Technology Instrument) (keys : List (Party × Good))
    (before : ∀ old ∈ front, Responsibility.NonFinancialOperation old.operation) :
    ∀ request ∈ productiveFrom seed claim current operator front keys, Responsibility.NonFinancialOperation request.operation := by
  induction keys generalizing front with
  | nil => exact before
  | cons key rest inherited =>
      dsimp only [productiveFrom]
      split
      · exact inherited _ (append_material _ _ before trivial)
      · exact inherited _ before

omit [DecidableEq Technology] in
theorem current_need_bills_are_nonfinancial :
    ∀ request ∈ needsWord seed claim current, Responsibility.NonFinancialOperation request.operation := by
  intro request member
  obtain ⟨actor,_,inside⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp inside with necessity | maintenance
  · split_ifs at necessity <;> simp_all [command,Responsibility.NonFinancialOperation]
  · split_ifs at maintenance <;> simp_all [command,Responsibility.NonFinancialOperation]

theorem current_production_is_nonfinancial (operator : Party) (technology : Technology) :
    ∀ request ∈ productionPrefix seed claim current operator technology, Responsibility.NonFinancialOperation request.operation := by
  intro request member
  unfold productionPrefix at member
  split_ifs at member <;> simp_all [command,Responsibility.NonFinancialOperation,List.mem_replicate]
  rcases member with original | original <;> simp_all

theorem the_material_plan_keeps_every_original_financial_address (operator : Party) (technology : Technology) :
    ((actualLaw seed).next current.raw (materialPlan seed claim current operator technology)).claims = current.raw.claims := by
  apply Responsibility.nonfinancial_word_keeps_every_original_claim
  unfold materialPlan
  split
  · exact current_need_bills_are_nonfinancial seed claim current
  · apply productive_repairs_preserve_the_original_nonfinancial_prefix
    apply gross_refunds_preserve_the_original_nonfinancial_prefix
    intro request member
    rcases List.mem_append.mp member with funded | needed
    · exact funding_preserves_the_original_nonfinancial_prefix seed claim current operator _ _
        (current_production_is_nonfinancial seed claim current operator technology) request funded
    · exact current_need_bills_are_nonfinancial seed claim current request needed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu
