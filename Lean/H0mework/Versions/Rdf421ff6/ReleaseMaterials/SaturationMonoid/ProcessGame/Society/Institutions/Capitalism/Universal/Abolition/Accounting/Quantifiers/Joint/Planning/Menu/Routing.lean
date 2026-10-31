import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu.Production

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

/-- Both original rows share this original refund. The extra reserve covers
only still-active productive debt and this word's real prior costs. -/
def grossFrom (current : Current seed claim) : RawEvent Party Good Port Technology Instrument →
    List (Entitlement.Duty.Key (Party := Party) (Good := Good)) → RawEvent Party Good Port Technology Instrument
  | front, [] => front
  | front, key :: rest =>
      let work := primitiveAnalysis seed claim current front
      let pKey := (key.1,key.2.2)
      let reservation := if 0 < current.productive pKey ∧
          key.2.1 ∈ Responsibility.controllerCohort mechanism past nature response ∧
          pKey ∈ Responsibility.Family.positiveScope mechanism past nature response then
        max 0 (current.productive pKey - work.netProductive pKey) else 0
      let due := work.gross key + reservation
      let next := if 0 < due then front ++ [command seed key.1 (.transfer key.2.1 key.1 [(key.2.2,due)])] else front
      grossFrom current next rest

def productiveFrom (current : Current seed claim) (operator : Party) :
    RawEvent Party Good Port Technology Instrument → List (Party × Good) → RawEvent Party Good Port Technology Instrument
  | front, [] => front
  | front, key :: rest =>
      let work := primitiveAnalysis seed claim current front
      let due := max 0 (current.productive key - work.netProductive key)
      let next := if 0 < current.productive key ∧ 0 < due ∧ operator ≠ key.1 then
        front ++ [command seed key.1 (.transfer operator key.1 [(key.2,due)])] else front
      productiveFrom current operator next rest

def materialPlan (current : Current seed claim) (operator : Party) (technology : Technology) :
    RawEvent Party Good Port Technology Instrument :=
  if Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current then needsWord seed claim current else
  let funded := fundedNeeds seed claim current operator (productionPrefix seed claim current operator technology)
  let refunded := grossFrom seed claim current funded (Entitlement.Duty.scope (window seed))
  productiveFrom seed claim current operator refunded (Responsibility.Family.positiveScope mechanism past nature response)

def plantPlan (current : Current seed claim) (operator : Party) (technology : Technology) :
    RawEvent Party Good Port Technology Instrument :=
  materialPlan seed claim current operator technology ++ settlements seed

/-- The finite menu is generated from current source actors and original
requested technology parameters. It contains no caller cap or future table. -/
def operators (current : Current seed claim) : List Party :=
  if Current.productivePaid seed claim current then
    ((Entitlement.Duty.scope (window seed)).filter (fun key => 0 < current.gross key) |>.map (fun key => key.2.1)).dedup
  else Responsibility.controllerCohort mechanism past nature response

def plans (current : Current seed claim) : List (RawEvent Party Good Port Technology Instrument) :=
  if Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current then
    [needsWord seed claim current ++ settlements seed] else
    (operators seed claim current).flatMap fun operator =>
      (technologies seed claim current).map (plantPlan seed claim current operator)

theorem every_plan_keeps_the_original_actor_technology_and_financial_tail
    (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (original : word ∈ plans seed claim current) :
    (Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current ∧
      word = needsWord seed claim current ++ settlements seed) ∨
    ∃ operator ∈ operators seed claim current,
      ∃ technology ∈ technologies seed claim current,
        word = materialPlan seed claim current operator technology ++ Evolution.Ingress.Joint.Settlement.word seed := by
  unfold plans at original
  split at original
  · next paid => exact .inl ⟨paid.1,paid.2,List.mem_singleton.mp original⟩
  · right
    obtain ⟨operator,cohort,inside⟩ := List.mem_flatMap.mp original
    obtain ⟨technology,parameter,same⟩ := List.mem_map.mp inside
    exact ⟨operator,cohort,technology,parameter,same.symm⟩

theorem a_paid_original_pair_cannot_generate_another_compulsory_material_action
    (current : Current seed claim) (paid : Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current)
    (operator : Party) (technology : Technology) :
    plantPlan seed claim current operator technology = needsWord seed claim current ++ settlements seed := by
  rw [plantPlan,materialPlan,if_pos paid]

omit [DecidableEq Technology] in
theorem a_gross_operator_after_productive_settlement_has_a_live_original_cause
    (current : Current seed claim) (paid : Current.productivePaid seed claim current)
    (operator : Party) (original : operator ∈ operators seed claim current) :
    ∃ key ∈ Entitlement.Duty.scope (window seed), 0 < current.gross key ∧ key.2.1 = operator := by
  rw [operators,if_pos paid] at original
  obtain ⟨key,original,same⟩ := List.mem_map.mp (List.mem_dedup.mp original)
  have member := List.mem_filter.mp original
  exact ⟨key,member.1,of_decide_eq_true member.2,same⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu
