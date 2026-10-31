import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu.Routing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology] in
private theorem append_no_consent (front : RawEvent Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (before : ∀ old ∈ front, old.consents = [])
    (none : request.consents = []) : ∀ old ∈ front ++ [request], old.consents = [] := by
  intro old member
  rcases List.mem_append.mp member with original | added
  · exact before old original
  · cases List.mem_singleton.mp added
    exact none

omit [DecidableEq Technology] in
private theorem funding_no_consent (operator : Party) (front : RawEvent Party Good Port Technology Instrument)
    (keys : List (Party × Good)) (before : ∀ request ∈ front, request.consents = []) :
    ∀ request ∈ fundNeedsFrom seed claim current operator front keys, request.consents = [] := by
  induction keys generalizing front with
  | nil => exact before
  | cons key rest inherited =>
      dsimp only [fundNeedsFrom]
      split
      · exact inherited _ (append_no_consent _ _ before rfl)
      · exact inherited _ before

omit [DecidableEq Technology] in
private theorem refunds_no_consent (front : RawEvent Party Good Port Technology Instrument)
    (keys : List (Entitlement.Duty.Key (Party := Party) (Good := Good))) (before : ∀ request ∈ front, request.consents = []) :
    ∀ request ∈ grossFrom seed claim current front keys, request.consents = [] := by
  induction keys generalizing front with
  | nil => exact before
  | cons key rest inherited =>
      dsimp only [grossFrom]
      split_ifs <;> first
      | exact inherited _ before
      | apply inherited; exact append_no_consent _ _ before rfl

omit [DecidableEq Technology] in
private theorem repairs_no_consent (operator : Party) (front : RawEvent Party Good Port Technology Instrument)
    (keys : List (Party × Good)) (before : ∀ request ∈ front, request.consents = []) :
    ∀ request ∈ productiveFrom seed claim current operator front keys, request.consents = [] := by
  induction keys generalizing front with
  | nil => exact before
  | cons key rest inherited =>
      dsimp only [productiveFrom]
      split
      · exact inherited _ (append_no_consent _ _ before rfl)
      · exact inherited _ before

omit [DecidableEq Technology] in
theorem need_bills_have_no_controller_consent : ∀ request ∈ needsWord seed claim current, request.consents = [] := by
  intro request member
  obtain ⟨actor,_,inside⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp inside with necessity | maintenance
  · split_ifs at necessity <;> simp_all [command]
  · split_ifs at maintenance <;> simp_all [command]

theorem production_has_no_controller_consent (operator : Party) (technology : Technology) :
    ∀ request ∈ productionPrefix seed claim current operator technology, request.consents = [] := by
  intro request member
  unfold productionPrefix at member
  split_ifs at member <;> simp_all [command,List.mem_replicate]
  rcases member with original | original <;> simp_all

theorem material_plan_requires_no_controller_consent (operator : Party) (technology : Technology) :
    ∀ request ∈ materialPlan seed claim current operator technology, request.consents = [] := by
  unfold materialPlan
  split
  · exact need_bills_have_no_controller_consent seed claim current
  · apply repairs_no_consent
    apply refunds_no_consent
    intro request member
    rcases List.mem_append.mp member with funding | need
    · exact funding_no_consent seed claim current operator _ _ (production_has_no_controller_consent seed claim current operator technology) request funding
    · exact need_bills_have_no_controller_consent seed claim current request need

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu
