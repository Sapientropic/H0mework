import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Selection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu.Consent

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning

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

omit [DecidableEq Technology] in
theorem every_original_financial_request_uses_no_extra_consent :
    ∀ request ∈ Menu.settlements seed, request.consents = [] := by
  intro request member
  obtain ⟨slot,_,inside⟩ := List.mem_flatMap.mp member
  obtain ⟨holder,_,generated⟩ := List.mem_filterMap.mp inside
  split at generated
  · cases Option.some.inj generated
    rfl
  · cases generated

theorem every_source_plan_requires_no_controller_consent
    (word : RawEvent Party Good Port Technology Instrument) (original : word ∈ Menu.plans seed claim current) :
    ∀ request ∈ word, request.consents = [] := by
  rcases Menu.every_plan_keeps_the_original_actor_technology_and_financial_tail seed claim current word original with
    ⟨_,_,same⟩ | ⟨operator,_,technology,_,same⟩
  · rw [same]
    intro request member
    rcases List.mem_append.mp member with needed | old
    · exact Menu.need_bills_have_no_controller_consent seed claim current request needed
    · exact every_original_financial_request_uses_no_extra_consent seed request old
  · rw [same]
    intro request member
    rcases List.mem_append.mp member with material | old
    · exact Menu.material_plan_requires_no_controller_consent seed claim current operator technology request material
    · exact every_original_financial_request_uses_no_extra_consent seed request old

theorem chosen_requires_no_controller_consent : ∀ request ∈ chosen seed claim current, request.consents = [] := by
  unfold chosen
  cases selection seed claim current with
  | ready word original resources => exact every_source_plan_requires_no_controller_consent seed claim current word original
  | blocked issues =>
      change ∀ request ∈ (Menu.plans seed claim current).headD
        (Menu.needsWord seed claim current ++ Menu.settlements seed), request.consents = []
      have all := every_source_plan_requires_no_controller_consent seed claim current
      cases available : Menu.plans seed claim current with
      | nil =>
          intro request member
          rcases List.mem_append.mp member with needed | old
          · exact Menu.need_bills_have_no_controller_consent seed claim current request needed
          · exact every_original_financial_request_uses_no_extra_consent seed request old
      | cons word rest =>
          apply all word
          rw [available]
          exact List.mem_cons_self

theorem selected_requires_no_controller_consent : ∀ request ∈ selected seed claim current, request.consents = [] := by
  intro request member
  apply chosen_requires_no_controller_consent seed claim current request
  exact (Entitlement.Execution.the_source_prefix_is_an_original_prefix _ _ _).subset member

theorem selected_is_literal_under_original_signer_resigning :
    (selected seed claim current).map (fun request => request.resign request.signer) = selected seed claim current := by
  calc
    _ = (selected seed claim current).map id := by
      apply List.map_congr_left
      intro request original
      exact Request.resign_self request (selected_requires_no_controller_consent seed claim current request original)
    _ = _ := List.map_id _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning
