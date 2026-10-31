import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Supply

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private theorem productive_items (current : Current) :
    law.rawItems current (candidate current .productive) =
      [⟨0, current, submission⟩, ⟨1, current, Response.production⟩,
       ⟨2, law.step current Response.production, request scope (law.step current Response.production) false .revoke⟩] := by
  simp only [candidate, signedWord, Response.Method.word, Response.Method.prefix,
    submission_preserves_authority_and_stock, List.cons_append, List.nil_append, RawLaw.rawItems, RawLaw.execute]

private theorem productive_material_refusal (current : Current) (active : Mandate.Response.Active current)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (actual : item ∈ law.rawItems current (candidate current .productive))
    (refused : ¬ law.Valid item.before item.request) :
    ∃ debit ∈ law.debit item.before item.request, 0 < debit.2 - item.before.stock debit.1.1 debit.1.2 := by
  rw [productive_items] at actual
  simp only [List.mem_cons, List.not_mem_nil, or_false] at actual
  rcases actual with same | same | same
  · subst item
    exact False.elim (refused (submission_valid current))
  · subst item
    have missing : current.stock false .feedstock < 1 :=
      lt_of_not_ge (fun enough => refused ((production_valid_iff_material current).mpr enough))
    refine ⟨((false, .feedstock), 1), ?_, sub_pos.mpr missing⟩
    simp [law, Mandate.law, RawLaw.debit, Response.production, base, locate]
  · subst item
    have unchanged : (law.step current Response.production).technology = current.technology :=
      method_prefix_keeps_the_signed_snapshot current .productive
    have activeAfter : Mandate.Response.Active (law.step current Response.production) := by
      unfold Mandate.Response.Active
      rw [unchanged]
      exact active
    have missing : (law.step current Response.production).stock false .service < 1 :=
      lt_of_not_ge (fun enough => refused ((revoke_valid_iff_material _ activeAfter).mpr enough))
    refine ⟨((false, .service), 1), ?_, sub_pos.mpr missing⟩
    simp [law, Mandate.law, RawLaw.debit, request, base, scope, locate]

theorem blocked_active_cut_has_a_positive_repair (current : Current) (active : Mandate.Response.Active current)
    (blocked : (select current).isPaid = false) : ∃ demand, demand ∈ demands current := by
  have notLegal : ¬ Legal current .productive := by
    generalize chosen : select current = selection at blocked
    cases selection
    next method included legal => cases blocked
    next refused => exact refused .productive (by simp [methods])
  have invalid : ∃ item ∈ law.rawItems current (candidate current .productive), ¬ law.Valid item.before item.request := by
    by_contra none
    apply notLegal
    intro item included
    by_contra refused
    exact none ⟨item, included, refused⟩
  obtain ⟨item, actual, refused⟩ := invalid
  have coreSame : core current = candidate current .productive := by
    unfold core
    generalize chosen : select current = selection at blocked ⊢
    cases selection
    next method included legal => cases blocked
    next refused => rfl
  have inCore : item ∈ law.rawItems current (core current) := by rwa [coreSame]
  obtain ⟨refusal, recorded, exactItem⟩ := every_actual_refusal_is_recorded current item inCore refused
  obtain ⟨debit, required, shortfall⟩ := productive_material_refusal current active item actual refused
  rw [← exactItem] at required shortfall
  obtain ⟨demand, present, _⟩ := every_positive_gap_is_recorded current refusal recorded debit required shortfall
  have exactDemands : demands current = gaps current := by
    unfold demands
    generalize chosen : select current = selection at blocked ⊢
    cases selection
    next method included legal => cases blocked
    next refused => rfl
  exact ⟨demand, by rwa [exactDemands]⟩

theorem blocked_active_cut_actually_attempts_a_positive_supply (current : Current)
    (active : Mandate.Response.Active current) (blocked : (select current).isPaid = false) :
    ∃ event ∈ supplies current, 0 < event.demand.quantity ∧
      event.item ∈ law.rawItems current (word current) := by
  obtain ⟨demand, present⟩ := blocked_active_cut_has_a_positive_repair current active blocked
  have mapped : demand ∈ (supplies current).map SupplyEvent.demand := by
    rwa [supplies, supply_trace_keeps_every_original_demand]
  obtain ⟨event, included, same⟩ := List.mem_map.mp mapped
  exact ⟨event, included, by rw [same]; exact demand.shortfall,
    every_supply_is_in_the_original_word current event included⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
