import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

noncomputable section

def natureIngressAt (past : List InputAt) : Prop :=
  ∃ baseline completed, publicPast past = baseline :: completed ∧ completed.length = preparation.length

/-- Before and after the event's own input position, identical consumed
prefixes cannot reveal which unknown request will be or was supplied. -/
theorem the_source_cannot_consult_unknown_nature_outside_its_actual_ingress
    (localRead : List InputAt → InputAt) (first second : RequestAt) (past : List InputAt)
    (outside : ¬ natureIngressAt past) :
    selectedWith localRead first past = selectedWith localRead second past := by
  unfold selectedWith
  split
  · cases shape : publicPast past with
    | nil => rfl
    | cons baseline completed =>
        have other : completed.length ≠ preparation.length := by
          intro same
          exact outside ⟨baseline, completed, shape, same⟩
        simp only [other, ↓reduceIte]
  · rfl

theorem the_nature_ingress_submits_only_the_original_raw_request
    (localRead : List InputAt → InputAt) (nature : RequestAt) (past : List InputAt)
    (atInput : natureIngressAt past) :
    selectedWith localRead nature past = .primitive nature := by
  obtain ⟨baseline,completed,shape,position⟩ := atInput
  have offered := the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1
  unfold selectedWith
  simp only [offered, ↓reduceIte, shape, position, Nat.lt_irrefl]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
