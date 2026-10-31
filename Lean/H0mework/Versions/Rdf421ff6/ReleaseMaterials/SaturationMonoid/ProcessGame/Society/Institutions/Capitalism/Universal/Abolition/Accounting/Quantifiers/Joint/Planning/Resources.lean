import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Primitive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

/-- Source recipe, stock envelope, original bills and allocation capacity.
No actual Valid, paid target, whole-ledger receipt or future success is a field. -/
structure Resources (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) : Prop where
  recipe : Priority.Adequacy.Capacity.RecipeFacts (actualLaw seed) (primitiveItems seed claim current word)
  startup : Priority.Adequacy.Capacity.Startup (actualLaw seed) current.raw word
  needs : Priority.Adequacy.Capacity.Needs (actualLaw seed) current.raw seed.current.members word
  productive : ∀ key ∈ Responsibility.Family.positiveScope mechanism past nature response,
    current.productive key ≤ max 0 ((primitiveAnalysis seed claim current word).netProductive key)
  gross : ∀ key ∈ Entitlement.Duty.scope (window seed),
    current.gross key ≤ grossCredits seed claim current word key

instance [DecidableEq Technology] (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Resources seed claim current word) :=
  decidable_of_iff (Priority.Adequacy.Capacity.RecipeFacts (actualLaw seed) (primitiveItems seed claim current word) ∧
    Priority.Adequacy.Capacity.Startup (actualLaw seed) current.raw word ∧
    Priority.Adequacy.Capacity.Needs (actualLaw seed) current.raw seed.current.members word ∧
    (∀ key ∈ Responsibility.Family.positiveScope mechanism past nature response,
      current.productive key ≤ max 0 ((primitiveAnalysis seed claim current word).netProductive key)) ∧
    (∀ key ∈ Entitlement.Duty.scope (window seed), current.gross key ≤ grossCredits seed claim current word key))
    ⟨fun facts => ⟨facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2⟩,
      fun facts => ⟨facts.recipe,facts.startup,facts.needs,facts.productive,facts.gross⟩⟩

theorem resource_conditions (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (resources : Resources seed claim current word) :
    Primitive.Conditions (actualLaw seed) (primitiveItems seed claim current word) :=
  Priority.Adequacy.Capacity.primitive_resources_generate_the_complete_conditions
    (actualLaw seed) current.raw word resources.recipe resources.startup

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning
