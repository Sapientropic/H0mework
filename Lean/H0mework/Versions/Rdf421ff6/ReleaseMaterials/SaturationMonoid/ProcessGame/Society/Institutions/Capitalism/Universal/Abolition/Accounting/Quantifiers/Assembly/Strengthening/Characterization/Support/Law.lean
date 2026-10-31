import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global.Capital

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support

open Source.Program Source.ProgrammeControl
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- A closed port need not grant access. Whenever its controller can use
it, the same interpretation cannot exclude another person. -/
def NoAsymmetry : Prop :=
  ∀ (raw : RawCurrent Party Good Technology Instrument) port person,
    law.allowed raw.technology port (law.controller raw.technology port) = true →
      law.allowed raw.technology port person = true

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem no_asymmetry_iff_no_private_phase :
    NoAsymmetry law ↔ ∀ raw port person, ¬ PrivatePhase law raw port person := by
  constructor
  · intro shared raw port person phase
    exact Bool.noConfusion ((shared raw port person phase.1).symm.trans phase.2)
  · intro absent raw port person controller
    cases allowed : law.allowed raw.technology port person with
    | true => rfl
    | false => exact False.elim (absent raw port person ⟨controller,allowed⟩)

omit [DecidableEq Port] in
theorem no_asymmetry_generates_the_complete_no_capital_contract
    (shared : NoAsymmetry law) : Global.NoCapital law where
  private_phase := (no_asymmetry_iff_no_private_phase law).1 shared
  kernel := fun raw word ⟨capital⟩ =>
    (no_asymmetry_iff_no_private_phase law).1 shared _ _ _ capital.checked.1.2.2.1
  proper := fun raw word ⟨capital⟩ =>
    (no_asymmetry_iff_no_private_phase law).1 shared _ _ _ capital.dependency.checked.1.2.2.1
  surplus := fun raw word ⟨capital⟩ =>
    (no_asymmetry_iff_no_private_phase law).1 shared _ _ _ capital.dependency.checked.1.2.2.1
  fresh_history := by
    intro input same port item fresh
    obtain ⟨_,_,person,_,phase⟩ := fresh
    rw [same] at phase
    exact (no_asymmetry_iff_no_private_phase law).1 shared _ _ _ phase

omit [DecidableEq Port] in
/-- Exact support for the existing complete exclusion contract. It does
not say that every isolated permission denial realizes a capital circuit. -/
theorem the_existing_no_capital_contract_iff_its_minimal_permission_support :
    Global.NoCapital law ↔ NoAsymmetry law :=
  ⟨fun clear => (no_asymmetry_iff_no_private_phase law).2 clear.private_phase,
    no_asymmetry_generates_the_complete_no_capital_contract law⟩

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem every_private_phase_refutes_the_exact_permission_support
    (raw : RawCurrent Party Good Technology Instrument) (port : Port) (person : Party)
    (phase : PrivatePhase law raw port person) : ¬ NoAsymmetry law := by
  intro shared
  exact (no_asymmetry_iff_no_private_phase law).1 shared raw port person phase

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem fully_open_is_a_sufficient_special_case
    (opened : ∀ technology port person, law.allowed technology port person = true) : NoAsymmetry law :=
  fun _ port person _ => opened _ port person

omit [DecidableEq Port] in
/-- Uniform closure is another allowed interpretation of the same data;
absence of a private phase does not assert that needs can be paid. -/
theorem uniformly_closed_also_has_the_same_no_capital_contract :
    Global.NoCapital {law with allowed := fun _ _ _ => false} :=
  no_asymmetry_generates_the_complete_no_capital_contract _ (by
    intro raw port person impossible
    exact Bool.noConfusion impossible)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem a_uniformly_closed_inhabited_port_is_not_fully_open
    (technology : Technology) (port : Port) (person : Party) :
    ¬ ∀ technology port person, ({law with allowed := fun _ _ _ => false} : RawLaw Party Good Port Technology Instrument).allowed
      technology port person = true := by
  intro opened
  exact Bool.noConfusion (opened technology port person)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support
