import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.NoControl

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global

open Source.Program Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- This is uniform in states and complete words, rather than a census of
the first discovered circuit. Historical evidence is never deleted. -/
structure NoCapital (law : RawLaw Party Good Port Technology Instrument) : Prop where
  private_phase : ∀ raw port person, ¬ PrivatePhase law raw port person
  kernel : ∀ raw word, ¬ Nonempty (Kernel.CapitalRelationKernel law raw word)
  proper : ∀ raw word, ¬ Nonempty (Kernel.AssetAuthority.ProperCapitalKernel law raw word)
  surplus : ∀ raw word, ¬ Nonempty (Kernel.ActualSurplus.Witness law raw word)
  fresh_history : ∀ (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument),
    input.law = law → ∀ port item, ¬ History.FreshControl input port item

omit [DecidableEq Port] in
theorem noCapitalOfOpen (law : RawLaw Party Good Port Technology Instrument)
    (opened : ∀ technology port person, law.allowed technology port person = true) : NoCapital law where
  private_phase := fun raw port person phase => by
    have denied := phase.2
    rw [opened] at denied
    cases denied
  kernel := Functions.open_permissions_have_no_capital_kernel law opened
  proper := fun raw word ⟨capital⟩ =>
    Functions.open_permissions_have_no_capital_kernel law opened raw word ⟨capital.dependency⟩
  surplus := fun raw word ⟨capital⟩ =>
    Functions.open_permissions_have_no_capital_kernel law opened raw word ⟨capital.dependency⟩
  fresh_history := by
    intro input same port item fresh
    obtain ⟨_,_,person,_,phase⟩ := fresh
    have denied := phase.2
    rw [same,opened] at denied
    cases denied

omit [DecidableEq Port] in
/-- A proposed source law has no exclusive-control authority when compiled
through the same public interpretation. This does not identify two epochs. -/
theorem publicLawNoCapital (sourceLaw : RawLaw Party Good Port Technology Instrument) :
    NoCapital (PublicFunction.physicalLaw sourceLaw) :=
  noCapitalOfOpen _ (fun _ _ _ => rfl)

theorem old_historical_ports_cannot_mint_current_control
    {law : RawLaw Party Good Port Technology Instrument} (clear : NoCapital law)
    (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
    (endpoint : History.Visit input) (capital : History.Capital input endpoint)
    (raw : RawCurrent Party Good Technology Instrument) (person : Party) :
    ¬ PrivatePhase law raw capital.access.port person := clear.private_phase _ _ _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global
