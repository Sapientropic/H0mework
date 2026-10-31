import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Original
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

open Source.Program Innovation

noncomputable section

attribute [local irreducible] Joint.actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

/-- Credits are accumulated from the actual item fold's G allocation.
They are not manufactured by subtracting two obligation snapshots. -/
def credits (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) : ℚ :=
  Joint.Allocation.Kernel.grossCharged
    (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response)
    (Entitlement.Duty.scope (Joint.window seed)) (Joint.Allocation.actualReadings seed)
    current.productive current.productiveDeclared current.grossDeclared key
    ⟨fun _ => 0,current.gross,current.gross_nonnegative⟩
    ((Joint.actualLaw seed).rawItems current.raw word)

theorem the_actual_allocation_conserves_every_original_cell
    (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    (Joint.Current.advance seed claim current word).gross key + credits seed claim current word key =
      current.gross key := by
  exact Joint.Allocation.Kernel.every_original_cell_has_exact_material_conservation
    (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response)
    (Entitlement.Duty.scope (Joint.window seed)) (Joint.Allocation.actualReadings seed)
    current.productive current.productiveDeclared current.grossDeclared key
    ⟨fun _ => 0,current.gross,current.gross_nonnegative⟩
    ((Joint.actualLaw seed).rawItems current.raw word)

theorem only_actual_nonnegative_allocations_discharge_gross
    (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    0 ≤ credits seed claim current word key := by
  have conserved := the_actual_allocation_conserves_every_original_cell seed claim current word key
  have bounded := Joint.Current.actual_word_never_refills_gross seed claim current word key
  linarith

def returned (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :
    Profit.Vector (Party := Party) (Good := Good) :=
  -position (Entitlement.Duty.scope (Joint.window seed)) (credits seed claim current word)

def liability (current : Joint.Current seed claim) : Profit.Vector (Party := Party) (Good := Good) :=
  -position (Entitlement.Duty.scope (Joint.window seed)) current.gross

theorem actual_return_and_next_liability_preserve_the_whole_original_position
    (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :
    position (Entitlement.Duty.scope (Joint.window seed)) current.gross + returned seed claim current word +
      liability seed claim (Joint.Current.advance seed claim current word) = 0 := by
  have same : current.gross = fun key =>
      (Joint.Current.advance seed claim current word).gross key + credits seed claim current word key :=
    funext fun key => (the_actual_allocation_conserves_every_original_cell seed claim current word key).symm
  unfold returned liability
  conv_lhs => arg 1; arg 1; rw [same,position_add]
  abel

theorem original_control_return_and_unpaid_liability_cancel_in_the_actual_next
    (word : RawEvent Party Good Port Technology Instrument) :
    let original := Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)
    originalControl (Joint.window seed) + returned seed claim original word +
      liability seed claim (Joint.Current.advance seed claim original word) = 0 := by
  dsimp only
  rw [every_source_control_leg_is_counted_once_in_the_original_matrix]
  exact actual_return_and_next_liability_preserve_the_whole_original_position seed claim
    (Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)) word

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution
