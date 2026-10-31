import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.FullAccount
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay

open Source.Program Innovation
noncomputable section
attribute [local irreducible] Joint.actualLaw Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

def incomeAt (current : Joint.Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument) :=
  Coalition.Restitution.actualIncome seed claim current (Joint.Boundary.executed seed claim current proposal)

def retainedAt (current : Joint.Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument) :=
  Coalition.Restitution.retainedActualIncome seed claim current (Joint.Boundary.executed seed claim current proposal)

/-- Full-account comparison of one actual source prefix, including its
remaining original obligation. Other flows are retained without being certified legitimate. -/
theorem the_actual_prefix_keeps_every_material_and_financial_effect
    (current : Joint.Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument) :
    incomeAt seed claim current proposal +
        Coalition.Restitution.liability seed claim (Joint.Boundary.next seed claim current proposal) =
      retainedAt seed claim current proposal + Coalition.Restitution.liability seed claim current := by
  let word := Joint.Boundary.executed seed claim current proposal
  have conserved := Coalition.Restitution.actual_return_and_next_liability_preserve_the_whole_original_position
    seed claim current word
  have retained := Coalition.Restitution.retained_actual_income_keeps_the_actual_full_account seed claim current word
  change Coalition.Restitution.actualIncome seed claim current word +
      Coalition.Restitution.liability seed claim (Joint.Current.advance seed claim current word) = _
  calc
    _ = (Coalition.Restitution.actualIncome seed claim current word - Coalition.Restitution.returned seed claim current word) -
        Coalition.Restitution.position (Entitlement.Duty.scope (Joint.window seed)) current.gross +
        (Coalition.Restitution.position (Entitlement.Duty.scope (Joint.window seed)) current.gross +
          Coalition.Restitution.returned seed claim current word +
          Coalition.Restitution.liability seed claim (Joint.Current.advance seed claim current word)) := by abel
    _ = (Coalition.Restitution.actualIncome seed claim current word - Coalition.Restitution.returned seed claim current word) -
        Coalition.Restitution.position (Entitlement.Duty.scope (Joint.window seed)) current.gross := by rw [conserved,add_zero]
    _ = _ := by
      rw [← retained]
      simp only [retainedAt,Coalition.Restitution.liability,word,sub_eq_add_neg]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay
