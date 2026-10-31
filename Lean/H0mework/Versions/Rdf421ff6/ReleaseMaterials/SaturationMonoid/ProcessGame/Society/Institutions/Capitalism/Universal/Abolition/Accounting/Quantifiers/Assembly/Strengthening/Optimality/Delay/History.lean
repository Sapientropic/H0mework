import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Flow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay

open Source.Program Innovation
noncomputable section
attribute [local irreducible] Joint.actualLaw

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

def income : Joint.Current seed claim → List (RawEvent Party Good Port Technology Instrument) →
    Profit.Vector (Party := Party) (Good := Good)
  | _,[] => 0
  | current,proposal :: rest => incomeAt seed claim current proposal +
      income (Joint.Boundary.next seed claim current proposal) rest

def retained : Joint.Current seed claim → List (RawEvent Party Good Port Technology Instrument) →
    Profit.Vector (Party := Party) (Good := Good)
  | _,[] => 0
  | current,proposal :: rest => retainedAt seed claim current proposal +
      retained (Joint.Boundary.next seed claim current proposal) rest

def executedWords : Joint.Current seed claim → List (RawEvent Party Good Port Technology Instrument) →
    List (RawEvent Party Good Port Technology Instrument)
  | _,[] => []
  | current,proposal :: rest => Joint.Boundary.executed seed claim current proposal ::
      executedWords (Joint.Boundary.next seed claim current proposal) rest

theorem every_program_prefix_is_charged_against_its_original_liability
    (current : Joint.Current seed claim) (proposals : List (RawEvent Party Good Port Technology Instrument)) :
    income seed claim current proposals +
        Coalition.Restitution.liability seed claim (Joint.Boundary.afterInputs seed claim current proposals) =
      retained seed claim current proposals + Coalition.Restitution.liability seed claim current := by
  induction proposals generalizing current with
  | nil => simp only [income,retained,Joint.Boundary.afterInputs,zero_add]
  | cons proposal rest inherited =>
      have first := the_actual_prefix_keeps_every_material_and_financial_effect seed claim current proposal
      have later := inherited (Joint.Boundary.next seed claim current proposal)
      change incomeAt seed claim current proposal + income seed claim (Joint.Boundary.next seed claim current proposal) rest +
        Coalition.Restitution.liability seed claim
          (Joint.Boundary.afterInputs seed claim (Joint.Boundary.next seed claim current proposal) rest) =
        retainedAt seed claim current proposal + retained seed claim (Joint.Boundary.next seed claim current proposal) rest +
          Coalition.Restitution.liability seed claim current
      calc
        _ = incomeAt seed claim current proposal +
            (income seed claim (Joint.Boundary.next seed claim current proposal) rest +
              Coalition.Restitution.liability seed claim
                (Joint.Boundary.afterInputs seed claim (Joint.Boundary.next seed claim current proposal) rest)) := by abel
        _ = incomeAt seed claim current proposal +
            (retained seed claim (Joint.Boundary.next seed claim current proposal) rest +
              Coalition.Restitution.liability seed claim (Joint.Boundary.next seed claim current proposal)) := by rw [later]
        _ = retained seed claim (Joint.Boundary.next seed claim current proposal) rest +
            (incomeAt seed claim current proposal +
              Coalition.Restitution.liability seed claim (Joint.Boundary.next seed claim current proposal)) := by abel
        _ = _ := by rw [first]; abel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay
