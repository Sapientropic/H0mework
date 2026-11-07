import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Comparison
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Original

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay

open Source.Program Innovation
noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

/-- A challenger chooses only a proposal from the observed prefix and current.
The source alone computes the executed prefix and next; there is no target parameter. -/
abbrev Strategy := List (RawEvent Party Good Port Technology Instrument) → Joint.Current seed claim →
  RawEvent Party Good Port Technology Instrument

def observe (policy : Strategy seed claim) (opening : Joint.Current seed claim) : Nat →
    Joint.Current seed claim × List (RawEvent Party Good Port Technology Instrument)
  | 0 => (opening,[])
  | ticks + 1 =>
      let prior := observe policy opening ticks
      let proposal := policy prior.2 prior.1
      (Joint.Boundary.next seed claim prior.1 proposal,prior.2 ++ [proposal])

private theorem after_append (current : Joint.Current seed claim)
    (left right : List (RawEvent Party Good Port Technology Instrument)) :
    Joint.Boundary.afterInputs seed claim current (left ++ right) =
      Joint.Boundary.afterInputs seed claim (Joint.Boundary.afterInputs seed claim current left) right := by
  induction left generalizing current with
  | nil => rfl
  | cons input rest inherited => exact inherited _

theorem adaptive_choices_cannot_replace_the_source_generated_current
    (policy : Strategy seed claim) (opening : Joint.Current seed claim) (ticks : Nat) :
    (observe seed claim policy opening ticks).1 =
      Joint.Boundary.afterInputs seed claim opening (observe seed claim policy opening ticks).2 := by
  induction ticks with
  | zero => rfl
  | succ ticks inherited =>
      change Joint.Boundary.next seed claim (observe seed claim policy opening ticks).1 _ =
        Joint.Boundary.afterInputs seed claim opening ((observe seed claim policy opening ticks).2 ++ [_])
      rw [after_append]
      change Joint.Boundary.next seed claim (observe seed claim policy opening ticks).1 _ =
        Joint.Boundary.next seed claim (Joint.Boundary.afterInputs seed claim opening (observe seed claim policy opening ticks).2) _
      rw [← inherited]

theorem every_adaptive_pair_preserves_the_entire_coalition_comparison
    (opening : Joint.Current seed claim) (delayed baseline : Strategy seed claim)
    (delayTicks baseTicks : Nat) (members : Party → Bool) (good : Good) :
    Coalition.read members good (income seed claim opening (observe seed claim delayed opening delayTicks).2 +
        Coalition.Restitution.liability seed claim (observe seed claim delayed opening delayTicks).1) -
      Coalition.read members good (income seed claim opening (observe seed claim baseline opening baseTicks).2 +
        Coalition.Restitution.liability seed claim (observe seed claim baseline opening baseTicks).1) =
      Coalition.read members good (retained seed claim opening (observe seed claim delayed opening delayTicks).2) -
        Coalition.read members good (retained seed claim opening (observe seed claim baseline opening baseTicks).2) := by
  rw [adaptive_choices_cannot_replace_the_source_generated_current,
    adaptive_choices_cannot_replace_the_source_generated_current]
  exact every_coalition_retains_all_real_contributions_and_other_positions seed claim opening _ _ members good

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay
