import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Failure
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers.Crossing

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Consumers

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (primitiveScript)
open Civil.Persistence
open Civil.Persistence.Consumers.Crossing
open Conflict.Consumers.Evolving (front)
open Reparation.Actual (publishAfter run)

noncomputable section

def TheFirstSixAreWritten : Prop :=
  let past := primitiveScript front
  let written := publishAfter (run opening id past) [attempted]
  ∃ attack : OriginalAttack opening id (past ++ [attempted]),
    (firstCrossing []).originalAttack past rfl = some attack ∧ attack.val.quantity = 6 ∧
    ∃ balance, ∃ row, written.next.read row = .inr (attack.val, balance)

theorem the_first_six_are_written_on_the_original_refusal : TheFirstSixAreWritten := by
  obtain ⟨attack, original, amount, _⟩ := the_first_failure_is_the_original_six_unit_reparation_opening
  exact ⟨attack, original, amount, an_original_breakthrough_is_written_at_its_first_failed_prefix attack⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Consumers
