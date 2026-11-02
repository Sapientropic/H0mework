import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer.Matrix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Needs

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer

open Source.Program
open Innovation

noncomputable section

def noNeedsWord : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit :=
  [⟨0,[],false,[],.revise 2 2⟩] ++ List.replicate 4 ⟨0,[],false,[],.produce 2⟩ ++
    [⟨0,[],false,[],.transfer 2 0 [(.material,8),(.result,2)]⟩,
     ⟨0,[],false,[],.transfer 2 1 [(.material,5),(.result,1)]⟩]

def missingNeedBearer (word : RawEvent Control.Scenario.Party Control.Scenario.Good Bool Nat Unit) :
    Option Control.Scenario.Party :=
  match Family.inspectActualNeeds familyClaim matrixActive Control.Scenario.openLaw word [0,1,2] with
  | .paid _ => none
  | .necessity actor _ _ | .maintenance actor _ _ => some actor

set_option maxHeartbeats 2400000 in
theorem actual_maintenance_is_paid_in_the_same_full_matrix_execution :
    missingNeedBearer matrixWord = none := by decide +kernel

set_option maxHeartbeats 2400000 in
theorem clearing_the_control_matrix_does_not_hide_an_unpaid_necessity_bearer :
    Family.State.isPaid familyClaim
        (Family.State.advance familyClaim matrixActive Control.Scenario.openLaw noNeedsWord) ∧
      missingNeedBearer noNeedsWord = some 0 := by decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer
