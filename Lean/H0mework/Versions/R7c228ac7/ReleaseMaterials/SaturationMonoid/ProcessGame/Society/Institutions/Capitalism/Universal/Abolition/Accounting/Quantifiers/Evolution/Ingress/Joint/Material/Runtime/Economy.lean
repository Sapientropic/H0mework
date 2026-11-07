import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Context
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

attribute [local irreducible] Current.advance Planning.selected

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def sharedFace : SourceNativeRootSemanticFaceAt (Inquiry.root seed claim) (nextVisit seed claim) :=
  { projection := .component Inquiry.Projection.shared,active := PUnit.unit,classifier_eq := rfl }

theorem the_actual_root_debt_rows_read_the_same_shared_face :
    (Factory.Context.support (current seed claim)).1.2 = some (.current (sharedFace seed claim).rootRead) ∧
      (Factory.Context.support (current seed claim)).2 = some (sharedFace seed claim).rootRead := ⟨rfl,rfl⟩

theorem the_actual_root_control_return_and_visible_residual_cancel :
    Coalition.Restitution.originalControl (Quantifiers.Joint.window seed) +
      Coalition.Restitution.returned seed claim (Material.shared seed claim) (Material.word seed claim) +
      Coalition.Restitution.liability seed claim (sharedFace seed claim).rootRead = 0 := by
  change _ + _ + Coalition.Restitution.liability seed claim (sharedAt seed claim (nextVisit seed claim).current) = 0
  rw [the_actual_next_uses_the_one_source_computed_shared_state]
  exact Coalition.Restitution.original_control_return_and_unpaid_liability_cancel_in_the_actual_next
    seed claim (Material.word seed claim)

theorem no_coalition_keeps_unaccounted_control_income_in_the_actual_root
    (members : Party → Bool) (good : Good) :
    Coalition.read members good
      (Coalition.Restitution.originalControl (Quantifiers.Joint.window seed) +
        Coalition.Restitution.returned seed claim (Material.shared seed claim) (Material.word seed claim) +
        Coalition.Restitution.liability seed claim (sharedFace seed claim).rootRead) = 0 := by
  rw [the_actual_root_control_return_and_visible_residual_cancel,map_zero]

theorem sufficient_resources_remove_the_actual_root_restitution_residual
    (enough : Planning.Enough seed claim (Material.shared seed claim)) :
    Coalition.Restitution.liability seed claim (sharedFace seed claim).rootRead = 0 :=
  Coalition.Restitution.a_paid_original_matrix_has_no_remaining_restitution_position seed claim _
    (primitive_resources_force_both_actual_root_rows_to_be_paid seed claim enough).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
