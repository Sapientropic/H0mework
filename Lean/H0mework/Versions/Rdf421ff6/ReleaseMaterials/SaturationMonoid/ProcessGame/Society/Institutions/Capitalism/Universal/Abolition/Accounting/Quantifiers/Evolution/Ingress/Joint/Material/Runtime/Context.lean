import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def current : Factory.Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) (Admission.N seed claim) where
  V := V seed claim
  root := Inquiry.root seed claim
  visit := nextVisit seed claim
  row := nextRow seed claim
  authority := nextAuthority seed claim
  basis := Inquiry.basis seed claim
  raw := (sharedAt seed claim (nextVisit seed claim).current).raw
  rawFace := { projection := .component Inquiry.Projection.raw,active := PUnit.unit,classifier_eq := rfl }
  raw_heq := HEq.rfl
  actualLaw := actualLaw seed
  members := seed.current.members
  contextFace := { projection := .component Inquiry.Projection.context,active := PUnit.unit,classifier_eq := rfl }
  context_heq := HEq.rfl

theorem the_actual_whole_root_returns_this_current :
    (RootInquiryProcessNode.answered (presentation seed claim) PUnit.unit).erase = Factory.Context.erase (current seed claim) :=
  the_actual_process_resumes_at_its_joint_material_root seed claim

theorem the_current_coordinate_is_the_source_generated_body_successor :
    (nextVisit seed claim).current = next seed claim (initial seed) :=
  Abolition.Accounting.Root.Compiler.successor_current (flow seed claim) (initial seed)

theorem the_actual_next_uses_the_one_source_computed_shared_state :
    sharedAt seed claim (nextVisit seed claim).current = Planning.actualNext seed claim (Material.shared seed claim) :=
  (congrArg (sharedAt seed claim) (the_current_coordinate_is_the_source_generated_body_successor seed claim)).trans
    (the_first_material_next_is_the_source_selected_actual_next seed claim)

theorem the_actual_next_material_face_is_the_real_physical_next :
    Factory.Context.readRaw (current seed claim) = (Execution.Selected.result seed claim).next.raw :=
  (Factory.Context.readRaw_eq (current seed claim)).trans
    ((congrArg (fun shared : Current seed claim => shared.raw)
      (the_actual_next_uses_the_one_source_computed_shared_state seed claim)).trans
        (Execution.Selected.physical_and_financial_execution_have_the_same_material_next seed claim).symm)

theorem primitive_resources_force_both_actual_root_rows_to_be_paid
    (enough : Planning.Enough seed claim (Material.shared seed claim)) :
    Current.productivePaid seed claim (sharedAt seed claim (nextVisit seed claim).current) ∧
      Current.grossPaid seed claim (sharedAt seed claim (nextVisit seed claim).current) := by
  rw [the_actual_next_uses_the_one_source_computed_shared_state]
  have actual := Planning.sufficient_source_resources_force_the_actual_shared_payment
    seed claim (Material.shared seed claim) enough
  exact ⟨actual.productivePaid,actual.grossPaid⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
