import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Context
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Facts
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.NoRetake

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

def boundaryFace : SourceNativeRootSemanticFaceAt (Inquiry.root seed claim) (nextVisit seed claim) :=
  { projection := .component Inquiry.Projection.boundary,active := PUnit.unit,classifier_eq := rfl }

theorem the_actual_boundary_keeps_the_exact_executed_source_word :
    (boundaryFace seed claim).rootRead.executableWord = Material.word seed claim :=
  (Boundary.reply seed claim (Material.shared seed claim)
    (Planning.chosen seed claim (Material.shared seed claim))).source_executed

theorem the_actual_boundary_and_root_read_the_same_after :
    Boundary.next seed claim (Material.shared seed claim) (Planning.chosen seed claim (Material.shared seed claim)) =
      sharedAt seed claim (nextVisit seed claim).current :=
  (Boundary.the_actual_source_selected_next_is_this_same_shared_current seed claim (Material.shared seed claim)).trans
    (the_actual_next_uses_the_one_source_computed_shared_state seed claim).symm

theorem the_actual_root_reply_has_its_source_authority_disposition :
    Boundary.AuthorityDispositionAt seed claim (Material.shared seed claim)
      (Planning.chosen seed claim (Material.shared seed claim)) (boundaryFace seed claim).rootRead.classification :=
  Boundary.the_actual_reply_keeps_the_requested_authority_disposition seed claim (Material.shared seed claim)
    (Planning.chosen seed claim (Material.shared seed claim))

theorem a_refused_actual_root_request_cannot_buy_an_old_row_permit
    (refusal : Boundary.RefusalAt seed claim (Material.shared seed claim)
      (Planning.chosen seed claim (Material.shared seed claim))
      (Boundary.verdict seed claim (Material.shared seed claim) (Planning.chosen seed claim (Material.shared seed claim)))) :
    ¬ Boundary.Permit seed claim (Material.shared seed claim) (Planning.chosen seed claim (Material.shared seed claim)) :=
  Boundary.actual_refusal_excludes_a_joint_old_row_permit seed claim (Material.shared seed claim)
    (Planning.chosen seed claim (Material.shared seed claim)) refusal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
