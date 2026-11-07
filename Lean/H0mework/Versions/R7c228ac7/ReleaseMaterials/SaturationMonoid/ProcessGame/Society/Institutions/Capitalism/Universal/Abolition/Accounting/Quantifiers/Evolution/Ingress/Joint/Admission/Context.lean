import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def basis : Abolition.Root.Registered.Macro.Inquiry.Basis (N seed grossClaim) where
  entry := fun support => oldEntry (state? := support.2) ((Rebase.basis seed grossClaim).entry support.1)
  disposition := fun support kind => match kind with
    | .supportSettlement => (Rebase.basis seed grossClaim).disposition support.1 .supportSettlement
    | .transfer => .inl ((Rebase.basis seed grossClaim).disposition support.1 .transfer)
    | .lawSurfaceExtension => .inl ((Rebase.basis seed grossClaim).disposition support.1 .lawSurfaceExtension)

def rawFace : SourceNativeRootSemanticFaceAt (root seed grossClaim) (nextVisit seed grossClaim) :=
  { projection := .component (.inherited (.component Rebase.Projection.raw))
    active := PUnit.unit,classifier_eq := rfl }

def contextFace : SourceNativeRootSemanticFaceAt (root seed grossClaim) (nextVisit seed grossClaim) :=
  { projection := .component (.inherited (.component Rebase.Projection.context))
    active := PUnit.unit,classifier_eq := rfl }

def current : Factory.Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) (N seed grossClaim) where
  V := V seed grossClaim
  root := root seed grossClaim
  visit := nextVisit seed grossClaim
  row := nextRow seed grossClaim
  authority := nextAuthority seed grossClaim
  basis := basis seed grossClaim
  raw := (declaredShared seed grossClaim).raw
  rawFace := rawFace seed grossClaim
  raw_heq := HEq.rfl
  actualLaw := seed.current.actualLaw
  members := seed.current.members
  contextFace := contextFace seed grossClaim
  context_heq := HEq.rfl

theorem the_returned_current_is_the_actual_whole_root_next :
    (RootInquiryProcessNode.answered (presentation seed grossClaim) PUnit.unit).erase =
      Factory.Context.erase (current seed grossClaim) :=
  the_actual_process_resumes_at_the_same_joint_root seed grossClaim

theorem both_original_material_rows_point_to_the_same_declared_current :
    (Factory.Context.support (current seed grossClaim)).1.2 = some (.current (declaredShared seed grossClaim)) ∧
      (Factory.Context.support (current seed grossClaim)).2 = some (declaredShared seed grossClaim) := by
  rw [show Factory.Context.support (current seed grossClaim) = support seed grossClaim true from
    the_actual_next_has_one_shared_declared_current seed grossClaim]
  exact the_first_write_updates_both_old_and_new_rows_to_the_same_shared_value seed grossClaim

theorem the_admission_keeps_the_same_live_material_cursor :
    Factory.Context.readRaw (current seed grossClaim) = currentRaw seed :=
  Factory.Context.readRaw_eq _

theorem every_original_financial_row_keeps_the_same_actual_account :
    (Background.shape seed).AllRead seed.input seed.depth seed.count (Background.nativeAccount seed)
      (Factory.Context.support (current seed grossClaim)).1.1 := by
  have same := congrArg (fun pair => pair.1.1)
    (the_actual_next_has_one_shared_declared_current seed grossClaim)
  have old := congrArg Prod.fst
    (the_old_side_of_the_declaration_already_uses_the_same_shared_pointer seed grossClaim)
  exact (same.trans old).symm ▸ Background.all_original_rows_of_the_family_read_one_current_account seed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission
