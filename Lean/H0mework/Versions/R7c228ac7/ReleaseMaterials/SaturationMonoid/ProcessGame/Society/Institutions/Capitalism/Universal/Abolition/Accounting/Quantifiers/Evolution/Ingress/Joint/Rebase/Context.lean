import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Installation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Context

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

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

def basis : Abolition.Root.Registered.Macro.Inquiry.Basis (NewN seed grossClaim) where
  entry := fun support => oldEntry (state? := support.2) ((Background.family seed).entry support.1)
  disposition := fun support kind => match kind with
    | .supportSettlement => (Background.family seed).disposition support.1 .supportSettlement
    | .transfer => .inl ((Background.family seed).disposition support.1 .transfer)
    | .lawSurfaceExtension => .inl ((Background.family seed).disposition support.1 .lawSurfaceExtension)

def current : Factory.Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) (NewN seed grossClaim) where
  V := V seed grossClaim
  root := root seed grossClaim
  visit := nextVisit seed grossClaim
  row := nextRow seed grossClaim
  authority := nextAuthority seed grossClaim
  basis := basis seed grossClaim
  raw := (Current.initial seed grossClaim).raw
  rawFace := rawFace seed grossClaim (nextVisit seed grossClaim)
  raw_heq := HEq.rfl
  actualLaw := seed.current.actualLaw
  members := seed.current.members
  contextFace := contextFace seed grossClaim (nextVisit seed grossClaim)
  context_heq := HEq.rfl

theorem the_returned_current_is_the_actual_whole_root_next :
    (RootInquiryProcessNode.answered (presentation seed grossClaim) PUnit.unit).erase =
      Factory.Context.erase (current seed grossClaim) :=
  the_actual_process_resumes_at_the_same_joint_root seed grossClaim

theorem every_live_source_read_uses_the_original_material_cursor :
    Factory.Context.readRaw (current seed grossClaim) = currentRaw seed :=
  Factory.Context.readRaw_eq _

theorem the_current_reads_the_same_joint_productive_pointer :
    (Factory.Context.support (current seed grossClaim)).2 =
      some (.current (Current.initial seed grossClaim)) :=
  congrArg Prod.snd (the_actual_next_is_the_common_current_with_all_original_finance_rows seed grossClaim)

theorem all_financial_rows_read_the_actual_background_account :
    (Background.shape seed).AllRead seed.input seed.depth seed.count (Background.nativeAccount seed)
      (Factory.Context.support (current seed grossClaim)).1 := by
  have same := congrArg Prod.fst
    (the_actual_next_is_the_common_current_with_all_original_finance_rows seed grossClaim)
  exact same.symm ▸ Background.all_original_rows_of_the_family_read_one_current_account seed

theorem historical_productive_cache_is_not_the_live_row
    (historical : (Productive.oldLaw seed).DebtState) :
    (Factory.Context.support (current seed grossClaim)).2 ≠ some (.legacy historical) := by
  intro same
  have actual := the_current_reads_the_same_joint_productive_pointer seed grossClaim
  have impossible := Option.some.inj (actual.symm.trans same)
  cases impossible

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
