import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Ledger
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.NativeEvolution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Casts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)

theorem the_first_write_is_the_same_joint_native_write :
    HEq (firstWrite prior origin registered).destination
      (jointStepLedgerEvolution
        (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start prior origin)
        (Accounting.owner input depth count prior origin) (firstStep origin registered).step).destination :=
  Financial.Installation.Admission.joint_destination_cast_heq
    (the_complete_old_support_is_the_same_source_target prior origin registered).symm
    (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start prior origin)
    (Accounting.owner input depth count prior origin) (firstStep origin registered).step

theorem joint_destination_of_same_actual_write
    {base : WorldRelationNetwork} {debtLaw : DebtActivationLaw}
    {leftBefore rightBefore left right : base.Support} {source target : debtLaw.DebtState}
    (leftWrite : LedgerWriteEvolutionAt base ⟨leftBefore⟩ ⟨left⟩)
    (rightWrite : LedgerWriteEvolutionAt base ⟨rightBefore⟩ ⟨right⟩)
    (sameSource : leftBefore = rightBefore) (sameSupport : left = right)
    (sameDestination : HEq leftWrite.destination rightWrite.destination)
    (leftEntry : OpenResponsibilityAt base leftBefore) (rightEntry : OpenResponsibilityAt base rightBefore)
    (step : debtLaw.StepAt source target) :
    HEq (jointStepLedgerEvolution leftWrite leftEntry step).destination
      (jointStepLedgerEvolution rightWrite rightEntry step).destination := by
  cases sameSource
  cases sameSupport
  rcases leftWrite with ⟨leftDestination, leftOrigin⟩
  rcases rightWrite with ⟨rightDestination, rightOrigin⟩
  have same : leftDestination = rightDestination := eq_of_heq sameDestination
  cases same
  rfl

#print axioms the_first_write_is_the_same_joint_native_write

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born
