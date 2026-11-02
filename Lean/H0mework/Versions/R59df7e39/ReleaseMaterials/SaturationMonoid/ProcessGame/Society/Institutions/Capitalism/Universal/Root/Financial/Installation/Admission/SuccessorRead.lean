import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Living

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

theorem successor_support_eq_of_native
    {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary} {source : SourceNativeSource N V}
    {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (write : V.NativeWriteAt current)
    (structural : source.toRootSource.actual.compile occurrence = .nativeWrite write)
    (target : source.toRootSource.actual.OccurrenceAt (V.nativeTarget write))
    (evolution : LedgerWriteEvolutionAt N ⟨source.toRootSource.account.supportOf occurrence⟩
      ⟨source.toRootSource.account.supportOf target⟩)
    (image_eq : generated = .nativeWrite write structural target evolution)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    source.toRootSource.account.supportOf successor.targetOccurrence = source.toRootSource.account.supportOf target := by
  cases image_eq
  rfl

theorem joint_successor_destination_heq
    {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary} {source : SourceNativeSource N V}
    {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (write : V.NativeWriteAt current)
    (structural : source.toRootSource.actual.compile occurrence = .nativeWrite write)
    (target : source.toRootSource.actual.OccurrenceAt (V.nativeTarget write))
    (evolution : LedgerWriteEvolutionAt N ⟨source.toRootSource.account.supportOf occurrence⟩
      ⟨source.toRootSource.account.supportOf target⟩)
    (image_eq : generated = .nativeWrite write structural target evolution)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    {law : DebtActivationLaw} {first last : law.DebtState}
    (owner : OpenResponsibilityAt N (source.toRootSource.account.supportOf occurrence))
    (paid : law.StepAt first last) :
    HEq (jointStepLedgerEvolution successor.ledgerEvolution owner paid).destination
      (jointStepLedgerEvolution evolution owner paid).destination := by
  cases image_eq
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
