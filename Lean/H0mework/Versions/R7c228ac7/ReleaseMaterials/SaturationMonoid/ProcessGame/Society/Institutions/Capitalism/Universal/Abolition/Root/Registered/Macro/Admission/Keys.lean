import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation (KeepsKeys)

noncomputable section

private theorem joint_keeps_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after : N.Support} {source target : law.DebtState}
    (base : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩)
    (owner : OpenResponsibilityAt N before) (paid : law.StepAt source target)
    (same : KeepsKeys base) : KeepsKeys (jointStepLedgerEvolution base owner paid) := by
  constructor
  · rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact congrArg Sum.inl (same.1 ⟨old, opened⟩)
    | inr debt => rcases opened with ⟨⟨sameId⟩⟩; subst debt; rfl
  · rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact congrArg Sum.inl (same.2 ⟨old, opened⟩)
    | inr debt => rcases opened with ⟨⟨sameId⟩⟩; subst debt; rfl

private theorem cast_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    (sourceSupport targetSupport : N.Support) (source before after : law.DebtState)
    (same : before = after)
    (evolution : LedgerWriteEvolutionAt (ExtendedNetwork N law)
      (activeLedger sourceSupport source) (activeLedger targetSupport before))
    (keys : KeepsKeys evolution) : KeepsKeys
      (Eq.mp (congrArg (fun state => LedgerWriteEvolutionAt (ExtendedNetwork N law)
        (activeLedger sourceSupport source) (activeLedger targetSupport state)) same) evolution) := by
  cases same
  exact keys

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

theorem whole_keys (current : Current frame registered) : KeepsKeys (wholeEvolution frame registered current) := by
  refine cast_keys _ _ _ _ _ (next_state frame registered current.2).symm (actionEvolution frame registered current) ?_
  unfold actionEvolution
  cases actionReceipt frame registered current.2 with
  | inl paid => exact joint_keeps_keys _ _ _ (frame.whole_keys current.1)
  | inr carried => exact Financial.Installation.wholeTransport_keeps_keys _ _ _ (frame.whole_keys current.1)

theorem open_fibres (support : (N frame registered).Support)
    (responsibility : (N frame registered).Responsibility) :
    Subsingleton ((N frame registered).OpenAt support responsibility) := by
  rcases support with ⟨support, active⟩
  cases responsibility with
  | inl old => exact frame.open_fibres support old
  | inr debt => cases active <;> dsimp only [N, ExtendedNetwork, extendedNetwork, DebtOpenAt] <;> infer_instance

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source frame registered) :=
  identityOnlyWorldLedgerRestructuringLaw (source frame registered)
    ((N frame registered).anchorAt (supportAt frame registered (initial frame registered))) (open_fibres frame registered)

private theorem patch_origin_injective (current : Current frame registered) :
    Function.Injective (fun entry => ((patch frame registered current).toLedgerWriteEvolution.origin entry).1) := by
  rw [patch_origin]
  exact Financial.Installation.keys_imply_origin_injective _ (whole_keys frame registered current) (open_fibres frame registered)

private theorem patch_destination_injective (current : Current frame registered) :
    Function.Injective (fun entry => ((patch frame registered current).toLedgerWriteEvolution.destination entry).1) := by
  rw [patch_destination]
  exact Financial.Installation.keys_imply_destination_injective _ (whole_keys frame registered current) (open_fibres frame registered)

def restructuringCertification {current : (V frame registered).Current}
    (occurrence : (source frame registered).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw frame registered)
      ((ledgerCompiler frame registered).compile occurrence) := by
  cases occurrence_eq_emitted frame registered occurrence
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> apply ExactLedgerRestructuringCertificationAt.ofInjective
  · exact patch_origin_injective frame registered current
  · exact patch_destination_injective frame registered current
  · exact patch_origin_injective frame registered current
  · exact patch_destination_injective frame registered current

def restructuringSource : SourceNativeRestructuringLedgerSource (N frame registered) (V frame registered) where
  source := source frame registered
  compiler := {
    ledgerCompiler := ledgerCompiler frame registered
    restructuringLaw := restructuringLaw frame registered
    certifyRestructuring := restructuringCertification frame registered }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
