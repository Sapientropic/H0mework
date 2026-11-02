import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

abbrev entryCard := @Financial.Installation.Runtime.entryCard
abbrev erasedEntryCard := Financial.Installation.Runtime.erasedEntryCard
abbrev erasedProjectionCard := Financial.Installation.Runtime.erasedProjectionCard

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}

theorem native_entry_card
    (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (current : frame.V.Current) :
    entryCard frame.root.toAuthoritativeRoot.toLedgerRoot current =
      entryCard frame.root.toAuthoritativeRoot.toLedgerRoot (frame.next current) := by
  change Nat.card (OpenResponsibilityAt frame.N (frame.sourceSupport current)) =
    Nat.card (OpenResponsibilityAt frame.N (frame.sourceSupport (frame.next current)))
  have sourceFinite : Finite (OpenResponsibilityAt frame.N (frame.sourceSupport current)) := frame.entries_finite current
  have targetFinite : Finite (OpenResponsibilityAt frame.N (frame.sourceSupport (frame.next current))) := frame.entries_finite (frame.next current)
  exact Nat.le_antisymm
    (Nat.card_le_card_of_injective _
      (Financial.Installation.keys_imply_destination_injective (frame.wholeEvolution current)
        (frame.whole_keys current) frame.open_fibres))
    (Nat.card_le_card_of_injective _
      (Financial.Installation.keys_imply_origin_injective (frame.wholeEvolution current)
        (frame.whole_keys current) frame.open_fibres))

theorem admitted_entry_card
    (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    {origin : frame.V.Current}
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)
    (current : Admission.Current frame registered) :
    entryCard (Admission.livingRoot frame registered).toAuthoritativeRoot.toLedgerRoot current =
      entryCard frame.root.toAuthoritativeRoot.toLedgerRoot current.1 + 1 := by
  have sourceFinite : Finite (OpenResponsibilityAt frame.N (frame.sourceSupport current.1)) := frame.entries_finite current.1
  let rows := activeInventoryPresentation (law := registered.law)
    (Admission.state frame registered current.2)
    (ConstructivePresentation.refl (OpenResponsibilityAt frame.N (frame.sourceSupport current.1)))
  exact (Nat.card_congr (show Option (OpenResponsibilityAt frame.N (frame.sourceSupport current.1)) ≃
      OpenResponsibilityAt (Admission.N frame registered) (Admission.supportAt frame registered current) from
      ⟨rows.forward, rows.backward, rows.backward_forward, rows.forward_backward⟩)).symm.trans Finite.card_option

private def accountingProjectionEquiv : Accounting.Projection ≃ Fin 6 where
  toFun := fun projection => match projection with
    | .ledger => 0 | .account => 1 | .pending => 2 | .physical => 3 | .sourceInput => 4 | .sourceExecution => 5
  invFun := fun index => Fin.cases .ledger (Fin.cases .account (Fin.cases .pending
    (Fin.cases .physical (Fin.cases .sourceInput (fun _ => .sourceExecution))))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def queryProjectionEquiv : Inquiry.Projection ≃ Fin 4 where
  toFun := fun projection => match projection with
    | .query => 0 | .answer => 1 | .compilation => 2 | .consumer => 3
  invFun := fun index => Fin.cases .query (Fin.cases .answer (Fin.cases .compilation (fun _ => .consumer))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def ingressProjectionEquiv : Ingress.Projection ≃ Fin 3 where
  toFun := fun projection => match projection with
    | .input => 0 | .sourceSelection => 1 | .compilation => 2
  invFun := fun index => Fin.cases .input (Fin.cases .sourceSelection (fun _ => .compilation)) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

theorem accounting_projection_finite : Finite Accounting.Projection := Finite.of_equiv (Fin 6) accountingProjectionEquiv.symm
theorem inquiry_projection_finite : Finite Inquiry.Projection := Finite.of_equiv (Fin 4) queryProjectionEquiv.symm
theorem ingress_projection_finite : Finite Ingress.Projection := Finite.of_equiv (Fin 3) ingressProjectionEquiv.symm

theorem accounting_projection_card : Nat.card Accounting.Projection = 6 :=
  (Nat.card_congr accountingProjectionEquiv).trans (Nat.card_fin 6)
theorem inquiry_projection_card : Nat.card Inquiry.Projection = 4 :=
  (Nat.card_congr queryProjectionEquiv).trans (Nat.card_fin 4)
theorem ingress_projection_card : Nat.card Ingress.Projection = 3 :=
  (Nat.card_congr ingressProjectionEquiv).trans (Nat.card_fin 3)

def cofaceEquiv (A B : Type) : SourceNativeProjectionCoface A B ≃ A ⊕ B where
  toFun := fun projection => match projection with
    | .inherited value => .inl value
    | .component value => .inr value
  invFun := fun projection => match projection with
    | .inl value => .inherited value
    | .inr value => .component value
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun projection => by cases projection <;> rfl

private def rawProjectionEquiv : Raw.Projection ≃ Fin 9 where
  toFun := fun projection => match projection with
    | .internalQuery => 0 | .internalAnswer => 1 | .internalCompilation => 2 | .internalConsumer => 3
    | .rawQuery => 4 | .rawReport => 5 | .rawCompilation => 6 | .rawConsumer => 7 | .snapshot => 8
  invFun := fun index => Fin.cases .internalQuery (Fin.cases .internalAnswer
    (Fin.cases .internalCompilation (Fin.cases .internalConsumer (Fin.cases .rawQuery
      (Fin.cases .rawReport (Fin.cases .rawCompilation (Fin.cases .rawConsumer (fun _ => .snapshot)))))))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def reentryProjectionEquiv : Reentry.Projection ≃ Fin 5 where
  toFun := fun projection => match projection with
    | .ledger => 0 | .account => 1 | .physical => 2 | .sourceInput => 3 | .sourceResult => 4
  invFun := fun index => Fin.cases .ledger (Fin.cases .account (Fin.cases .physical
    (Fin.cases .sourceInput (fun _ => .sourceResult)))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def admissionProjectionEquiv : Admission.OwnProjection ≃ Fin 3 where
  toFun := fun projection => match projection with
    | .ledger => 0 | .account => 1 | .admission => 2
  invFun := fun index => Fin.cases .ledger (Fin.cases .account (fun _ => .admission)) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

theorem raw_projection_finite : Finite Raw.Projection := Finite.of_equiv (Fin 9) rawProjectionEquiv.symm
theorem reentry_projection_finite : Finite Reentry.Projection := Finite.of_equiv (Fin 5) reentryProjectionEquiv.symm
theorem admission_projection_finite : Finite Admission.OwnProjection := Finite.of_equiv (Fin 3) admissionProjectionEquiv.symm

theorem raw_projection_card : Nat.card Raw.Projection = 9 := (Nat.card_congr rawProjectionEquiv).trans (Nat.card_fin 9)
theorem reentry_projection_card : Nat.card Reentry.Projection = 5 := (Nat.card_congr reentryProjectionEquiv).trans (Nat.card_fin 5)
theorem admission_projection_card : Nat.card Admission.OwnProjection = 3 := (Nat.card_congr admissionProjectionEquiv).trans (Nat.card_fin 3)

theorem base_projection_card (reader : Raw.Reader input depth count) :
    Nat.card (Inquiry.basePackage (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader).frame.root.toAuthoritativeRoot.source.projectionLaw.Projection = 15 := by
  have first : Finite Accounting.Projection := accounting_projection_finite
  have second : Finite Raw.Projection := raw_projection_finite
  change Nat.card (SourceNativeProjectionCoface Accounting.Projection Raw.Projection) = 15
  rw [Nat.card_congr (cofaceEquiv _ _), Nat.card_sum, accounting_projection_card, raw_projection_card]

theorem original_frames_projection_mod (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat) :
    Nat.card (Financial.Installation.Runtime.frames input depth count).native.root.toAuthoritativeRoot.source.projectionLaw.Projection % 4 = 2 := by
  induction count with
  | zero =>
      change Nat.card Financial.Installation.AccountSource.Projection % 4 = 2
      rw [Financial.Installation.Runtime.base_projection_card]
  | succ count inherited =>
      let prior := Financial.Installation.Runtime.frames input depth count
      have finite : Finite prior.native.root.toAuthoritativeRoot.source.projectionLaw.Projection := prior.projectionFinite
      change Nat.card (prior.next input).native.root.toAuthoritativeRoot.source.projectionLaw.Projection % 4 = 2
      unfold Financial.Installation.Runtime.Frame.next
      split
      · rename_i registered selected
        change Nat.card (Financial.Installation.Admission.nativeFrame input prior.native registered).root.toAuthoritativeRoot.source.projectionLaw.Projection % 4 = 2
        rw [Financial.Installation.Runtime.child_projection_card]
        change Nat.card prior.native.root.toAuthoritativeRoot.source.projectionLaw.Projection % 4 = 2 at inherited
        omega
      · exact inherited

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
