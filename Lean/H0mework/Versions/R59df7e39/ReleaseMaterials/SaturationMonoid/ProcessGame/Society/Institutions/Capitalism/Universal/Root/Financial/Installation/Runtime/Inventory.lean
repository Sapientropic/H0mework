import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Protocol
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Inventory
import Mathlib.Tactic.FinCases

/-! Registry separation reads real ledger growth and installed source
coordinates.  No fresh label is attached to an occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open DebtActivationWorld

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev entryCard {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure N V) (current : V.Current) :=
  RootGeneratedDebtActivationJointSource.Native.Request.Inventory.entryCard root current
abbrev erasedEntryCard := RootGeneratedDebtActivationJointSource.Native.Request.Inventory.erasedEntryCard

omit [DecidableEq Port] in
theorem programme_entry_lower (current : (ProgrammeSource.V input).Current) :
    2 ≤ entryCard (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toLedgerRoot current := by
  change 2 ≤ Nat.card (OpenResponsibilityAt (ProgrammeSource.N input) (ProgrammeSource.supportAt input current))
  let rows (choice : Bool) : OpenResponsibilityAt (ProgrammeSource.N input) (ProgrammeSource.supportAt input current) :=
    ProgrammeSource.sourceEntry input current (if choice then .obstruction else .inherited)
  have distinct : Function.Injective rows := by
    intro left right same
    have keys := congrArg Sigma.fst same
    cases current <;> cases left <;> cases right <;> first | rfl | cases keys
  have finiteSource : Finite (OpenResponsibilityAt (ProgrammeSource.N input) (ProgrammeSource.supportAt input current)) :=
    base_finite input current
  have lower := Nat.card_le_card_of_injective rows distinct
  simpa using lower

theorem native_entry_card (frame : NativeFrame input) (current : frame.V.Current) :
    entryCard frame.root.toAuthoritativeRoot.toLedgerRoot current =
      entryCard frame.root.toAuthoritativeRoot.toLedgerRoot
        (frame.V.nativeTarget (frame.program.emit current).write) := by
  let image := frame.program.emit current
  have sourceFinite : Finite (OpenResponsibilityAt frame.N
      (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.root.emitted current))) :=
    RootGeneratedDebtActivationJointSource.Native.Request.Inventory.source_finite frame.program current
  have targetFinite : Finite (OpenResponsibilityAt frame.N
      (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf image.targetOccurrence)) :=
    RootGeneratedDebtActivationJointSource.Native.Request.Inventory.target_finite frame.program current
  have same : Nat.card (OpenResponsibilityAt frame.N
      (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.root.emitted current))) =
      Nat.card (OpenResponsibilityAt frame.N
        (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf image.targetOccurrence)) := by
    exact Nat.le_antisymm
      (Nat.card_le_card_of_injective _ (frame.destination_injective current))
      (Nat.card_le_card_of_injective _ (frame.origin_injective current))
  exact same.trans (congrArg (fun support => Nat.card (OpenResponsibilityAt frame.N support))
    (congrArg frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      image.target_emitted))

theorem admitted_entry_card (frame : NativeFrame input) {origin : frame.V.Current}
    (registered : Registration input frame origin) (current : Admission.Current input frame registered) :
    entryCard (Admission.livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot current =
      entryCard frame.root.toAuthoritativeRoot.toLedgerRoot current.1 + 1 := by
  have sourceFinite : Finite (OpenResponsibilityAt frame.N
      (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.root.emitted current.1))) :=
    RootGeneratedDebtActivationJointSource.Native.Request.Inventory.source_finite frame.program current.1
  let presentation := activeInventoryPresentation (law := registered.law input frame)
    (Admission.state input frame registered current.2) (ConstructivePresentation.refl
      (OpenResponsibilityAt frame.N
        (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (frame.root.emitted current.1))))
  exact (Nat.card_congr (show Option (OpenResponsibilityAt frame.N
    (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (frame.root.emitted current.1))) ≃ OpenResponsibilityAt (Admission.N input frame registered)
      (Admission.supportAt input frame registered current) from
    ⟨presentation.forward, presentation.backward, presentation.backward_forward, presentation.forward_backward⟩)).symm.trans
      Finite.card_option

def erasedProjectionCard (source : AnyAuthoritativeRootCurrent) : Nat :=
  Nat.card source.current.root.source.projectionLaw.Projection

private def baseProjectionEquiv : AccountSource.Projection ≃ Fin 6 where
  toFun := fun projection => match projection with
    | .ledger => 0 | .account => 1 | .pending => 2 | .observation => 3 | .compilation => 4 | .consumer => 5
  invFun := fun index => Fin.cases .ledger (Fin.cases .account (Fin.cases .pending
    (Fin.cases .observation (Fin.cases .compilation (fun _ => .consumer))))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def oldProjectionEquiv : ProgrammeLiving.Projection ≃ Fin 4 where
  toFun := fun projection => match projection with
    | .ledger => 0 | .execution => 1 | .consumer => 2 | .inquiry => 3
  invFun := fun index => Fin.cases .ledger (Fin.cases .execution (Fin.cases .consumer (fun _ => .inquiry))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def admittedProjectionEquiv : Admission.OwnProjection ≃ Fin 4 where
  toFun := fun projection => match projection with
    | .ledger => 0 | .observation => 1 | .compilation => 2 | .consumer => 3
  invFun := fun index => Fin.cases .ledger (Fin.cases .observation (Fin.cases .compilation (fun _ => .consumer))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

theorem base_projection_card : Nat.card AccountSource.Projection = 6 :=
  (Nat.card_congr baseProjectionEquiv).trans (Nat.card_fin 6)

theorem base_projection_finite : Finite AccountSource.Projection :=
  Finite.of_equiv (Fin 6) baseProjectionEquiv.symm

theorem own_projection_finite : Finite Admission.OwnProjection :=
  Finite.of_equiv (Fin 4) admittedProjectionEquiv.symm

theorem programme_projection_card : Nat.card ProgrammeLiving.Projection = 4 :=
  (Nat.card_congr oldProjectionEquiv).trans (Nat.card_fin 4)

theorem child_projection_card (frame : NativeFrame input) {origin : frame.V.Current}
    (registered : Registration input frame origin)
    [Finite frame.root.toAuthoritativeRoot.source.projectionLaw.Projection] :
    Nat.card (Admission.nativeFrame input frame registered).root.toAuthoritativeRoot.source.projectionLaw.Projection =
      Nat.card frame.root.toAuthoritativeRoot.source.projectionLaw.Projection + 4 := by
  have : Finite Admission.OwnProjection := Finite.of_equiv (Fin 4) admittedProjectionEquiv.symm
  change Nat.card (frame.root.toAuthoritativeRoot.source.projectionLaw.Projection ⊕ Admission.OwnProjection) = _
  rw [Nat.card_sum, (Nat.card_congr admittedProjectionEquiv).trans (Nat.card_fin 4)]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
