import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Math
import H0mework.Versions.R2.Foundation.Inquiry.Engine
import Mathlib.SetTheory.Cardinal.NatCard

/-! Complete compiler rows generate finiteness of the actual ledger fibre.
Its cardinality is conserved by source-paid identity restructuring; row
indices may repeat and are never interpreted as inventory cardinality. -/
set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Inventory
open RootInquiryCompletion DebtActivationWorld SourceOperationEffects

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V}
variable (program : Native.Program lower) (scope : Native.IdentityScope program)

include program in
theorem source_finite (current : V.Current) : Finite (OpenResponsibilityAt N
    (lower.source.source.toRootSource.account.supportOf (lower.emitted current))) :=
  Finite.of_surjective (program.emit current).rows.sourceEntryAt
    (fun entry => ⟨(program.emit current).coverage.destinationIndex entry,
      (program.emit current).coverage.destination_sound entry⟩)

theorem target_finite (current : V.Current) : Finite (OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf (program.emit current).targetOccurrence)) := by
  exact Finite.of_surjective (program.emit current).rows.targetEntryAt
    (fun entry => ⟨(program.emit current).coverage.originIndex entry,
      (program.emit current).coverage.origin_sound entry⟩)

include scope in
theorem native_card_generated (current : V.Current) :
    Nat.card (OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf (lower.emitted current))) =
      Nat.card (OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf (program.emit current).targetOccurrence)) := by
  let sourceFinite := Finite.of_surjective (program.emit current).rows.sourceEntryAt
    (fun entry => ⟨(program.emit current).coverage.destinationIndex entry,
      (program.emit current).coverage.destination_sound entry⟩)
  let targetFinite := Finite.of_surjective (program.emit current).rows.targetEntryAt
    (fun entry => ⟨(program.emit current).coverage.originIndex entry,
      (program.emit current).coverage.origin_sound entry⟩)
  exact Nat.le_antisymm
    (Nat.card_le_card_of_injective _ (Native.Identity.destination_injective scope.defaultAnchor
      scope.openAt_subsingleton (scope.certify current)))
    (Nat.card_le_card_of_injective _ (Native.Identity.origin_injective scope.defaultAnchor
      scope.openAt_subsingleton (scope.certify current)))

noncomputable def entryCard (root : SourceNativeLedgerRootClosure N V) (current : V.Current) : Nat :=
  Nat.card (OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted current)))

noncomputable def erasedEntryCard (current : AnyAuthoritativeRootCurrent.{u}) : Nat :=
  entryCard current.current.root.toLedgerRoot current.current.visit.current

include scope in
theorem native_card_eq (current : V.Current) : entryCard lower current =
    entryCard lower (V.nativeTarget (program.emit current).write) :=
  (native_card_generated program scope current).trans
    (congrArg (fun support => Nat.card (OpenResponsibilityAt N support))
      (congrArg lower.source.source.toRootSource.account.supportOf (program.emit current).target_emitted))

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current} (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)

noncomputable section
include program in
theorem active_card (current : Native.Current registered) :
    Nat.card (OpenResponsibilityAt (Native.World registered) (Native.supportAt registered current)) =
      entryCard lower current.1 + 1 := by
  let sourceFinite := source_finite program current.1
  let presentation := activeInventoryPresentation
    (law := Idle.law registered.input.environment registered.input.expression) current.2.state
    (show ConstructivePresentation (OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1)))
      (OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1))) from
      ⟨id, id, fun _ => rfl, fun _ => rfl⟩)
  exact (Nat.card_congr (show Option (OpenResponsibilityAt N
    (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1))) ≃
      OpenResponsibilityAt (Native.World registered) (Native.supportAt registered current) from
      ⟨presentation.forward, presentation.backward, presentation.backward_forward, presentation.forward_backward⟩)).symm.trans
        Finite.card_option
variable (old : RootInquiryStateAt N V)
variable (requestProgram : Native.Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (request : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (requestScope : Native.IdentityScope requestProgram)

include requestScope in
theorem finite_old_card (count : Nat) :
    entryCard old.root.toAuthoritativeRoot.toLedgerRoot
      (Request.finiteVisit old requestProgram request requestScope count).current.1 =
        entryCard old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (native_card_eq requestProgram requestScope
        (Request.finiteVisit old requestProgram request requestScope count).current.1).symm.trans ih

theorem newfinite_card (count : Nat) :
    entryCard (Request.targetRoot old requestProgram request requestScope).toAuthoritativeRoot.toLedgerRoot
      (Request.finiteVisit old requestProgram request requestScope count).current =
        entryCard old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current + 1 :=
  (active_card requestProgram request (Request.finiteVisit old requestProgram request requestScope count).current).trans
    (congrArg (fun size => size + 1) (finite_old_card old requestProgram request requestScope count))

theorem newfinite_finite (count : Nat) :
    Finite (OpenResponsibilityAt (Request.NewN old request)
      ((Request.targetRoot old requestProgram request requestScope).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((Request.targetRoot old requestProgram request requestScope).emitted
          (Request.finiteVisit old requestProgram request requestScope count).current))) :=
  source_finite (Request.nextProgram old requestProgram request requestScope)
    (Request.finiteVisit old requestProgram request requestScope count).current

theorem birth_math_erasure_ne (count : Nat) :
    (⟨N, ⟨V, old.root.toAuthoritativeRoot, old.visit⟩⟩ : AnyAuthoritativeRootCurrent.{u}) ≠
      ⟨Request.NewN old request,
        ⟨Request.NewV old requestProgram request,
          (Request.targetRoot old requestProgram request requestScope).toAuthoritativeRoot,
          Request.temporalVisit old requestProgram request requestScope count⟩⟩ := by
  intro same
  have inventories := congrArg erasedEntryCard same
  change entryCard old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current =
    entryCard (Request.targetRoot old requestProgram request requestScope).toAuthoritativeRoot.toLedgerRoot
      (Request.finiteVisit old requestProgram request requestScope count).current at inventories
  exact Nat.ne_add_one _ (inventories.trans (newfinite_card old requestProgram request requestScope count))

end

end RootGeneratedDebtActivationJointSource.Native.Request.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
