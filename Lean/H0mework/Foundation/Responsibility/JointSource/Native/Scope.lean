import H0mework.Foundation.Responsibility.JointSource.Native.Readback
import H0mework.Foundation.Responsibility.JointSource.Native.Identity

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)

/-- The old source's paid identity restructuring certificate, not a new-row
coverage or target-action assumption. -/
structure IdentityScope where
  defaultAnchor : N.Anchor
  openAt_subsingleton : (support : N.Support) → (responsibility : N.Responsibility) →
    Subsingleton (N.OpenAt support responsibility)
  certify : (current : V.Current) → ExactLedgerRestructuringCertificationAt
    (identityOnlyWorldLedgerRestructuringLaw lower.source.source defaultAnchor openAt_subsingleton)
    (lower.emitted current) (program.emit current).evolution

variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)
variable (scope : IdentityScope program)

private theorem castOriginInjective {current next : V.Current}
    {target actual : lower.source.source.toRootSource.actual.OccurrenceAt next}
    (same : target = actual)
    (packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
      (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf target⟩,
      LedgerCompleteFiniteCoverageAt rows)
    (injective : Function.Injective (fun entry =>
      ((FiniteGeneratedLedgerWritePatchAt.complete packet.1 packet.2).toLedgerWriteEvolution.origin entry).1)) :
    Function.Injective (fun entry =>
      ((FiniteGeneratedLedgerWritePatchAt.complete
        ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
          (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf actual⟩,
          LedgerCompleteFiniteCoverageAt rows).1)
        ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
          (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf actual⟩,
          LedgerCompleteFiniteCoverageAt rows).2)).toLedgerWriteEvolution.origin entry).1) := by
  cases same
  exact injective

private theorem castDestinationInjective {current next : V.Current}
    {target actual : lower.source.source.toRootSource.actual.OccurrenceAt next}
    (same : target = actual)
    (packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
      (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf target⟩,
      LedgerCompleteFiniteCoverageAt rows)
    (injective : Function.Injective (fun entry =>
      ((FiniteGeneratedLedgerWritePatchAt.complete packet.1 packet.2).toLedgerWriteEvolution.destination entry).1)) :
    Function.Injective (fun entry =>
      ((FiniteGeneratedLedgerWritePatchAt.complete
        ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
          (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf actual⟩,
          LedgerCompleteFiniteCoverageAt rows).1)
        ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
          (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf actual⟩,
          LedgerCompleteFiniteCoverageAt rows).2)).toLedgerWriteEvolution.destination entry).1) := by
  cases same
  exact injective

include scope in
theorem oldFold_origin_injective (current : Current registered) :
    Function.Injective (fun entry => ((oldFold program registered current).origin entry).1) := by
  have paid := Identity.origin_injective scope.defaultAnchor scope.openAt_subsingleton (scope.certify current.1)
  have folded : Function.Injective (fun entry =>
      ((FiniteGeneratedLedgerWritePatchAt.complete (program.emit current.1).rows
        (program.emit current.1).coverage).toLedgerWriteEvolution.origin entry).1) := by
    rw [(program.emit current.1).fold_eq]
    exact paid
  exact castOriginInjective (image_target program registered current)
    ⟨(program.emit current.1).rows, (program.emit current.1).coverage⟩ folded

include scope in
theorem oldFold_destination_injective (current : Current registered) :
    Function.Injective (fun entry => ((oldFold program registered current).destination entry).1) := by
  have paid := Identity.destination_injective scope.defaultAnchor scope.openAt_subsingleton (scope.certify current.1)
  have folded : Function.Injective (fun entry =>
      ((FiniteGeneratedLedgerWritePatchAt.complete (program.emit current.1).rows
        (program.emit current.1).coverage).toLedgerWriteEvolution.destination entry).1) := by
    rw [(program.emit current.1).fold_eq]
    exact paid
  exact castDestinationInjective (image_target program registered current)
    ⟨(program.emit current.1).rows, (program.emit current.1).coverage⟩ folded

private def oldEntryRead {law : DebtActivationLaw.{u}} {support : N.Support}
    {state : law.DebtState} : OpenResponsibilityAt (ExtendedNetwork N law) (support, some state) →
      Option (OpenResponsibilityAt N support)
  | ⟨.inl responsibility, opened⟩ => some ⟨responsibility, opened⟩
  | ⟨.inr _, _⟩ => none

theorem oldEntry_injective {law : DebtActivationLaw.{u}} {support : N.Support} {state : law.DebtState} :
    Function.Injective (oldEntry (N := N) (law := law) (support := support) (state? := some state)) := by
  intro left right same
  exact Option.some.inj (congrArg (oldEntryRead (state := state)) same)

private theorem injectiveWithMath {law : DebtActivationLaw.{u}} {sourceSupport targetSupport : N.Support}
    {sourceState targetState : law.DebtState}
    (oldMap : OpenResponsibilityAt N sourceSupport → OpenResponsibilityAt N targetSupport)
    (newMap : OpenResponsibilityAt (ExtendedNetwork N law) (sourceSupport, some sourceState) →
      OpenResponsibilityAt (ExtendedNetwork N law) (targetSupport, some targetState))
    (oldSquare : (entry : OpenResponsibilityAt N sourceSupport) →
      newMap (oldEntry (law := law) (state? := some sourceState) entry) =
        oldEntry (law := law) (state? := some targetState) (oldMap entry))
    (mathSquare : newMap (debtEntry (N := N) (law := law) sourceSupport sourceState) =
      debtEntry (N := N) (law := law) targetSupport targetState)
    (oldInjective : Function.Injective oldMap) : Function.Injective newMap := by
  rintro ⟨left, leftOpen⟩ ⟨right, rightOpen⟩ same
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          have generated := (oldSquare ⟨left, leftOpen⟩).symm.trans
            (same.trans (oldSquare ⟨right, rightOpen⟩))
          exact congrArg (oldEntry (law := law) (state? := some sourceState))
            (oldInjective (oldEntry_injective generated))
      | inr right =>
          rcases rightOpen with ⟨⟨rightEq⟩⟩
          subst right
          have generated := (oldSquare ⟨left, leftOpen⟩).symm.trans (same.trans mathSquare)
          exact nomatch congrArg Sigma.fst generated
  | inr left =>
      rcases leftOpen with ⟨⟨leftEq⟩⟩
      subst left
      cases right with
      | inl right =>
          have generated := mathSquare.symm.trans (same.trans (oldSquare ⟨right, rightOpen⟩))
          exact nomatch congrArg Sigma.fst generated
      | inr right =>
          rcases rightOpen with ⟨⟨rightEq⟩⟩
          subst right
          rfl

include scope in
theorem patch_origin_injective (current : Current registered) : Function.Injective (fun entry =>
    ((patch program registered current).toLedgerWriteEvolution.origin entry).1) :=
  injectiveWithMath (fun entry => ((oldFold program registered current).origin entry).1)
    (fun entry => ((patch program registered current).toLedgerWriteEvolution.origin entry).1)
    (patch_origin_old program registered current) (patch_origin_math program registered current)
    (oldFold_origin_injective program registered scope current)

include scope in
theorem patch_destination_injective (current : Current registered) : Function.Injective (fun entry =>
    ((patch program registered current).toLedgerWriteEvolution.destination entry).1) :=
  injectiveWithMath (fun entry => ((oldFold program registered current).destination entry).1)
    (fun entry => ((patch program registered current).toLedgerWriteEvolution.destination entry).1)
    (patch_destination_old program registered current) (patch_destination_math program registered current)
    (oldFold_destination_injective program registered scope current)

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
