import H0mework.Foundation.Responsibility.JointSource.Successor.Compiler
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Law

/-! Bind the existing complete obligation vocabulary to the packet source's
actual original occurrence. The finite-patch representation is not inspected. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Restructuring
open SourceOperationEffects DebtActivationWorld CompilerFromPacketSourceLaw
open Native.Restructuring (originalLaw MathLaw vocabulary oldObligation mathObligation readOld readOld_old oldObligation_injective)

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (packetAt : (current : V.Current) → Packet old.toLedgerRoot current)

def obligationAt {current : Current registered}
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current)
    {support : (World registered).Support} (entry : OpenResponsibilityAt (World registered) support) :
    (vocabulary old registered).Obligation := by
  rcases support with ⟨support, state⟩
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl prior =>
      exact oldObligation old registered ((originalLaw old).obligationAt (originalOccurrence registered packetAt occurrence) ⟨prior, opened⟩)
  | inr debt =>
      cases state with
      | none => exact nomatch opened
      | some state =>
          rcases opened with ⟨⟨same⟩⟩
          cases same
          exact mathObligation old registered support state

abbrev law : SourceNativeLedgerRestructuringLaw (source registered packetAt) where
  vocabulary := vocabulary old registered
  sourceEventAt := fun occurrence => .inl ((originalLaw old).sourceEventAt (originalOccurrence registered packetAt occurrence))
  obligationAt := obligationAt old registered packetAt
  responsibilityKey := fun entry => match readOld old registered entry with
    | some prior => .inl ((originalLaw old).responsibilityKey prior)
    | none => .inr (MathLaw old registered).debtId
  anchorKey := fun identity => match identity with
    | .inl prior => (originalLaw old).anchorKey prior
    | .inr pair => pair.1
  incidenceKey := fun incidence => match incidence with
    | .inl prior => (originalLaw old).incidenceKey prior
    | .inr current => current
  lineageKey := fun lineage => match lineage with
    | .inl prior => (originalLaw old).lineageKey prior
    | .inr current => current
  responsibility_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior =>
        dsimp only [obligationAt]
        rw [readOld_old]
        exact congrArg Sum.inl ((originalLaw old).responsibility_commutes
          (originalOccurrence registered packetAt occurrence) ⟨prior, opened⟩)
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  anchor_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior => exact (originalLaw old).anchor_commutes (originalOccurrence registered packetAt occurrence) ⟨prior, opened⟩
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  incidence_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior => exact (originalLaw old).incidence_commutes (originalOccurrence registered packetAt occurrence) ⟨prior, opened⟩
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  lineage_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior => exact (originalLaw old).lineage_commutes (originalOccurrence registered packetAt occurrence) ⟨prior, opened⟩
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  obligationAt_injective := by
    intro current occurrence support first second same
    rcases support with ⟨support, state⟩
    rcases first with ⟨first, firstOpen⟩
    rcases second with ⟨second, secondOpen⟩
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            exact congrArg (oldEntry (law := MathLaw old registered) (state? := state))
              ((originalLaw old).obligationAt_injective (originalOccurrence registered packetAt occurrence)
                (oldObligation_injective old registered same))
        | inr second =>
            cases state with
            | none => exact nomatch secondOpen
            | some state => rcases secondOpen with ⟨⟨sameId⟩⟩; cases sameId; exact nomatch congrArg AdmittedObligation.content same
    | inr first =>
        cases state with
        | none => exact nomatch firstOpen
        | some state =>
            rcases firstOpen with ⟨⟨sameId⟩⟩
            cases sameId
            cases second with
            | inl second => exact nomatch congrArg AdmittedObligation.content same
            | inr second => rcases secondOpen with ⟨⟨sameId⟩⟩; cases sameId; rfl

end RootGeneratedDebtActivationJointSource.Successor.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
