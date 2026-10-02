import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Compiler

/-! Independent consumers use the installed source's actual certificate,
canonical whole write, descendant-family kernel and original joint payer. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring
open SourceOperationEffects DebtActivationWorld DebtActivationLedger

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (program : Program old.toLedgerRoot) {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (current : (JointV program registered).Current)

def actualCertificate : ExactLedgerRestructuringCertificationAt (law old program registered)
    (emitted program registered current) (patch program registered current).toLedgerWriteEvolution :=
  (authoritySource old program registered).restructuringSource.compiler.certifyRestructuring
    (emitted program registered current)

def splitConsumer
    (left right : OpenResponsibilityAt (World registered) (supportAt registered (targetCurrent program registered current)))
    (same : ((patch program registered current).toLedgerWriteEvolution.origin left).1 =
      ((patch program registered current).toLedgerWriteEvolution.origin right).1) :
    PLift (left = right) ⊕
      (Σ coverage : SourceNativeSplitCoverageAt (law old program registered) (emitted program registered current)
        (patch program registered current).toLedgerWriteEvolution left right same,
        DescendantFamily (vocabulary old registered) coverage.receipt.sourceEvent
          ((law old program registered).obligationAt (emitted program registered current)
            ((patch program registered current).toLedgerWriteEvolution.origin left).1) coverage.receipt.children) :=
  match (actualCertificate old program registered current).split left right same with
  | .identity equality => .inl ⟨equality⟩
  | .split coverage => .inr ⟨coverage, coverage.descendantFamily⟩

def mergeConsumer
    (left right : OpenResponsibilityAt (World registered) (supportAt registered current))
    (same : ((patch program registered current).toLedgerWriteEvolution.destination left).1 =
      ((patch program registered current).toLedgerWriteEvolution.destination right).1) :
    PLift (left = right) ⊕
      (Σ coverage : SourceNativeMergeCoverageAt (law old program registered) (emitted program registered current)
        (patch program registered current).toLedgerWriteEvolution left right same,
        (parent : (vocabulary old registered).Obligation) → parent ∈ coverage.receipt.parents →
          (vocabulary old registered).LocalDischargePreservedAt coverage.receipt.sourceEvent
            parent.content coverage.receipt.target.content) :=
  match (actualCertificate old program registered current).merge left right same with
  | .identity equality => .inl ⟨equality⟩
  | .merge coverage => .inr ⟨coverage, fun _ member => coverage.receipt.every_parent_retains_localDischarge member⟩

def actualSuccessor : SourceNativeLedgerGeneratedSuccessorAt (emitted program registered current)
    ((authoritySource old program registered).restructuringSource.compiler.ledgerCompiler.compile
      (emitted program registered current)) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((authoritySource old program registered).restructuringSource.compiler.ledgerCompiler.compile
      (emitted program registered current))).get (by rfl)

theorem actual_next : (actualSuccessor old program registered current).targetCurrent =
    targetCurrent program registered current := rfl

variable (paid : GeneratedStepAt (MathLaw old registered) current.2.state)
variable (action : mathAction current.2 = .inr paid)
include action in
theorem full_paid_destination :
    HEq (actualSuccessor old program registered current).ledgerEvolution.destination
      (jointStepLedgerEvolution (law := MathLaw old registered)
        (native program registered current).baseLedger current.2.owner paid.2).destination :=
  paid_destination program registered current paid action

theorem original_projection (projection : old.source.projectionLaw.Projection) :
    HEq ((authoritySource old program registered).projectionLaw.outcomeAt (.inl projection)
      (emitted program registered current))
      (old.source.projectionLaw.outcomeAt projection (old.emitted current.1)) :=
  original_projection_outcome program registered old.source.projectionLaw (emitted program registered current) projection

end RootGeneratedDebtActivationJointSource.Native.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
