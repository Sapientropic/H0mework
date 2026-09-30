import H0mework.Versions.Y1.Arithmetic.RiemannRuntime.Debt.Runtime.ClozelStageThreeIncidenceDebtInactiveRoot

/-!
# Exact handoff after the stage-three incidence debt is paid

The installed active phase terminates only the projection-debt episode.  Its
handoff removes that settled row, preserves the inherited canonical arithmetic
row, and resumes at the exact canonical successor in the debt-inactive root.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction.BranchNeutralDebtGate.TerminalHandoff

open CanonicalUnitArithmeticRoot
open DebtActivationWorld
open BranchNeutralDebtGate

noncomputable section

variable {observation : GeneratedRiemannZeroObservation}
variable {nontrivial : ¬ ∃ n : Nat,
  observation.coordinate = -2 * (n + 1)}

local notation "Law" =>
  stageThreeIncidenceProjectionDebtLaw observation nontrivial
local notation "W" =>
  StageThreeIncidenceProjectionDebtNetwork observation nontrivial

def activeInstalledOldEntry
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    OpenResponsibilityAt W (ActiveRoot.installedSupport receipt) :=
  DebtActivationWorld.oldEntry (law := Law) (state? := some (.installed receipt))
    (rootLedgerEntry
      (ActiveRoot.baseSupport
        (observation := observation) (nontrivial := nontrivial)))

def targetOldEntry
    (_receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    OpenResponsibilityAt W
      (InactiveRoot.supportAt
        (InactiveRoot.initialBaseCurrent
          (observation := observation) (nontrivial := nontrivial))) :=
  InactiveRoot.inactiveEntry
    (InactiveRoot.initialBaseCurrent
      (observation := observation) (nontrivial := nontrivial))

def oldRowHandoffLineage
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    RootDebtLineageAt W (activeInstalledOldEntry receipt)
      (targetOldEntry receipt) where
  lineage_eq := rfl
  claim_eq := rfl

def inactiveOccurrenceUnitPresentation
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    ConstructivePresentation
      ((InactiveRoot.authoritativeRoot receipt).toRoot.actual.OccurrenceAt
        (InactiveRoot.authoritativeRoot receipt).toRoot.source.initial)
      PUnit where
  forward := fun _ => PUnit.unit
  backward := fun _ =>
    InactiveRoot.emitted receipt
      (InactiveRoot.initialBaseCurrent
        (observation := observation) (nontrivial := nontrivial))
  backward_forward := by
    rintro ⟨support, event⟩
    cases event
    rfl
  forward_backward := by
    intro event
    cases event
    rfl

def terminalHandoff
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeTerminalHandoffLaw (ActiveRoot.authoritySource receipt) :=
  SourceNativeTerminalHandoffLaw.create
    (fun {_current} _history {_occurrence} _terminal => PUnit)
    (fun {_current} _history {_occurrence} _terminal => PUnit.unit)
    (fun _event => InactiveRoot.vocabulary
      (observation := observation) (nontrivial := nontrivial))
    (fun _event => InactiveRoot.authoritativeRoot receipt)
    (fun _event => inactiveOccurrenceUnitPresentation receipt)
    (by
      intro current history occurrence terminal event
      cases event
      rfl)
    (by
      intro current history occurrence terminal event
      cases event
      rfl)
    (by
      intro current history occurrence terminal event targetEntry
      cases current with
      | pending => exact nomatch terminal.terminal
      | installed =>
          rcases occurrence with ⟨support, sourceEvent⟩
          cases sourceEvent
          cases InactiveRoot.inactiveEntry_unique
            (InactiveRoot.initialBaseCurrent
              (observation := observation) (nontrivial := nontrivial))
            targetEntry
          exact .inl ⟨activeInstalledOldEntry receipt,
            oldRowHandoffLineage receipt⟩)
    (by
      intro current history occurrence terminal event sourceEntry targetEntry
        sameDebt
      cases InactiveRoot.inactiveEntry_unique
        (InactiveRoot.initialBaseCurrent
          (observation := observation) (nontrivial := nontrivial))
        targetEntry
      change 0 ≤ sourceEntry.progressBudget
      exact Nat.zero_le _)
    (by
      intro current history occurrence terminal event sourceEntry left right
        leftDebt rightDebt
      exact InactiveRoot.inactiveEntry_unique
        (InactiveRoot.initialBaseCurrent
          (observation := observation) (nontrivial := nontrivial)) left |>.trans
        ((InactiveRoot.inactiveEntry_unique
          (InactiveRoot.initialBaseCurrent
            (observation := observation) (nontrivial := nontrivial)) right).symm))

def livingActiveRoot
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLivingRootClosure W
      (ActiveRoot.vocabulary
        (observation := observation) (nontrivial := nontrivial)) where
  source :=
    { base := ActiveRoot.authoritySource receipt
      terminalHandoff := terminalHandoff receipt }
  emitted := ActiveRoot.emitted receipt
  compiler_commutes := ActiveRoot.authoritativeRoot receipt |>.compiler_commutes

def installedVisit
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    RootVisit (livingActiveRoot receipt).toAuthoritativeRoot.toRoot :=
  (livingActiveRoot receipt).toAuthoritativeRoot.toRoot.initialVisit.next rfl

def generatedInactiveCurrent
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeAuthoritativeRootCurrentAt W :=
  (livingActiveRoot receipt).generatedNextCurrentAt (.finite (installedVisit receipt))

theorem generatedInactiveCurrent_root
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (generatedInactiveCurrent receipt).root =
      InactiveRoot.authoritativeRoot receipt :=
  rfl

theorem generatedInactiveCurrent_support
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (generatedInactiveCurrent receipt).root.toRoot.supportAt
        (generatedInactiveCurrent receipt).visit.current =
      InactiveRoot.supportAt
        (InactiveRoot.initialBaseCurrent
          (observation := observation) (nontrivial := nontrivial)) :=
  rfl

end
end IntegralGraphJointAction.BranchNeutralDebtGate.TerminalHandoff
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.TerminalHandoff.generatedInactiveCurrent_support
