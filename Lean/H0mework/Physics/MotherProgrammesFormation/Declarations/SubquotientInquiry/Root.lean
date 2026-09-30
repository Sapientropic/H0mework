import H0mework.Physics.MotherProgrammesFormation.Declarations.SubquotientInquiry.Source

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotientInquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Stage9C.Revision CofinalHistorySettlementFace

noncomputable section

def rawWorld (ready : Ready) : SourceNativeLivingRawWorld MaterialN SpinPair.V where
  source := ⟨declarationSource ready,
    (declarationSource ready).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)⟩
  emitted := SpinPair.emitted

def livingRoot (ready : Ready) : SourceNativeLivingRootClosure MaterialN SpinPair.V :=
  (rawWorld ready).toLivingRoot ⟨fun _ => rfl⟩

def initialVisit (ready : Ready) :
    SourceNativeTemporalVisitAt (livingRoot ready).toAuthoritativeRoot.toLedgerRoot :=
  .finite (livingRoot ready).toAuthoritativeRoot.toRoot.initialVisit

def visitAt (ready : Ready) : ℕ →
    SourceNativeTemporalVisitAt (livingRoot ready).toAuthoritativeRoot.toLedgerRoot
  | 0 => initialVisit ready
  | depth + 1 => (visitAt ready depth).next rfl

def entryAt (ready : Ready) (depth : ℕ) :
    OpenResponsibilityAt MaterialN (SpinPair.support (visitAt ready depth).current) :=
  materialEntry (SpinPair.support (visitAt ready depth).current)

def initialGenerated (ready : Ready) :=
  (livingRoot ready).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (initialVisit ready)

def initialEntryRow (ready : Ready) :
    (initialGenerated ready).GeneratedEntryRowAt (entryAt ready 0) :=
  ((initialGenerated ready).canonicalGeneratedEntryRow? (entryAt ready 0)).get (by rfl)

def authorityAt (ready : Ready) : (depth : ℕ) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt (livingRoot ready)
      (visitAt ready depth) (entryAt ready depth)
  | 0 => .generatedFromInitialRow (livingRoot ready) (entryAt ready 0) (initialEntryRow ready)
  | depth + 1 => (authorityAt ready depth).next rfl

def anchorAt (ready : Ready) (depth : ℕ) : Anchor :=
  ⟨(visitAt ready depth).current, SpinPair.emitted (visitAt ready depth).current⟩

def historyRecognition (ready : Ready) : SourceNativeCofinalHistoryRecognitionAt (livingRoot ready) where
  materialLaw := ActualFormation.historyLaw
  installation :=
    (MotherNativePhysicalQuery.historyRecognition ready.val.typeLaw ready.val.actionLaw).installation.trans
      (originalQueryInstallation ready)

theorem original_ledgerRoot_preserved (ready : Ready) :
    (livingRoot ready).toAuthoritativeRoot.toLedgerRoot = SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_ledger_preserved (ready : Ready) (current : SpinPair.Current) :
    (livingRoot ready).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

theorem original_next_preserved (ready : Ready) (current : SpinPair.Current) :
    ((livingRoot ready).toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? =
      (SpinPair.livingRoot.toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? := rfl

theorem generated_next (ready : Ready) (depth : ℕ) :
    (livingRoot ready).generatedNextCurrentAt (visitAt ready depth) =
      ⟨SpinPair.V, (livingRoot ready).toAuthoritativeRoot, visitAt ready (depth + 1)⟩ :=
  (livingRoot ready).generatedNextCurrentAt_eq_nativeWriteBranch (visitAt ready depth)
    (materialActionAt (SpinPair.underlying (visitAt ready depth).current)) rfl
    (SpinPair.emitted (SpinPair.next (visitAt ready depth).current))
    (SpinPair.generatedPatch (SpinPair.emitted (visitAt ready depth).current)).toLedgerWriteEvolution
    rfl rfl

theorem original_visit_preserved (ready : Ready) (depth : ℕ) :
    visitAt ready depth = MotherNativePhysicalQuery.visitAt ready.val.typeLaw ready.val.actionLaw depth := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      exact congrArg (fun visit => visit.next (next := SpinPair.next visit.current) rfl) prior

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotientInquiry
