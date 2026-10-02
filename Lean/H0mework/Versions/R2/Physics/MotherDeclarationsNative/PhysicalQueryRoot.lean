import H0mework.Versions.R2.Physics.MotherDeclarationsNative.PhysicalQuerySource

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Stage9C.Revision CofinalHistorySettlementFace

noncomputable section

def rawWorld (typeLaw actionLaw : Law) : SourceNativeLivingRawWorld MaterialN SpinPair.V where
  source := ⟨declarationSource typeLaw actionLaw,
    (declarationSource typeLaw actionLaw).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)⟩
  emitted := SpinPair.emitted

def livingRoot (typeLaw actionLaw : Law) : SourceNativeLivingRootClosure MaterialN SpinPair.V :=
  (rawWorld typeLaw actionLaw).toLivingRoot ⟨fun _ => rfl⟩

def initialVisit (typeLaw actionLaw : Law) :
    SourceNativeTemporalVisitAt (livingRoot typeLaw actionLaw).toAuthoritativeRoot.toLedgerRoot :=
  .finite (livingRoot typeLaw actionLaw).toAuthoritativeRoot.toRoot.initialVisit

def visitAt (typeLaw actionLaw : Law) : ℕ →
    SourceNativeTemporalVisitAt (livingRoot typeLaw actionLaw).toAuthoritativeRoot.toLedgerRoot
  | 0 => initialVisit typeLaw actionLaw
  | depth + 1 => (visitAt typeLaw actionLaw depth).next rfl

def entryAt (typeLaw actionLaw : Law) (depth : ℕ) :
    OpenResponsibilityAt MaterialN (SpinPair.support (visitAt typeLaw actionLaw depth).current) :=
  materialEntry (SpinPair.support (visitAt typeLaw actionLaw depth).current)

def initialGenerated (typeLaw actionLaw : Law) :=
  (livingRoot typeLaw actionLaw).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit typeLaw actionLaw)

def initialEntryRow (typeLaw actionLaw : Law) :
    (initialGenerated typeLaw actionLaw).GeneratedEntryRowAt (entryAt typeLaw actionLaw 0) :=
  ((initialGenerated typeLaw actionLaw).canonicalGeneratedEntryRow? (entryAt typeLaw actionLaw 0)).get (by rfl)

def authorityAt (typeLaw actionLaw : Law) : (depth : ℕ) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt (livingRoot typeLaw actionLaw)
      (visitAt typeLaw actionLaw depth) (entryAt typeLaw actionLaw depth)
  | 0 => .generatedFromInitialRow (livingRoot typeLaw actionLaw)
      (entryAt typeLaw actionLaw 0) (initialEntryRow typeLaw actionLaw)
  | depth + 1 => (authorityAt typeLaw actionLaw depth).next rfl

def anchorAt (typeLaw actionLaw : Law) (depth : ℕ) : Anchor :=
  ⟨(visitAt typeLaw actionLaw depth).current, SpinPair.emitted (visitAt typeLaw actionLaw depth).current⟩

def historyRecognition (typeLaw actionLaw : Law) :
    SourceNativeCofinalHistoryRecognitionAt (livingRoot typeLaw actionLaw) where
  materialLaw := ActualFormation.historyLaw
  installation :=
    (SourceNativeProjectionLaw.InstallationAt.componentCoface
      SpinPair.authoritativeRoot.source ActualFormation.historyLaw.toProjectionLaw).trans
      (.inheritedCoface historySource (projectionLaw typeLaw actionLaw))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery
