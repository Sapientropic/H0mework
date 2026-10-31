import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedWorld

/-!
# Canonical authority along the revised loss-allocation root

This module owns the single visit-indexed entry and causal-entry authority
lineage of the already generated revised root.  Inquiry states and later
sequential actions consume these definitions; neither layer recompiles a
second authority chain.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9ProofCarryingRenewalU8RevisedAuthority

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld

def temporalVisitAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    SourceNativeTemporalVisitAt
      (revisedLivingRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot :=
  .finite (revisedVisitAtFrom oldVisit index)

def inquiryEventAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :=
  ULift.up.{1, 0}
    ((revisedLivingRootAt oldVisit).emitted
      (revisedVisitAtFrom oldVisit index).current)

def inquiryEntryReadoutAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    OpenResponsibilityAt
      (M9ProofCarryingRenewalU8RevisedWorld.NewNAt oldVisit)
      ((revisedLivingRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((revisedLivingRootAt oldVisit).emitted
          (revisedVisitAtFrom oldVisit index).current)) :=
  revisedInquiryEntryAtVisit oldVisit
    (revisedVisitAtFrom oldVisit index).current

theorem nextEqAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    ((revisedLivingRootAt oldVisit).toAuthoritativeRoot.toRoot.evolutionAt
      (revisedVisitAtFrom oldVisit index).current).nextCurrent? =
      some (revisedVisitAtFrom oldVisit (index + 1)).current :=
  rfl

theorem temporalVisit_next_eq_atFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    (temporalVisitAtFrom oldVisit index).next (nextEqAtFrom oldVisit index) =
      temporalVisitAtFrom oldVisit (index + 1) :=
  rfl

theorem canonicalTargetReadout_eq_atFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    (revisedLivingRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
        (nextEqAtFrom oldVisit index)
        (inquiryEntryReadoutAtFrom oldVisit index) =
      inquiryEntryReadoutAtFrom oldVisit (index + 1) := by
  cases index with
  | zero => rfl
  | succ index => rfl

def visitEntryAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (index : Nat) →
      OpenResponsibilityAt
        (M9ProofCarryingRenewalU8RevisedWorld.NewNAt oldVisit)
        ((revisedLivingRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          ((revisedLivingRootAt oldVisit).emitted
            (revisedVisitAtFrom oldVisit index).current))
  | 0 => newRevisedEntryAt oldVisit
  | index + 1 =>
      (revisedLivingRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
        (nextEqAtFrom oldVisit index) (visitEntryAtFrom oldVisit index)

theorem visitEntry_eq_inquiryReadout_atFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    visitEntryAtFrom oldVisit index =
      inquiryEntryReadoutAtFrom oldVisit index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (revisedLivingRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
            (nextEqAtFrom oldVisit index) (visitEntryAtFrom oldVisit index) =
          inquiryEntryReadoutAtFrom oldVisit (index + 1)
      rw [inductionHypothesis,
        canonicalTargetReadout_eq_atFrom oldVisit index]

def initialAuthorityAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (revisedLivingRootAt oldVisit) (temporalVisitAtFrom oldVisit 0)
        (visitEntryAtFrom oldVisit 0) :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    (revisedLivingRootAt oldVisit) (visitEntryAtFrom oldVisit 0)
      .initial).get (by rfl)).2

def authorityAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (index : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (revisedLivingRootAt oldVisit) (temporalVisitAtFrom oldVisit index)
          (visitEntryAtFrom oldVisit index)
  | 0 => initialAuthorityAtFrom oldVisit
  | index + 1 =>
      (authorityAtFrom oldVisit index).next (nextEqAtFrom oldVisit index)

abbrev inquiryAuthorityAtFrom
    (oldVisit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (revisedLivingRootAt oldVisit) (temporalVisitAtFrom oldVisit index)
        (inquiryEntryReadoutAtFrom oldVisit index) := by
  rw [← visitEntry_eq_inquiryReadout_atFrom oldVisit index]
  exact authorityAtFrom oldVisit index

/-! Definitionally specialized initial-old-visit facade. -/

abbrev initialOldVisit := jointRoot.toAuthoritativeRoot.toRoot.initialVisit

def temporalVisitAt (index : Nat) :=
  temporalVisitAtFrom initialOldVisit index

def inquiryEventAt (index : Nat) :=
  inquiryEventAtFrom initialOldVisit index

def inquiryEntryReadoutAt (index : Nat) :=
  inquiryEntryReadoutAtFrom initialOldVisit index

theorem nextEq (index : Nat) :
    (revisedLivingRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (revisedVisitAt index).current).nextCurrent? =
      some (revisedVisitAt (index + 1)).current :=
  nextEqAtFrom initialOldVisit index

theorem temporalVisit_next_eq (index : Nat) :
    (temporalVisitAt index).next (nextEq index) =
      temporalVisitAt (index + 1) :=
  temporalVisit_next_eq_atFrom initialOldVisit index

theorem canonicalTargetReadout_eq (index : Nat) :
    revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
        (nextEq index) (inquiryEntryReadoutAt index) =
      inquiryEntryReadoutAt (index + 1) :=
  canonicalTargetReadout_eq_atFrom initialOldVisit index

def visitEntryAt (index : Nat) :=
  visitEntryAtFrom initialOldVisit index

theorem visitEntry_eq_inquiryReadout (index : Nat) :
    visitEntryAt index = inquiryEntryReadoutAt index :=
  visitEntry_eq_inquiryReadout_atFrom initialOldVisit index

def initialAuthority := initialAuthorityAtFrom initialOldVisit

def authorityAt (index : Nat) :=
  authorityAtFrom initialOldVisit index

abbrev inquiryAuthorityAt (index : Nat) :=
  inquiryAuthorityAtFrom initialOldVisit index

end
end M9ProofCarryingRenewalU8RevisedAuthority
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedAuthority.visitEntry_eq_inquiryReadout_atFrom
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedAuthority.inquiryAuthorityAtFrom
