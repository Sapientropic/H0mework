import H0mework.Realization.Audit.CausalLedgerRoot

/-!
# Living authority over a provenance-carrying residual audit root

The audit source, finite patch, failure projection, U7 row and minimal coface
share one concrete origin-bearing occurrence.  This generic layer does not
claim that an arbitrary origin belongs to a domain root; authoritative use is
through a source-indexed generated transition.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedCausalResidualAudit

open RootGeneratedProofRelevantRestructuring
open RootGeneratedResidualAdmission
open RootGeneratedResidualAuditLedger
open ObstructionGeneratedMinimalCoface

universe u

section Restructuring

variable (N : WorldRelationNetwork.{u}) (focus : N.Support)
variable (Residual : Type u) (distinguished : Residual)
variable [Subsingleton Residual]
variable (Origin : Type u) (distinguishedOrigin : Origin)

theorem causalAuditPatch_destination_eq
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current)
    (entry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.account.supportOf occurrence)) :
    ((causalAuditPatch N focus Residual distinguished Origin
      distinguishedOrigin occurrence).toLedgerWriteEvolution.destination
        entry).1 = entry := by
  cases causalAuditOccurrence_eq_emitted N focus Residual Origin
    distinguishedOrigin occurrence
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl _ => rfl
  | inr coordinate =>
      cases Subsingleton.elim coordinate distinguished
      rcases opened with ⟨⟨support_eq⟩⟩
      cases support_eq
      rfl

theorem causalAuditPatch_origin_eq
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current)
    (entry : OpenResponsibilityAt (ExtendedNetwork N focus Residual)
      ((causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.account.supportOf occurrence)) :
    ((causalAuditPatch N focus Residual distinguished Origin
      distinguishedOrigin occurrence).toLedgerWriteEvolution.origin
        entry).1 = entry := by
  cases causalAuditOccurrence_eq_emitted N focus Residual Origin
    distinguishedOrigin occurrence
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl _ => rfl
  | inr coordinate =>
      cases Subsingleton.elim coordinate distinguished
      rcases opened with ⟨⟨support_eq⟩⟩
      cases support_eq
      rfl

def causalAuditRestructuringLaw : SourceNativeLedgerRestructuringLaw
    (causalAuditSource N focus Residual Origin distinguishedOrigin) :=
  RootGeneratedProofRelevantRestructuring.law
    (ExtendedNetwork N focus Residual) focus
    (causalAuditSource N focus Residual Origin distinguishedOrigin)

def causalAuditRestructuringCertification
    {current : AuditV.Current}
    (occurrence :
      (causalAuditSource N focus Residual Origin distinguishedOrigin
        ).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (causalAuditRestructuringLaw N focus Residual Origin distinguishedOrigin)
      ((causalAuditCompiler N focus Residual distinguished Origin
        distinguishedOrigin).compile occurrence) := by
  cases causalAuditOccurrence_eq_emitted N focus Residual Origin
    distinguishedOrigin occurrence
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right equality =>
      (causalAuditPatch_origin_eq N focus Residual distinguished Origin
        distinguishedOrigin
        (causalAuditEmitted N focus Residual Origin distinguishedOrigin current)
        left).symm.trans
        (equality.trans
          (causalAuditPatch_origin_eq N focus Residual distinguished Origin
            distinguishedOrigin
            (causalAuditEmitted N focus Residual Origin distinguishedOrigin current)
            right)))
    (fun left right equality =>
      (causalAuditPatch_destination_eq N focus Residual distinguished Origin
        distinguishedOrigin
        (causalAuditEmitted N focus Residual Origin distinguishedOrigin current)
        left).symm.trans
        (equality.trans
          (causalAuditPatch_destination_eq N focus Residual distinguished Origin
            distinguishedOrigin
            (causalAuditEmitted N focus Residual Origin distinguishedOrigin current)
            right)))

def causalAuditRestructuringSource : SourceNativeRestructuringLedgerSource
    (ExtendedNetwork N focus Residual) AuditV where
  source := causalAuditSource N focus Residual Origin distinguishedOrigin
  compiler :=
    { ledgerCompiler := causalAuditCompiler N focus Residual distinguished
        Origin distinguishedOrigin
      restructuringLaw := causalAuditRestructuringLaw N focus Residual Origin
        distinguishedOrigin
      certifyRestructuring := causalAuditRestructuringCertification N focus
        Residual distinguished Origin distinguishedOrigin }

end Restructuring

section Authority

variable (N : WorldRelationNetwork.{u}) (focus : N.Support)
variable (Residual : Type u) (distinguished : Residual)
variable [Subsingleton Residual]
variable (Origin : Type u) (distinguishedOrigin : Origin)
variable (oldTheory : TheoryState N)
variable (oldU7 : U7ProducerCalculus N)
variable (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)

abbrev CausalResidualWorld := ExtendedNetwork N focus Residual

abbrev causalExtendedU7 : U7ProducerCalculus
    (CausalResidualWorld N focus Residual) :=
  extendU7 (Residual := Residual) focus oldU7

abbrev causalExtendedCalculus : U7ObstructionEvolutionCalculus
    (CausalResidualWorld N focus Residual)
    (causalExtendedU7 N focus Residual oldU7) :=
  extendU7Calculus (Residual := Residual) focus oldU7 oldCalculus

abbrev causalFailure := residualFailure focus oldTheory distinguished

def causalAuditFailureProjectionLaw : SourceNativeProjectionLaw
    (causalAuditRestructuringSource N focus Residual distinguished Origin
      distinguishedOrigin).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _ {_current} _occurrence _active =>
    SourceNativeRootExpressibilityFailureTokenAt
      (causalFailure N focus Residual distinguished oldTheory)
      (causalExtendedCalculus N focus Residual oldU7 oldCalculus)
      ((causalExtendedCalculus N focus Residual oldU7 oldCalculus).source.emit
        (residualObstruction focus distinguished))
  project := fun _ {_current} _occurrence _active => .canonical

def causalAuditAuthoritySource : SourceNativeAuthoritySource
    (CausalResidualWorld N focus Residual) AuditV where
  restructuringSource := causalAuditRestructuringSource N focus Residual
    distinguished Origin distinguishedOrigin
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      (causalAuditRestructuringSource N focus Residual distinguished Origin
        distinguishedOrigin)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := liftTheory focus oldTheory
  projectionLaw := causalAuditFailureProjectionLaw N focus Residual
    distinguished Origin distinguishedOrigin oldTheory oldU7 oldCalculus

def causalAuditAuthoritativeRoot : SourceNativeAuthoritativeRootClosure
    (CausalResidualWorld N focus Residual) AuditV where
  source := causalAuditAuthoritySource N focus Residual distinguished Origin
    distinguishedOrigin oldTheory oldU7 oldCalculus
  emitted := causalAuditEmitted N focus Residual Origin distinguishedOrigin
  compiler_commutes := fun _ => rfl

def causalAuditLivingRoot : SourceNativeLivingRootClosure
    (CausalResidualWorld N focus Residual) AuditV :=
  (causalAuditAuthoritativeRoot N focus Residual distinguished Origin
    distinguishedOrigin oldTheory oldU7 oldCalculus).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

abbrev causalAuditVisit : SourceNativeTemporalVisitAt
    (causalAuditLivingRoot N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus
      ).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (causalAuditLivingRoot N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus
      ).toAuthoritativeRoot.toRoot.initialVisit

def causalAuditInitialGenerated :=
  (causalAuditLivingRoot N focus Residual distinguished Origin
    distinguishedOrigin oldTheory oldU7 oldCalculus
    ).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (causalAuditVisit N focus Residual distinguished Origin
        distinguishedOrigin oldTheory oldU7 oldCalculus)

def causalAuditInitialRow :=
  ((causalAuditInitialGenerated N focus Residual distinguished Origin
    distinguishedOrigin oldTheory oldU7 oldCalculus).canonicalGeneratedEntryRow?
      (residualEntry focus distinguished)).get (by rfl)

def causalAuditLivingCausalAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (causalAuditLivingRoot N focus Residual distinguished Origin
        distinguishedOrigin oldTheory oldU7 oldCalculus)
      (causalAuditVisit N focus Residual distinguished Origin
        distinguishedOrigin oldTheory oldU7 oldCalculus)
      (residualEntry focus distinguished) :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    (causalAuditLivingRoot N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus)
    (residualEntry focus distinguished) .initial).get (by rfl)).2

theorem causalAuditRootDispositionCommutes :
    U7DemandEntryRootDispositionCommutesAt
      (causalExtendedCalculus N focus Residual oldU7 oldCalculus)
      ((causalExtendedCalculus N focus Residual oldU7 oldCalculus).source.emit
        (residualObstruction focus distinguished))
      (residualEntry focus distinguished)
      (((causalAuditLivingRoot N focus Residual distinguished Origin
        distinguishedOrigin oldTheory oldU7 oldCalculus
          ).toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
          ((causalAuditLivingRoot N focus Residual distinguished Origin
            distinguishedOrigin oldTheory oldU7 oldCalculus).emitted
              (causalAuditVisit N focus Residual distinguished Origin
                distinguishedOrigin oldTheory oldU7 oldCalculus).current)
        ).entryDisposition (residualEntry focus distinguished)) := by
  constructor
  · exact heq_of_eq
      (residual_u7_demand_entry focus oldU7 oldCalculus distinguished).symm
  · rfl

def causalAuditFailureFace : SourceNativeRootExpressibilityFailureFaceAt
    (causalAuditLivingRoot N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus).toAuthoritativeRoot
    (causalAuditVisit N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus)
    (U7 := causalExtendedU7 N focus Residual oldU7)
    (causalFailure N focus Residual distinguished oldTheory) where
  lawSurface_eq := rfl
  projection := PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  calculus := causalExtendedCalculus N focus Residual oldU7 oldCalculus
  u7Event :=
    (causalExtendedCalculus N focus Residual oldU7 oldCalculus).source.emit
      (residualObstruction focus distinguished)
  u7Event_eq_emit := rfl
  theoryAudit := residual_u7_theoryAudit focus oldU7 oldCalculus distinguished
  support_eq := rfl
  rootEntry := residualEntry focus distinguished
  rootEntryAtFailure_eq := rfl
  rootDispositionCommutes := causalAuditRootDispositionCommutes N focus
    Residual distinguished Origin distinguishedOrigin oldTheory oldU7
      oldCalculus
  project_heq := HEq.rfl

def causalAuditSuccessor : CausalEntrySuccessorAt
    (causalAuditLivingRoot N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus
      ).toAuthoritativeRoot.toLedgerRoot
    (causalAuditVisit N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus)
    (residualEntry focus distinguished) :=
  CausalEntrySuccessorAt.ofNonterminal rfl

def causalAuditRootedFailure : RootedActualExpressibilityFailureAt
    (causalAuditLivingRoot N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus).toAuthoritativeRoot
    (causalAuditVisit N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus)
    (causalExtendedU7 N focus Residual oldU7)
    (causalFailure N focus Residual distinguished oldTheory) :=
  RootedActualExpressibilityFailureAt.ofRootFailureFace
    (causalAuditFailureFace N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus)
    (causalAuditLivingCausalAuthority N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus).toAuthoritativeAuthority
    (causalAuditSuccessor N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus)

def causalAuditGeneratedMinimalCoface : GeneratedMinimalCofaceAt
    (causalAuditRootedFailure N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus) :=
  root_obstruction_generates_minimal_coface
    (causalAuditRootedFailure N focus Residual distinguished Origin
      distinguishedOrigin oldTheory oldU7 oldCalculus)

end Authority

end RootGeneratedCausalResidualAudit
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
