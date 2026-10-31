import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Identification.FullDomainRepairAuthorityObstruction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization

/-!
# M14 direct consumer for full-domain repair authority

The full-domain observer now enters the generic `AuthorityObserver/K`
machinery.  Its visible image cannot carry the canonical-repair readout, and
no observer-factored identification, policy, or probability readout can be
authority-complete.  Exact source origins nevertheless continue to generate
their proof-carrying repairs.

The positive refinement adds only the existing pre-emitter `failureKind`.
It preserves the coarse observation, separates the exact origin carrier, and
lets the already installed repair compiler factor the canonical repair.  No
caller label, probability measure, occurrence trace, or second repair law is
introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingFullDomainRepairAuthorityObstructionRegression

noncomputable section

open UBI Policy
open Observer
open M14UBIPeriodicRootHistory
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14FullDomainReachabilityCollision
open M14FullDomainRepairAuthorityObstruction

universe uOutput

/-! ## Exact source readout and coarse-observer obstruction -/

def canonicalRepairReadoutAt (depth : Nat) :
    OccurrenceReadout (RepairFailureOriginAt depth) ExactExitRepair where
  read := canonicalRepairAt

def canonicalRepairReadoutAuthorityCompleteAt (depth : Nat) :
    AuthorityCompleteReadoutAt (fullDomainRepairObserverAt depth)
      (canonicalRepairReadoutAt depth) where
  decodeAuthority := id
  readsActualAuthority := fun _origin => rfl

theorem canonicalRepairReadout_not_fullDomain_factorizable
    (depth : Nat) :
    ¬ Nonempty (ReadoutFactorization (fullDomainRepairObserverAt depth)
      (canonicalRepairReadoutAt depth)) := by
  rintro ⟨factorization⟩
  exact (fullDomainRepairCanonicalDirectionAt depth)
    |>.boundary_rejectsAuthorityCompleteReadout factorization
      (canonicalRepairReadoutAuthorityCompleteAt depth)

/-- Data-processing form of the no-go: every readout that factors through
the coarse full-domain observer fails authority completeness, at any output
universe. -/
theorem fullDomain_factoredReadout_not_authorityComplete
    (depth : Nat)
    {Output : Type uOutput}
    (readout : OccurrenceReadout (RepairFailureOriginAt depth) Output)
    (factorization : ReadoutFactorization
      (fullDomainRepairObserverAt depth) readout) :
    ¬ Nonempty (AuthorityCompleteReadoutAt
      (fullDomainRepairObserverAt depth) readout) :=
  (fullDomainRepairCanonicalDirectionAt depth)
    |>.boundary_noAuthorityCompleteReadout factorization

theorem every_origin_generates_proofCarryingRepair
    (depth : Nat) (origin : RepairFailureOriginAt depth) :
    SourceGeneratedProofCarryingExitRepairAt origin
      ((canonicalRepairReadoutAt depth).read origin) :=
  SourceGeneratedProofCarryingExitRepairAt.generate origin

/-! ## Positive source refinement by the existing failure kind -/

abbrev FailureKindRefinedFullDomainVisible :=
  FullDomainReachabilityObservation × ExactExitFailureKind

def failureKindRefinedFullDomainRepairObserverAt (depth : Nat) :
    AuthorityObserver (RepairFailureOriginAt depth)
      FailureKindRefinedFullDomainVisible ExactExitRepair where
  forget := fun origin =>
    (fullDomainReachabilityObservationAt depth origin, origin.failureKind)
  authorityK := canonicalRepairAt

@[simp] theorem failureKindRefinement_preserves_coarse
    (depth : Nat) (origin : RepairFailureOriginAt depth) :
    ((failureKindRefinedFullDomainRepairObserverAt depth).forget origin).1 =
      (fullDomainRepairObserverAt depth).forget origin :=
  rfl

theorem failureKindRefinement_forget_injective (depth : Nat) :
    Function.Injective
      (failureKindRefinedFullDomainRepairObserverAt depth).forget := by
  intro left right equal
  have kindsEqual := congrArg Prod.snd equal
  cases left with
  | tenureCapture leftFailure =>
      cases right with
      | tenureCapture rightFailure => congr
      | routeBottleneck rightFailure => cases kindsEqual
  | routeBottleneck leftFailure =>
      cases right with
      | tenureCapture rightFailure => cases kindsEqual
      | routeBottleneck rightFailure => congr

def canonicalRepair_failureKindRefined_factorizationAt (depth : Nat) :
    ReadoutFactorization
      (failureKindRefinedFullDomainRepairObserverAt depth)
      (canonicalRepairReadoutAt depth) where
  visibleReadout := fun visible =>
    (periodicUBISourceAt depth).installed.payload.consumer.repairAt visible.2
  factorizes := fun _origin => rfl

def canonicalRepair_failureKindRefined_authorityCompleteAt (depth : Nat) :
    AuthorityCompleteReadoutAt
      (failureKindRefinedFullDomainRepairObserverAt depth)
      (canonicalRepairReadoutAt depth) where
  decodeAuthority := id
  readsActualAuthority := fun _origin => rfl

def failureKindRefined_repairAuthorityFactorizationAt (depth : Nat) :
    AuthorityFactorization
      (failureKindRefinedFullDomainRepairObserverAt depth) :=
  (canonicalRepair_failureKindRefined_factorizationAt depth)
    |>.toAuthorityFactorization
      (canonicalRepair_failureKindRefined_authorityCompleteAt depth)

/-! ## Complete obstruction readout -/

theorem fullDomainRepairAuthorityNoGos (depth : Nat) :
    (¬ Nonempty (AuthorityFactorization
        (fullDomainRepairObserverAt depth))) ∧
      (¬ ∃ reconstruct : FullDomainReachabilityObservation →
          RepairFailureOriginAt depth,
        Function.LeftInverse reconstruct
          (fullDomainRepairObserverAt depth).forget) ∧
      (¬ Nonempty (FaithfulAuthorityReconstruction
        (fullDomainRepairObserverAt depth))) ∧
      (¬ Nonempty (NaturalSurrogateSection
        (fullDomainRepairObserverAt depth))) ∧
      (¬ Nonempty (NaturalAuthorityReconstruction
        (fullDomainRepairObserverAt depth))) := by
  let direction := fullDomainRepairCanonicalDirectionAt depth
  let vertical := fullDomainRepairVerticalAt depth
  exact
    ⟨direction.boundary_noAuthorityFactorization,
      direction.boundary_noOccurrenceLeftInverse,
      direction.boundaryKernelPair.noFaithfulAuthorityReconstruction,
      vertical.noNaturalSurrogateSection,
      direction.boundary_noNaturalAuthorityReconstruction⟩

theorem fullDomainRepairObstructionAt (depth : Nat) :
    Nonempty (AuthorityKernelPair (fullDomainRepairObserverAt depth)) ∧
      Nonempty (AuthorityChangingVerticalAutomorphism
        (fullDomainRepairObserverAt depth)) ∧
      Nonempty (RootedObserverObstructionAt
        (fullDomainRepairVerticalAt depth)) ∧
      Nonempty (SourceGeneratedObserverAttachingDirectionAt
        (fullDomainRepairRootedObserverObstructionAt depth)) :=
  ⟨⟨fullDomainRepairKernelPairAt depth⟩,
    ⟨fullDomainRepairVerticalAt depth⟩,
    ⟨fullDomainRepairRootedObserverObstructionAt depth⟩,
    ⟨fullDomainRepairCanonicalDirectionAt depth⟩⟩

theorem failureKindRefinementControls (depth : Nat) :
    (∀ origin : RepairFailureOriginAt depth,
      ((failureKindRefinedFullDomainRepairObserverAt depth).forget origin).1 =
        (fullDomainRepairObserverAt depth).forget origin) ∧
      Function.Injective
        (failureKindRefinedFullDomainRepairObserverAt depth).forget ∧
      Nonempty (ReadoutFactorization
        (failureKindRefinedFullDomainRepairObserverAt depth)
        (canonicalRepairReadoutAt depth)) ∧
      Nonempty (AuthorityFactorization
        (failureKindRefinedFullDomainRepairObserverAt depth)) :=
  ⟨failureKindRefinement_preserves_coarse depth,
    failureKindRefinement_forget_injective depth,
    ⟨canonicalRepair_failureKindRefined_factorizationAt depth⟩,
    ⟨failureKindRefined_repairAuthorityFactorizationAt depth⟩⟩

structure ProofCarryingFullDomainRepairAuthorityObstructionCertificate : Prop where
  everyDepthObstruction : ∀ depth : Nat,
    Nonempty (AuthorityKernelPair (fullDomainRepairObserverAt depth)) ∧
      Nonempty (AuthorityChangingVerticalAutomorphism
        (fullDomainRepairObserverAt depth)) ∧
      Nonempty (RootedObserverObstructionAt
        (fullDomainRepairVerticalAt depth)) ∧
      Nonempty (SourceGeneratedObserverAttachingDirectionAt
        (fullDomainRepairRootedObserverObstructionAt depth))
  noGos : ∀ depth : Nat,
    (¬ Nonempty (AuthorityFactorization
        (fullDomainRepairObserverAt depth))) ∧
      (¬ ∃ reconstruct : FullDomainReachabilityObservation →
          RepairFailureOriginAt depth,
        Function.LeftInverse reconstruct
          (fullDomainRepairObserverAt depth).forget) ∧
      (¬ Nonempty (FaithfulAuthorityReconstruction
        (fullDomainRepairObserverAt depth))) ∧
      (¬ Nonempty (NaturalSurrogateSection
        (fullDomainRepairObserverAt depth))) ∧
      (¬ Nonempty (NaturalAuthorityReconstruction
        (fullDomainRepairObserverAt depth)))
  canonicalRepairNotCoarseFactorized : ∀ depth : Nat,
    ¬ Nonempty (ReadoutFactorization (fullDomainRepairObserverAt depth)
      (canonicalRepairReadoutAt depth))
  everySourceAwareRepair : ∀ (depth : Nat)
    (origin : RepairFailureOriginAt depth),
    SourceGeneratedProofCarryingExitRepairAt origin
      ((canonicalRepairReadoutAt depth).read origin)
  sourceRefinement : ∀ depth : Nat,
    (∀ origin : RepairFailureOriginAt depth,
      ((failureKindRefinedFullDomainRepairObserverAt depth).forget origin).1 =
        (fullDomainRepairObserverAt depth).forget origin) ∧
      Function.Injective
        (failureKindRefinedFullDomainRepairObserverAt depth).forget ∧
      Nonempty (ReadoutFactorization
        (failureKindRefinedFullDomainRepairObserverAt depth)
        (canonicalRepairReadoutAt depth)) ∧
      Nonempty (AuthorityFactorization
        (failureKindRefinedFullDomainRepairObserverAt depth))

theorem proofCarryingFullDomainRepairAuthorityObstructionDirectConsumer :
    ProofCarryingFullDomainRepairAuthorityObstructionCertificate where
  everyDepthObstruction := fullDomainRepairObstructionAt
  noGos := fullDomainRepairAuthorityNoGos
  canonicalRepairNotCoarseFactorized :=
    canonicalRepairReadout_not_fullDomain_factorizable
  everySourceAwareRepair := every_origin_generates_proofCarryingRepair
  sourceRefinement := failureKindRefinementControls

end
end M14ProofCarryingFullDomainRepairAuthorityObstructionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainRepairAuthorityObstructionRegression.canonicalRepairReadout_not_fullDomain_factorizable
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainRepairAuthorityObstructionRegression.fullDomain_factoredReadout_not_authorityComplete
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainRepairAuthorityObstructionRegression.failureKindRefinement_forget_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainRepairAuthorityObstructionRegression.proofCarryingFullDomainRepairAuthorityObstructionDirectConsumer
