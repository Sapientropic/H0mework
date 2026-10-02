import H0mework.Versions.R2.Physics.RootHistory.PhysicalRootClosure
import H0mework.Versions.R2.Physics.RootHistory.PhysicalRootRuntime

/-!
# Stage Ten physical root-current admission regression

Checks the public admission mouth of the fixed physical root.  Raw
configurations cannot construct a current; private final credentials cannot be
caller-built; and source, occurrence, target, or presentation parameters cannot
fork the generated closure or typed answer-and-next.
-/

namespace SaturationMonoid.PhysicsCore.StageTenPhysicalRootCurrentAdmissionRegression

open ProofFreeRicherAnholonomicSource
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyDirectPrefixQuadraticCoframeBoundary
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageTenPhysicalRoot

set_option autoImplicit false

noncomputable section

theorem registered_current_has_one_native_action
    (current : RootCurrent)
    (action : ActionAt current) :
    action = rootActionAt current := by
  cases action
  rfl

theorem raw_configuration_cannot_mint_root_current
    (_configuration : StageNineHolonomicConfiguration) : True := by
  fail_if_success
    exact RootCurrent.mk (.assembly quadraticCofaceSettlement _configuration)
  trivial

theorem action_index_cannot_mint_root_current
    (_configuration : StageNineHolonomicConfiguration) : True := by
  fail_if_success
    exact
      (⟨_, ActionAt.assembly quadraticCofaceSettlement _configuration⟩ :
        Sigma ActionAt).1
  trivial

theorem closure_constructor_is_not_public : True := by
  fail_if_success
    let _leaked := StageTenPhysicalRootClosure.mk
  trivial

theorem authority_receipt_constructor_is_not_public : True := by
  fail_if_success
    let _leaked := ZeroUnregisteredPhysicalAuthorityReceipt.mk
  trivial

theorem arbitrary_source_cannot_change_fixed_closure
    (_source : SmoothUnifiedSource)
    (candidate : StageTenPhysicalRootClosure) :
    candidate = stageTenPhysicalRootClosure :=
  candidate.eq_generated

theorem gravity_event_cannot_be_cast_to_sibling_visit : True := by
  fail_if_success
    exact
      (stageTenPhysicalRootClosure.gravityEvent :
        ExactTemporalCausalRootEventAt sourceNativeRoot initialTemporalVisit)
  trivial

/-- An activated occurrence cannot be replayed at the next registered Physics
current, even though both belong to the same source and compiler. -/
theorem boundary_runtime_tick_cannot_replay_at_coface : True := by
  fail_if_success
    exact (physicalRuntimeSeed.tick :
      ExactActivatedRootOccurrenceAt physicalRuntimeAfterBoundary)
  trivial

/-- The five named Stage-Ten rows are a prefix.  The post-assembly occurrence
is another native write and source-generates a further runtime state. -/
theorem postAssembly_runtime_remains_living :
    Nonempty (LivingRuntimeState physicalRuntimeProcess) :=
  ⟨physicalRuntimeAfterAssembly.tick.next⟩

/-- The boundary coordinate cannot multiply one old failure across arbitrary
presentation points.  Its dependent evidence retains the source-generated
singular point. -/
theorem boundary_obstruction_evidence_fixes_source_point
    {support : RootCurrent} {point : BasePoint}
    (evidence :
      (rootResidualAt support).coordinateAt .coframeBoundary point) :
    point =
      fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint :=
  evidence.down.2

private def futureAssemblyVisit :
    SourceNativeTemporalVisitAt sourceNativeRoot :=
  livingRootNextVisit afterAssemblyTemporalVisit

private def futureGravityVisit :
    SourceNativeTemporalVisitAt sourceNativeRoot :=
  livingRootNextVisit futureAssemblyVisit

/-- The complete-coordinate mouth remains active beyond the named five-row
prefix.  A later gravity first-jet effect is answered at that exact visit and
cannot disappear behind a prefix-only authority receipt. -/
theorem future_gravity_firstJet_effect_has_registered_U7
    (point : BasePoint)
    (evidence :
      (rootResidualAt futureGravityVisit.current).coordinateAt
        .gravityCoframeFirstJet point) :
    (rootResidualDemandAt .gravityCoframeFirstJet point evidence).entry =
        rootOccurrenceLedgerEntry
          (sourceNativeRoot.generatedAtTemporalVisit futureGravityVisit
            ).occurrence ∧
      Nonempty
        (SourceNativeRootResidualAnswerAndNextAt futureGravityVisit
          (rootResidualObstructionAt .gravityCoframeFirstJet point evidence)
          (rootCausalEntryAuthorityAt futureGravityVisit)) :=
  zeroUnregisteredPhysicalAuthorityReceipt.obstructionFactorizes
    futureGravityVisit .gravityCoframeFirstJet point evidence

theorem caller_target_cannot_replace_gravity_next
    (_target : StageNineHolonomicConfiguration)
    (candidate : SourceNativeLivingCausalEntryAnswerAndNextAt livingRoot
      afterCofaceTemporalVisit (rootLedgerEntry firstGravityCurrent)
      stageTenPhysicalRootClosure.gravityLiveAuthority) :
    candidate.nextCurrent.visit.current = firstAssemblyCurrent := by
  rw [SourceNativeLivingCausalEntryAnswerAndNextAt.eq candidate
    stageTenPhysicalRootGravityAnswerAndNext]
  exact stageTenPhysicalRootGravityAnswer_nextCurrent_eq_assembly

theorem free_parameter_cannot_fork_gravity_answer
    (_selector : Bool)
    (candidate : SourceNativeLivingCausalEntryAnswerAndNextAt livingRoot
      afterCofaceTemporalVisit (rootLedgerEntry firstGravityCurrent)
      stageTenPhysicalRootClosure.gravityLiveAuthority) :
    candidate = stageTenPhysicalRootGravityAnswerAndNext :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.eq _ _

end

end SaturationMonoid.PhysicsCore.StageTenPhysicalRootCurrentAdmissionRegression
