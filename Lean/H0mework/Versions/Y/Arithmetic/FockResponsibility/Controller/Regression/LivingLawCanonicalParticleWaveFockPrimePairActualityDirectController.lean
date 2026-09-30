import H0mework.Versions.Y.Arithmetic.FockResponsibility.Controller.LivingLawCanonicalParticleWaveFockPrimePairActualityTargetSixInactiveHandoff
import H0mework.Versions.Y.Arithmetic.FockResponsibility.Obstruction.LivingLawCanonicalParticleWaveFockPrimePairActualityRootSemanticObstruction

/-!
# Regression: Goldbach direct controller

The target-six named controller consumes the direct positive installation,
strictly pays its literal actuality row, generates a faithful terminal, and
only then hands control to the canonical arithmetic next current.  A residual
keeps the same live row, is answered in the root-semantic old language after
U7 audit, and has neither a U8 failure nor an ordinary source-ledger install.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityDirectControllerRegression

open CanonicalUnitArithmeticRoot
open DebtActivationLedger
open DebtActivationWorld
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDirectResponsibility
open ParticleWaveFockPrimePairActualityRootSemanticObstruction
open ParticleWaveFockPrimePairActualityTargetSixInactiveHandoff
open RootGeneratedDebtActivationDirectPositive
open RootGeneratedDebtActivationDirect
open RootGeneratedDebtActivationDirectObstruction

noncomputable section

/-- The named live root is the exact image of the previous direct
`NativeStepInstallationAt` mouth. -/
theorem targetSix_liveCompiler_is_directInstallation :
    (ledgerCompiler positive).compile (paymentOccurrence positive) =
      NativeStepInstallationAt.generated (directStepInstallation positive) :=
  liveCompiler_eq_directStepInstallation positive

/-- The source-generated branch, not a caller branch selector, inhabits that
same direct installation mouth. -/
def targetSix_generatedDirectInstallation :
    GeneratedSourceNativeLedgerInstallationAt Activation
      (rootSource positive) .live EventAt.payment :=
  generatedDirectStepInstallation positive

theorem targetSix_live_row_is_actuality_claim_and_unit_budget :
    Activation.liveDebtEntry.claim =
        .inr (ParticleWaveFockPrimePairActualityDirect.directRuntimeActuality 1).claim ∧
      Activation.liveDebtEntry.progressBudget = 1 :=
  ⟨ParticleWaveFockPrimePairActualityTargetSixActionDebt.liveDebtEntry_claim,
    ParticleWaveFockPrimePairActualityTargetSixActionDebt.liveDebtEntry_budget⟩

theorem targetSix_action_source_is_same_actuality_occurrence :
    Activation.lowerOccurrence =
      (ParticleWaveFockPrimePairActualityDirect.directRuntimeActuality 1
        ).sourceOccurrence :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.lowerOccurrence_eq_actualitySource

theorem targetSix_payment_is_strict :
    (debtEntry (N := BaseN) Activation.lowerSupport targetState
      ).progressBudget < Activation.liveDebtEntry.progressBudget :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.targetSixStrictDebit

theorem targetSix_paid_terminal_is_direct :
    (terminalPatch positive).toLedgerTerminalEvolution =
      ParticleWaveFockPrimePairActualityTargetSixActionDebt.targetSixWholeLedgerTerminal := by
  rfl

theorem targetSix_next_is_after_terminal :
    generatedTerminalHandoff.visit.current =
      CanonicalUnitArithmeticRoot.next Activation.lowerSupport :=
  generatedTerminalHandoff_is_inactive_next.2.2

theorem targetSix_has_no_obstruction_branch :
    IsEmpty (GeneratedObstructionAt Activation) :=
  GeneratedObstructionAt.isEmpty_of_generatedStep sourceDisposition_is_step

theorem targetSix_payment_current_has_no_old_depth_jump :
    (controllerAuthoritativeRoot.toRoot.evolutionAt
      (RootGeneratedDebtActivationDirectPositive.initialVisit positive).current
      ).nextCurrent? = some .paid :=
  rfl

theorem targetSix_action_step_forces_fourier_nonzero :
    ParticleWaveFockRuntimeExactPrimeFourierSibling.runtimePrimeOnlyFourierCoefficient
      1 ≠ 0 :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.actionStep_fourierCoefficient_ne_zero

/-- A faithful residual is not reclassified as a representation failure:
the generated inquiry audit takes the old-language-answer constructor. -/
theorem residual_audit_is_oldLanguageAnswered
    (depth : Nat)
    (residual : PrimePairActualityObstructionAt (Actuality depth)) :
    ParticleWaveFockPrimePairActualityRootSemanticObstruction.rootSemanticInquiryAuditOfResidual
        depth residual =
      .oldLanguageAnswered
        (RootSemantic.theoryAudit
          (ParticleWaveFockPrimePairActualityRootSemanticObstruction.generatedObstructionOfResidual
            depth residual)
          ParticleWaveFockPrimePairActualityDirectResponsibility.oldU7
          ParticleWaveFockPrimePairActualityDirectResponsibility.oldU7Calculus)
        (RootSemantic.oldLanguageAnswer
          (ParticleWaveFockPrimePairActualityRootSemanticObstruction.generatedObstructionOfResidual
            depth residual)) :=
  rfl

theorem residual_has_no_rootSemantic_expressibilityFailure
    (depth : Nat)
    (residual : PrimePairActualityObstructionAt (Actuality depth)) :
    IsEmpty (ActualExpressibilityFailure
      (TheoryState.rootSemantic
        (ParticleWaveFockPrimePairActualityDirectResponsibility.source depth).World)
      (RootSemantic.obstruction
        (ParticleWaveFockPrimePairActualityRootSemanticObstruction.generatedObstructionOfResidual
          depth residual))) :=
  ParticleWaveFockPrimePairActualityRootSemanticObstruction.residual_rootSemantic_failure_isEmpty
    depth residual

#print axioms targetSix_liveCompiler_is_directInstallation
#print axioms targetSix_live_row_is_actuality_claim_and_unit_budget
#print axioms targetSix_action_source_is_same_actuality_occurrence
#print axioms targetSix_payment_is_strict
#print axioms targetSix_paid_terminal_is_direct
#print axioms targetSix_next_is_after_terminal
#print axioms targetSix_has_no_obstruction_branch
#print axioms targetSix_action_step_forces_fourier_nonzero
#print axioms residual_audit_is_oldLanguageAnswered
#print axioms residual_has_no_rootSemantic_expressibilityFailure
#print axioms RootGeneratedDebtActivationDirectPositive.paymentPatch_evolution
#print axioms RootGeneratedDebtActivationDirectPositive.liveCompiler_eq_directStepInstallation
#print axioms RootGeneratedDebtActivationDirectPositive.liveCompiler_factors_generatedDirectMouth

end


end ParticleWaveFockPrimePairActualityDirectControllerRegression
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
