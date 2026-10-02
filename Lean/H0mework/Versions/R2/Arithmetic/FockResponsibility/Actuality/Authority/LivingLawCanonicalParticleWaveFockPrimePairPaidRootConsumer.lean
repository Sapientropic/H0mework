import H0mework.Versions.R2.Foundation.Runtime.GatedClaimPaidRoot
import H0mework.Versions.R2.Arithmetic.FockResponsibility.Actuality.Runtime.LivingLawCanonicalParticleWaveFockPrimePairGatedClaimCurrent
import H0mework.Versions.R2.Arithmetic.FockResponsibility.Actuality.Regression.LivingLawCanonicalParticleWaveFockPrimePairActualityDebtRegression

/-! Target six consumes the generic paid-root authority end to end. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairPaidRootConsumer

open GatedClaimPreProcess GatedClaimPaidRoot GatedClaimRootAuthority
open ParticleWaveFockPrimePairGatedClaimCurrent
open ParticleWaveFockPrimePairPendingClaimBirth
open ParticleWaveFockPrimePairActualityDebt
open ParticleWaveFockPrimePairActualityDebtRegression

noncomputable section

def targetSixAdvance :
    SourceNativeGatedClaimAdvanceAt (gatedCurrent 1) :=
  SourceNativeGatedClaimAdvanceAt.generate (gatedCurrent 1) depthOnePayment

def targetSixSupportTerminal :
    (pendingClaimBirth 1).law.SupportTerminalAt
      targetSixAdvance.targetState := by
  change SettlementAt (.settled depthOneSettlement)
  exact .actual depthOneSettlement

def targetSixWholeTerminal :
  SourceNativeGatedClaimWholeTerminalAt targetSixAdvance.targetCurrent :=
  SourceNativeGatedClaimWholeTerminalAt.ofSupportTerminal
    targetSixSupportTerminal

def targetSixInput : InputAt (pendingClaimBirth 1) where
  advance := targetSixAdvance
  terminal := targetSixWholeTerminal

def targetSixPendingAuthority := pendingDebtCausalAuthority targetSixInput

def targetSixPaidAuthority := paidDebtCausalAuthority targetSixInput

theorem target_six_root_payment_is_strict :
    targetSixInput.advance.targetCurrent.entry.progressBudget <
      (gatedCurrent 1).entry.progressBudget :=
  targetSixInput.advance.strict_debit

theorem target_six_root_discharges_actuality_claim :
    ((authoritativeRoot targetSixInput).generatedLedgerAt .paid
      ).entryDisposition targetSixInput.advance.targetCurrent.entry =
        .terminal (paidDebtTerminal targetSixInput) :=
  paid_debt_disposition_is_terminal targetSixInput

end

end ParticleWaveFockPrimePairPaidRootConsumer
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
