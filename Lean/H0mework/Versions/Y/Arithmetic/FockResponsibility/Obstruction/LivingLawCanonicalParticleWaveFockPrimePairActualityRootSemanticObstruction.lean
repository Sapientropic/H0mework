import H0mework.Foundation.Responsibility.DebtObstructionSemantics
import H0mework.Versions.Y.Arithmetic.FockResponsibility.DirectResponsibility

/-!
# Prime-pair actuality residual in root semantics

The legacy settlement-classifier source remains useful only as a negative
diagnostic.  Its faithful residual keeps the same live claim, lineage and
budget through U7.  Because the residual is already a literal obstruction of
the extended root world, root semantics answers it in the old language;
there is no expressibility failure, U8 revision or ordinary successor.

This file is not the target-six positive controller.  That controller is
driven solely by the source-generated physical action.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityRootSemanticObstruction

open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDirectResponsibility
open RootGeneratedDebtActivationDirect
open RootGeneratedDebtActivationDirectObstruction

noncomputable section

def generatedObstructionOfResidual
    (depth : Nat)
    (residual : PrimePairActualityObstructionAt (Actuality depth)) :
    GeneratedObstructionAt
      (ParticleWaveFockPrimePairActualityDirectResponsibility.source depth) := by
  let activation :=
    ParticleWaveFockPrimePairActualityDirectResponsibility.source depth
  generalize sourceGenerated : activation.generatedDisposition = disposition
  cases disposition with
  | supportTerminal closed =>
      exact False.elim ((open_supportTerminal_isEmpty depth).false closed)
  | step paid =>
      exact False.elim <| (open_step_isEmpty_of_residual depth residual).false
        ⟨_, paid⟩
  | obstruction obstruction =>
      exact GeneratedObstructionAt.ofGenerated obstruction sourceGenerated

def rootSemanticInquiryAuditOfResidual
    (depth : Nat)
    (residual : PrimePairActualityObstructionAt (Actuality depth)) :=
  RootGeneratedDebtActivationDirectObstruction.RootSemantic.inquiryAudit
    (generatedObstructionOfResidual depth residual)
    ParticleWaveFockPrimePairActualityDirectResponsibility.oldU7
    ParticleWaveFockPrimePairActualityDirectResponsibility.oldU7Calculus

theorem residual_rootSemantic_failure_isEmpty
    (depth : Nat)
    (residual : PrimePairActualityObstructionAt (Actuality depth)) :
    IsEmpty (ActualExpressibilityFailure
      (TheoryState.rootSemantic
        (ParticleWaveFockPrimePairActualityDirectResponsibility.source depth).World)
      (RootGeneratedDebtActivationDirectObstruction.RootSemantic.obstruction
        (generatedObstructionOfResidual depth residual))) :=
  RootSemantic.actualExpressibilityFailure_isEmpty
    (generatedObstructionOfResidual depth residual)

theorem residual_no_ordinary_sourceLedger_installation
    (depth : Nat)
    (residual : PrimePairActualityObstructionAt (Actuality depth))
    {RootV : Vocabulary}
    (rootSource : SourceNativeSource
      (ParticleWaveFockPrimePairActualityDirectResponsibility.source depth).World
      RootV)
    (rootCurrent : RootV.Current)
    (event : rootSource.law.EventAt rootCurrent
      ⟨(ParticleWaveFockPrimePairActualityDirectResponsibility.source depth
        ).lowerSupport,
        some (ParticleWaveFockPrimePairActualityDirectResponsibility.source depth
          ).state⟩) :
    IsEmpty (GeneratedSourceNativeLedgerInstallationAt
      (ParticleWaveFockPrimePairActualityDirectResponsibility.source depth)
      rootSource rootCurrent event) :=
  (generatedObstructionOfResidual depth residual).noSourceLedgerInstallation
    rootSource rootCurrent event

end

end ParticleWaveFockPrimePairActualityRootSemanticObstruction
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
