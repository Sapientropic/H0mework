import H0mework.Arithmetic.RiemannRuntime.PairedOmegaEffectRowMaterial

/-!
# Fixed-root runtime for the A1c paired-Omega effect row

The canonical unit-arithmetic authority is extended before emission by the
source-generated paired effect law.  The lower source, emitter and ledger
compiler are unchanged.  At the initial exact visit the installed effect row
factorizes through the same whole ledger and generates its causal successor;
the existing q-rich separator reads the row's `logNorm` field exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticRoot

noncomputable section

def runtimeEffectAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeEffectLaw observation nontrivial).toAuthoritySource
    authoritativeRoot.source

def runtimeEffectLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimeEffectAuthoritySource observation nontrivial
  terminalHandoff :=
    (runtimeEffectAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

/-- Fixed projection extension of the canonical arithmetic root.  It retains
the exact lower ledger source and emitter. -/
def runtimeEffectRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimeEffectLivingSource observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimeEffectRoot_reuses_lower_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeEffectRoot observation nontrivial).toAuthoritativeRoot.toLedgerRoot.source =
        ledgerSource ∧
      (runtimeEffectRoot observation nontrivial).emitted = emitted := by
  exact ⟨rfl, rfl⟩

theorem runtimeEffectRoot_projects_paired_occurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (((((((pairedJointActionOccurrence observation nontrivial
        (Character.GlobalCoPoissonCurrent.stageSqrtScaleUnit 0)).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst =
          CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence ∧
      (runtimeEffectRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimeEffectRoot observation nontrivial).emitted = emitted := by
  exact ⟨pairedJointActionOccurrence_projects_to_seed
      observation nontrivial _ ,
    runtimeEffectRoot_reuses_lower_source_emitter observation nontrivial⟩

def runtimeEffectRecognition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeEffectDynamicalRecognitionAt
      (runtimeEffectRoot observation nontrivial) where
  effectLaw := runtimeEffectLaw observation nontrivial
  installation :=
    SourceNativeProjectionLaw.InstallationAt.effectDynamicalComponent
      authoritativeRoot.source (runtimeEffectLaw observation nontrivial)

def runtimeEffectVisit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeTemporalVisitAt
      (runtimeEffectRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (runtimeEffectRoot observation nontrivial
    ).toAuthoritativeRoot.toRoot.initialVisit

def runtimeEffectSourceAuthority
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeEffectRecognition observation nontrivial).CausalEntryAuthorityAt
      (runtimeEffectVisit observation nontrivial)
      (rootLedgerEntry initialCurrent) :=
  ((SourceNativeEffectDynamicalRecognitionAt.CausalEntryAuthorityAt.generatedFromInitial?
      (runtimeEffectRecognition observation nontrivial)
      (rootLedgerEntry initialCurrent) .initial).get (by rfl)).2

def runtimeEffectRootedActive
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeEffectRecognition observation nontrivial).RootedActiveOutcomeAt
      (runtimeEffectVisit observation nontrivial) :=
  (runtimeEffectRecognition observation nontrivial
    ).generatedRootedActiveAtVisit
    (runtimeEffectVisit observation nontrivial) () rfl
    (runtimeEffectSourceAuthority observation nontrivial)

theorem installedRuntimeEffect_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    let registered := runtimeEffectRootedActive observation nontrivial
    let root := runtimeEffectRoot observation nontrivial
    let visit := runtimeEffectVisit observation nontrivial
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          (runtimeEffectRecognition observation nontrivial
            ).rootEffectProjection)
        registered.installedFiber ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit :=
  (runtimeEffectRootedActive observation nontrivial
    ).installedAuthority_factorizes

def installedRuntimeEffectOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (runtimeEffectLaw observation nontrivial).eventVocabulary.emit
    ((runtimeEffectRoot observation nontrivial).emitted
      (runtimeEffectVisit observation nontrivial).current)

def installedRuntimeEffectValue
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : RuntimeEffect :=
  (installedRuntimeEffectOccurrence observation nontrivial).effect

@[simp] theorem installedRuntimeEffectValue_eq_initial
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    installedRuntimeEffectValue observation nontrivial =
      generateRuntimeEffect observation nontrivial initialCurrent := by
  rfl

theorem installedRuntimeEffectValue_conservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (installedRuntimeEffectValue observation nontrivial).phase =
      (installedRuntimeEffectValue observation nontrivial).retained +
        (installedRuntimeEffectValue observation nontrivial).centeredTrace := by
  rw [installedRuntimeEffectValue_eq_initial]
  exact generateRuntimeEffect_conservation observation nontrivial initialCurrent

/-- Direct production consumer of the installed effect row. -/
theorem branchNormalizedSeparator_eq_installedRuntimeEffect
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat)
    (row : CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.FactorRow
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence.root
      stage) :
    InverseZeroFibre.branchNormalizedQRichSeparator
        (InverseZeroFibre.mathlibLeftRegressionComponent observation)
        stage row =
      -(CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.quotientCoefficient
          row : ℂ) *
        ((installedRuntimeEffectValue observation nontrivial).logNorm : ℂ) := by
  rw [installedRuntimeEffectValue_eq_initial]
  exact branchNormalizedSeparator_eq_pairedOmegaRootEffect
    observation nontrivial 0 stage row

def runtimeEffectCausalSuccessor
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeEffectRootedActive observation nontrivial).CausalSuccessorAt :=
  (runtimeEffectRootedActive observation nontrivial).generatedCausalClosure

def runtimeEffectTargetAuthority
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (runtimeEffectCausalSuccessor observation nontrivial).targetAuthority

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
