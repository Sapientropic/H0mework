import H0mework.Versions.R7e4da746.Arithmetic.RiemannRuntime.PairedOmegaFiniteEffectHistory

/-!
# Named runtime facade for the A1c paired-Omega effect

The facade names the installed effect and source-calculation components at
every source-reachable finite runtime state. Each readout factorizes through
the same compiler occurrence, whole ledger and generated next.
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

noncomputable section

inductive RuntimeEffectFace (observation : GeneratedRiemannZeroObservation)
  | pairedOmega
  | combCalculation (half : OriginalKCombCalculation.Half observation)
  | bFiniteCalculation (half : OriginalKCombCalculation.Half observation)
  | coefficientBSelfCalculation (half : OriginalKCombCalculation.Half observation)
  | exteriorArithmeticCalculation (half : OriginalKCombCalculation.Half observation) (column : Fin 3) (side : Fin 2) (cutoff : Nat)
  | wholeDebtRCalculation (half : OriginalKCombCalculation.Half observation)
  deriving DecidableEq

def runtimeEffectFacade
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRuntimeFacade CanonicalUnitArithmeticRoot.N where
  process := runtimeEffectProcess observation nontrivial
  FaceAt := fun _ => RuntimeEffectFace observation
  componentAt := fun _ face => match face with
    | .pairedOmega => (runtimeEffectRecognition observation nontrivial).effectComponent
    | .combCalculation _ => OriginalKCombCalculation.component observation nontrivial
    | .bFiniteCalculation _ => OriginalKBFiniteCalculation.component observation nontrivial
    | .coefficientBSelfCalculation _ => OriginalKCoefficientBSelfCalculation.component observation nontrivial
    | .exteriorArithmeticCalculation _ _ _ _ => OriginalKExteriorArithmeticCalculation.component observation nontrivial
    | .wholeDebtRCalculation _ => OriginalKWholeDebtRCalculationFace.component observation nontrivial
  installationAt := fun _ face => match face with
    | .pairedOmega => (runtimeEffectRecognition observation nontrivial).installation
    | .combCalculation _ => runtimeCombCalculationInstallation observation nontrivial
    | .bFiniteCalculation _ => runtimeBFiniteCalculationInstallation observation nontrivial
    | .coefficientBSelfCalculation _ => runtimeCoefficientBSelfCalculationInstallation observation nontrivial
    | .exteriorArithmeticCalculation _ _ _ _ => runtimeExteriorArithmeticCalculationInstallation observation nontrivial
    | .wholeDebtRCalculation _ => runtimeWholeDebtRCalculationInstallation observation nontrivial
  projectionAt := fun _ face => match face with
    | .pairedOmega => PUnit.unit
    | .combCalculation half => half
    | .bFiniteCalculation half => half
    | .coefficientBSelfCalculation half => half
    | .exteriorArithmeticCalculation half column side cutoff => (half, column, side, cutoff)
    | .wholeDebtRCalculation half => half

def runtimeEffectFacadeReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth)
    .pairedOmega

/-- The named facade and the causally registered effect row are the same
installed source fibre at every finite compiler visit. -/
theorem runtimeEffectFacadeReadoutAt_heq_installedFiber
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    HEq (runtimeEffectFacadeReadoutAt observation nontrivial depth)
      (runtimeEffectRootedActiveAt observation nontrivial depth
        ).installedFiber := by
  change HEq
    ((runtimeEffectRecognition observation nontrivial).effectComponent.outcomeAt
      PUnit.unit
      ((runtimeEffectRoot observation nontrivial).emitted
        (runtimeEffectVisitAt observation nontrivial
          (runtimeEffectRuntimeAt observation nontrivial depth).state).current))
    (runtimeEffectRootedActiveAt observation nontrivial depth).installedFiber
  rw [runtimeEffectRuntimeAt_state observation nontrivial depth]
  exact heq_of_eq <|
    (runtimeEffectRootedActiveAt observation nontrivial depth
      ).componentOutcome_eq_installedFiber

/-- Named-facade provenance at every finite stage: the readout, exact
occurrence, whole ledger and generated next are one runtime tick. -/
theorem runtimeEffectFacadeReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    type_of%
      ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
        (runtimeEffectRuntimeAt observation nontrivial depth)
        RuntimeEffectFace.pairedOmega) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth)
    RuntimeEffectFace.pairedOmega


def runtimeCombCalculationReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth) (.combCalculation half)

theorem runtimeCombCalculationReadoutAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeCombCalculationReadoutAt observation nontrivial depth half =
      .inl ⟨PUnit.unit, OriginalKCombCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)⟩ := rfl

def runtimeCombCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  match runtimeCombCalculationReadoutAt observation nontrivial depth half with
  | .inl ⟨_, result⟩ => result
  | .inr impossible => nomatch impossible

theorem runtimeCombCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeCombCalculationResultAt observation nontrivial depth half =
      OriginalKCombCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

theorem runtimeCombCalculationReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) : type_of%
    ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
      (runtimeEffectRuntimeAt observation nontrivial depth) (.combCalculation half)) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth) (.combCalculation half)


/-- The installed source calculation is read at the exact emitted occurrence. -/
def runtimeBFiniteCalculationReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth) (.bFiniteCalculation half)

theorem runtimeBFiniteCalculationReadoutAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeBFiniteCalculationReadoutAt observation nontrivial depth half =
      .inl ⟨PUnit.unit, OriginalKBFiniteCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)⟩ := rfl

def runtimeBFiniteCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  match runtimeBFiniteCalculationReadoutAt observation nontrivial depth half with
  | .inl ⟨_, result⟩ => result
  | .inr impossible => nomatch impossible

theorem runtimeBFiniteCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeBFiniteCalculationResultAt observation nontrivial depth half =
      OriginalKBFiniteCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

/-- Coverage binds the actual calculation, whole ledger and generated next. -/
theorem runtimeBFiniteCalculationReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) : type_of%
    ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
      (runtimeEffectRuntimeAt observation nontrivial depth) (.bFiniteCalculation half)) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth) (.bFiniteCalculation half)


/-- The installed source calculation is read at the exact emitted occurrence. -/
def runtimeCoefficientBSelfCalculationReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth) (.coefficientBSelfCalculation half)

theorem runtimeCoefficientBSelfCalculationReadoutAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeCoefficientBSelfCalculationReadoutAt observation nontrivial depth half =
      .inl ⟨PUnit.unit, OriginalKCoefficientBSelfCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)⟩ := rfl

def runtimeCoefficientBSelfCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  match runtimeCoefficientBSelfCalculationReadoutAt observation nontrivial depth half with
  | .inl ⟨_, result⟩ => result
  | .inr impossible => nomatch impossible

theorem runtimeCoefficientBSelfCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half =
      OriginalKCoefficientBSelfCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

/-- Coverage binds the actual calculation, whole ledger and generated next. -/
theorem runtimeCoefficientBSelfCalculationReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) : type_of%
    ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
      (runtimeEffectRuntimeAt observation nontrivial depth) (.coefficientBSelfCalculation half)) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth) (.coefficientBSelfCalculation half)


/-- The installed source calculation is read at the exact emitted occurrence. -/
def runtimeExteriorArithmeticCalculationReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (column : Fin 3) (side : Fin 2) (cutoff : Nat) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth) (.exteriorArithmeticCalculation half column side cutoff)

theorem runtimeExteriorArithmeticCalculationReadoutAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (column : Fin 3) (side : Fin 2) (cutoff : Nat) :
    runtimeExteriorArithmeticCalculationReadoutAt observation nontrivial depth half column side cutoff =
      .inl ⟨PUnit.unit, OriginalKExteriorArithmeticCalculation.result observation nontrivial half column side cutoff
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)⟩ := rfl

def runtimeExteriorArithmeticCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (column : Fin 3) (side : Fin 2) (cutoff : Nat) :=
  match runtimeExteriorArithmeticCalculationReadoutAt observation nontrivial depth half column side cutoff with
  | .inl ⟨_, result⟩ => result
  | .inr impossible => nomatch impossible

theorem runtimeExteriorArithmeticCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (column : Fin 3) (side : Fin 2) (cutoff : Nat) :
    runtimeExteriorArithmeticCalculationResultAt observation nontrivial depth half column side cutoff =
      OriginalKExteriorArithmeticCalculation.result observation nontrivial half column side cutoff
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

/-- Coverage binds the actual calculation, whole ledger and generated next. -/
theorem runtimeExteriorArithmeticCalculationReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (column : Fin 3) (side : Fin 2) (cutoff : Nat) : type_of%
    ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
      (runtimeEffectRuntimeAt observation nontrivial depth) (.exteriorArithmeticCalculation half column side cutoff)) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth) (.exteriorArithmeticCalculation half column side cutoff)

def runtimeWholeDebtRCalculationReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth) (.wholeDebtRCalculation half)

theorem runtimeWholeDebtRCalculationReadoutAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationReadoutAt observation nontrivial depth half =
      .inl ⟨PUnit.unit, OriginalKWholeDebtRCalculationFace.paNativeCayleyBundle observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)⟩ := rfl

def runtimeWholeDebtRCalculationPaNativeCayleyBundleAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  match runtimeWholeDebtRCalculationReadoutAt observation nontrivial depth half with
  | .inl ⟨_, result⟩ => result
  | .inr impossible => nomatch impossible


def runtimeWholeDebtRCalculationPaNativePortBundleAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationPaNativeCayleyBundleAt observation nontrivial depth half).1

def runtimeWholeDebtRCalculationReturnJetBundleAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationPaNativePortBundleAt observation nontrivial depth half).1

def runtimeWholeDebtRCalculationForcedBundleAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationReturnJetBundleAt observation nontrivial depth half).1

theorem runtimeWholeDebtRCalculationForcedBundleAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationForcedBundleAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.forcedBundle observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeWholeDebtRCalculationReturnBundleAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationForcedBundleAt observation nontrivial depth half).1

theorem runtimeWholeDebtRCalculationReturnBundleAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationReturnBundleAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.returnJordanBundle observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeWholeDebtRCalculationJointBundleAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationReturnBundleAt observation nontrivial depth half).1

theorem runtimeWholeDebtRCalculationJointBundleAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationJointBundleAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.jointBundle observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeWholeDebtRCalculationNativeResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationJointBundleAt observation nontrivial depth half).1

theorem runtimeWholeDebtRCalculationNativeResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationNativeResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.nativeResult observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeWholeDebtRCalculationExtendedResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationNativeResultAt observation nontrivial depth half).1

theorem runtimeWholeDebtRCalculationExtendedResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationExtendedResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.extendedResult observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeWholeDebtRCalculationCompleteResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationExtendedResultAt observation nontrivial depth half).1

theorem runtimeWholeDebtRCalculationCompleteResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationCompleteResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.completeResult observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeWholeDebtRCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationCompleteResultAt observation nontrivial depth half).1

theorem runtimeWholeDebtRCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeWholeDebtRCalculationResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimePowerWaveCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationCompleteResultAt observation nontrivial depth half).2

theorem runtimePowerWaveCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimePowerWaveCalculationResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.waveResult observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeReciprocalCotestCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeWholeDebtRCalculationExtendedResultAt observation nontrivial depth half).2

theorem runtimeReciprocalCotestCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeReciprocalCotestCalculationResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.rrResult observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimePrimitiveMobiusCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (index : Fin 3) :=
  (runtimeWholeDebtRCalculationNativeResultAt observation nontrivial depth half).2 index

theorem runtimePrimitiveMobiusCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (index : Fin 3) :
    runtimePrimitiveMobiusCalculationResultAt observation nontrivial depth half index =
      OriginalKWholeDebtRCalculationFace.mobiusResult observation nontrivial half index
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeJointMobiusFieldCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :=
  (runtimeWholeDebtRCalculationJointBundleAt observation nontrivial depth half).2 field

theorem runtimeJointMobiusFieldCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :
    runtimeJointMobiusFieldCalculationResultAt observation nontrivial depth half field =
      OriginalKWholeDebtRCalculationFace.jointResult observation nontrivial half field
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeReturnJordanCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.ResultAt
      OriginalKWholeDebtRCalculationFace.Base
      (OriginalKWholeDebtRCalculationFace.returnJordanReader observation nontrivial half field)
      ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) :=
  (runtimeWholeDebtRCalculationReturnBundleAt observation nontrivial depth half).2 field

theorem runtimeReturnJordanCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :
    runtimeReturnJordanCalculationResultAt observation nontrivial depth half field =
      OriginalKWholeDebtRCalculationFace.returnJordanResult observation nontrivial half field
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimePaNativeCayleyCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 3) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.ResultAt
      OriginalKWholeDebtRCalculationFace.Base
      (OriginalKWholeDebtRCalculationFace.paNativeCayleyReader observation nontrivial half field)
      ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) :=
  (runtimeWholeDebtRCalculationPaNativeCayleyBundleAt observation nontrivial depth half).2 field

theorem runtimePaNativeCayleyCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 3) :
    runtimePaNativeCayleyCalculationResultAt observation nontrivial depth half field =
      OriginalKWholeDebtRCalculationFace.paNativeCayleyResult observation nontrivial half field
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimePaNativePortCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.ResultAt
      OriginalKWholeDebtRCalculationFace.Base
      (OriginalKWholeDebtRCalculationFace.paNativePortReader observation nontrivial half field)
      ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) :=
  (runtimeWholeDebtRCalculationPaNativePortBundleAt observation nontrivial depth half).2 field

theorem runtimePaNativePortCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :
    runtimePaNativePortCalculationResultAt observation nontrivial depth half field =
      OriginalKWholeDebtRCalculationFace.paNativePortResult observation nontrivial half field
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeReturnJetCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.ResultAt
      OriginalKWholeDebtRCalculationFace.Base
      (OriginalKWholeDebtRCalculationFace.returnJetReader observation nontrivial half field)
      ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) :=
  (runtimeWholeDebtRCalculationReturnJetBundleAt observation nontrivial depth half).2 field

theorem runtimeReturnJetCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) (field : Fin 2) :
    runtimeReturnJetCalculationResultAt observation nontrivial depth half field =
      OriginalKWholeDebtRCalculationFace.returnJetResult observation nontrivial half field
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeForcedInverseCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.ResultAt
      OriginalKWholeDebtRCalculationFace.Base
      (OriginalKWholeDebtRCalculationFace.forcedReader observation nontrivial half)
      ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) :=
  (runtimeWholeDebtRCalculationForcedBundleAt observation nontrivial depth half).2

theorem runtimeForcedInverseCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeForcedInverseCalculationResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.forcedResult observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeJointMobiusCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  runtimeJointMobiusFieldCalculationResultAt observation nontrivial depth half 0

theorem runtimeJointMobiusCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeJointMobiusCalculationResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.jointResult observation nontrivial half 0
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

def runtimeJointMobiusRCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  runtimeJointMobiusFieldCalculationResultAt observation nontrivial depth half 1

theorem runtimeJointMobiusRCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeJointMobiusRCalculationResultAt observation nontrivial depth half =
      OriginalKWholeDebtRCalculationFace.jointResult observation nontrivial half 1
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

theorem runtimeWholeDebtRCalculationReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) : type_of%
    ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
      (runtimeEffectRuntimeAt observation nontrivial depth) (.wholeDebtRCalculation half)) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth) (.wholeDebtRCalculation half)

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
