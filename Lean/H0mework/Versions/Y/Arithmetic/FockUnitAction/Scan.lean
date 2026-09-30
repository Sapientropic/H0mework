import H0mework.Versions.Y.Arithmetic.FockUnitAction.Action

/-!
# Exact fixed-target unit-charge scans

The existing `GeneratedPathAt` remains the sole chronology.  This kernel
recursively appends same-whole existing-unit transfers and records their exact
endpoint equations.  It does not classify the endpoint or carry a terminal,
fibre, nonzero coefficient, settlement, residual successor, or next current.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockUnitChargeScan

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open ParticleWaveFockUnitChargeAction
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

/-- Edge count read from the unique generic path chronology. -/
def factorUnitPathLength {index : Nat} {indexInRange : 1 ≤ index}
    {source target : EffectiveSplitAt index} :
    GeneratedPathAt (factorUnitChargeLaw index indexInRange) source target → Nat
  | .nil => 0
  | .snoc prior _step => factorUnitPathLength prior + 1

/-- A finite scan made only by source-generated unit-transfer edges.  Its
private constructor prevents callers from installing an arbitrary mixed path
under the scan name. -/
structure UnitChargeScanAt {index : Nat} (indexInRange : 1 ≤ index)
    (source : EffectiveSplitAt index) (steps : Nat) : Type where
  private mk ::
  room : steps + 2 ≤ splitRight source
  target : EffectiveSplitAt index
  path : GeneratedPathAt (factorUnitChargeLaw index indexInRange) source target
  pathLength : factorUnitPathLength path = steps
  targetLeft : splitLeft target = splitLeft source + steps
  targetRightConservation : splitRight target + steps = splitRight source
  wholePreserved :
    (UnitHistory.generate (splitLeft source)).parallel
        (UnitHistory.generate (splitRight source)) =
      (UnitHistory.generate (splitLeft target)).parallel
        (UnitHistory.generate (splitRight target))

/-- Recursively generate the exact finite scan.  Every successor is a
`.unit` edge whose payload contains the existing-unit transfer receipt. -/
noncomputable def generateUnitChargeScan {index : Nat}
    (indexInRange : 1 ≤ index) (source : EffectiveSplitAt index) :
    (steps : Nat) → (room : steps + 2 ≤ splitRight source) →
      UnitChargeScanAt indexInRange source steps
  | 0, room =>
      { room := room
        target := source
        path := .nil
        pathLength := rfl
        targetLeft := by omega
        targetRightConservation := by omega
        wholePreserved := rfl }
  | steps + 1, room => by
      have priorRoom : steps + 2 ≤ splitRight source := by omega
      let prior := generateUnitChargeScan indexInRange source steps priorRoom
      have actionRoom : 3 ≤ splitRight prior.target := by
        have := prior.targetRightConservation
        omega
      let action := generateUnitChargeAction prior.target actionRoom
      exact
        { room := room
          target := action.target
          path := prior.path.snoc (.unit action)
          pathLength := by
            change factorUnitPathLength prior.path + 1 = steps + 1
            rw [prior.pathLength]
          targetLeft := by
            rw [action.target_eq, unitChargeTarget_left, prior.targetLeft]
            omega
          targetRightConservation := by
            have transferRead := action.rightWriteEquation
            have priorRead := prior.targetRightConservation
            omega
          wholePreserved := by
            calc
              (UnitHistory.generate (splitLeft source)).parallel
                    (UnitHistory.generate (splitRight source)) =
                  (UnitHistory.generate (splitLeft prior.target)).parallel
                    (UnitHistory.generate (splitRight prior.target)) :=
                prior.wholePreserved
              _ = action.sourceLeftHistory.parallel action.sourceRightHistory := by
                rw [action.sourceLeftHistory_eq, action.sourceRightHistory_eq]
              _ = action.targetLeftHistory.parallel action.targetRightHistory :=
                action.transfer.whole_eq
              _ = (UnitHistory.generate (splitLeft action.target)).parallel
                    (UnitHistory.generate (splitRight action.target)) := by
                rw [action.targetLeftHistory_generated,
                  action.targetRightHistory_generated] }

/-- A scan anchored to the exact occurrence which generated the fixed whole.
The scan contributes no independent occurrence or successor. -/
structure RootedUnitChargeScanAt
    {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index)
    (source : EffectiveSplitAt index) (steps : Nat)
    (scan : UnitChargeScanAt indexInRange source steps) : Type where
  private mk ::
  rootSource : RootGeneratedExactOccurrenceOperationalFactorDecayAt
    rootOccurrence index indexInRange
  rootSource_eq : rootSource =
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      rootOccurrence index indexInRange
  occurrenceRoot : rootSource.occurrence.root.rootOccurrence = rootOccurrence
  sourceWholeOccurrence :
    (UnitHistory.generate (splitLeft source)).parallel
        (UnitHistory.generate (splitRight source)) =
      rootSource.occurrence.fold terminalHistoryAlgebra
  targetWholeOccurrence :
    (UnitHistory.generate (splitLeft scan.target)).parallel
        (UnitHistory.generate (splitRight scan.target)) =
      rootSource.occurrence.fold terminalHistoryAlgebra

def generateRootedUnitChargeScan
    {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index)
    (source : EffectiveSplitAt index) (steps : Nat)
    (room : steps + 2 ≤ splitRight source) :
    RootedUnitChargeScanAt rootOccurrence index indexInRange source steps
      (generateUnitChargeScan indexInRange source steps room) := by
  let rootSource :=
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      rootOccurrence index indexInRange
  let scan := generateUnitChargeScan indexInRange source steps room
  have sourceWhole :
      (UnitHistory.generate (splitLeft source)).parallel
          (UnitHistory.generate (splitRight source)) =
        rootSource.occurrence.fold terminalHistoryAlgebra :=
    (generatedSplitWhole_eq_evenTarget source).trans rootSource.targetFold.symm
  exact
    { rootSource := rootSource
      rootSource_eq := rfl
      occurrenceRoot := rootSource.occurrenceRoot
      sourceWholeOccurrence := sourceWhole
      targetWholeOccurrence := scan.wholePreserved.symm.trans sourceWhole }

end
end ParticleWaveFockUnitChargeScan
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
