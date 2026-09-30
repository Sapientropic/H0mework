import H0mework.NavierStokes.SourceGeometry.SymmetryPreservation
import H0mework.NavierStokes.WholeReceipt.PrefixReceipt
import H0mework.NavierStokes.Accumulation.StandingPaidMediumState

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial

noncomputable section

private theorem source_modes_even :
    ∀ wave ∈ butterflyFirstStackModes, Even (wave 0) := by decide

theorem source_initial_even : OnEvenLattice concreteCounterexampleInitial.initialState := by
  change OnEvenLattice (butterflyFirstStackPhysicalState (-1))
  intro wave odd
  exact butterflyFirstStackPhysicalState_supported (-1) wave
    (fun inside => odd (source_modes_even wave inside))

theorem source_prefix_even (stage : ℕ)
    (actual : Icc (0 : ℝ) (WholePrefixState.duration concreteCounterexampleInitial stage)) :
    OnEvenLattice ((WholePrefixReceipt.receipt concreteCounterexampleInitial stage).wholePath actual) :=
  receipt_on_even_lattice _ source_initial_even actual

theorem source_contact_even (stage : ℕ) :
    OnEvenLattice (run concreteCounterexampleInitial stage).contact.physicalState := by
  let terminal : Icc (0 : ℝ) (WholePrefixState.duration concreteCounterexampleInitial stage) :=
    ⟨_, (WholePrefixState.duration_pos concreteCounterexampleInitial stage).le, le_rfl⟩
  have same := source_prefix_even stage terminal
  rw [WholePrefixReceipt.receipt_path] at same
  change OnEvenLattice (wholeRestartPrefixPhysicalTrajectory concreteCounterexampleInitial (stage + 1)
    (elapsedTime concreteCounterexampleInitial (stage + 1))) at same
  rw [wholeRestartPrefixPhysicalTrajectory_endpoint, run_succ_initialState] at same
  exact same

theorem source_nextReceipt_even (stage : ℕ)
    (actual : Icc (0 : ℝ) (wholeRestartDuration (run concreteCounterexampleInitial stage).contact)) :
    OnEvenLattice ((run concreteCounterexampleInitial stage).nextReceipt.wholePath actual) :=
  receipt_on_even_lattice _ (source_contact_even stage) actual

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
