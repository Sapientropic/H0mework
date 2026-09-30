import H0mework.Realization.Arithmetic.Incidence
import H0mework.NavierStokes.Accumulation.NativeFluidMediumRoot
import H0mework.NavierStokes.Accumulation.TemporalEnstrophyLedger

/-!
# Source-native restart-cell incidence

The quantized restart level is read here as the cardinality of the physical
threshold-cell carrier attached to the same generated whole-restart contact.
An exact one-cell update is an equivalence between the actual successor
carrier and the tagged union of the actual current carrier with one paid cell,
together with the emitter's actual `.oneCell` branch.

Consequently `levelNext = level + 1` is only a cardinal readout of actual
incidence.  The result numeral is never stored in the incidence receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRestartCellIncidence

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticIncidence
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot

noncomputable section

/-- Exact additive incidence emitted on the same native contact edge.
Authority includes the actual `.oneCell` branch of the contact compiler's
total effect; a naked equivalence cannot inhabit this mouth. -/
def NativeRestartCellIncidenceAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) : Prop :=
  ∃ debit : GeneratedWholeRestartCellDebitAt
      (generatedWholeRestartCanonicalReplay (run initial index).contact)
      (run initial index).nextContact,
    ∃ exact : debit.ExactValuedOneCellAt,
      runCellEffect initial index = .oneCell debit exact

/-- Cardinal readout of an installed one-cell incidence.  Addition is a
consequence of the carrier equivalence, not an input to this theorem. -/
theorem restartCoefficientLevelNat_succ_eq_add_one_of_cellIncidence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (incidence : NativeRestartCellIncidenceAt initial index) :
    restartCoefficientLevelNat initial (index + 1) =
      restartCoefficientLevelNat initial index + 1 := by
  rcases incidence with ⟨debit, exact, _effectEq⟩
  change
    wholeRestartCoefficientLevel (run initial index).nextContact =
      wholeRestartCoefficientLevel (run initial index).contact + 1
  exact debit.coefficientLevel_eq_add_one_of_exact exact

/-- Conditional adapter: a same-successor finite net-enstrophy debit proves
the physical incidence, then the top-level contact emitter's coherence law
identifies its actual branch as `.oneCell`.  No endpoint carrier or result
level is accepted from the caller. -/
theorem nativeRestartCellIncidenceAt_of_projectedNetDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (finiteDebit :
      (restartCoefficientLevelNat initial index : Real) - 1 -
          finiteStateVorticityCoefficientEnstrophy modes
            (run initial index).contact.physicalState <
        ∫ actual in (0 : Real)..
            (run initial index).nextContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run initial index).nextContact.prefixReceipt modes actual) :
    NativeRestartCellIncidenceAt initial index := by
  have levelEq :=
    restartCoefficientLevelNat_succ_eq_add_one_of_projectedNetDebit
      initial index modes zeroNotMem finiteDebit
  have contactLevelEq :
      wholeRestartCoefficientLevel (run initial index).nextContact =
        wholeRestartCoefficientLevel (run initial index).contact + 1 := by
    change
      wholeRestartCoefficientLevel (run initial index).nextContact =
        wholeRestartCoefficientLevel (run initial index).contact + 1 at levelEq
    exact levelEq
  generalize effectEq : runCellEffect initial index = effect
  cases effect with
  | oneCell debit exact => exact ⟨debit, exact, effectEq⟩
  | retainedResidual residual =>
      have exact := residual.debit.exact_of_coefficientLevel_eq_add_one
        contactLevelEq
      exact (residual.normalResidual.mismatch exact).elim

/-- Public numeric consumer routed through the actual incidence receipt. -/
theorem restartCoefficientLevelNat_succ_eq_add_one_via_cellIncidence_of_projectedNetDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (finiteDebit :
      (restartCoefficientLevelNat initial index : Real) - 1 -
          finiteStateVorticityCoefficientEnstrophy modes
            (run initial index).contact.physicalState <
        ∫ actual in (0 : Real)..
            (run initial index).nextContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run initial index).nextContact.prefixReceipt modes actual) :
    restartCoefficientLevelNat initial (index + 1) =
      restartCoefficientLevelNat initial index + 1 :=
  restartCoefficientLevelNat_succ_eq_add_one_of_cellIncidence initial index
    (nativeRestartCellIncidenceAt_of_projectedNetDebit
      initial index modes zeroNotMem finiteDebit)

/-! ## Installed valued normal form on the classical medium root -/

/-- The generic arithmetic material recognition, specialized to the exact
classical whole-restart medium root. -/
def nativeRestartArithmeticMaterialRecognition
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeRootArithmeticIncidenceRecognitionAt
      (nativeFluidMediumLivingRoot
        (classicalWholeRestartMediumSource initial)) :=
  nativeFluidMediumArithmeticMaterialRecognition
    (classicalWholeRestartMediumSource initial)

/-- Canonical root arithmetic step at one actual run depth. -/
def nativeRestartArithmeticStepAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :=
  (nativeRestartArithmeticMaterialRecognition initial).generateStepAt
    (.finite (nativeFluidMediumRootVisit
      (classicalWholeRestartMediumSource initial) stage))

private theorem classicalWholeRestartMedium_stateAfter_eq_runtime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (classicalWholeRestartMediumSource initial).stateAfter stage =
      runRuntime initial stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      change
        ((classicalWholeRestartMediumSource initial).stateAfter stage).next =
          (runRuntime initial stage).next
      rw [inductionHypothesis]

private theorem nativeRestartRootVisit_current_eq_stateAfter
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (nativeFluidMediumRootVisit
        (classicalWholeRestartMediumSource initial) stage).current =
      (classicalWholeRestartMediumSource initial).stateAfter stage := by
  induction stage with
  | zero => rfl
  | succ stage ih =>
      change
        (classicalWholeRestartMediumSource initial).successor
            (nativeFluidMediumRootVisit
              (classicalWholeRestartMediumSource initial) stage).current =
          (classicalWholeRestartMediumSource initial).successor
            ((classicalWholeRestartMediumSource initial).stateAfter stage)
      rw [ih]

/-- The installed root material is the arithmetic projection of the complete
standing-valued emitter payload.  In particular its left history is the live
anchor, not an independently reconstructed current scale. -/
theorem nativeRestartArithmeticStep_material_eq_standingValued
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (nativeRestartArithmeticStepAt initial stage).material =
      (nativeRestartStandingValuedArithmeticMaterial
        (runStandingCellEffect initial stage)).arithmeticMaterial := by
  change
    nativeFluidMediumArithmeticMaterialAt
        (classicalWholeRestartMediumSource initial)
        ((classicalWholeRestartMediumSource initial).generateOccurrence
          (nativeFluidMediumRootVisit
            (classicalWholeRestartMediumSource initial) stage).current) = _
  rw [nativeRestartRootVisit_current_eq_stateAfter initial stage,
    classicalWholeRestartMedium_stateAfter_eq_runtime initial stage]
  rfl

def NativeRestartRootNormalFormIsExact
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) : Prop :=
  match (nativeRestartArithmeticStepAt initial stage).parallelNormalForm with
  | .exact _ _ => True
  | .generatedResidual _ => False

def NativeRestartRootNormalFormIsResidual
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) : Prop :=
  match (nativeRestartArithmeticStepAt initial stage).parallelNormalForm with
  | .exact _ _ => False
  | .generatedResidual _ => True

/-- Total exact/residual normal form of the single standing-valued material.
No raw-current incidence is reconstructed after normalization. -/
theorem actualRestartOccurrence_totalValuedNormalForm
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    NativeRestartRootNormalFormIsExact initial stage ∨
      NativeRestartRootNormalFormIsResidual initial stage := by
  generalize normalEq :
    (nativeRestartArithmeticStepAt initial stage).parallelNormalForm = normal
  cases normal <;>
    simp [NativeRestartRootNormalFormIsExact,
      NativeRestartRootNormalFormIsResidual, normalEq]

/-! ## Finite recursive incidence program and whole-run fold -/

/-- Finite source program for the actual cell lineage.  It contains one
initial incidence and one local successor rule, never a completed family
`∀ index, NativeRestartCellIncidenceAt initial index`. -/
structure NativeRestartCellIncidenceProgram
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  initialAt : NativeRestartCellIncidenceAt initial 0
  advanceAt : (index : Nat) →
    NativeRestartCellIncidenceAt initial index →
      NativeRestartCellIncidenceAt initial (index + 1)

/-- Installation of the finite cell program on the exact classical-medium
living process. -/
def NativeRestartCellIncidenceProgram.toGeneratedInvariantLaw
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (program : NativeRestartCellIncidenceProgram initial) :
    SourceNativeGeneratedInvariantLaw
      (nativeFluidMediumLivingProcess
        (classicalWholeRestartMediumSource initial)) :=
  SourceNativeGeneratedInvariantLaw.create
    (process := nativeFluidMediumLivingProcess
      (classicalWholeRestartMediumSource initial))
    (InvariantAt := fun index =>
      PLift <| NativeRestartCellIncidenceAt initial index)
    (initialAt := ⟨program.initialAt⟩)
    (advanceAt := fun index prior =>
      ⟨program.advanceAt index prior.down⟩)

/-- Canonical incidence at one generated root depth. -/
theorem NativeRestartCellIncidenceProgram.generatedAt
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (program : NativeRestartCellIncidenceProgram initial)
    (index : Nat) : NativeRestartCellIncidenceAt initial index := by
  have generated : PLift (NativeRestartCellIncidenceAt initial index) := by
    simpa only [NativeRestartCellIncidenceProgram.toGeneratedInvariantLaw,
      SourceNativeGeneratedInvariantLaw.create,
      nativeFluidMediumLivingProcess_stateAfter] using
      program.toGeneratedInvariantLaw.generatedAt index
  exact generated.down

/-- Cardinal readout of the canonical incidence history gives the exact
linear quantized-level formula. -/
theorem restartCoefficientLevelNat_eq_initial_add_index_of_cellProgram
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (program : NativeRestartCellIncidenceProgram initial) :
    ∀ index : Nat,
      restartCoefficientLevelNat initial index =
        restartCoefficientLevelNat initial 0 + index
  | 0 => by simp
  | index + 1 => by
      rw [restartCoefficientLevelNat_succ_eq_add_one_of_cellIncidence
        initial index (program.generatedAt index)]
      rw [restartCoefficientLevelNat_eq_initial_add_index_of_cellProgram
        program index]
      omega

theorem restartCoefficientCeiling_injective_of_cellProgram
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (program : NativeRestartCellIncidenceProgram initial) :
    Function.Injective (restartCoefficientCeiling initial) := by
  intro left right equality
  have levelEquality :
      restartCoefficientLevelNat initial left =
        restartCoefficientLevelNat initial right := by
    rw [restartCoefficientCeiling_eq_levelNat_cast,
      restartCoefficientCeiling_eq_levelNat_cast] at equality
    exact_mod_cast equality
  rw [restartCoefficientLevelNat_eq_initial_add_index_of_cellProgram
      program left,
    restartCoefficientLevelNat_eq_initial_add_index_of_cellProgram
      program right] at levelEquality
  omega

/-- Exact whole-run consumer: a finite source-generated one-cell program
closes the reciprocal-barrier p-series and hence the complete actual clock. -/
theorem contactTime_summable_of_cellProgram
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (program : NativeRestartCellIncidenceProgram initial) :
    Summable fun index => (run initial index).contact.time.1 :=
  contactTime_summable_of_restartCoefficientCeiling_injective initial
    (restartCoefficientCeiling_injective_of_cellProgram program)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRestartCellIncidence
end NavierStokes
end SaturationMonoid
