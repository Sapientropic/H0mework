import H0mework.NavierStokes.Crossing.GluingNegativeOneBridge

/-!
# Large-data crossing self-forcing reduction

The canonical component producer does more than expose a formal list.  All
components are equal source-generated fractions of the actual finite crossing
core, while the vorticity nonlinearity is quadratic.  Consequently the sum of
all primitive component self forcings is exactly `1 / count` of the finite
core's nonlinear `H⁻¹` forcing.

This is the analytic gain available on the faithful-zero gluing branch.  The
caller supplies neither a smallness parameter nor a component count: the
actual crossing core and the fixed half-critical scale generate both.  Cross
and tail interactions are not discarded; they remain the separately tracked
complete gluing residual from the imported bridge.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalDualSquareReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteComponentSources
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open AffineRelaxation

noncomputable section

/-- The internally selected finite crossing core has finite whole gradient
mass because its sharp support is the generated finite inventory. -/
theorem wholeRestartCrossingFiniteCore_gradient_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          (wholeRestartCrossingFiniteCoreState
            initial index crossed wave) :=
  summable_wholeStateVorticityGradientDensity_of_supported
    (wholeRestartCrossingFiniteCoreModes initial index crossed)
    (wholeRestartCrossingFiniteCoreState initial index crossed)
    (wholeRestartInitialState_supported
      (run initial index).contact
      (wholeRestartCrossingFiniteCoreRadius initial index crossed))

/-- An actual half-critical crossing forces at least three canonical
components in its source-selected finite core.  The lower bound is generated
from the crossing inequality and the least core itself; it is not a caller
component-count premise. -/
theorem wholeRestartCrossingFiniteCore_three_le_componentCount
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    3 ≤ canonicalHalfCriticalComponentCount ν
      (wholeRestartCrossingFiniteCoreState initial index crossed) := by
  let modes := wholeRestartCrossingFiniteCoreModes initial index crossed
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  let ceiling := wholeRestartHalfCriticalCoefficientCeiling ν
  have coreSupported : ∀ wave : IntegerWavevector,
      wave ∉ modes → core wave = 0 := by
    exact wholeRestartInitialState_supported
      (run initial index).contact
      (wholeRestartCrossingFiniteCoreRadius initial index crossed)
  have coreMassEq :
      wholeVorticityEuclideanMass core =
        finiteStateVorticityCoefficientEnstrophy modes
          (run initial index).contact.physicalState := by
    rw [wholeVorticityEuclideanMass_eq_finite_of_supported
      modes core coreSupported]
    have coreEq :
        core = complexSharpSupportProjection modes
          (run initial index).contact.physicalState := by
      simpa [core, modes] using
        wholeRestartCrossingFiniteCoreState_eq_sharpSupportProjection
          initial index crossed
    rw [coreEq,
      finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
  have ceilingPos : 0 < ceiling := by
    simpa [ceiling] using wholeRestartHalfCriticalCoefficientCeiling_pos ν
  have ceilingLtMass : ceiling < wholeVorticityEuclideanMass core := by
    unfold ceiling wholeRestartHalfCriticalCoefficientCeiling
    apply (div_lt_iff₀ criticalEnstrophyLatticeConstant_pos).2
    rw [coreMassEq]
    simpa only [mul_comm] using
      wholeRestartCrossingFiniteCoreRadius_crossed initial index crossed
  have ratioGt :
      (1 : ℝ) < wholeVorticityEuclideanMass core / ceiling := by
    exact (lt_div_iff₀ ceilingPos).2 (by simpa using ceilingLtMass)
  have ratioGtNatCast :
      ((1 : ℕ) : ℝ) < wholeVorticityEuclideanMass core / ceiling := by
    simpa using ratioGt
  have ceilGt :
      1 < Nat.ceil (wholeVorticityEuclideanMass core / ceiling) :=
    (Nat.lt_ceil).2 ratioGtNatCast
  change
    3 ≤ Nat.ceil (wholeVorticityEuclideanMass core / ceiling) + 1
  omega

/-- Physical nonlinear `H⁻¹` state of the exact finite crossing core. -/
def wholeRestartCrossingFiniteCoreNegativeOneState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 :=
  wholeStateVorticityNonlinearNegativeOneState
    (wholeRestartCrossingFiniteCoreState initial index crossed)
    (wholeStateTransverse_sharpSupportProjection
      (wholeRestartCrossingFiniteCoreModes initial index crossed)
      (run initial index).contact.physicalState
      (run initial index).contact.transverse)
    (wholeRestartCrossingFiniteCore_gradient_summable
      initial index crossed)

/-- Quadratic scaling sends one canonical component forcing to the square of
the generated reciprocal component count times the finite-core forcing. -/
theorem wholeRestartCrossingFiniteComponentNegativeOneState_eq_core_smul
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingFiniteComponentNegativeOneState
        initial index crossed =
      (((canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState
            initial index crossed) : ℝ)⁻¹ : ℂ) ^ 2) •
        wholeRestartCrossingFiniteCoreNegativeOneState
          initial index crossed := by
  apply lp.ext
  funext output
  change
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
          (canonicalHalfCriticalComponent ν
            (wholeRestartCrossingFiniteCoreState initial index crossed)) output =
      (((canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState
            initial index crossed) : ℝ)⁻¹ : ℂ) ^ 2) •
        wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
          (wholeRestartCrossingFiniteCoreState initial index crossed) output
  unfold wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
  by_cases outputZero : output = 0
  · simp [outputZero]
  · rw [if_neg outputZero, if_neg outputZero]
    unfold canonicalHalfCriticalComponent
    rw [wholeStateVorticityNonlinearCoefficientAt_real_smul]
    module

/-- After summing every generated occurrence, one power of the component
count cancels.  The complete primitive self forcing is exactly the reciprocal
count times the finite-core forcing. -/
theorem wholeRestartCrossingFiniteComponentSelfNegativeOneState_eq_core_smul
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingFiniteComponentSelfNegativeOneState
        initial index crossed =
      ((canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState
            initial index crossed) : ℝ)⁻¹ : ℂ) •
        wholeRestartCrossingFiniteCoreNegativeOneState
          initial index crossed := by
  let count :=
    canonicalHalfCriticalComponentCount ν
      (wholeRestartCrossingFiniteCoreState initial index crossed)
  have countNe : count ≠ 0 :=
    canonicalHalfCriticalComponentCount_ne_zero ν _
  rw [wholeRestartCrossingFiniteComponentSelfNegativeOneState,
    wholeRestartCrossingFiniteComponentNegativeOneState_eq_core_smul]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  change
    (count : ℂ) * (((count : ℝ)⁻¹ : ℂ) ^ 2) =
      ((count : ℝ)⁻¹ : ℂ)
  push_cast
  field_simp

/-- On the faithful-zero gluing branch, the actual whole nonlinear forcing
is exactly the generated reciprocal-count finite-core forcing.  This is the
large-data analytic reduction produced by the component/gluing mechanism. -/
theorem wholeRestartCrossingWholeNegativeOneState_eq_core_smul_of_gluing_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0) :
    wholeStateVorticityNonlinearNegativeOneState
        (run initial index).contact.physicalState
        (run initial index).contact.transverse
        (run initial index).contact.gradient_summable =
      ((canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState
            initial index crossed) : ℝ)⁻¹ : ℂ) •
        wholeRestartCrossingFiniteCoreNegativeOneState
          initial index crossed := by
  have selfEq :
      wholeStateVorticityNonlinearNegativeOneState
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable =
        wholeRestartCrossingFiniteComponentSelfNegativeOneState
          initial index crossed := by
    unfold wholeRestartCrossingCompleteSourceGluingNegativeOneState
      at gluingZero
    exact sub_eq_zero.mp gluingZero
  rw [selfEq,
    wholeRestartCrossingFiniteComponentSelfNegativeOneState_eq_core_smul]

/-- On the faithful-zero branch, the actual whole nonlinearity has no output
outside the pair-output support of the source-selected finite core.  This is
an exact support consequence of the same component/gluing identity, not a
cutoff or tail-silence premise. -/
theorem
    wholeRestartCrossingWholeNonlinearCoefficientAt_eq_zero_of_gluing_zero_of_not_mem_pairOutput
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport
        (wholeRestartCrossingFiniteCoreModes initial index crossed)) :
    wholeStateVorticityNonlinearCoefficientAt
        (run initial index).contact.physicalState output = 0 := by
  have gluingRowZero :
      (fun wave =>
        wholeRestartCrossingCompleteSourceGluingResidual
          initial index crossed wave) = 0 :=
    (wholeRestartCrossingCompleteSourceGluingNegativeOneState_eq_zero_iff
      initial index crossed).1 gluingZero
  have componentZero :
      wholeStateVorticityNonlinearCoefficientAt
          (canonicalHalfCriticalComponent ν
            (wholeRestartCrossingFiniteCoreState initial index crossed))
          output = 0 :=
    wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_supported
      (wholeRestartCrossingFiniteCoreModes initial index crossed)
      (canonicalHalfCriticalComponent ν
        (wholeRestartCrossingFiniteCoreState initial index crossed))
      (wholeRestartCrossingFiniteComponent_supported
        initial index crossed)
      output outputNotMem
  have selfZero :
      wholeRestartCrossingFiniteComponentSelfRow
          initial index crossed output = 0 := by
    rw [wholeRestartCrossingFiniteComponentSelfRow_eq_nsmul,
      componentZero]
    simp
  have ledger :=
    wholeRestartCrossingWholeNonlinear_eq_sourceSelf_add_gluing
      initial index crossed output
  rw [selfZero, congrFun gluingRowZero output] at ledger
  simpa using ledger

/-- The faithful-zero branch has an exact reciprocal-count square gain in
the physical nonlinear `H⁻¹` norm. -/
theorem wholeRestartCrossingWholeNegativeOneState_norm_sq_eq_core_of_gluing_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0) :
    ‖wholeStateVorticityNonlinearNegativeOneState
        (run initial index).contact.physicalState
        (run initial index).contact.transverse
        (run initial index).contact.gradient_summable‖ ^ 2 =
      (canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState
            initial index crossed) : ℝ)⁻¹ ^ 2 *
        ‖wholeRestartCrossingFiniteCoreNegativeOneState
          initial index crossed‖ ^ 2 := by
  rw [wholeRestartCrossingWholeNegativeOneState_eq_core_smul_of_gluing_zero
    initial index crossed gluingZero, norm_smul, mul_pow]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]

/-- The reciprocal-count forcing gain is controlled by the generated
half-critical component mass and the exact finite-core gradient mass. -/
theorem wholeRestartCrossingWholeNegativeOneState_norm_sq_le_component_ceiling
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0) :
    ‖wholeStateVorticityNonlinearNegativeOneState
        (run initial index).contact.physicalState
        (run initial index).contact.transverse
        (run initial index).contact.gradient_summable‖ ^ 2 ≤
      4 * criticalEnstrophyLatticeConstant *
        wholeStateVorticityGradientMass
          (wholeRestartCrossingFiniteCoreState initial index crossed) *
        wholeRestartHalfCriticalCoefficientCeiling ν := by
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  let count := canonicalHalfCriticalComponentCount ν core
  have reciprocalSqNonneg : 0 ≤ (count : ℝ)⁻¹ ^ 2 := sq_nonneg _
  have coreBound :
      ‖wholeRestartCrossingFiniteCoreNegativeOneState
          initial index crossed‖ ^ 2 ≤
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeVorticityEuclideanMass core := by
    simpa [wholeRestartCrossingFiniteCoreNegativeOneState,
      criticalEnstrophyLatticeConstant, core] using
      wholeStateVorticityNonlinearNegativeOneState_norm_sq_le
        core
        (wholeStateTransverse_sharpSupportProjection
          (wholeRestartCrossingFiniteCoreModes initial index crossed)
          (run initial index).contact.physicalState
          (run initial index).contact.transverse)
        (wholeRestartCrossingFiniteCore_gradient_summable
          initial index crossed)
  have scaledBound :
      (count : ℝ)⁻¹ ^ 2 *
          ‖wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed‖ ^ 2 ≤
        (count : ℝ)⁻¹ ^ 2 *
          (4 * criticalEnstrophyLatticeConstant *
            wholeStateVorticityGradientMass core *
            wholeVorticityEuclideanMass core) :=
    mul_le_mul_of_nonneg_left coreBound reciprocalSqNonneg
  have componentMassEq :
      wholeVorticityEuclideanMass
          (canonicalHalfCriticalComponent ν core) =
        (count : ℝ)⁻¹ ^ 2 * wholeVorticityEuclideanMass core := by
    simpa [canonicalHalfCriticalComponent, count] using
      wholeVorticityEuclideanMass_real_smul
        (count : ℝ)⁻¹ core
  have componentMassLe :
      wholeVorticityEuclideanMass
          (canonicalHalfCriticalComponent ν core) ≤
        wholeRestartHalfCriticalCoefficientCeiling ν :=
    (canonicalHalfCriticalComponent_mass_lt_ceiling ν core).le
  rw [wholeRestartCrossingWholeNegativeOneState_norm_sq_eq_core_of_gluing_zero
    initial index crossed gluingZero]
  calc
    (count : ℝ)⁻¹ ^ 2 *
          ‖wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed‖ ^ 2 ≤
        (count : ℝ)⁻¹ ^ 2 *
          (4 * criticalEnstrophyLatticeConstant *
            wholeStateVorticityGradientMass core *
            wholeVorticityEuclideanMass core) := scaledBound
    _ =
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeVorticityEuclideanMass
            (canonicalHalfCriticalComponent ν core) := by
      rw [componentMassEq]
      ring
    _ ≤
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeRestartHalfCriticalCoefficientCeiling ν := by
      exact mul_le_mul_of_nonneg_left componentMassLe
        (mul_nonneg
          (mul_nonneg (by norm_num)
            criticalEnstrophyLatticeConstant_nonneg)
          (by
            unfold wholeStateVorticityGradientMass
            exact tsum_nonneg fun wave =>
              mul_nonneg (integerWaveNormSq_nonneg wave)
                (complexCoordinateAmplitudeSq_nonneg _)))

/-- Before any gluing branch is inspected, the generated component count
already pays the complete primitive source-self forcing.  The extra count is
not an external multiplicity certificate: it is the same count selected by
the actual crossing core producer. -/
theorem
    wholeRestartCrossingFiniteComponentSelfNegativeOneState_count_mul_norm_sq_le_component_ceiling
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (canonicalHalfCriticalComponentCount ν
        (wholeRestartCrossingFiniteCoreState
          initial index crossed) : ℝ) *
        ‖wholeRestartCrossingFiniteComponentSelfNegativeOneState
          initial index crossed‖ ^ 2 ≤
      4 * criticalEnstrophyLatticeConstant *
        wholeStateVorticityGradientMass
          (wholeRestartCrossingFiniteCoreState initial index crossed) *
        wholeRestartHalfCriticalCoefficientCeiling ν := by
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  let count := canonicalHalfCriticalComponentCount ν core
  have countNonneg : 0 ≤ (count : ℝ) := by positivity
  have reciprocalSqNonneg : 0 ≤ (count : ℝ)⁻¹ ^ 2 := sq_nonneg _
  have scaleNonneg : 0 ≤ (count : ℝ) * (count : ℝ)⁻¹ ^ 2 :=
    mul_nonneg countNonneg reciprocalSqNonneg
  have coreBound :
      ‖wholeRestartCrossingFiniteCoreNegativeOneState
          initial index crossed‖ ^ 2 ≤
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeVorticityEuclideanMass core := by
    simpa [wholeRestartCrossingFiniteCoreNegativeOneState,
      criticalEnstrophyLatticeConstant, core] using
      wholeStateVorticityNonlinearNegativeOneState_norm_sq_le
        core
        (wholeStateTransverse_sharpSupportProjection
          (wholeRestartCrossingFiniteCoreModes initial index crossed)
          (run initial index).contact.physicalState
          (run initial index).contact.transverse)
        (wholeRestartCrossingFiniteCore_gradient_summable
          initial index crossed)
  have countComponentMassLe :
      (count : ℝ) *
          wholeVorticityEuclideanMass
            (canonicalHalfCriticalComponent ν core) ≤
        wholeRestartHalfCriticalCoefficientCeiling ν := by
    simpa [count, core] using
      canonicalHalfCriticalComponent_count_mul_mass_le_ceiling ν core
  have componentMassEq :
      wholeVorticityEuclideanMass
          (canonicalHalfCriticalComponent ν core) =
        (count : ℝ)⁻¹ ^ 2 * wholeVorticityEuclideanMass core := by
    simpa [canonicalHalfCriticalComponent, count] using
      wholeVorticityEuclideanMass_real_smul
        (count : ℝ)⁻¹ core
  rw [wholeRestartCrossingFiniteComponentSelfNegativeOneState_eq_core_smul,
    norm_smul, mul_pow]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    (count : ℝ) *
          ((count : ℝ)⁻¹ ^ 2 *
            ‖wholeRestartCrossingFiniteCoreNegativeOneState
              initial index crossed‖ ^ 2) =
        ((count : ℝ) * (count : ℝ)⁻¹ ^ 2) *
          ‖wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed‖ ^ 2 := by ring
    _ ≤
        ((count : ℝ) * (count : ℝ)⁻¹ ^ 2) *
          (4 * criticalEnstrophyLatticeConstant *
            wholeStateVorticityGradientMass core *
            wholeVorticityEuclideanMass core) :=
      mul_le_mul_of_nonneg_left coreBound scaleNonneg
    _ =
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          ((count : ℝ) *
            wholeVorticityEuclideanMass
              (canonicalHalfCriticalComponent ν core)) := by
      rw [componentMassEq]
      ring
    _ ≤
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeRestartHalfCriticalCoefficientCeiling ν := by
      exact mul_le_mul_of_nonneg_left countComponentMassLe
        (mul_nonneg
          (mul_nonneg (by norm_num)
            criticalEnstrophyLatticeConstant_nonneg)
          (by
            unfold wholeStateVorticityGradientMass
            exact tsum_nonneg fun wave =>
              mul_nonneg (integerWaveNormSq_nonneg wave)
                (complexCoordinateAmplitudeSq_nonneg _)))

/-- The faithful-zero branch retains the source-generated reciprocal count
all the way through the whole `H⁻¹` estimate.  Multiplying the actual forcing
square by the actual component count still costs only one half-critical
gradient ceiling. -/
theorem
    wholeRestartCrossingWholeNegativeOneState_count_mul_norm_sq_le_component_ceiling
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0) :
    (canonicalHalfCriticalComponentCount ν
        (wholeRestartCrossingFiniteCoreState
          initial index crossed) : ℝ) *
        ‖wholeStateVorticityNonlinearNegativeOneState
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable‖ ^ 2 ≤
      4 * criticalEnstrophyLatticeConstant *
        wholeStateVorticityGradientMass
          (wholeRestartCrossingFiniteCoreState initial index crossed) *
        wholeRestartHalfCriticalCoefficientCeiling ν := by
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  let count := canonicalHalfCriticalComponentCount ν core
  have countNonneg : 0 ≤ (count : ℝ) := by positivity
  have reciprocalSqNonneg : 0 ≤ (count : ℝ)⁻¹ ^ 2 := sq_nonneg _
  have scaleNonneg : 0 ≤ (count : ℝ) * (count : ℝ)⁻¹ ^ 2 :=
    mul_nonneg countNonneg reciprocalSqNonneg
  have coreBound :
      ‖wholeRestartCrossingFiniteCoreNegativeOneState
          initial index crossed‖ ^ 2 ≤
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeVorticityEuclideanMass core := by
    simpa [wholeRestartCrossingFiniteCoreNegativeOneState,
      criticalEnstrophyLatticeConstant, core] using
      wholeStateVorticityNonlinearNegativeOneState_norm_sq_le
        core
        (wholeStateTransverse_sharpSupportProjection
          (wholeRestartCrossingFiniteCoreModes initial index crossed)
          (run initial index).contact.physicalState
          (run initial index).contact.transverse)
        (wholeRestartCrossingFiniteCore_gradient_summable
          initial index crossed)
  have countComponentMassLe :
      (count : ℝ) *
          wholeVorticityEuclideanMass
            (canonicalHalfCriticalComponent ν core) ≤
        wholeRestartHalfCriticalCoefficientCeiling ν := by
    simpa [count, core] using
      canonicalHalfCriticalComponent_count_mul_mass_le_ceiling ν core
  have componentMassEq :
      wholeVorticityEuclideanMass
          (canonicalHalfCriticalComponent ν core) =
        (count : ℝ)⁻¹ ^ 2 * wholeVorticityEuclideanMass core := by
    simpa [canonicalHalfCriticalComponent, count] using
      wholeVorticityEuclideanMass_real_smul
        (count : ℝ)⁻¹ core
  rw [wholeRestartCrossingWholeNegativeOneState_norm_sq_eq_core_of_gluing_zero
    initial index crossed gluingZero]
  calc
    (count : ℝ) *
          ((count : ℝ)⁻¹ ^ 2 *
            ‖wholeRestartCrossingFiniteCoreNegativeOneState
              initial index crossed‖ ^ 2) =
        ((count : ℝ) * (count : ℝ)⁻¹ ^ 2) *
          ‖wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed‖ ^ 2 := by ring
    _ ≤
        ((count : ℝ) * (count : ℝ)⁻¹ ^ 2) *
          (4 * criticalEnstrophyLatticeConstant *
            wholeStateVorticityGradientMass core *
            wholeVorticityEuclideanMass core) :=
      mul_le_mul_of_nonneg_left coreBound scaleNonneg
    _ =
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          ((count : ℝ) *
            wholeVorticityEuclideanMass
              (canonicalHalfCriticalComponent ν core)) := by
      rw [componentMassEq]
      ring
    _ ≤
        4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeRestartHalfCriticalCoefficientCeiling ν := by
      exact mul_le_mul_of_nonneg_left countComponentMassLe
        (mul_nonneg
          (mul_nonneg (by norm_num)
            criticalEnstrophyLatticeConstant_nonneg)
          (by
            unfold wholeStateVorticityGradientMass
            exact tsum_nonneg fun wave =>
              mul_nonneg (integerWaveNormSq_nonneg wave)
                (complexCoordinateAmplitudeSq_nonneg _)))

/-- The generated sharp core cannot carry more gradient mass than the same
actual crossing current. -/
theorem wholeRestartCrossingFiniteCore_gradientMass_le_whole
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeStateVorticityGradientMass
        (wholeRestartCrossingFiniteCoreState initial index crossed) ≤
      wholeStateVorticityGradientMass
        (run initial index).contact.physicalState := by
  let modes := wholeRestartCrossingFiniteCoreModes initial index crossed
  let whole := (run initial index).contact.physicalState
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  have coreSupported : ∀ wave : IntegerWavevector,
      wave ∉ modes → core wave = 0 := by
    exact wholeRestartInitialState_supported
      (run initial index).contact
      (wholeRestartCrossingFiniteCoreRadius initial index crossed)
  rw [wholeStateVorticityGradientMass_eq_finite_of_supported
    modes core coreSupported]
  have finiteEq :
      finiteStateVorticityEnstrophyMass modes core =
        finiteStateVorticityEnstrophyMass modes whole := by
    unfold finiteStateVorticityEnstrophyMass
    apply Finset.sum_congr rfl
    intro wave waveMem
    have coreEq : core = complexSharpSupportProjection modes whole := by
      simpa [core, modes, whole] using
        wholeRestartCrossingFiniteCoreState_eq_sharpSupportProjection
          initial index crossed
    rw [coreEq]
    simp [complexSharpSupportProjection_apply, waveMem]
  rw [finiteEq]
  exact finiteStateVorticityEnstrophyMass_le_wholeGradientMass
    modes whole (run initial index).contact.gradient_summable

/-- After evaluating the half-critical ceiling and using the actual crossing
count `≥ 3`, the faithful-zero whole forcing is genuinely sub-viscous:
three copies of its `H⁻¹` square fit below two viscous gradient copies.
No smallness, count, or absorption certificate enters the mouth. -/
theorem wholeRestartCrossingWholeNegativeOneState_three_mul_norm_sq_le_actualGradient
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0) :
    3 * ‖wholeStateVorticityNonlinearNegativeOneState
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable‖ ^ 2 ≤
      2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass
          (run initial index).contact.physicalState := by
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  let count := canonicalHalfCriticalComponentCount ν core
  let forcingSq :=
    ‖wholeStateVorticityNonlinearNegativeOneState
      (run initial index).contact.physicalState
      (run initial index).contact.transverse
      (run initial index).contact.gradient_summable‖ ^ 2
  have countBound :=
    wholeRestartCrossingWholeNegativeOneState_count_mul_norm_sq_le_component_ceiling
      initial index crossed gluingZero
  have constantIdentity :
      4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass core *
          wholeRestartHalfCriticalCoefficientCeiling ν =
        2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass core := by
    unfold wholeRestartHalfCriticalCoefficientCeiling
    field_simp [criticalEnstrophyLatticeConstant_pos.ne']
    ring
  rw [constantIdentity] at countBound
  have threeLeCountNat : 3 ≤ count := by
    simpa [count, core] using
      wholeRestartCrossingFiniteCore_three_le_componentCount
        initial index crossed
  have threeLeCount : (3 : ℝ) ≤ count := by exact_mod_cast threeLeCountNat
  have forcingSqNonneg : 0 ≤ forcingSq := by
    exact sq_nonneg _
  calc
    3 * forcingSq ≤ (count : ℝ) * forcingSq :=
      mul_le_mul_of_nonneg_right threeLeCount forcingSqNonneg
    _ ≤
        2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass core := by
      simpa [count, core, forcingSq] using countBound
    _ ≤
        2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass
            (run initial index).contact.physicalState :=
      mul_le_mul_of_nonneg_left
        (wholeRestartCrossingFiniteCore_gradientMass_le_whole
          initial index crossed)
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg _))
          (sq_nonneg _))

/-- Quantitative faithful-zero consumer.  The actual large-data nonlinear
forcing is bounded by a viscosity-scale multiple of the actual whole gradient
mass, with no caller-selected smallness knob.  The factor `2` is the current
sharp output of the existing whole `H⁻¹` estimate; improving it is a genuine
analytic question, not a component-count choice. -/
theorem wholeRestartCrossingWholeNegativeOneState_norm_sq_le_actualGradient
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0) :
    ‖wholeStateVorticityNonlinearNegativeOneState
        (run initial index).contact.physicalState
        (run initial index).contact.transverse
        (run initial index).contact.gradient_summable‖ ^ 2 ≤
      2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass
          (run initial index).contact.physicalState := by
  have componentBound :=
    wholeRestartCrossingWholeNegativeOneState_norm_sq_le_component_ceiling
      initial index crossed gluingZero
  have constantIdentity :
      4 * criticalEnstrophyLatticeConstant *
          wholeStateVorticityGradientMass
            (wholeRestartCrossingFiniteCoreState initial index crossed) *
          wholeRestartHalfCriticalCoefficientCeiling ν =
        2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass
            (wholeRestartCrossingFiniteCoreState initial index crossed) := by
    unfold wholeRestartHalfCriticalCoefficientCeiling
    field_simp [criticalEnstrophyLatticeConstant_pos.ne']
    ring
  rw [constantIdentity] at componentBound
  exact componentBound.trans
    (mul_le_mul_of_nonneg_left
      (wholeRestartCrossingFiniteCore_gradientMass_le_whole
        initial index crossed)
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (sq_nonneg _)))

/-- Every actual half-critical crossing now has an internally generated
physical alternative.  Either the entire whole nonlinear forcing collapses
to the reciprocal-count finite-core forcing, or the complete gluing
obstruction survives in `H⁻¹` and the existing native residual process writes
it into the next keep or the uniquely forced trace.

No branch, residual, nonzero witness, or next-state certificate is accepted
from the caller. -/
theorem wholeRestartCrossing_reduced_forcing_or_native_residual_transport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (wholeStateVorticityNonlinearNegativeOneState
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable =
        ((canonicalHalfCriticalComponentCount ν
            (wholeRestartCrossingFiniteCoreState
              initial index crossed) : ℝ)⁻¹ : ℂ) •
          wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed) ∨
      (wholeRestartCrossingCompleteSourceGluingNegativeOneState
            initial index crossed ≠ 0 ∧
        (wholeRestartComponentGluingResidualRow initial (index + 1) ≠ 0 ∨
          linearResidualTrace wholeRestartComponentGluingResidualTailKeep
              (wholeRestartComponentGluingResidualTail initial index) 0 ≠
            0)) := by
  by_cases gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0
  · exact Or.inl
      (wholeRestartCrossingWholeNegativeOneState_eq_core_smul_of_gluing_zero
        initial index crossed gluingZero)
  · right
    refine ⟨gluingZero, ?_⟩
    have nativeNonzero :
        wholeRestartComponentGluingResidualRow initial index ≠ 0 :=
      (wholeRestartComponentGluingResidualRow_nonzero_iff_negativeOne
        initial index crossed).2 gluingZero
    exact wholeRestartComponentGluingResidual_nonzero_next_or_trace
      initial index nativeNonzero

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
end NavierStokes
end SaturationMonoid
