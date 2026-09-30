import H0mework.NavierStokes.Restart.HalfCriticalDualSquareReduction

/-!
# Canonical half-critical component gluing on the whole vorticity carrier

An arbitrary whole Fourier state has a source-free, canonical equal-piece
decomposition whose pieces are strictly below the fixed half-critical mass
threshold.  This file keeps the generated occurrence order and expands the
whole nonlinear row into the exact sum of its self rows and all ordered cross
rows.  The cross ledger is the responsibility created by component formation;
it is not discarded by first summing equal Fourier coordinates.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing

open scoped BigOperators ENNReal

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalDualSquareReduction

noncomputable section

/-! ## Whole-carrier algebra -/

theorem wholeRestartHalfCriticalCoefficientCeiling_pos
    (ν : Viscosity) :
    0 < wholeRestartHalfCriticalCoefficientCeiling ν := by
  unfold wholeRestartHalfCriticalCoefficientCeiling
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos ν.coeff_pos))
      (sq_pos_of_pos (by positivity)))
    criticalEnstrophyLatticeConstant_pos

theorem wholeVorticityEuclideanMass_nonneg
    (state : ComplexVorticityHilbertState) :
    0 ≤ wholeVorticityEuclideanMass state := by
  unfold wholeVorticityEuclideanMass
  exact tsum_nonneg fun _ => sq_nonneg _

theorem wholeVorticityEuclideanMass_real_smul
    (scale : ℝ)
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass (scale • state) =
      scale ^ 2 * wholeVorticityEuclideanMass state := by
  have rowScale : ∀ wave : IntegerWavevector,
      vorticityRowAmplitude (scale • state) wave ^ 2 =
        scale ^ 2 * vorticityRowAmplitude state wave ^ 2 := by
    intro wave
    rw [vorticityRowAmplitude_sq, vorticityRowAmplitude_sq]
    change
      complexCoordinateVectorNormSq ((scale : ℂ) • state wave) = _
    rw [complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
    ring
  unfold wholeVorticityEuclideanMass
  simp_rw [rowScale]
  rw [tsum_mul_left]

theorem wholeStateTransverse_zero :
    WholeStateTransverse (0 : ComplexVorticityHilbertState) := by
  intro wave
  simp

theorem wholeStateTransverse_add
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right) :
    WholeStateTransverse (left + right) := by
  intro wave
  simp [dotProduct_add, leftTransverse wave, rightTransverse wave]

theorem wholeStateTransverse_real_smul
    (scale : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state) :
    WholeStateTransverse (scale • state) := by
  intro wave
  simp [dotProduct_smul, stateTransverse wave]

/-! ## Canonical no-parameter half-critical component producer -/

/-- The source-determined number of equal components.  The final successor
makes the strict half-critical inequality automatic, including at zero mass. -/
def canonicalHalfCriticalComponentCount
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) : ℕ :=
  Nat.ceil
      (wholeVorticityEuclideanMass state /
        wholeRestartHalfCriticalCoefficientCeiling ν) + 1

/-- One occurrence of the canonical equal component. -/
def canonicalHalfCriticalComponent
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  ((canonicalHalfCriticalComponentCount ν state : ℝ)⁻¹) • state

/-- Ordered occurrence list of the canonical equal components. -/
def canonicalHalfCriticalComponents
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    List ComplexVorticityHilbertState :=
  List.replicate
    (canonicalHalfCriticalComponentCount ν state)
    (canonicalHalfCriticalComponent ν state)

theorem canonicalHalfCriticalComponentCount_pos
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    0 < canonicalHalfCriticalComponentCount ν state := by
  unfold canonicalHalfCriticalComponentCount
  omega

theorem canonicalHalfCriticalComponentCount_ne_zero
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    canonicalHalfCriticalComponentCount ν state ≠ 0 :=
  Nat.ne_of_gt (canonicalHalfCriticalComponentCount_pos ν state)

theorem wholeVorticityEuclideanMass_lt_count_mul_ceiling
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass state <
      (canonicalHalfCriticalComponentCount ν state : ℝ) *
        wholeRestartHalfCriticalCoefficientCeiling ν := by
  let mass := wholeVorticityEuclideanMass state
  let ceiling := wholeRestartHalfCriticalCoefficientCeiling ν
  have ceilingPos : 0 < ceiling := by
    simpa [ceiling] using
      wholeRestartHalfCriticalCoefficientCeiling_pos ν
  have ratioLe :
      mass / ceiling ≤ (Nat.ceil (mass / ceiling) : ℝ) :=
    Nat.le_ceil (mass / ceiling)
  have ratioLt :
      mass / ceiling <
        (Nat.ceil (mass / ceiling) + 1 : ℕ) := by
    exact lt_of_le_of_lt ratioLe (by exact_mod_cast Nat.lt_succ_self _)
  have massLt :
      mass <
        (Nat.ceil (mass / ceiling) + 1 : ℕ) * ceiling := by
    apply (div_lt_iff₀ ceilingPos).mp
    simpa [mul_assoc] using ratioLt
  simpa [canonicalHalfCriticalComponentCount, mass, ceiling] using massLt

theorem canonicalHalfCriticalComponent_mass_lt_ceiling
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass
        (canonicalHalfCriticalComponent ν state) <
      wholeRestartHalfCriticalCoefficientCeiling ν := by
  let count := canonicalHalfCriticalComponentCount ν state
  let mass := wholeVorticityEuclideanMass state
  let ceiling := wholeRestartHalfCriticalCoefficientCeiling ν
  have countPosNat : 0 < count := by
    simpa [count] using canonicalHalfCriticalComponentCount_pos ν state
  have countPos : (0 : ℝ) < count := by exact_mod_cast countPosNat
  have massNonneg : 0 ≤ mass := by
    simpa [mass] using wholeVorticityEuclideanMass_nonneg state
  have massLt : mass < (count : ℝ) * ceiling := by
    simpa [mass, count, ceiling] using
      wholeVorticityEuclideanMass_lt_count_mul_ceiling ν state
  rw [canonicalHalfCriticalComponent,
    wholeVorticityEuclideanMass_real_smul]
  change ((count : ℝ)⁻¹) ^ 2 * mass < ceiling
  have countOne : (1 : ℝ) ≤ count := by exact_mod_cast countPosNat
  have massLtSquare : mass < (count : ℝ) ^ 2 * ceiling := by
    have countLeSquare : (count : ℝ) ≤ (count : ℝ) ^ 2 := by
      nlinarith
    have ceilingPos : 0 < ceiling := by
      simpa [ceiling] using
        wholeRestartHalfCriticalCoefficientCeiling_pos ν
    nlinarith
  field_simp
  nlinarith

/-- The source-generated component count is not disposable bookkeeping.
After one component has been formed, multiplying its mass back by the actual
count still stays below the half-critical ceiling.  This retains the extra
reciprocal-count gain needed by downstream large-data consumers. -/
theorem canonicalHalfCriticalComponent_count_mul_mass_le_ceiling
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    (canonicalHalfCriticalComponentCount ν state : ℝ) *
        wholeVorticityEuclideanMass
          (canonicalHalfCriticalComponent ν state) ≤
      wholeRestartHalfCriticalCoefficientCeiling ν := by
  let count := canonicalHalfCriticalComponentCount ν state
  let mass := wholeVorticityEuclideanMass state
  let ceiling := wholeRestartHalfCriticalCoefficientCeiling ν
  have countPosNat : 0 < count := by
    simpa [count] using canonicalHalfCriticalComponentCount_pos ν state
  have countNe : (count : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt countPosNat)
  have massLt : mass < (count : ℝ) * ceiling := by
    simpa [mass, count, ceiling] using
      wholeVorticityEuclideanMass_lt_count_mul_ceiling ν state
  rw [canonicalHalfCriticalComponent,
    wholeVorticityEuclideanMass_real_smul]
  change
    (count : ℝ) * ((count : ℝ)⁻¹ ^ 2 * mass) ≤ ceiling
  field_simp [countNe]
  exact massLt.le

theorem canonicalHalfCriticalComponent_strictly_halfCritical
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    criticalEnstrophyLatticeConstant *
        wholeVorticityEuclideanMass
          (canonicalHalfCriticalComponent ν state) <
      (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
  have componentLt :=
    canonicalHalfCriticalComponent_mass_lt_ceiling ν state
  rw [wholeRestartHalfCriticalCoefficientCeiling] at componentLt
  simpa only [mul_comm] using
    (lt_div_iff₀ criticalEnstrophyLatticeConstant_pos).mp componentLt

@[simp] theorem canonicalHalfCriticalComponents_length
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    (canonicalHalfCriticalComponents ν state).length =
      canonicalHalfCriticalComponentCount ν state := by
  simp [canonicalHalfCriticalComponents]

theorem canonicalHalfCriticalComponents_sum
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState) :
    (canonicalHalfCriticalComponents ν state).sum = state := by
  let count := canonicalHalfCriticalComponentCount ν state
  have countNe : count ≠ 0 := by
    simpa [count] using canonicalHalfCriticalComponentCount_ne_zero ν state
  rw [canonicalHalfCriticalComponents, List.sum_replicate,
    canonicalHalfCriticalComponent]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul]
  simp [count, countNe]

theorem canonicalHalfCriticalComponents_forall_halfCritical
    (ν : Viscosity)
    (state component : ComplexVorticityHilbertState)
    (componentMem : component ∈ canonicalHalfCriticalComponents ν state) :
    criticalEnstrophyLatticeConstant *
        wholeVorticityEuclideanMass component <
      (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
  have componentEq :
      component = canonicalHalfCriticalComponent ν state := by
    have replicated := componentMem
    simp only [canonicalHalfCriticalComponents, List.mem_replicate]
      at replicated
    exact replicated.2
  subst component
  exact canonicalHalfCriticalComponent_strictly_halfCritical ν state

theorem canonicalHalfCriticalComponents_forall_transverse
    (ν : Viscosity)
    (state component : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (componentMem : component ∈ canonicalHalfCriticalComponents ν state) :
    WholeStateTransverse component := by
  have componentEq :
      component = canonicalHalfCriticalComponent ν state := by
    have replicated := componentMem
    simp only [canonicalHalfCriticalComponents, List.mem_replicate]
      at replicated
    exact replicated.2
  subst component
  exact wholeStateTransverse_real_smul _ _ stateTransverse

/-! ## Exact ordered self/cross gluing ledger -/

theorem finiteStateVelocityCoefficient_add
    (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    finiteStateVelocityCoefficient (left + right) wave =
      finiteStateVelocityCoefficient left wave +
        finiteStateVelocityCoefficient right wave := by
  change
    biotSavartVelocityCoefficient wave (left wave + right wave) =
      biotSavartVelocityCoefficient wave (left wave) +
        biotSavartVelocityCoefficient wave (right wave)
  by_cases waveZero : wave = 0
  · subst wave
    simp
  · rw [biotSavartVelocityCoefficient, if_neg waveZero,
      biotSavartVelocityCoefficient, if_neg waveZero,
      biotSavartVelocityCoefficient, if_neg waveZero,
      map_add, smul_add]

theorem finiteStateVelocityCoefficient_real_smul
    (scale : ℝ)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    finiteStateVelocityCoefficient (scale • state) wave =
      (scale : ℂ) • finiteStateVelocityCoefficient state wave := by
  change
    biotSavartVelocityCoefficient wave ((scale : ℂ) • state wave) = _
  exact biotSavartVelocityCoefficient_smul wave scale (state wave)

@[simp] theorem finiteStateVelocityCoefficient_zero
    (wave : IntegerWavevector) :
    finiteStateVelocityCoefficient
        (0 : ComplexVorticityHilbertState) wave = 0 := by
  change biotSavartVelocityCoefficient wave 0 = 0
  by_cases waveZero : wave = 0
  · subst wave
    simp
  · simp [biotSavartVelocityCoefficient, waveZero]

theorem finiteStateVorticityBilinearPairContribution_add_left
    (left₁ left₂ right : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        (left₁ + left₂) right pair =
      finiteStateVorticityBilinearPairContribution left₁ right pair +
        finiteStateVorticityBilinearPairContribution left₂ right pair := by
  simp [finiteStateVorticityBilinearPairContribution,
    finiteStateVelocityCoefficient_add]
  module

theorem finiteStateVorticityBilinearPairContribution_add_right
    (left right₁ right₂ : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        left (right₁ + right₂) pair =
      finiteStateVorticityBilinearPairContribution left right₁ pair +
        finiteStateVorticityBilinearPairContribution left right₂ pair := by
  simp [finiteStateVorticityBilinearPairContribution,
    finiteStateVelocityCoefficient_add]
  module

theorem finiteStateVorticityNonlinearPairContribution_real_smul
    (scale : ℝ)
    (state : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityNonlinearPairContribution
        (scale • state) pair =
      ((scale : ℂ) ^ 2) •
        finiteStateVorticityNonlinearPairContribution state pair := by
  have stateApply : ∀ wave : IntegerWavevector,
      (scale • state) wave = (scale : ℂ) • state wave := by
    intro wave
    rfl
  simp only [finiteStateVorticityNonlinearPairContribution,
    stateApply,
    finiteStateVelocityCoefficient_real_smul,
    dotProduct_smul, smul_smul]
  module

theorem wholeStateVorticityNonlinearCoefficientAt_real_smul
    (scale : ℝ)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt
        (scale • state) output =
      ((scale : ℂ) ^ 2) •
        wholeStateVorticityNonlinearCoefficientAt state output := by
  unfold wholeStateVorticityNonlinearCoefficientAt
  simp_rw [finiteStateVorticityNonlinearPairContribution_real_smul]
  rw [tsum_const_smul'']

theorem wholeStateVorticityBilinearCoefficientAt_add_left
    (left₁ left₂ right : ComplexVorticityHilbertState)
    (left₁Transverse : WholeStateTransverse left₁)
    (left₂Transverse : WholeStateTransverse left₂)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        (left₁ + left₂) right output =
      wholeStateVorticityBilinearCoefficientAt left₁ right output +
        wholeStateVorticityBilinearCoefficientAt left₂ right output := by
  unfold wholeStateVorticityBilinearCoefficientAt
  rw [← Summable.tsum_add
    (summable_wholeStateVorticityBilinearPair
      left₁ right left₁Transverse output)
    (summable_wholeStateVorticityBilinearPair
      left₂ right left₂Transverse output)]
  apply tsum_congr
  intro first
  exact finiteStateVorticityBilinearPairContribution_add_left
    left₁ left₂ right (first, output - first)

theorem wholeStateVorticityBilinearCoefficientAt_add_right
    (left right₁ right₂ : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        left (right₁ + right₂) output =
      wholeStateVorticityBilinearCoefficientAt left right₁ output +
        wholeStateVorticityBilinearCoefficientAt left right₂ output := by
  unfold wholeStateVorticityBilinearCoefficientAt
  rw [← Summable.tsum_add
    (summable_wholeStateVorticityBilinearPair
      left right₁ leftTransverse output)
    (summable_wholeStateVorticityBilinearPair
      left right₂ leftTransverse output)]
  apply tsum_congr
  intro first
  exact finiteStateVorticityBilinearPairContribution_add_right
    left right₁ right₂ (first, output - first)

theorem wholeStateVorticityNonlinearCoefficientAt_add
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt (left + right) output =
      wholeStateVorticityNonlinearCoefficientAt left output +
        wholeStateVorticityNonlinearCoefficientAt right output +
      wholeStateVorticityBilinearCoefficientAt left right output +
        wholeStateVorticityBilinearCoefficientAt right left output := by
  rw [← wholeStateVorticityBilinearCoefficientAt_self]
  rw [wholeStateVorticityBilinearCoefficientAt_add_left
      left right (left + right) leftTransverse rightTransverse output]
  rw [wholeStateVorticityBilinearCoefficientAt_add_right
      left left right leftTransverse output]
  rw [wholeStateVorticityBilinearCoefficientAt_add_right
      right left right rightTransverse output]
  rw [wholeStateVorticityBilinearCoefficientAt_self,
    wholeStateVorticityBilinearCoefficientAt_self]
  abel

/-- Ordered cross responsibility.  At each occurrence it records both
orientations against every later occurrence before coefficient quotienting. -/
def wholeComponentCrossGluingResidual :
    List ComplexVorticityHilbertState →
      IntegerWavevector → ComplexCoordinateVector
  | [], _output => 0
  | head :: tail, output =>
      wholeComponentCrossGluingResidual tail output +
        (tail.map fun other =>
          wholeStateVorticityBilinearCoefficientAt head other output).sum +
        (tail.map fun other =>
          wholeStateVorticityBilinearCoefficientAt other head output).sum

theorem wholeStateTransverse_listSum
    (components : List ComplexVorticityHilbertState)
    (allTransverse : ∀ component ∈ components,
      WholeStateTransverse component) :
    WholeStateTransverse components.sum := by
  induction components with
  | nil => exact wholeStateTransverse_zero
  | cons head tail inductionHypothesis =>
      exact wholeStateTransverse_add head tail.sum
        (allTransverse head (by simp))
        (inductionHypothesis (by
          intro component componentMem
          exact allTransverse component (by simp [componentMem])))

theorem wholeStateVorticityBilinearCoefficientAt_listSum_left
    (components : List ComplexVorticityHilbertState)
    (right : ComplexVorticityHilbertState)
    (allTransverse : ∀ component ∈ components,
      WholeStateTransverse component)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        components.sum right output =
      (components.map fun component =>
        wholeStateVorticityBilinearCoefficientAt
          component right output).sum := by
  induction components with
  | nil =>
      simp [wholeStateVorticityBilinearCoefficientAt,
        finiteStateVorticityBilinearPairContribution]
  | cons head tail inductionHypothesis =>
      have headTransverse : WholeStateTransverse head :=
        allTransverse head (by simp)
      have tailTransverse : ∀ component ∈ tail,
          WholeStateTransverse component := by
        intro component componentMem
        exact allTransverse component (by simp [componentMem])
      have tailSumTransverse : WholeStateTransverse tail.sum := by
        exact wholeStateTransverse_listSum tail tailTransverse
      rw [List.sum_cons,
        wholeStateVorticityBilinearCoefficientAt_add_left
          head tail.sum right headTransverse tailSumTransverse output,
        inductionHypothesis tailTransverse]
      rfl

theorem wholeStateVorticityBilinearCoefficientAt_listSum_right
    (left : ComplexVorticityHilbertState)
    (components : List ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        left components.sum output =
      (components.map fun component =>
        wholeStateVorticityBilinearCoefficientAt
          left component output).sum := by
  induction components with
  | nil =>
      simp [wholeStateVorticityBilinearCoefficientAt,
        finiteStateVorticityBilinearPairContribution]
  | cons head tail inductionHypothesis =>
      rw [List.sum_cons,
        wholeStateVorticityBilinearCoefficientAt_add_right
          left head tail.sum leftTransverse output,
        inductionHypothesis]
      rfl

theorem wholeStateVorticityNonlinearCoefficientAt_listSum_self_cross
    (components : List ComplexVorticityHilbertState)
    (allTransverse : ∀ component ∈ components,
      WholeStateTransverse component)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt components.sum output =
      (components.map fun component =>
        wholeStateVorticityNonlinearCoefficientAt component output).sum +
      wholeComponentCrossGluingResidual components output := by
  induction components with
  | nil =>
      simp [wholeStateVorticityNonlinearCoefficientAt,
        finiteStateVorticityNonlinearPairContribution,
        wholeComponentCrossGluingResidual]
  | cons head tail inductionHypothesis =>
      have headTransverse : WholeStateTransverse head :=
        allTransverse head (by simp)
      have tailTransverse : ∀ component ∈ tail,
          WholeStateTransverse component := by
        intro component componentMem
        exact allTransverse component (by simp [componentMem])
      have tailSumTransverse : WholeStateTransverse tail.sum := by
        exact wholeStateTransverse_listSum tail tailTransverse
      rw [List.sum_cons,
        wholeStateVorticityNonlinearCoefficientAt_add
          head tail.sum headTransverse tailSumTransverse output,
        inductionHypothesis tailTransverse,
        wholeStateVorticityBilinearCoefficientAt_listSum_right
          head tail headTransverse output,
        wholeStateVorticityBilinearCoefficientAt_listSum_left
          tail head tailTransverse output]
      simp only [List.map_cons, List.sum_cons,
        wholeComponentCrossGluingResidual]
      abel

/-- Canonical arbitrary-state half-critical gluing theorem.  The original
whole nonlinear row is exactly reconstructed from strictly half-critical
self rows plus the ordered cross-occurrence residual. -/
theorem canonicalHalfCriticalComponents_wholeNonlinear_self_cross
    (ν : Viscosity)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt state output =
      ((canonicalHalfCriticalComponents ν state).map fun component =>
        wholeStateVorticityNonlinearCoefficientAt component output).sum +
      wholeComponentCrossGluingResidual
        (canonicalHalfCriticalComponents ν state) output := by
  calc
    wholeStateVorticityNonlinearCoefficientAt state output =
        wholeStateVorticityNonlinearCoefficientAt
          (canonicalHalfCriticalComponents ν state).sum output := by
      rw [canonicalHalfCriticalComponents_sum]
    _ = _ :=
      wholeStateVorticityNonlinearCoefficientAt_listSum_self_cross
        (canonicalHalfCriticalComponents ν state)
        (fun component componentMem =>
          canonicalHalfCriticalComponents_forall_transverse
            ν state component stateTransverse componentMem)
        output

/-! ## Exact scaling regression -/

/-- For two equal half occurrences the pre-quotient cross ledger carries
exactly the other half of the original quadratic row.  This validates the
ledger's quadratic coefficient without replacing the general List theorem. -/
theorem wholeComponentCrossGluingResidual_two_equal_halves
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeComponentCrossGluingResidual
        [((1 / 2 : ℝ) • state), ((1 / 2 : ℝ) • state)] output =
      ((1 / 2 : ℂ)) •
        wholeStateVorticityNonlinearCoefficientAt state output := by
  simp only [wholeComponentCrossGluingResidual, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
  rw [wholeStateVorticityBilinearCoefficientAt_self,
    wholeStateVorticityNonlinearCoefficientAt_real_smul]
  norm_num
  module

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
end NavierStokes
end SaturationMonoid
