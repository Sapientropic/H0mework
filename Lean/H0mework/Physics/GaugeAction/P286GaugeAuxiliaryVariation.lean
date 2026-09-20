import H0mework.Physics.Exterior.HyperchargeAuxiliaryVariation

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeAuxiliaryVariation

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNineCoframeTwoFormPairing
open StageNineGravityAuxiliaryVariation
open StageNineHyperchargeAuxiliaryVariation
open EmpiricalReferenceScaleCouplingBoundary
open Matrix
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem specialUnitaryLiePairing_add_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (first + second) residual =
      specialUnitaryLiePairing first residual +
        specialUnitaryLiePairing second residual := by
  simp [specialUnitaryLiePairing, Matrix.add_mul, Matrix.trace_add]
  ring

theorem specialUnitaryLiePairing_add_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing residual (first + second) =
      specialUnitaryLiePairing residual first +
        specialUnitaryLiePairing residual second := by
  simp [specialUnitaryLiePairing, Matrix.mul_add, Matrix.trace_add]
  ring

theorem specialUnitaryLiePairing_smul_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (parameter • first) residual =
      parameter * specialUnitaryLiePairing first residual := by
  simp [specialUnitaryLiePairing, Matrix.trace_smul]

theorem specialUnitaryLiePairing_smul_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing residual (parameter • first) =
      parameter * specialUnitaryLiePairing residual first := by
  simp [specialUnitaryLiePairing, Matrix.trace_smul]

theorem specialUnitaryLiePairing_symmetric
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing first second =
      specialUnitaryLiePairing second first := by
  unfold specialUnitaryLiePairing
  rw [Matrix.trace_mul_comm]

theorem specialUnitaryLiePairing_self_eq_sum_normSq
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing matrix matrix =
      ∑ row : n, ∑ column : n,
        Complex.normSq ((matrix : Matrix n n ℂ) column row) := by
  unfold specialUnitaryLiePairing
  calc
    -(Matrix.trace
        ((matrix : Matrix n n ℂ) * (matrix : Matrix n n ℂ))).re =
      (Matrix.trace
        ((-(matrix : Matrix n n ℂ)) *
          (matrix : Matrix n n ℂ))).re := by simp
    _ = (Matrix.trace
        (star (matrix : Matrix n n ℂ) *
          (matrix : Matrix n n ℂ))).re := by
      rw [specialUnitaryLieMatrix_star]
    _ = _ := by
      simp [Matrix.trace, Matrix.mul_apply, star_eq_conjTranspose,
        Complex.normSq_apply, Complex.mul_re]

theorem specialUnitaryLiePairing_self_nonnegative
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    0 ≤ specialUnitaryLiePairing matrix matrix := by
  rw [specialUnitaryLiePairing_self_eq_sum_normSq]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem specialUnitaryLiePairing_self_eq_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing matrix matrix = 0 ↔ matrix = 0 := by
  rw [specialUnitaryLiePairing_self_eq_sum_normSq]
  constructor
  · intro sumZero
    apply Subtype.ext
    funext row column
    have columnSumZero :
        (∑ candidateRow : n,
          Complex.normSq
            ((matrix : Matrix n n ℂ) candidateRow column)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).mp
          sumZero column (Finset.mem_univ column)
    have entryNormZero :
        Complex.normSq ((matrix : Matrix n n ℂ) row column) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
        Complex.normSq_nonneg _)).mp columnSumZero row (Finset.mem_univ row)
    exact Complex.normSq_eq_zero.mp entryNormZero
  · intro matrixZero
    subst matrix
    simp

theorem hyperchargeLiePairing_add_left
    (first second residual : HyperchargeLieScalar) :
    hyperchargeLiePairing (first + second) residual =
      hyperchargeLiePairing first residual +
        hyperchargeLiePairing second residual := by
  simp_rw [hyperchargeLiePairing_eq_coordinate_mul, map_add]
  ring

theorem hyperchargeLiePairing_add_right
    (first second residual : HyperchargeLieScalar) :
    hyperchargeLiePairing residual (first + second) =
      hyperchargeLiePairing residual first +
        hyperchargeLiePairing residual second := by
  simp_rw [hyperchargeLiePairing_eq_coordinate_mul, map_add]
  ring

theorem hyperchargeLiePairing_smul_left
    (parameter : ℝ) (first residual : HyperchargeLieScalar) :
    hyperchargeLiePairing (parameter • first) residual =
      parameter * hyperchargeLiePairing first residual := by
  simp_rw [hyperchargeLiePairing_eq_coordinate_mul, map_smul]
  ring

theorem hyperchargeLiePairing_smul_right
    (parameter : ℝ) (first residual : HyperchargeLieScalar) :
    hyperchargeLiePairing residual (parameter • first) =
      parameter * hyperchargeLiePairing residual first := by
  simp_rw [hyperchargeLiePairing_eq_coordinate_mul, map_smul]
  ring

theorem hyperchargeLiePairing_symmetric
    (first second : HyperchargeLieScalar) :
    hyperchargeLiePairing first second =
      hyperchargeLiePairing second first := by
  rw [hyperchargeLiePairing_eq_coordinate_mul,
    hyperchargeLiePairing_eq_coordinate_mul]
  ring

def p286LiePairing (first second : P286LieBlockData) : ℝ :=
  specialUnitaryLiePairing first.1 second.1 +
    specialUnitaryLiePairing first.2.1 second.2.1 +
    hyperchargeLiePairing first.2.2 second.2.2

theorem p286LiePairing_add_left
    (first second residual : P286LieBlockData) :
    p286LiePairing (first + second) residual =
      p286LiePairing first residual + p286LiePairing second residual := by
  simp [p286LiePairing, specialUnitaryLiePairing_add_left,
    hyperchargeLiePairing_add_left]
  ring

theorem p286LiePairing_add_right
    (first second residual : P286LieBlockData) :
    p286LiePairing residual (first + second) =
      p286LiePairing residual first + p286LiePairing residual second := by
  simp [p286LiePairing, specialUnitaryLiePairing_add_right,
    hyperchargeLiePairing_add_right]
  ring

theorem p286LiePairing_smul_left
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LiePairing (parameter • first) residual =
      parameter * p286LiePairing first residual := by
  simp [p286LiePairing, specialUnitaryLiePairing_smul_left,
    hyperchargeLiePairing_smul_left]
  ring

theorem p286LiePairing_smul_right
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LiePairing residual (parameter • first) =
      parameter * p286LiePairing residual first := by
  simp [p286LiePairing, specialUnitaryLiePairing_smul_right,
    hyperchargeLiePairing_smul_right]
  ring

theorem p286LiePairing_symmetric (first second : P286LieBlockData) :
    p286LiePairing first second = p286LiePairing second first := by
  simp [p286LiePairing, specialUnitaryLiePairing_symmetric,
    hyperchargeLiePairing_symmetric]

theorem p286LiePairing_self_nonnegative (data : P286LieBlockData) :
    0 ≤ p286LiePairing data data := by
  have strongNonnegative :=
    specialUnitaryLiePairing_self_nonnegative data.1
  have weakNonnegative :=
    specialUnitaryLiePairing_self_nonnegative data.2.1
  have hyperchargeNonnegative :
      0 ≤ hyperchargeLiePairing data.2.2 data.2.2 := by
    rw [hyperchargeLiePairing_eq_coordinate_mul]
    exact mul_self_nonneg _
  unfold p286LiePairing
  linarith

theorem p286LiePairing_self_eq_zero_iff (data : P286LieBlockData) :
    p286LiePairing data data = 0 ↔ data = 0 := by
  constructor
  · intro pairingZero
    have strongNonnegative :=
      specialUnitaryLiePairing_self_nonnegative data.1
    have weakNonnegative :=
      specialUnitaryLiePairing_self_nonnegative data.2.1
    have hyperchargeNonnegative :
        0 ≤ hyperchargeLiePairing data.2.2 data.2.2 := by
      rw [hyperchargeLiePairing_eq_coordinate_mul]
      exact mul_self_nonneg _
    have strongZero : specialUnitaryLiePairing data.1 data.1 = 0 := by
      unfold p286LiePairing at pairingZero
      linarith
    have weakZero : specialUnitaryLiePairing data.2.1 data.2.1 = 0 := by
      unfold p286LiePairing at pairingZero
      linarith
    have hyperchargeZero :
        hyperchargeLiePairing data.2.2 data.2.2 = 0 := by
      unfold p286LiePairing at pairingZero
      linarith
    have strongDataZero : data.1 = 0 :=
      (specialUnitaryLiePairing_self_eq_zero_iff data.1).mp strongZero
    have weakDataZero : data.2.1 = 0 :=
      (specialUnitaryLiePairing_self_eq_zero_iff data.2.1).mp weakZero
    have hyperchargeDataZero : data.2.2 = 0 := by
      apply hyperchargeCoordinateEquiv.injective
      rw [hyperchargeLiePairing_eq_coordinate_mul] at hyperchargeZero
      exact sq_eq_zero_iff.mp (by simpa [pow_two] using hyperchargeZero)
    exact Prod.ext strongDataZero (Prod.ext weakDataZero hyperchargeDataZero)
  · intro dataZero
    subst data
    simp [p286LiePairing, specialUnitaryLiePairing,
      hyperchargeLiePairing]

def p286CoordinateLiePairing
    (first second : P286CoordinateCarrier) : ℝ :=
  p286LiePairing (p286CoordinateEquiv.symm first)
    (p286CoordinateEquiv.symm second)

theorem p286CoordinateLiePairing_add_left
    (first second residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing (first + second) residual =
      p286CoordinateLiePairing first residual +
        p286CoordinateLiePairing second residual := by
  unfold p286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_add]
  exact p286LiePairing_add_left _ _ _

theorem p286CoordinateLiePairing_add_right
    (first second residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing residual (first + second) =
      p286CoordinateLiePairing residual first +
        p286CoordinateLiePairing residual second := by
  unfold p286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_add]
  exact p286LiePairing_add_right _ _ _

theorem p286CoordinateLiePairing_smul_left
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing (parameter • first) residual =
      parameter * p286CoordinateLiePairing first residual := by
  unfold p286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_smul]
  exact p286LiePairing_smul_left _ _ _

theorem p286CoordinateLiePairing_smul_right
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing residual (parameter • first) =
      parameter * p286CoordinateLiePairing residual first := by
  unfold p286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_smul]
  exact p286LiePairing_smul_right _ _ _

theorem p286CoordinateLiePairing_symmetric
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first second =
      p286CoordinateLiePairing second first :=
  p286LiePairing_symmetric _ _

theorem p286CoordinateLiePairing_self_nonnegative
    (coordinate : P286CoordinateCarrier) :
    0 ≤ p286CoordinateLiePairing coordinate coordinate :=
  p286LiePairing_self_nonnegative _

theorem p286CoordinateLiePairing_self_eq_zero_iff
    (coordinate : P286CoordinateCarrier) :
    p286CoordinateLiePairing coordinate coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro pairingZero
    have typedZero : p286CoordinateEquiv.symm coordinate = 0 :=
      (p286LiePairing_self_eq_zero_iff _).mp pairingZero
    apply p286CoordinateEquiv.symm.injective
    simpa using typedZero
  · intro coordinateZero
    subst coordinate
    simp [p286CoordinateLiePairing, p286LiePairing,
      specialUnitaryLiePairing, hyperchargeLiePairing]

def p286CoordinateLiePairingBilinear :
    P286CoordinateCarrier →ₗ[ℝ] P286CoordinateCarrier →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := fun second => p286CoordinateLiePairing first second
      map_add' := by
        intro second third
        exact p286CoordinateLiePairing_add_right second third first
      map_smul' := by
        intro parameter second
        simpa [smul_eq_mul] using
          p286CoordinateLiePairing_smul_right parameter second first }
  map_add' := by
    intro first second
    ext residual
    exact p286CoordinateLiePairing_add_left first second residual
  map_smul' := by
    intro parameter first
    ext residual
    simpa [smul_eq_mul] using
      p286CoordinateLiePairing_smul_left parameter first residual

@[simp] theorem p286CoordinateLiePairingBilinear_apply
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairingBilinear first second =
      p286CoordinateLiePairing first second :=
  rfl

theorem p286CoordinateLiePairing_apply_continuous
    (first second : BasePoint → P286CoordinateCarrier)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      p286CoordinateLiePairing (first point) (second point) := by
  have bilinearContinuous : Continuous fun pair :
      P286CoordinateCarrier × P286CoordinateCarrier =>
      p286CoordinateLiePairingBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((p286CoordinateLiePairingBilinear.toContinuousBilinearMap.continuous.comp
        continuous_fst).prodMk continuous_snd)
  have actual :=
    bilinearContinuous.comp (firstContinuous.prodMk secondContinuous)
  exact actual.congr fun point => rfl

theorem suLieBracket_add_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    suLieBracket (first + second) residual =
      suLieBracket first residual + suLieBracket second residual := by
  apply Subtype.ext
  simp [suLieBracket, Matrix.add_mul, Matrix.mul_add]
  abel

theorem suLieBracket_add_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    suLieBracket residual (first + second) =
      suLieBracket residual first + suLieBracket residual second := by
  apply Subtype.ext
  simp [suLieBracket, Matrix.add_mul, Matrix.mul_add]
  abel

theorem suLieBracket_smul_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    suLieBracket (parameter • first) residual =
      parameter • suLieBracket first residual := by
  apply Subtype.ext
  simp [suLieBracket]
  rw [smul_sub]

theorem suLieBracket_smul_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    suLieBracket residual (parameter • first) =
      parameter • suLieBracket residual first := by
  apply Subtype.ext
  simp [suLieBracket]
  rw [smul_sub]

theorem p286LieBracket_add_left
    (first second residual : P286LieBlockData) :
    p286LieBracket (first + second) residual =
      p286LieBracket first residual + p286LieBracket second residual := by
  apply Prod.ext
  · exact suLieBracket_add_left first.1 second.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_add_left first.2.1 second.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_add_right
    (first second residual : P286LieBlockData) :
    p286LieBracket residual (first + second) =
      p286LieBracket residual first + p286LieBracket residual second := by
  apply Prod.ext
  · exact suLieBracket_add_right first.1 second.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_add_right first.2.1 second.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_smul_left
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LieBracket (parameter • first) residual =
      parameter • p286LieBracket first residual := by
  apply Prod.ext
  · exact suLieBracket_smul_left parameter first.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_smul_left parameter first.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_smul_right
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LieBracket residual (parameter • first) =
      parameter • p286LieBracket residual first := by
  apply Prod.ext
  · exact suLieBracket_smul_right parameter first.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_smul_right parameter first.2.1 residual.2.1
    · simp [p286LieBracket]

def p286CoordinateLieBracket
    (first second : P286CoordinateCarrier) : P286CoordinateCarrier :=
  p286CoordinateEquiv
    (p286LieBracket (p286CoordinateEquiv.symm first)
      (p286CoordinateEquiv.symm second))

theorem p286CoordinateLieBracket_add_left
    (first second residual : P286CoordinateCarrier) :
    p286CoordinateLieBracket (first + second) residual =
      p286CoordinateLieBracket first residual +
        p286CoordinateLieBracket second residual := by
  unfold p286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_add, p286LieBracket_add_left, map_add]

theorem p286CoordinateLieBracket_add_right
    (first second residual : P286CoordinateCarrier) :
    p286CoordinateLieBracket residual (first + second) =
      p286CoordinateLieBracket residual first +
        p286CoordinateLieBracket residual second := by
  unfold p286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_add, p286LieBracket_add_right, map_add]

theorem p286CoordinateLieBracket_smul_left
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    p286CoordinateLieBracket (parameter • first) residual =
      parameter • p286CoordinateLieBracket first residual := by
  unfold p286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBracket_smul_left, map_smul]

theorem p286CoordinateLieBracket_smul_right
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    p286CoordinateLieBracket residual (parameter • first) =
      parameter • p286CoordinateLieBracket residual first := by
  unfold p286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBracket_smul_right, map_smul]

def p286CoordinateLieBracketBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      P286CoordinateCarrier →ₗ[ℝ] P286CoordinateCarrier where
  toFun first :=
    { toFun := fun second => p286CoordinateLieBracket first second
      map_add' := by
        intro second third
        exact p286CoordinateLieBracket_add_right second third first
      map_smul' := by
        intro parameter second
        exact p286CoordinateLieBracket_smul_right parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact p286CoordinateLieBracket_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    exact p286CoordinateLieBracket_smul_left parameter first residual

@[simp] theorem p286CoordinateLieBracketBilinear_apply
    (first second : P286CoordinateCarrier) :
    p286CoordinateLieBracketBilinear first second =
      p286CoordinateLieBracket first second :=
  rfl

theorem p286CoordinateLieBracket_apply_continuous
    (first second : BasePoint → P286CoordinateCarrier)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      p286CoordinateLieBracket (first point) (second point) := by
  have bilinearContinuous : Continuous fun pair :
      P286CoordinateCarrier × P286CoordinateCarrier =>
      p286CoordinateLieBracketBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((p286CoordinateLieBracketBilinear.toContinuousBilinearMap.continuous.comp
        continuous_fst).prodMk continuous_snd)
  have actual :=
    bilinearContinuous.comp (firstContinuous.prodMk secondContinuous)
  exact actual.congr fun point => rfl

theorem p286ConnectionDerivative_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection : LorentzianIndex) :
    Continuous fun point =>
      p286CoordinateEquiv
        (p286ConnectionDerivative configuration point derivativeDirection
          formDirection) := by
  have derivativeContinuous : Continuous
      (fderiv ℝ (fun candidate =>
        p286CoordinateEquiv
          (configuration.gaugeConnection candidate formDirection))) :=
    (smooth.2.2.2.2.1 formDirection).continuous_fderiv (by simp)
  have directionContinuous : Continuous fun _ : BasePoint =>
      coordinateDirection derivativeDirection := continuous_const
  have evaluatedContinuous : Continuous fun point =>
      (fderiv ℝ (fun candidate =>
        p286CoordinateEquiv
          (configuration.gaugeConnection candidate formDirection)) point)
        (coordinateDirection derivativeDirection) :=
    isBoundedBilinearMap_apply.continuous.comp
      (derivativeContinuous.prodMk directionContinuous)
  unfold p286ConnectionDerivative fieldDirectionalDerivative
  simpa only [p286CoordinateEquiv.apply_symm_apply] using evaluatedContinuous

def holonomicP286GaugeCurvatureCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Fin 6 → P286CoordinateCarrier :=
  fun pair => p286CoordinateEquiv
    (holonomicGaugeCurvature configuration point pair)

def holonomicP286GaugeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Fin 6 → P286CoordinateCarrier :=
  fun pair => p286CoordinateEquiv
    (configuration.gaugeAuxiliary point pair)

theorem holonomicP286GaugeCurvatureCoordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous (holonomicP286GaugeCurvatureCoordinate configuration) := by
  apply continuous_pi
  intro pair
  have firstDerivative := p286ConnectionDerivative_coordinate_continuous
    configuration smooth (pairFirst pair) (pairSecond pair)
  have secondDerivative := p286ConnectionDerivative_coordinate_continuous
    configuration smooth (pairSecond pair) (pairFirst pair)
  have firstConnection : Continuous fun point =>
      p286CoordinateEquiv
        (configuration.gaugeConnection point (pairFirst pair)) :=
    (smooth.2.2.2.2.1 (pairFirst pair)).continuous
  have secondConnection : Continuous fun point =>
      p286CoordinateEquiv
        (configuration.gaugeConnection point (pairSecond pair)) :=
    (smooth.2.2.2.2.1 (pairSecond pair)).continuous
  have bracketContinuous := p286CoordinateLieBracket_apply_continuous
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point (pairFirst pair)))
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point (pairSecond pair)))
    firstConnection secondConnection
  have coordinateEquality :
      (fun point => holonomicP286GaugeCurvatureCoordinate
        configuration point pair) =
      fun point =>
        p286CoordinateEquiv
            (p286ConnectionDerivative configuration point
              (pairFirst pair) (pairSecond pair)) -
          p286CoordinateEquiv
            (p286ConnectionDerivative configuration point
              (pairSecond pair) (pairFirst pair)) +
          p286CoordinateLieBracket
            (p286CoordinateEquiv
              (configuration.gaugeConnection point (pairFirst pair)))
            (p286CoordinateEquiv
              (configuration.gaugeConnection point (pairSecond pair))) := by
    funext point
    simp [holonomicP286GaugeCurvatureCoordinate,
      holonomicGaugeCurvature, p286CoordinateLieBracket]
  rw [coordinateEquality]
  exact firstDerivative.sub secondDerivative |>.add bracketContinuous

theorem holonomicP286GaugeAuxiliaryCoordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous (holonomicP286GaugeAuxiliaryCoordinate configuration) := by
  apply continuous_pi
  intro pair
  exact (smooth.2.2.2.2.2.1 pair).continuous

theorem p286CoordinateEquiv_liftGaugeTwoFormOperator
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → P286LieBlockData) (output : Fin 6) :
    p286CoordinateEquiv (liftGaugeTwoFormOperator operator form output) =
      liftGaugeTwoFormOperator operator
        (fun input => p286CoordinateEquiv (form input)) output := by
  unfold liftGaugeTwoFormOperator
  simp only [map_sum, map_smul]

theorem generatedGaugeTwoFormMetricPairing_p286_eq_coordinate
    (coframe : LorentzianCoframe)
    (first second : Fin 6 → P286LieBlockData) :
    generatedGaugeTwoFormMetricPairing p286LiePairing coframe first second =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        (fun pair => p286CoordinateEquiv (first pair))
        (fun pair => p286CoordinateEquiv (second pair)) := by
  unfold generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
  simp_rw [← p286CoordinateEquiv_liftGaugeTwoFormOperator]
  simp

@[simp] theorem liftGaugeTwoFormOperator_p286_strong
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → P286LieBlockData) (output : Fin 6) :
    (liftGaugeTwoFormOperator operator form output).1 =
      liftGaugeTwoFormOperator operator (fun input => (form input).1) output := by
  unfold liftGaugeTwoFormOperator
  rw [Prod.fst_sum]
  rfl

@[simp] theorem liftGaugeTwoFormOperator_p286_weak
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → P286LieBlockData) (output : Fin 6) :
    (liftGaugeTwoFormOperator operator form output).2.1 =
      liftGaugeTwoFormOperator operator (fun input => (form input).2.1) output := by
  unfold liftGaugeTwoFormOperator
  rw [Prod.snd_sum, Prod.fst_sum]
  rfl

@[simp] theorem liftGaugeTwoFormOperator_p286_hypercharge
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → P286LieBlockData) (output : Fin 6) :
    (liftGaugeTwoFormOperator operator form output).2.2 =
      liftGaugeTwoFormOperator operator (fun input => (form input).2.2) output := by
  unfold liftGaugeTwoFormOperator
  rw [Prod.snd_sum, Prod.snd_sum]
  rfl

theorem generatedGaugeTwoFormMetricPairing_p286_decompose
    (coframe : LorentzianCoframe)
    (first second : Fin 6 → P286LieBlockData) :
    generatedGaugeTwoFormMetricPairing p286LiePairing coframe first second =
      generatedGaugeTwoFormMetricPairing specialUnitaryLiePairing coframe
          (fun pair => (first pair).1) (fun pair => (second pair).1) +
        generatedGaugeTwoFormMetricPairing specialUnitaryLiePairing coframe
          (fun pair => (first pair).2.1) (fun pair => (second pair).2.1) +
        generatedGaugeTwoFormMetricPairing hyperchargeLiePairing coframe
          (fun pair => (first pair).2.2) (fun pair => (second pair).2.2) := by
  unfold generatedGaugeTwoFormMetricPairing p286LiePairing
  simp only [liftGaugeTwoFormOperator_p286_strong,
    liftGaugeTwoFormOperator_p286_weak,
    liftGaugeTwoFormOperator_p286_hypercharge]
  simp only [mul_add, Finset.sum_add_distrib]

theorem generatedGaugeSectorBFDensity_p286_decompose
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : Fin 6 → P286LieBlockData) :
    generatedGaugeSectorBFDensity p286LiePairing coframe
        spacetimeHodge operator curvature auxiliary =
      generatedGaugeSectorBFDensity specialUnitaryLiePairing coframe
          spacetimeHodge operator
          (fun pair => (curvature pair).1)
          (fun pair => (auxiliary pair).1) +
        generatedGaugeSectorBFDensity specialUnitaryLiePairing coframe
          spacetimeHodge operator
          (fun pair => (curvature pair).2.1)
          (fun pair => (auxiliary pair).2.1) +
        generatedGaugeSectorBFDensity hyperchargeLiePairing coframe
          spacetimeHodge operator
          (fun pair => (curvature pair).2.2)
          (fun pair => (auxiliary pair).2.2) := by
  unfold generatedGaugeSectorBFDensity
  rw [generatedGaugeTwoFormMetricPairing_p286_decompose,
    generatedGaugeTwoFormMetricPairing_p286_decompose]
  simp only [liftGaugeTwoFormOperator_p286_strong,
    liftGaugeTwoFormOperator_p286_weak,
    liftGaugeTwoFormOperator_p286_hypercharge]
  ring

theorem generatedGaugeSectorBFDensity_p286_eq_coordinate
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : Fin 6 → P286LieBlockData) :
    generatedGaugeSectorBFDensity p286LiePairing coframe
        spacetimeHodge operator curvature auxiliary =
      generatedGaugeSectorBFDensity p286CoordinateLiePairing coframe
        spacetimeHodge operator
        (fun pair => p286CoordinateEquiv (curvature pair))
        (fun pair => p286CoordinateEquiv (auxiliary pair)) := by
  unfold generatedGaugeSectorBFDensity
  rw [generatedGaugeTwoFormMetricPairing_p286_eq_coordinate,
    generatedGaugeTwoFormMetricPairing_p286_eq_coordinate]
  simp_rw [p286CoordinateEquiv_liftGaugeTwoFormOperator]

abbrev P286GaugeTwoForm := Fin 6 → P286CoordinateCarrier

theorem liftGaugeTwoFormOperator_add_p286
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (first second : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator operator (first + second) =
      liftGaugeTwoFormOperator operator first +
        liftGaugeTwoFormOperator operator second := by
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem liftGaugeTwoFormOperator_smul_p286
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (parameter : ℝ) (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator operator (parameter • form) =
      parameter • liftGaugeTwoFormOperator operator form := by
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [mul_comm]

theorem liftGaugeTwoFormOperator_sub_p286
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (first second : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator operator (first - second) =
      liftGaugeTwoFormOperator operator first -
        liftGaugeTwoFormOperator operator second := by
  have negMap : liftGaugeTwoFormOperator operator (-second) =
      -liftGaugeTwoFormOperator operator second := by
    have scaled := liftGaugeTwoFormOperator_smul_p286 operator (-1) second
    simpa only [neg_one_smul] using scaled
  rw [sub_eq_add_neg, sub_eq_add_neg,
    liftGaugeTwoFormOperator_add_p286, negMap]

theorem generatedGaugeTwoFormMetricPairing_p286_add_left
    (coframe : LorentzianCoframe)
    (first second residual : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        (first + second) residual =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          first residual +
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          second residual := by
  unfold generatedGaugeTwoFormMetricPairing
  rw [liftGaugeTwoFormOperator_add_p286]
  simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_left]
  simp only [mul_add, Finset.sum_add_distrib]

theorem generatedGaugeTwoFormMetricPairing_p286_add_right
    (coframe : LorentzianCoframe)
    (first second residual : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        residual (first + second) =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          residual first +
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          residual second := by
  unfold generatedGaugeTwoFormMetricPairing
  rw [liftGaugeTwoFormOperator_add_p286]
  simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_right]
  simp only [mul_add, Finset.sum_add_distrib]

theorem generatedGaugeTwoFormMetricPairing_p286_smul_left
    (coframe : LorentzianCoframe) (parameter : ℝ)
    (first residual : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        (parameter • first) residual =
      parameter *
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          first residual := by
  unfold generatedGaugeTwoFormMetricPairing
  rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem generatedGaugeTwoFormMetricPairing_p286_smul_right
    (coframe : LorentzianCoframe) (parameter : ℝ)
    (first residual : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        residual (parameter • first) =
      parameter *
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          residual first := by
  unfold generatedGaugeTwoFormMetricPairing
  rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem generatedGaugeTwoFormMetricPairing_p286_sub_right
    (coframe : LorentzianCoframe)
    (first second residual : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        residual (first - second) =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          residual first -
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          residual second := by
  rw [sub_eq_add_neg,
    generatedGaugeTwoFormMetricPairing_p286_add_right]
  have negPairing :=
    generatedGaugeTwoFormMetricPairing_p286_smul_right coframe (-1)
      second residual
  rw [show -second = (-1 : ℝ) • second by simp, negPairing]
  ring

theorem generatedGaugeTwoFormMetricPairing_p286_symmetric
    (coframe : LorentzianCoframe)
    (first second : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        first second =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        second first := by
  unfold generatedGaugeTwoFormMetricPairing
  apply Finset.sum_congr rfl
  intro pair _
  rw [p286CoordinateLiePairing_symmetric]

def p286CoordinateGaugeAuxiliaryFirstVariationDensity
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary variation : P286GaugeTwoForm) : ℝ :=
  generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
      variation (liftGaugeTwoFormOperator spacetimeHodge curvature) -
    (1 / 2 : ℝ) *
      (generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          variation
          (liftGaugeTwoFormOperator spacetimeHodge
            (liftGaugeTwoFormOperator operator auxiliary)) +
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          auxiliary
          (liftGaugeTwoFormOperator spacetimeHodge
            (liftGaugeTwoFormOperator operator variation)))

def p286CoordinateGaugeAuxiliarySecondVariationDensity
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (variation : P286GaugeTwoForm) : ℝ :=
  -(1 / 2 : ℝ) *
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
      variation
      (liftGaugeTwoFormOperator spacetimeHodge
        (liftGaugeTwoFormOperator operator variation))

theorem generatedGaugeSectorBFDensity_p286Coordinate_auxiliary_quadratic
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary variation : P286GaugeTwoForm)
    (parameter : ℝ) :
    generatedGaugeSectorBFDensity p286CoordinateLiePairing coframe
        spacetimeHodge operator curvature
        (auxiliary + parameter • variation) =
      generatedGaugeSectorBFDensity p286CoordinateLiePairing coframe
          spacetimeHodge operator curvature auxiliary +
        parameter * p286CoordinateGaugeAuxiliaryFirstVariationDensity
          coframe spacetimeHodge operator curvature auxiliary variation +
        parameter ^ 2 * p286CoordinateGaugeAuxiliarySecondVariationDensity
          coframe spacetimeHodge operator variation := by
  unfold generatedGaugeSectorBFDensity
    p286CoordinateGaugeAuxiliaryFirstVariationDensity
    p286CoordinateGaugeAuxiliarySecondVariationDensity
  simp only [liftGaugeTwoFormOperator_add_p286,
    liftGaugeTwoFormOperator_smul_p286,
    generatedGaugeTwoFormMetricPairing_p286_add_left,
    generatedGaugeTwoFormMetricPairing_p286_add_right,
    generatedGaugeTwoFormMetricPairing_p286_smul_left,
    generatedGaugeTwoFormMetricPairing_p286_smul_right]
  ring

theorem liftGaugeTwoFormOperator_p286Coordinate_apply
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : P286GaugeTwoForm) (output : Fin 6)
    (internal : P286CoordinateIndex) :
    liftGaugeTwoFormOperator operator form output internal =
      operator (fun input => form input internal) output := by
  unfold liftGaugeTwoFormOperator
  rw [WithLp.ofLp_sum]
  rw [Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [gaugeOperator_apply_eq_sum_coefficient]

theorem liftGaugeTwoFormOperator_coframeHodge_square_p286
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear coframe)
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear coframe) form) =
      -form := by
  funext output
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  have innerEquality :
      (fun input =>
        liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear coframe) form input internal) =
      coframeGaugeSpacetimeHodgeLinear coframe
        (fun input => form input internal) := by
    funext input
    exact liftGaugeTwoFormOperator_p286Coordinate_apply
      (coframeGaugeSpacetimeHodgeLinear coframe) form input internal
  rw [innerEquality,
    coframeGaugeSpacetimeHodgeLinear_square coframe nondegenerate]
  rfl

theorem liftGaugeTwoFormOperator_smul_operator_p286
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (parameter : ℝ) (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator (parameter • operator) form =
      parameter • liftGaugeTwoFormOperator operator form := by
  funext output
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  simp only [Pi.smul_apply, WithLp.ofLp_smul]
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  simp

theorem liftGaugeTwoFormOperator_coframeHodge_constitutive_p286
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (couplingSquared : ℝ) (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear coframe)
        (liftGaugeTwoFormOperator
          (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe) form) =
      (-couplingSquared) • form := by
  rw [liftGaugeTwoFormOperator_smul_operator_p286,
    liftGaugeTwoFormOperator_smul_p286,
    liftGaugeTwoFormOperator_coframeHodge_square_p286
      coframe nondegenerate]
  ext output internal
  simp

theorem p286CoordinateGaugeConstitutiveBilinear_symmetric
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (couplingSquared : ℝ) (first second : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe first
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear coframe)
          (liftGaugeTwoFormOperator
            (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            second)) =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe second
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear coframe)
          (liftGaugeTwoFormOperator
            (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
            first)) := by
  rw [liftGaugeTwoFormOperator_coframeHodge_constitutive_p286 coframe
      nondegenerate couplingSquared second,
    liftGaugeTwoFormOperator_coframeHodge_constitutive_p286 coframe
      nondegenerate couplingSquared first]
  rw [show (-couplingSquared) • second =
      (-couplingSquared) • second by rfl,
    generatedGaugeTwoFormMetricPairing_p286_smul_right,
    generatedGaugeTwoFormMetricPairing_p286_smul_right,
    generatedGaugeTwoFormMetricPairing_p286_symmetric coframe first second]

def p286CoordinateGaugeAuxiliaryEquationResidual
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (couplingSquared : ℝ)
    (curvature auxiliary : P286GaugeTwoForm) : P286GaugeTwoForm :=
  curvature -
    liftGaugeTwoFormOperator (couplingSquared • spacetimeHodge) auxiliary

theorem p286CoordinateGaugeAuxiliaryFirstVariationDensity_eq_residualPairing
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (couplingSquared : ℝ)
    (curvature auxiliary variation : P286GaugeTwoForm) :
    p286CoordinateGaugeAuxiliaryFirstVariationDensity coframe
        (coframeGaugeSpacetimeHodgeLinear coframe)
        (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
        curvature auxiliary variation =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        variation
        (liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear coframe)
          (p286CoordinateGaugeAuxiliaryEquationResidual
            (coframeGaugeSpacetimeHodgeLinear coframe)
            couplingSquared curvature auxiliary)) := by
  unfold p286CoordinateGaugeAuxiliaryFirstVariationDensity
    p286CoordinateGaugeAuxiliaryEquationResidual
  rw [← p286CoordinateGaugeConstitutiveBilinear_symmetric coframe
    nondegenerate couplingSquared variation auxiliary]
  rw [liftGaugeTwoFormOperator_sub_p286,
    generatedGaugeTwoFormMetricPairing_p286_sub_right]
  ring

def p286CurvatureCoordinate
    (field : StageNineContinuumPointField) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (field.gaugeCurvature pair)

def p286AuxiliaryCoordinate
    (field : StageNineContinuumPointField) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (field.gaugeAuxiliary pair)

def withP286GaugeAuxiliaryCoordinate
    (field : StageNineContinuumPointField)
    (auxiliary : P286GaugeTwoForm) : StageNineContinuumPointField :=
  { field with
    gaugeAuxiliary := fun pair => p286CoordinateEquiv.symm (auxiliary pair) }

@[simp] theorem p286AuxiliaryCoordinate_withP286GaugeAuxiliaryCoordinate
    (field : StageNineContinuumPointField)
    (auxiliary : P286GaugeTwoForm) :
    p286AuxiliaryCoordinate
        (withP286GaugeAuxiliaryCoordinate field auxiliary) = auxiliary := by
  funext pair
  exact p286CoordinateEquiv.apply_symm_apply (auxiliary pair)

def p286GaugeAuxiliaryFirstVariationDensity
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (variation : P286GaugeTwoForm) : ℝ :=
  generatedVolumeDensity field *
    p286CoordinateGaugeAuxiliaryFirstVariationDensity field.coframe
      (coframeGaugeSpacetimeHodgeLinear field.coframe)
      (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
        coframeGaugeSpacetimeHodgeLinear field.coframe)
      (p286CurvatureCoordinate field) (p286AuxiliaryCoordinate field) variation

def p286GaugeAuxiliarySecondVariationDensity
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (variation : P286GaugeTwoForm) : ℝ :=
  generatedVolumeDensity field *
    p286CoordinateGaugeAuxiliarySecondVariationDensity field.coframe
      (coframeGaugeSpacetimeHodgeLinear field.coframe)
      (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
        coframeGaugeSpacetimeHodgeLinear field.coframe) variation

def generatedUnifiedLocalDensityP286IndependentCore
    (source : SmoothUnifiedSource)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedGravitySimplicityDensity field +
    generatedGravityBFDensity field +
    generatedScalarKineticDensity source chart point field -
    StageNineDynamicBreakingVacuum.generatedScalarPotential
      source chart point field.scalar +
    generatedContinuumMatterDensity source chart point field

theorem generatedUnifiedLocalDensity_p286_decomposition
    (source : SmoothUnifiedSource)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point field =
      generatedVolumeDensity field *
        (generatedUnifiedLocalDensityP286IndependentCore source chart point field +
          generatedGaugeSectorBFDensity p286CoordinateLiePairing field.coframe
            (coframeGaugeSpacetimeHodgeLinear field.coframe)
            (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
              coframeGaugeSpacetimeHodgeLinear field.coframe)
            (p286CurvatureCoordinate field)
            (p286AuxiliaryCoordinate field)) := by
  unfold generatedUnifiedLocalDensityAtBoundary
    generatedUnifiedLocalDensityCoreAtBoundary
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
    generatedUnifiedLocalDensityP286IndependentCore
  dsimp only
  have couplingStrongWeak :
      (sourceGeneratedUnifiedCouplings source).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings source).weakCouplingSquared := rfl
  have couplingStrongHypercharge :
      (sourceGeneratedUnifiedCouplings source).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared := rfl
  rw [← couplingStrongWeak, ← couplingStrongHypercharge]
  rw [← generatedGaugeSectorBFDensity_p286_decompose]
  rw [generatedGaugeSectorBFDensity_p286_eq_coordinate]
  unfold p286CurvatureCoordinate p286AuxiliaryCoordinate
  ring

@[simp] theorem generatedVolumeDensity_withP286GaugeAuxiliaryCoordinate
    (field : StageNineContinuumPointField)
    (auxiliary : P286GaugeTwoForm) :
    generatedVolumeDensity (withP286GaugeAuxiliaryCoordinate field auxiliary) =
      generatedVolumeDensity field := by
  rfl

@[simp] theorem withP286GaugeAuxiliaryCoordinate_coframe
    (field : StageNineContinuumPointField)
    (auxiliary : P286GaugeTwoForm) :
    (withP286GaugeAuxiliaryCoordinate field auxiliary).coframe = field.coframe := by
  rfl

@[simp] theorem p286CurvatureCoordinate_withP286GaugeAuxiliaryCoordinate
    (field : StageNineContinuumPointField)
    (auxiliary : P286GaugeTwoForm) :
    p286CurvatureCoordinate (withP286GaugeAuxiliaryCoordinate field auxiliary) =
      p286CurvatureCoordinate field := by
  rfl

@[simp] theorem generatedUnifiedLocalDensityP286IndependentCore_with
    (source : SmoothUnifiedSource)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (auxiliary : P286GaugeTwoForm) :
    generatedUnifiedLocalDensityP286IndependentCore source chart point
        (withP286GaugeAuxiliaryCoordinate field auxiliary) =
      generatedUnifiedLocalDensityP286IndependentCore source chart point field := by
  rfl

theorem generatedUnifiedLocalDensity_p286Auxiliary_quadratic
    (source : SmoothUnifiedSource)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : P286GaugeTwoForm) (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (withP286GaugeAuxiliaryCoordinate field
          (p286AuxiliaryCoordinate field + parameter • variation)) =
      generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point field +
        parameter * p286GaugeAuxiliaryFirstVariationDensity
          source field variation +
        parameter ^ 2 * p286GaugeAuxiliarySecondVariationDensity
          source field variation := by
  rw [generatedUnifiedLocalDensity_p286_decomposition,
    generatedUnifiedLocalDensity_p286_decomposition]
  simp only [generatedVolumeDensity_withP286GaugeAuxiliaryCoordinate,
    withP286GaugeAuxiliaryCoordinate_coframe,
    generatedUnifiedLocalDensityP286IndependentCore_with,
    p286CurvatureCoordinate_withP286GaugeAuxiliaryCoordinate,
    p286AuxiliaryCoordinate_withP286GaugeAuxiliaryCoordinate]
  rw [generatedGaugeSectorBFDensity_p286Coordinate_auxiliary_quadratic]
  unfold p286GaugeAuxiliaryFirstVariationDensity
    p286GaugeAuxiliarySecondVariationDensity
  ring

def varyP286GaugeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeTwoForm) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) +
          parameter • variation point pair) }

theorem toContinuumPointField_varyP286GaugeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeTwoForm) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField
        (varyP286GaugeAuxiliaryCoordinate configuration variation parameter)
        point =
      withP286GaugeAuxiliaryCoordinate
        (toContinuumPointField configuration point)
        (p286AuxiliaryCoordinate (toContinuumPointField configuration point) +
          parameter • variation point) := by
  rfl

def holonomicP286GaugeAuxiliaryFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeTwoForm) (point : BasePoint) : ℝ :=
  p286GaugeAuxiliaryFirstVariationDensity source
    (toContinuumPointField configuration point) (variation point)

def holonomicP286GaugeAuxiliarySecondVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeTwoForm) (point : BasePoint) : ℝ :=
  p286GaugeAuxiliarySecondVariationDensity source
    (toContinuumPointField configuration point) (variation point)

theorem holonomicLocalDensity_p286GaugeAuxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeTwoForm) (parameter : ℝ)
    (point : BasePoint) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (varyP286GaugeAuxiliaryCoordinate configuration variation parameter)
          point) =
      generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter * holonomicP286GaugeAuxiliaryFirstVariationDensity
          source configuration variation point +
        parameter ^ 2 * holonomicP286GaugeAuxiliarySecondVariationDensity
          source configuration variation point := by
  rw [toContinuumPointField_varyP286GaugeAuxiliaryCoordinate]
  exact generatedUnifiedLocalDensity_p286Auxiliary_quadratic source chart point
    (toContinuumPointField configuration point) (variation point) parameter

end


end SaturationMonoid.PhysicsCore.StageNineP286GaugeAuxiliaryVariation
