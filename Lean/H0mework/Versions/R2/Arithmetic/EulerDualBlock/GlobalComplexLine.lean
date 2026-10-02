import H0mework.Versions.R2.Arithmetic.EulerDualBlock.GlobalDeterminantSection
import H0mework.Versions.R2.Arithmetic.EulerGlobal.CoordinateGerm
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.CoordinateProjectionObstruction

/-!
# One global complex coordinate on the whole block determinant line

The common coordinate map is applied to the actual prime-dual block action
matrix before its determinant is taken.  Both eigenline factors are certified
divisors of that same canonical block determinant.  The cofinal reciprocal
Euler germ is then used only as the native coordinate of the dual determinant
line; Mathlib `riemannZeta` supplies the installed analytic coordinate, with
the ordinary half-plane equality as their overlap law.

Thus a Mathlib zeta zero is a point of one two-chart determinant-line section,
not a unital zero of the Dirichlet-convolution reciprocal and not a
specialization of any finite `AdjoinRoot (C D_stage)`.  No identity theorem,
analytic continuation argument, fixedness, endpoint law, or critical-line
equation enters this producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticCofinalEulerPrefix
open CanonicalUnitArithmeticCommonCarrier
open CanonicalUnitArithmeticDualReadouts
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationDeterminantLocalNormalization
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerRuntimePrimePowerLanding
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier

noncomputable section

open ArithmeticGeneration

abbrev CoordinatePair := ℂ × ℂ
abbrev PairFunctionRing := CoordinatePair → ℂ

def pairReversal (pair : CoordinatePair) : CoordinatePair :=
  (pair.2, pair.1)

abbrev NativePair :=
  {pair : CoordinatePair // 1 < pair.1.re ∧ 1 < pair.2.re}

/-! The common coordinate map is installed on the action coefficients before
the determinant is taken. -/

def commonCoordinateBaseChange :
    BlockCoordinateRing →+* PairFunctionRing :=
  installedBlockEvaluation

def baseChangedBlockOperatorMatrix (stage : Nat) :
    Matrix (BaseIndex seedOccurrence.root stage)
      (BaseIndex seedOccurrence.root stage) PairFunctionRing :=
  commonCoordinateBaseChange.mapMatrix
    (blockOperatorMatrix seedOccurrence.root stage)

def baseChangedBlockDeterminant (stage : Nat) : PairFunctionRing :=
  (baseChangedBlockOperatorMatrix stage).det

theorem baseChangedBlockDeterminant_eq_source (stage : Nat) :
    baseChangedBlockDeterminant stage =
      commonCoordinateBaseChange
        (blockDeterminantSection seedOccurrence.root stage) := by
  unfold baseChangedBlockDeterminant baseChangedBlockOperatorMatrix
  rw [← RingHom.map_det]
  congr 1
  rw [blockDeterminantSection,
    ← LinearMap.det_toMatrix
      (Pi.basisFun BlockCoordinateRing
        (BaseIndex seedOccurrence.root stage)),
    blockEulerOperator_toMatrix]

def baseChangedWholeVertexDeterminant (stage : Nat) : PairFunctionRing :=
  ∏ _role : WholeRole seedOccurrence.root stage,
    baseChangedBlockDeterminant stage

def baseChangedWholeRelationDeterminant (stage : Nat) : PairFunctionRing :=
  ∏ _row : FactorRow seedOccurrence.root stage,
    baseChangedBlockDeterminant stage

theorem baseChangedWholeVertexDeterminant_eq_source (stage : Nat) :
    baseChangedWholeVertexDeterminant stage =
      commonCoordinateBaseChange
        (blockWholeVertexDeterminant seedOccurrence.root stage) := by
  rw [baseChangedWholeVertexDeterminant,
    blockWholeVertexDeterminant_eq_product, map_prod]
  apply Finset.prod_congr rfl
  intro role _membership
  exact baseChangedBlockDeterminant_eq_source stage

theorem baseChangedWholeRelationDeterminant_eq_source (stage : Nat) :
    baseChangedWholeRelationDeterminant stage =
      commonCoordinateBaseChange
        (blockWholeRelationDeterminant seedOccurrence.root stage) := by
  rw [baseChangedWholeRelationDeterminant,
    blockWholeRelationDeterminant_eq_product, map_prod]
  apply Finset.prod_congr rfl
  intro row _membership
  exact baseChangedBlockDeterminant_eq_source stage

theorem baseChangedWholeDeterminant_cancellation (stage : Nat) :
    baseChangedWholeVertexDeterminant stage =
      baseChangedBlockDeterminant stage *
        baseChangedWholeRelationDeterminant stage := by
  rw [baseChangedWholeVertexDeterminant_eq_source,
    baseChangedWholeRelationDeterminant_eq_source,
    baseChangedBlockDeterminant_eq_source, ← map_mul,
    blockWholeVertexDeterminant_eq_inner_mul_relation]

theorem baseChangedBlockDeterminant_apply (stage : Nat)
    (pair : CoordinatePair) :
    baseChangedBlockDeterminant stage pair =
      ∏ primeIndex : StagePrime seedOccurrence.root stage,
        ((1 - installedPrimeEigenvalue
            ((stageFactorization seedOccurrence.root stage).actualPrime
              primeIndex) pair.1) *
          (1 - installedPrimeEigenvalue
            ((stageFactorization seedOccurrence.root stage).actualPrime
              primeIndex) pair.2)) := by
  rw [baseChangedBlockDeterminant_eq_source]
  exact installedBlockEvaluation_section _ _ pair

/-! ## Eigenline factors inside the same block determinant

The two Euler factors are not supplied after the determinant.  They are the
two eigenline factors of the actual `2 × 2` block, each certified to divide
the canonical block determinant at the exact runtime stage.  Their
reciprocals are used only afterwards as native-chart coordinates. -/

def requestedBlockEigenFactor
    {requestedPrime : Nat.Primes}
    (_generated : GeneratedLocalDeterminantCoordinateFactorAt requestedPrime)
    (dualIndex : Fin 2) : BlockCoordinateRing :=
  match dualIndex with
  | 0 => 1 - blockA requestedPrime - blockB requestedPrime
  | 1 => 1 - blockA requestedPrime + blockB requestedPrime

theorem requestedBlockEigenFactor_product
    {requestedPrime : Nat.Primes}
    (generated : GeneratedLocalDeterminantCoordinateFactorAt requestedPrime) :
    requestedBlockEigenFactor generated 0 *
        requestedBlockEigenFactor generated 1 =
      blockLocalFactor seedOccurrence.root generated.factor.stage
        (stagePrimeIndex generated.factor) := by
  unfold requestedBlockEigenFactor blockLocalFactor
  rw [stagePrimeIndex_actualPrime]
  ring

theorem requestedBlockEigenFactor_dvd_section
    {requestedPrime : Nat.Primes}
    (generated : GeneratedLocalDeterminantCoordinateFactorAt requestedPrime)
    (dualIndex : Fin 2) :
    requestedBlockEigenFactor generated dualIndex ∣
      blockDeterminantSection seedOccurrence.root generated.factor.stage := by
  have localDivides :
      blockLocalFactor seedOccurrence.root generated.factor.stage
          (stagePrimeIndex generated.factor) ∣
        blockDeterminantSection seedOccurrence.root generated.factor.stage := by
    rw [blockDeterminantSection_eq_actual_product]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  apply dvd_trans ?_ localDivides
  fin_cases dualIndex
  · exact ⟨requestedBlockEigenFactor generated 1,
      (requestedBlockEigenFactor_product generated).symm⟩
  · exact ⟨requestedBlockEigenFactor generated 0, by
      rw [mul_comm]
      exact (requestedBlockEigenFactor_product generated).symm⟩

theorem requestedBlockEigenFactor_evaluation
    {requestedPrime : Nat.Primes}
    (generated : GeneratedLocalDeterminantCoordinateFactorAt requestedPrime)
    (dualIndex : Fin 2) (pair : CoordinatePair) :
    commonCoordinateBaseChange
        (requestedBlockEigenFactor generated dualIndex) pair =
      1 - installedPrimeEigenvalue requestedPrime
        (if dualIndex = 0 then pair.1 else pair.2) := by
  fin_cases dualIndex <;>
    simp [requestedBlockEigenFactor, commonCoordinateBaseChange,
      installedBlockEvaluation_A, installedBlockEvaluation_B,
      installedPairAverage, installedPairDifference] <;>
    ring

structure GeneratedBlockEigenlineCoordinateFactorAt
    (requestedPrime : Nat.Primes) (dualIndex : Fin 2) : Type where
  private mk ::
  generated : GeneratedLocalDeterminantCoordinateFactorAt requestedPrime
  eigenFactor : BlockCoordinateRing
  dividesWholeDeterminant : eigenFactor ∣
    blockDeterminantSection seedOccurrence.root generated.factor.stage
  eigenFactor_eq : eigenFactor =
    requestedBlockEigenFactor generated dualIndex

def GeneratedBlockEigenlineCoordinateFactorAt.generate
    (requestedPrime : Nat.Primes) (dualIndex : Fin 2) :
    GeneratedBlockEigenlineCoordinateFactorAt requestedPrime dualIndex := by
  let generated := GeneratedLocalDeterminantCoordinateFactorAt.generate
    requestedPrime
  exact ⟨generated, requestedBlockEigenFactor generated dualIndex,
    requestedBlockEigenFactor_dvd_section generated dualIndex, rfl⟩

@[simp] theorem GeneratedBlockEigenlineCoordinateFactorAt.generate_generated
    (requestedPrime : Nat.Primes) (dualIndex : Fin 2) :
    (GeneratedBlockEigenlineCoordinateFactorAt.generate
      requestedPrime dualIndex).generated =
        GeneratedLocalDeterminantCoordinateFactorAt.generate requestedPrime :=
  rfl

/-- The prime-dependent normalization is downstream of the common block
determinant.  It is applied to the certified eigenfactor itself: `A_p` first
reads as `pX`, then the requested prime supplies `X ↦ X/p`; the `B` direction
is killed only in this one eigenline chart. -/
def blockEigenlineNormalization (requestedPrime : Nat.Primes) :
    BlockCoordinateRing →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (Int.castRingHom ℚ)) fun index =>
      if index.2 = 0 then
        Polynomial.C (((index.1 : Nat) : ℚ)) * Polynomial.X *
          Polynomial.C ((((requestedPrime : Nat) : ℚ))⁻¹)
      else 0

def GeneratedBlockEigenlineCoordinateFactorAt.normalizedEigenFactor
    {requestedPrime : Nat.Primes} {dualIndex : Fin 2}
    (generated : GeneratedBlockEigenlineCoordinateFactorAt
      requestedPrime dualIndex) : Polynomial ℚ :=
  blockEigenlineNormalization requestedPrime generated.eigenFactor

theorem GeneratedBlockEigenlineCoordinateFactorAt.normalizedEigenFactor_eq_one_sub_X
    {requestedPrime : Nat.Primes} {dualIndex : Fin 2}
    (generated : GeneratedBlockEigenlineCoordinateFactorAt
      requestedPrime dualIndex) :
    generated.normalizedEigenFactor = 1 - Polynomial.X := by
  rw [normalizedEigenFactor, generated.eigenFactor_eq]
  have primeNonzero : (((requestedPrime : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast requestedPrime.property.ne_zero
  have cancel :
      Polynomial.C (((requestedPrime : Nat) : ℚ)) *
          Polynomial.C ((((requestedPrime : Nat) : ℚ))⁻¹) = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ primeNonzero, Polynomial.C_1]
  fin_cases dualIndex <;>
    simp [requestedBlockEigenFactor, blockEigenlineNormalization,
      blockA, blockB] <;>
    calc
      Polynomial.C (((requestedPrime : Nat) : ℚ)) * Polynomial.X *
            Polynomial.C ((((requestedPrime : Nat) : ℚ))⁻¹) =
          Polynomial.X *
            (Polynomial.C (((requestedPrime : Nat) : ℚ)) *
              Polynomial.C ((((requestedPrime : Nat) : ℚ))⁻¹)) := by ring
      _ = Polynomial.X := by rw [cancel, mul_one]

def GeneratedBlockEigenlineCoordinateFactorAt.normalizedEigenSeries
    {requestedPrime : Nat.Primes} {dualIndex : Fin 2}
    (generated : GeneratedBlockEigenlineCoordinateFactorAt
      requestedPrime dualIndex) : PowerSeries ℚ :=
  PowerSeries.invOfUnit
    (↑generated.normalizedEigenFactor : PowerSeries ℚ) 1

theorem GeneratedBlockEigenlineCoordinateFactorAt.normalizedEigenSeries_eq_geometric
    {requestedPrime : Nat.Primes} {dualIndex : Fin 2}
    (generated : GeneratedBlockEigenlineCoordinateFactorAt
      requestedPrime dualIndex) :
    generated.normalizedEigenSeries = PowerSeries.mk 1 := by
  unfold normalizedEigenSeries
  rw [generated.normalizedEigenFactor_eq_one_sub_X]
  have actual := normalizedActualLocalZetaSeries_eq_geometric
    generated.generated.factor dualIndex
  rw [normalizedActualLocalZetaSeries,
    normalizedActualLocalDeterminantFactor_eq_sourcePolynomial] at actual
  exact actual

/-- The arithmetic-function factor is now computed from the certified block
eigenfactor.  The existing local factor is a theorem-level readback, not the
definition of this value. -/
def GeneratedBlockEigenlineCoordinateFactorAt.arithmeticReadout
    {requestedPrime : Nat.Primes} {dualIndex : Fin 2}
    (generated : GeneratedBlockEigenlineCoordinateFactorAt
      requestedPrime dualIndex) : ArithmeticFunction ℚ :=
  ArithmeticFunction.ofPowerSeries (requestedPrime : Nat)
    generated.normalizedEigenSeries

theorem GeneratedBlockEigenlineCoordinateFactorAt.arithmeticReadout_eq_existing
    {requestedPrime : Nat.Primes} {dualIndex : Fin 2}
    (generated : GeneratedBlockEigenlineCoordinateFactorAt
      requestedPrime dualIndex) :
    generated.arithmeticReadout = generated.generated.arithmeticFactor := by
  unfold arithmeticReadout
    GeneratedLocalDeterminantCoordinateFactorAt.arithmeticFactor
  rw [generated.normalizedEigenSeries_eq_geometric,
    GeneratedLocalDeterminantCoordinateFactorAt.normalizedGlobalSeries_eq_actual,
    normalizedActualLocalZetaSeries_eq_geometric]

theorem GeneratedBlockEigenlineCoordinateFactorAt.installed_denominator
    {requestedPrime : Nat.Primes} {dualIndex : Fin 2}
    (generated : GeneratedBlockEigenlineCoordinateFactorAt
      requestedPrime dualIndex) (pair : CoordinatePair) :
    commonCoordinateBaseChange generated.eigenFactor pair =
      1 - installedPrimeEigenvalue requestedPrime
        (if dualIndex = 0 then pair.1 else pair.2) := by
  rw [generated.eigenFactor_eq]
  exact requestedBlockEigenFactor_evaluation generated.generated dualIndex pair

def blockEigenlineCoordinatePrefix (dualIndex : Fin 2) :
    UnitHistory → ArithmeticFunction ℚ
  | .empty => 1
  | .next prior =>
      (GeneratedBlockEigenlineCoordinateFactorAt.generate
        (primeAtStage prior.cardinalShadow) dualIndex).arithmeticReadout *
          blockEigenlineCoordinatePrefix dualIndex prior

theorem blockEigenlineCoordinatePrefix_eq_generatedDeterminantPrefix
    (dualIndex : Fin 2) (history : UnitHistory) :
    blockEigenlineCoordinatePrefix dualIndex history =
      determinantCoordinatePrefix history := by
  induction history with
  | empty => rfl
  | next prior inductionHypothesis =>
      rw [blockEigenlineCoordinatePrefix, determinantCoordinatePrefix,
        inductionHypothesis,
        GeneratedBlockEigenlineCoordinateFactorAt.arithmeticReadout_eq_existing,
        GeneratedBlockEigenlineCoordinateFactorAt.generate_generated]

theorem blockEigenlineCoordinatePrefix_eventually_eq_formalEulerCoefficients
    (dualIndex : Fin 2) (coefficient : Nat) :
    ∀ᶠ stage : Nat in Filter.atTop,
      blockEigenlineCoordinatePrefix dualIndex
          (CanonicalUnitArithmeticRuntimeCofinalEuler.runtimeWholeHistory stage)
          coefficient =
        (formalEulerCoefficients coefficient : ℚ) := by
  filter_upwards
    [CanonicalUnitArithmeticRuntimeCofinalEuler.runtimeEulerPrefix_eventually_eq_formalEulerCoefficients
      coefficient] with stage equality
  rw [blockEigenlineCoordinatePrefix_eq_generatedDeterminantPrefix,
    determinantCoordinatePrefix_eq_finiteEulerPrefix,
    castArithmeticFunction_apply]
  exact_mod_cast equality

/-- The global eigenline germ is generated directly from the prefixes whose
local factors were normalized from certified divisors of the common block
determinant.  It does not reuse `globalGermOccurrence`. -/
structure GeneratedBlockEigenlineGlobalGermAt
    (dualIndex : Fin 2) : Type where
  private mk ::
  coefficients : ArithmeticFunction ℚ
  generated : ∀ coefficient : Nat,
    ∀ᶠ stage : Nat in Filter.atTop,
      blockEigenlineCoordinatePrefix dualIndex
          (CanonicalUnitArithmeticRuntimeCofinalEuler.runtimeWholeHistory stage)
          coefficient = coefficients coefficient

def GeneratedBlockEigenlineGlobalGermAt.generate (dualIndex : Fin 2) :
    GeneratedBlockEigenlineGlobalGermAt dualIndex :=
  ⟨castArithmeticFunction formalEulerCoefficients,
    fun coefficient => by
      simpa only [castArithmeticFunction_apply] using
        blockEigenlineCoordinatePrefix_eventually_eq_formalEulerCoefficients
          dualIndex coefficient⟩

theorem GeneratedBlockEigenlineGlobalGermAt.coefficients_eq_zeta
    (dualIndex : Fin 2) :
    (GeneratedBlockEigenlineGlobalGermAt.generate dualIndex).coefficients =
      (ArithmeticFunction.zeta : ArithmeticFunction ℚ) := by
  change castArithmeticFunction formalEulerCoefficients =
    (ArithmeticFunction.zeta : ArithmeticFunction ℚ)
  rw [formalEulerCoefficients_eq_zeta, castArithmeticFunction_zeta]

noncomputable def blockEigenlineGlobalCoordinateGerm
    (dualIndex : Fin 2) (coordinate : ℂ) : ℂ :=
  LSeries (fun coefficient =>
    ((GeneratedBlockEigenlineGlobalGermAt.generate dualIndex).coefficients
      coefficient : ℂ)) coordinate

theorem blockEigenlineGlobalCoordinateGerm_eq_riemannZeta
    (dualIndex : Fin 2) {coordinate : ℂ}
    (converges : 1 < coordinate.re) :
    blockEigenlineGlobalCoordinateGerm dualIndex coordinate =
      riemannZeta coordinate := by
  unfold blockEigenlineGlobalCoordinateGerm
  rw [GeneratedBlockEigenlineGlobalGermAt.coefficients_eq_zeta]
  calc
    LSeries
        (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℚ) n : ℂ))
        coordinate = LSeries 1 coordinate := by
          apply LSeries_congr
          intro n nonzero
          simp [ArithmeticFunction.zeta_apply_ne nonzero]
    _ = riemannZeta coordinate := LSeries_one_eq_riemannZeta converges

/-! A determinant-line section is represented by two coordinates on two
overlapping frames.  It is not a ring element required to be invertible in
both frames. -/

structure ComplexDeterminantLineSection : Type where
  private mk ::
  nativeCoordinate : NativePair → ℂ
  analyticCoordinate : PairFunctionRing
  agreesOnNative : ∀ pair : NativePair,
    nativeCoordinate pair = analyticCoordinate pair.1

def generatedNativeCoordinate (pair : NativePair) : ℂ :=
  blockEigenlineGlobalCoordinateGerm 0 pair.1.1 *
    blockEigenlineGlobalCoordinateGerm 1 pair.1.2

def installedAnalyticCoordinate : PairFunctionRing :=
  fun pair => riemannZeta pair.1 * riemannZeta pair.2

@[simp] theorem installedAnalyticCoordinate_reversal
    (pair : CoordinatePair) :
    installedAnalyticCoordinate (pairReversal pair) =
      installedAnalyticCoordinate pair := by
  simp [installedAnalyticCoordinate, pairReversal, mul_comm]

theorem generatedNativeCoordinate_eq_installed
    (pair : NativePair) :
    generatedNativeCoordinate pair =
      installedAnalyticCoordinate pair.1 := by
  unfold generatedNativeCoordinate installedAnalyticCoordinate
  rw [blockEigenlineGlobalCoordinateGerm_eq_riemannZeta 0 pair.2.1,
    blockEigenlineGlobalCoordinateGerm_eq_riemannZeta 1 pair.2.2]

def installedComplexDeterminantLineSection :
    ComplexDeterminantLineSection where
  nativeCoordinate := generatedNativeCoordinate
  analyticCoordinate := installedAnalyticCoordinate
  agreesOnNative := generatedNativeCoordinate_eq_installed

/-! The producer keeps the exact whole determinant occurrence, the
pre-determinant common base change, and the two-chart section in one value.
The constructor is private, so no caller can submit an unrelated analytic
function. -/

structure RootGeneratedWholeBlockComplexDeterminantLineAt : Type where
  private mk ::
  stageOperatorMatrix : ∀ stage : Nat,
    Matrix (BaseIndex seedOccurrence.root stage)
      (BaseIndex seedOccurrence.root stage) PairFunctionRing
  stageInnerDeterminant : Nat → PairFunctionRing
  stageWholeVertexDeterminant : Nat → PairFunctionRing
  stageWholeRelationDeterminant : Nat → PairFunctionRing
  localEigenlineFactor : ∀ prime : Nat.Primes, ∀ dualIndex : Fin 2,
    GeneratedBlockEigenlineCoordinateFactorAt prime dualIndex
  lineSection : ComplexDeterminantLineSection
  operatorMatrix_eq : ∀ stage,
    stageOperatorMatrix stage = baseChangedBlockOperatorMatrix stage
  innerDeterminant_eq : ∀ stage,
    stageInnerDeterminant stage = (stageOperatorMatrix stage).det
  innerDeterminant_reads_source : ∀ stage,
    stageInnerDeterminant stage = commonCoordinateBaseChange
      (blockDeterminantSection seedOccurrence.root stage)
  wholeVertex_reads_source : ∀ stage,
    stageWholeVertexDeterminant stage = commonCoordinateBaseChange
      (blockWholeVertexDeterminant seedOccurrence.root stage)
  wholeRelation_reads_source : ∀ stage,
    stageWholeRelationDeterminant stage = commonCoordinateBaseChange
      (blockWholeRelationDeterminant seedOccurrence.root stage)
  wholeCancellation : ∀ stage,
    stageWholeVertexDeterminant stage =
      stageInnerDeterminant stage * stageWholeRelationDeterminant stage
  globalEigenlineGenerated : ∀ dualIndex : Fin 2, ∀ coefficient : Nat,
    ∀ᶠ stage : Nat in Filter.atTop,
      blockEigenlineCoordinatePrefix dualIndex
          (CanonicalUnitArithmeticRuntimeCofinalEuler.runtimeWholeHistory stage)
          coefficient =
        (GeneratedBlockEigenlineGlobalGermAt.generate dualIndex).coefficients
          coefficient
  exactRoot : globalBlockSectionFace.cofinalFace.root = seedOccurrence
  exactWholeOccurrence : ∀ stage,
    (blockWholeDeterminantOccurrence seedOccurrence.root stage).map Prod.fst =
      stageOccurrenceFrom seedOccurrence.root stage

def RootGeneratedWholeBlockComplexDeterminantLineAt.generate :
    RootGeneratedWholeBlockComplexDeterminantLineAt where
  stageOperatorMatrix := baseChangedBlockOperatorMatrix
  stageInnerDeterminant := baseChangedBlockDeterminant
  stageWholeVertexDeterminant := baseChangedWholeVertexDeterminant
  stageWholeRelationDeterminant := baseChangedWholeRelationDeterminant
  localEigenlineFactor := fun prime dualIndex =>
    GeneratedBlockEigenlineCoordinateFactorAt.generate prime dualIndex
  lineSection := installedComplexDeterminantLineSection
  operatorMatrix_eq := fun _ => rfl
  innerDeterminant_eq := fun _ => rfl
  innerDeterminant_reads_source := baseChangedBlockDeterminant_eq_source
  wholeVertex_reads_source := baseChangedWholeVertexDeterminant_eq_source
  wholeRelation_reads_source := baseChangedWholeRelationDeterminant_eq_source
  wholeCancellation := baseChangedWholeDeterminant_cancellation
  globalEigenlineGenerated := fun dualIndex coefficient =>
    (GeneratedBlockEigenlineGlobalGermAt.generate dualIndex).generated
      coefficient
  exactRoot := globalBlockSectionFace
    |>.preserves_root_local_successor_and_global_section |>.1
  exactWholeOccurrence := fun stage =>
    blockWholeDeterminantOccurrence_projects_source seedOccurrence.root stage

def installedWholeBlockComplexDeterminantLine :
    RootGeneratedWholeBlockComplexDeterminantLineAt :=
  RootGeneratedWholeBlockComplexDeterminantLineAt.generate

@[simp] theorem installedWholeBlockComplexDeterminantLine_nativeCoordinate
    (pair : NativePair) :
    installedWholeBlockComplexDeterminantLine.lineSection.nativeCoordinate pair =
      blockEigenlineGlobalCoordinateGerm 0 pair.1.1 *
        blockEigenlineGlobalCoordinateGerm 1 pair.1.2 :=
  rfl

theorem installedNativeCoordinate_generated_from_certifiedEigenlinePrefixes
    (pair : NativePair) :
    installedWholeBlockComplexDeterminantLine.lineSection.nativeCoordinate pair =
        blockEigenlineGlobalCoordinateGerm 0 pair.1.1 *
          blockEigenlineGlobalCoordinateGerm 1 pair.1.2 ∧
      (∀ dualIndex : Fin 2, ∀ coefficient : Nat,
        ∀ᶠ stage : Nat in Filter.atTop,
          blockEigenlineCoordinatePrefix dualIndex
              (CanonicalUnitArithmeticRuntimeCofinalEuler.runtimeWholeHistory
                stage) coefficient =
            (GeneratedBlockEigenlineGlobalGermAt.generate dualIndex
              ).coefficients coefficient) := by
  exact ⟨rfl,
    installedWholeBlockComplexDeterminantLine.globalEigenlineGenerated⟩

structure Point
    (face : RootGeneratedWholeBlockComplexDeterminantLineAt) : Type where
  pair : CoordinatePair
  sectionZero : face.lineSection.analyticCoordinate pair = 0

def Point.reversal
    (point : Point installedWholeBlockComplexDeterminantLine) :
    Point installedWholeBlockComplexDeterminantLine :=
  ⟨pairReversal point.pair, by
    change installedAnalyticCoordinate (pairReversal point.pair) = 0
    rw [installedAnalyticCoordinate_reversal]
    exact point.sectionZero⟩

@[simp] theorem Point.reversal_pair
    (point : Point installedWholeBlockComplexDeterminantLine) :
    point.reversal.pair = pairReversal point.pair :=
  rfl

def mathlibPair (coordinate : ℂ) : CoordinatePair :=
  (coordinate, coordinateReversal coordinate)

def mathlibZeroPoint (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0) :
    Point installedWholeBlockComplexDeterminantLine :=
  ⟨mathlibPair coordinate, by
    change riemannZeta coordinate *
      riemannZeta (coordinateReversal coordinate) = 0
    rw [zetaZero, zero_mul]⟩

@[simp] theorem mathlibZeroPoint_pair (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0) :
    (mathlibZeroPoint coordinate zetaZero).pair = mathlibPair coordinate :=
  rfl

@[simp] theorem mathlibZeroPoint_left (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0) :
    (mathlibZeroPoint coordinate zetaZero).pair.1 = coordinate :=
  rfl

@[simp] theorem mathlibZeroPoint_right (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0) :
    (mathlibZeroPoint coordinate zetaZero).pair.2 =
      coordinateReversal coordinate :=
  rfl

theorem coordinate_fixed_of_mathlibZeroPoint_fixed
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0)
    (fixed : mathlibZeroPoint coordinate zetaZero =
      (mathlibZeroPoint coordinate zetaZero).reversal) :
    coordinate = coordinateReversal coordinate := by
  have pairFixed := congrArg
    (Point.pair (face := installedWholeBlockComplexDeterminantLine)) fixed
  exact congrArg Prod.fst pairFixed

theorem preserves_same_whole_action_before_determinant_and_installs_point
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    globalBlockSectionFace.cofinalFace.root = seedOccurrence ∧
      (∀ stage,
        installedWholeBlockComplexDeterminantLine.stageInnerDeterminant stage =
          (installedWholeBlockComplexDeterminantLine.stageOperatorMatrix
            stage).det) ∧
      (∀ stage,
        installedWholeBlockComplexDeterminantLine.stageWholeVertexDeterminant
            stage =
          installedWholeBlockComplexDeterminantLine.stageInnerDeterminant
              stage *
            (installedWholeBlockComplexDeterminantLine
              ).stageWholeRelationDeterminant stage) ∧
      (mathlibZeroPoint coordinate zetaZero).pair =
        (coordinate, coordinateReversal coordinate) := by
  exact ⟨installedWholeBlockComplexDeterminantLine.exactRoot,
    installedWholeBlockComplexDeterminantLine.innerDeterminant_eq,
    installedWholeBlockComplexDeterminantLine.wholeCancellation,
    rfl⟩

end
end CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
