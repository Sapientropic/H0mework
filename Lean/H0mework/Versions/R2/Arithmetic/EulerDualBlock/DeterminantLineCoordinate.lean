import Mathlib.RingTheory.Ideal.Quotient.Operations
import H0mework.Versions.R2.Arithmetic.EulerDualBlock.GlobalAction
import H0mework.Versions.R2.Arithmetic.EulerDualBlock.GlobalDeterminantSection
import H0mework.Versions.R2.Arithmetic.EulerGlobal.CoordinateGerm
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.CoordinateProjectionObstruction

/-!
# Two-coordinate regression attached to the block determinant owner

The exact global prime-dual block face owns the finite determinant section.
This file attaches a two-coordinate Euler readout and a Mathlib analytic
principal quotient, then exposes its coordinate points.

The owner index records provenance but is not a proof that the analytic
principal quotient factors through the formal `D_stage` zero fibres.  That
factorization is deliberately a separate semantic obligation.  The
reciprocal Euler/Dirichlet realization appears only on the native chart; no
convolution unit is mapped to zero, and no fixedness or critical-line law
enters a point constructor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

noncomputable section

abbrev CoordinatePair := ℂ × ℂ
abbrev PairFunctionRing := CoordinatePair → ℂ

def pairReversal (pair : CoordinatePair) : CoordinatePair :=
  (pair.2, pair.1)

@[simp] theorem pairReversal_involutive (pair : CoordinatePair) :
    pairReversal (pairReversal pair) = pair :=
  rfl

/-! ## Direct global owner -/

abbrev ExactBlockActionAt (stage : Nat) :=
  BlockWholeVertex seedOccurrence.root stage →ₗ[BlockCoordinateRing]
    BlockWholeVertex seedOccurrence.root stage

def canonicalBlockActionFamily :
    (stage : Nat) → ExactBlockActionAt stage :=
  fun stage => (blockDeterminantOccurrence seedOccurrence.root stage).root.2.1

def canonicalBlockSectionFamily : Nat → BlockCoordinateRing :=
  fun stage => (blockDeterminantOccurrence seedOccurrence.root stage).root.2.2

@[simp] theorem canonicalBlockActionFamily_readback (stage : Nat) :
    canonicalBlockActionFamily stage =
      blockWholeVertexAction seedOccurrence.root stage :=
  blockDeterminantOccurrence_reads_action _ _

@[simp] theorem canonicalBlockSectionFamily_readback (stage : Nat) :
    canonicalBlockSectionFamily stage =
      blockDeterminantSection seedOccurrence.root stage :=
  blockDeterminantOccurrence_reads_section _ _

theorem canonicalBlockSectionFamily_successor (stage : Nat) :
    canonicalBlockSectionFamily (stage + 1) =
      relativeBlockDeterminantSection seedOccurrence.root stage *
        canonicalBlockSectionFamily stage := by
  rw [canonicalBlockSectionFamily_readback,
    canonicalBlockSectionFamily_readback]
  exact blockDeterminantSection_successor_factorization _ _

theorem canonicalBlockSectionFamily_installedEvaluation
    (stage : Nat) (pair : CoordinatePair) :
    installedBlockEvaluation (canonicalBlockSectionFamily stage) pair =
      ∏ primeIndex : StagePrime seedOccurrence.root stage,
        ((1 - installedPrimeEigenvalue
            ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)
              pair.1) *
          (1 - installedPrimeEigenvalue
            ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)
              pair.2)) := by
  rw [canonicalBlockSectionFamily_readback]
  exact installedBlockEvaluation_section _ _ _

/-- The same swap used on the analytic zero fibre is already an invariance
of the actual installed block evaluation. -/
theorem canonicalBlockSectionFamily_installedEvaluation_swap
    (stage : Nat) (pair : CoordinatePair) :
    installedBlockEvaluation (canonicalBlockSectionFamily stage)
        (pairReversal pair) =
      installedBlockEvaluation (canonicalBlockSectionFamily stage) pair := by
  rw [canonicalBlockSectionFamily_readback]
  exact installedBlockEvaluation_section_swap _ _ _

abbrev GlobalBlockSectionOwner :=
  CofinalPolynomialSection.RootGeneratedCofinalPolynomialSectionAt
    seedOccurrence dependentBlockProcessOccurrence
      dependentBlockProcessOccurrence_projects

abbrev GlobalBlockComponentOwner :=
  DependentDerivedGlobalState.RootGeneratedDependentDerivedGlobalStateAt
    dependentBlockComplexOccurrence

/-- The index keeps the framework-generated block face and the generated
Euler germ in one payload.  It supplies indexing provenance only; it does not
assert a coefficient-preserving zero-fibre specialization between them. -/
structure SectionOwner
    (_globalBlockComponent : GlobalBlockComponentOwner)
    (_globalBlockFace : GlobalBlockSectionOwner)
    (_globalGerm : GeneratedGlobalDeterminantCoordinateGerm) : Type where
  private mk ::

abbrev ExactSectionOwner :=
  SectionOwner globalBlockComplexFace globalBlockSectionFace
    globalGermOccurrence.root.2

def installedOwner : ExactSectionOwner := ⟨⟩

instance : Subsingleton ExactSectionOwner where
  allEq left right := by cases left; cases right; rfl

theorem installedOwner_preserves_uncancelled_global_component :
    globalBlockComplexFace.root = seedOccurrence :=
  preserves_exact_root_uncancelled_global_block_state.1

/-! ## Two charts of the owner-indexed section -/

abbrev NativePair :=
  {pair : CoordinatePair // 1 < pair.1.re ∧ 1 < pair.2.re}

noncomputable def nativeSection
    (_owner : ExactSectionOwner) (pair : NativePair) : ℂ :=
  globalDeterminantCoordinateGerm pair.1.1 *
    globalDeterminantCoordinateGerm pair.1.2

/-- Installed analytic regression chart.  No continuation theorem is used to
construct it, and it is not promoted here to the formal block zero fibre. -/
noncomputable def analyticSection
    (_owner : ExactSectionOwner) : PairFunctionRing :=
  fun pair => riemannZeta pair.1 * riemannZeta pair.2

@[simp] theorem analyticSection_reversal
    (owner : ExactSectionOwner) (pair : CoordinatePair) :
    analyticSection owner (pairReversal pair) = analyticSection owner pair := by
  simp [analyticSection, pairReversal, mul_comm]

/-- Nonempty overlap; only the two native half-plane L-series identities
are consumed. -/
theorem charts_overlap (owner : ExactSectionOwner) (pair : NativePair) :
    nativeSection owner pair = analyticSection owner pair.1 := by
  unfold nativeSection analyticSection
  rw [globalDeterminantCoordinateGerm_eq_riemannZeta pair.2.1,
    globalDeterminantCoordinateGerm_eq_riemannZeta pair.2.2]

/-! ## Principal analytic regression fibre -/

def analyticZeroIdeal (owner : ExactSectionOwner) : Ideal PairFunctionRing :=
  Ideal.span {analyticSection owner}

abbrev AnalyticZeroFiberRing (owner : ExactSectionOwner) :=
  PairFunctionRing ⧸ analyticZeroIdeal owner

def leftCoordinateFunction : PairFunctionRing := fun pair => pair.1
def rightCoordinateFunction : PairFunctionRing := fun pair => pair.2

def universalLeftCoordinate (owner : ExactSectionOwner) :
    AnalyticZeroFiberRing owner :=
  Ideal.Quotient.mk (analyticZeroIdeal owner) leftCoordinateFunction

def universalRightCoordinate (owner : ExactSectionOwner) :
    AnalyticZeroFiberRing owner :=
  Ideal.Quotient.mk (analyticZeroIdeal owner) rightCoordinateFunction

structure Point (owner : ExactSectionOwner) : Type where
  pair : CoordinatePair
  sectionZero : analyticSection owner pair = 0

theorem Point.analyticZeroIdeal_le_ker_evaluation
    {owner : ExactSectionOwner} (point : Point owner) :
    analyticZeroIdeal owner ≤
      RingHom.ker (Pi.evalRingHom
        (fun _pair : CoordinatePair => ℂ) point.pair) := by
  rw [analyticZeroIdeal, Ideal.span_le]
  intro function membership
  simp only [Set.mem_singleton_iff] at membership
  subst function
  exact point.sectionZero

def Point.specialization {owner : ExactSectionOwner} (point : Point owner) :
    AnalyticZeroFiberRing owner →+* ℂ :=
  Ideal.Quotient.lift (analyticZeroIdeal owner)
    (Pi.evalRingHom (fun _pair : CoordinatePair => ℂ) point.pair)
    point.analyticZeroIdeal_le_ker_evaluation

@[simp] theorem Point.specialization_mk
    {owner : ExactSectionOwner} (point : Point owner)
    (function : PairFunctionRing) :
    point.specialization
        (Ideal.Quotient.mk (analyticZeroIdeal owner) function) =
      function point.pair :=
  rfl

@[simp] theorem Point.specialization_universalLeftCoordinate
    {owner : ExactSectionOwner} (point : Point owner) :
    point.specialization (universalLeftCoordinate owner) = point.pair.1 :=
  rfl

@[simp] theorem Point.specialization_universalRightCoordinate
    {owner : ExactSectionOwner} (point : Point owner) :
    point.specialization (universalRightCoordinate owner) = point.pair.2 :=
  rfl

/-! ## Swap automorphism and descent -/

def swapFunctionRingEquiv : PairFunctionRing ≃+* PairFunctionRing where
  toFun function pair := function (pairReversal pair)
  invFun function pair := function (pairReversal pair)
  left_inv function := by funext pair; simp [pairReversal]
  right_inv function := by funext pair; simp [pairReversal]
  map_add' left right := rfl
  map_mul' left right := rfl

@[simp] theorem swapFunctionRingEquiv_analyticSection
    (owner : ExactSectionOwner) :
    swapFunctionRingEquiv (analyticSection owner) = analyticSection owner := by
  funext pair
  exact analyticSection_reversal owner pair

theorem analyticZeroIdeal_swap_stable (owner : ExactSectionOwner) :
    analyticZeroIdeal owner =
      (analyticZeroIdeal owner).map swapFunctionRingEquiv.toRingHom := by
  rw [analyticZeroIdeal, Ideal.map_span]
  simp [swapFunctionRingEquiv_analyticSection]

def zeroFiberSwap (owner : ExactSectionOwner) :
    AnalyticZeroFiberRing owner ≃+* AnalyticZeroFiberRing owner :=
  Ideal.quotientEquiv (analyticZeroIdeal owner) (analyticZeroIdeal owner)
    swapFunctionRingEquiv (analyticZeroIdeal_swap_stable owner)

@[simp] theorem zeroFiberSwap_universalLeftCoordinate
    (owner : ExactSectionOwner) :
    zeroFiberSwap owner (universalLeftCoordinate owner) =
      universalRightCoordinate owner := by
  rfl

@[simp] theorem zeroFiberSwap_universalRightCoordinate
    (owner : ExactSectionOwner) :
    zeroFiberSwap owner (universalRightCoordinate owner) =
      universalLeftCoordinate owner := by
  rfl

def Point.reversal {owner : ExactSectionOwner} (point : Point owner) :
    Point owner :=
  ⟨pairReversal point.pair, by
    rw [analyticSection_reversal]
    exact point.sectionZero⟩

@[simp] theorem Point.reversal_pair
    {owner : ExactSectionOwner} (point : Point owner) :
    point.reversal.pair = pairReversal point.pair :=
  rfl

/-! ## Mathlib point -/

def mathlibPair (coordinate : ℂ) : CoordinatePair :=
  (coordinate, coordinateReversal coordinate)

def pointOfMathlibZero (coordinate : ℂ)
    (zetaZero : riemannZeta coordinate = 0) : Point installedOwner :=
  ⟨mathlibPair coordinate, by
    unfold analyticSection mathlibPair
    rw [zetaZero, zero_mul]⟩

@[simp] theorem pointOfMathlibZero_pair
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    (pointOfMathlibZero coordinate zetaZero).pair = mathlibPair coordinate :=
  rfl

@[simp] theorem pointOfMathlibZero_specialization_left
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    (pointOfMathlibZero coordinate zetaZero).specialization
        (universalLeftCoordinate installedOwner) = coordinate :=
  rfl

@[simp] theorem pointOfMathlibZero_specialization_right
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    (pointOfMathlibZero coordinate zetaZero).specialization
        (universalRightCoordinate installedOwner) =
      coordinateReversal coordinate :=
  rfl

theorem coordinate_fixed_of_point_reversal_fixed
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0)
    (fixed : pointOfMathlibZero coordinate zetaZero =
      (pointOfMathlibZero coordinate zetaZero).reversal) :
    coordinate = coordinateReversal coordinate := by
  have pairFixed := congrArg (Point.pair (owner := installedOwner)) fixed
  exact congrArg Prod.fst pairFixed

theorem direct_owner_zero_fibre_point_splice
    (stage : Nat) (pair : CoordinatePair)
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    (GlobalBlockDeterminantSectionDiagram.obj
        (Opposite.op stage)).polynomial =
        Polynomial.C (canonicalBlockSectionFamily stage) ∧
      installedBlockEvaluation (canonicalBlockSectionFamily stage) pair =
        ∏ primeIndex : StagePrime seedOccurrence.root stage,
          ((1 - installedPrimeEigenvalue
              ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)
                pair.1) *
            (1 - installedPrimeEigenvalue
              ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)
                pair.2)) ∧
      installedBlockEvaluation (canonicalBlockSectionFamily stage)
          (pairReversal pair) =
        installedBlockEvaluation (canonicalBlockSectionFamily stage) pair ∧
      analyticSection installedOwner
          (pointOfMathlibZero coordinate zetaZero).pair = 0 ∧
      (pointOfMathlibZero coordinate zetaZero).specialization
          (universalLeftCoordinate installedOwner) = coordinate ∧
      (pointOfMathlibZero coordinate zetaZero).specialization
          (universalRightCoordinate installedOwner) =
        coordinateReversal coordinate := by
  exact ⟨globalBlockSection_reads_same_action_occurrence stage,
    canonicalBlockSectionFamily_installedEvaluation stage pair,
    canonicalBlockSectionFamily_installedEvaluation_swap stage pair,
    (pointOfMathlibZero coordinate zetaZero).sectionZero,
    pointOfMathlibZero_specialization_left coordinate zetaZero,
    pointOfMathlibZero_specialization_right coordinate zetaZero⟩

end
end CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
