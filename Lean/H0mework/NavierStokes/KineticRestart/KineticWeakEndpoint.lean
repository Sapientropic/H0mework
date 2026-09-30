import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Order.MonotoneConvergence
import H0mework.NavierStokes.Crossing.TangentCoercivity

/-!
# Source-generated kinetic weak endpoint of the whole restart run

The actual contact sequence of the native whole restart run is uniformly
bounded in the already existing kinetic `H⁻¹` Euclidean Hilbert carrier.
Sequential Banach--Alaoglu and the Hilbert Riesz equivalence therefore
generate one weak endpoint and one strictly monotone source subsequence.

When accumulated physical time is bounded, the same subsequence converges
to the source-generated supremum time.  No endpoint, subsequence, norm bound,
compactness witness, or target trajectory enters either theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint

open scoped ENNReal

open Filter Metric Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity

noncomputable section

/-- The complete nonzero-frequency kinetic endpoint carrier already used
by the whole-state kinetic pairing. -/
abbrev WholeRestartKineticEndpointState :=
  lp (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2

/-- The actual contact at one native occurrence, read in the kinetic
Euclidean carrier before any limiting operation. -/
def wholeRestartContactKineticState
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) : WholeRestartKineticEndpointState :=
  puncturedWholeVorticityKineticEuclideanState
    (run initial index).contact.physicalState

/-- Every actual contact is bounded by the initial contact in the same
kinetic Hilbert norm. -/
theorem wholeRestartContactKineticState_norm_le_initial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    ‖wholeRestartContactKineticState initial index‖ ≤
      ‖wholeRestartContactKineticState initial 0‖ := by
  have massLe :=
    run_contact_kineticMass_antitone initial (Nat.zero_le index)
  have squareLe :
      ‖wholeRestartContactKineticState initial index‖ ^ 2 ≤
        ‖wholeRestartContactKineticState initial 0‖ ^ 2 := by
    calc
      ‖wholeRestartContactKineticState initial index‖ ^ 2 =
          puncturedWholeVorticityKineticMass
            (run initial index).contact.physicalState :=
        puncturedWholeVorticityKineticEuclideanState_norm_sq _
      _ ≤
          puncturedWholeVorticityKineticMass
            (run initial 0).contact.physicalState := massLe
      _ = ‖wholeRestartContactKineticState initial 0‖ ^ 2 :=
        (puncturedWholeVorticityKineticEuclideanState_norm_sq _).symm
  nlinarith [norm_nonneg (wholeRestartContactKineticState initial index),
    norm_nonneg (wholeRestartContactKineticState initial 0), squareLe]

/-! ## Source-generated scalar kinetic limit -/

/-- The scalar kinetic ledger of the actual contact at one native
occurrence, expressed on the same Euclidean endpoint carrier. -/
def wholeRestartContactKineticMass
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) : ℝ :=
  ‖wholeRestartContactKineticState initial index‖ ^ 2

/-- The actual kinetic mass ledger is antitone along the native run. -/
theorem wholeRestartContactKineticMass_antitone
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Antitone (wholeRestartContactKineticMass initial) := by
  intro left right leftLeRight
  have massLe :=
    run_contact_kineticMass_antitone initial leftLeRight
  simpa only [wholeRestartContactKineticMass,
    wholeRestartContactKineticState,
    puncturedWholeVorticityKineticEuclideanState_norm_sq] using massLe

/-- The source-generated lower endpoint of the actual scalar kinetic
ledger.  No limit value is supplied by a caller. -/
def wholeRestartKineticMassLimit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : ℝ :=
  ⨅ index : ℕ, wholeRestartContactKineticMass initial index

theorem wholeRestartKineticMassLimit_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    0 ≤ wholeRestartKineticMassLimit initial := by
  exact le_ciInf fun index =>
    sq_nonneg ‖wholeRestartContactKineticState initial index‖

/-- The complete actual kinetic mass sequence converges to its internally
generated lower endpoint. -/
theorem wholeRestartContactKineticMass_tendsto_limit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto
      (wholeRestartContactKineticMass initial)
      atTop
      (nhds (wholeRestartKineticMassLimit initial)) := by
  exact tendsto_atTop_ciInf
    (wholeRestartContactKineticMass_antitone initial)
    ⟨0, Set.forall_mem_range.mpr fun index =>
      sq_nonneg ‖wholeRestartContactKineticState initial index‖⟩

/-- Riesz realization of one actual kinetic contact in the weak-star dual
carrier used for sequential Banach--Alaoglu. -/
def wholeRestartContactKineticWeakDual
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) : WeakDual ℂ WholeRestartKineticEndpointState :=
  StrongDual.toWeakDual
    (InnerProductSpace.toDual ℂ WholeRestartKineticEndpointState
      (wholeRestartContactKineticState initial index))

theorem wholeRestartContactKineticWeakDual_mem_initialClosedBall
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    wholeRestartContactKineticWeakDual initial index ∈
      WeakDual.toStrongDual ⁻¹'
        Metric.closedBall 0
          ‖wholeRestartContactKineticState initial 0‖ := by
  change
    dist
        (WeakDual.toStrongDual
          (wholeRestartContactKineticWeakDual initial index))
        0 ≤
      ‖wholeRestartContactKineticState initial 0‖
  rw [dist_zero_right]
  change
    ‖InnerProductSpace.toDual ℂ WholeRestartKineticEndpointState
        (wholeRestartContactKineticState initial index)‖ ≤
      ‖wholeRestartContactKineticState initial 0‖
  rw [(InnerProductSpace.toDual
    ℂ WholeRestartKineticEndpointState).norm_map]
  exact wholeRestartContactKineticState_norm_le_initial initial index

/-! ## Countable kinetic test core -/

/-- A finite support together with one index into the canonical dense
sequence of the finite-dimensional row carrier at each supported wave. -/
private abbrev KineticFiniteApproximationCode :=
  Σ support : Finset NonzeroIntegerWavevector, support → ℕ

private def kineticFiniteApproximation
    (code : KineticFiniteApproximationCode) :
    WholeRestartKineticEndpointState :=
  ∑ wave : code.1,
    lp.single 2 wave.1
      (TopologicalSpace.denseSeq ComplexCoordinateEuclidean
        (code.2 wave))

private theorem norm_kineticFiniteSum_le
    {support : Finset NonzeroIntegerWavevector}
    (term : support → WholeRestartKineticEndpointState) :
    ‖∑ wave : support, term wave‖ ≤
      ∑ wave : support, ‖term wave‖ := by
  exact norm_sum_le Finset.univ term

private theorem dist_kineticFiniteSum_le
    {support : Finset NonzeroIntegerWavevector}
    (left right : support → WholeRestartKineticEndpointState) :
    dist (∑ wave : support, left wave) (∑ wave : support, right wave) ≤
      ∑ wave : support, dist (left wave) (right wave) := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    ‖∑ wave : support, (left wave - right wave)‖ ≤
        ∑ wave : support, ‖left wave - right wave‖ :=
      norm_kineticFiniteSum_le (fun wave => left wave - right wave)
    _ = ∑ wave : support, dist (left wave) (right wave) := by
      simp only [dist_eq_norm]

private theorem norm_kineticSingle_sub
    (wave : NonzeroIntegerWavevector)
    (left right : ComplexCoordinateEuclidean) :
    ‖(lp.single 2 wave left : WholeRestartKineticEndpointState) -
        lp.single 2 wave right‖ = dist left right := by
  simpa only [dist_eq_norm] using
    (lp.isometry_single
      (E := fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean)
      (p := 2) wave).dist_eq left right

set_option maxHeartbeats 800000 in
private theorem kineticFiniteApproximation_denseRange :
    DenseRange kineticFiniteApproximation := by
  rw [Metric.denseRange_iff]
  intro state epsilon epsilonPos
  have halfPos : 0 < epsilon / 2 := by linarith
  have finiteApproximationTendsto :
      Tendsto
        (fun support : Finset NonzeroIntegerWavevector =>
          ∑ wave ∈ support, lp.single 2 wave (state wave))
        atTop (nhds state) :=
    lp.hasSum_single ENNReal.ofNat_ne_top state
  have eventuallyHalf :
      ∀ᶠ support : Finset NonzeroIntegerWavevector in atTop,
        dist
          (∑ wave ∈ support, lp.single 2 wave (state wave))
          state < epsilon / 2 :=
    finiteApproximationTendsto
      (Metric.ball_mem_nhds state halfPos)
  obtain ⟨support, supportClose⟩ := eventuallyHalf.exists
  let delta := epsilon / (2 * ((support.card : ℝ) + 1))
  have deltaPos : 0 < delta := by
    dsimp only [delta]
    positivity
  have rowApproximation :
      ∀ wave : support,
        ∃ code : ℕ,
          dist (state wave.1)
            (TopologicalSpace.denseSeq
              ComplexCoordinateEuclidean code) < delta := by
    intro wave
    exact
      (TopologicalSpace.denseRange_denseSeq
        ComplexCoordinateEuclidean).exists_dist_lt
          (state wave.1) deltaPos
  choose rowCode rowCodeClose using rowApproximation
  let code : KineticFiniteApproximationCode :=
    ⟨support, rowCode⟩
  refine ⟨code, ?_⟩
  let exactFinite : WholeRestartKineticEndpointState :=
    ∑ wave : support, lp.single 2 wave.1 (state wave.1)
  have exactClose : dist state exactFinite < epsilon / 2 := by
    have supportClose' := supportClose
    rw [← support.sum_attach] at supportClose'
    rw [Finset.attach_eq_univ] at supportClose'
    simpa only [exactFinite, dist_comm] using supportClose'
  have approximationDistanceLe :
      dist exactFinite (kineticFiniteApproximation code) ≤
        (support.card : ℝ) * delta := by
    calc
      dist exactFinite (kineticFiniteApproximation code) ≤
          ∑ wave : support,
            dist
              (lp.single 2 wave.1 (state wave.1) :
                WholeRestartKineticEndpointState)
              (lp.single 2 wave.1
                (TopologicalSpace.denseSeq
                  ComplexCoordinateEuclidean (rowCode wave)) :
                WholeRestartKineticEndpointState) := by
        simpa only [exactFinite, kineticFiniteApproximation, code] using
          dist_kineticFiniteSum_le
            (fun wave : support =>
              (lp.single 2 wave.1 (state wave.1) :
                WholeRestartKineticEndpointState))
            (fun wave : support =>
              (lp.single 2 wave.1
                (TopologicalSpace.denseSeq
                  ComplexCoordinateEuclidean (rowCode wave)) :
                WholeRestartKineticEndpointState))
      _ =
          ∑ wave : support,
            dist (state wave.1)
              (TopologicalSpace.denseSeq
                ComplexCoordinateEuclidean (rowCode wave)) := by
        apply Finset.sum_congr rfl
        intro wave _waveMem
        simpa only [dist_eq_norm] using
          norm_kineticSingle_sub wave.1
            (state wave.1)
            (TopologicalSpace.denseSeq
              ComplexCoordinateEuclidean (rowCode wave))
      _ ≤ ∑ _wave : support, delta := by
        exact Finset.sum_le_sum fun wave _waveMem =>
          (rowCodeClose wave).le
      _ = (support.card : ℝ) * delta := by
        simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_coe, nsmul_eq_mul]
  have cardDeltaLt :
      (support.card : ℝ) * delta < epsilon / 2 := by
    dsimp only [delta]
    have cardNonneg : 0 ≤ (support.card : ℝ) := Nat.cast_nonneg _
    have denominatorPos : 0 < (support.card : ℝ) + 1 := by linarith
    calc
      (support.card : ℝ) *
          (epsilon / (2 * ((support.card : ℝ) + 1))) =
          epsilon / 2 *
            ((support.card : ℝ) / ((support.card : ℝ) + 1)) := by
        field_simp
      _ < epsilon / 2 * 1 := by
        have ratioLt :
            (support.card : ℝ) / ((support.card : ℝ) + 1) < 1 :=
          (div_lt_one denominatorPos).2 (by linarith)
        exact mul_lt_mul_of_pos_left ratioLt halfPos
      _ = epsilon / 2 := by ring
  have approximationClose :
      dist exactFinite (kineticFiniteApproximation code) < epsilon / 2 :=
    approximationDistanceLe.trans_lt cardDeltaLt
  calc
    dist state (kineticFiniteApproximation code) ≤
        dist state exactFinite +
          dist exactFinite (kineticFiniteApproximation code) :=
      dist_triangle _ exactFinite _
    _ < epsilon / 2 + epsilon / 2 :=
      add_lt_add exactClose approximationClose
    _ = epsilon := by ring

noncomputable instance
    instSeparableSpaceWholeRestartKineticEndpointState :
    TopologicalSpace.SeparableSpace WholeRestartKineticEndpointState :=
  TopologicalSpace.SeparableSpace.of_denseRange
    kineticFiniteApproximation kineticFiniteApproximation_denseRange

private theorem norm_sq_le_of_weak_tendsto_of_norm_sq_tendsto
    (sequence : ℕ → WholeRestartKineticEndpointState)
    (endpoint : WholeRestartKineticEndpointState)
    (limit : ℝ)
    (weakTendsto :
      ∀ test : WholeRestartKineticEndpointState,
        Tendsto
          (fun index => inner ℂ (sequence index) test)
          atTop
          (nhds (inner ℂ endpoint test)))
    (normSqTendsto :
      Tendsto (fun index => ‖sequence index‖ ^ 2) atTop (nhds limit))
    (limitNonneg : 0 ≤ limit) :
    ‖endpoint‖ ^ 2 ≤ limit := by
  have weakRealTendsto :
      Tendsto
        (fun index => (inner ℂ (sequence index) endpoint).re)
        atTop
        (nhds (‖endpoint‖ ^ 2)) := by
    have evaluated :=
      (Complex.continuous_re.tendsto (inner ℂ endpoint endpoint)).comp
        (weakTendsto endpoint)
    change
      Tendsto
        (fun index => (inner ℂ (sequence index) endpoint).re)
        atTop
        (nhds ((inner ℂ endpoint endpoint).re)) at evaluated
    have endpointInnerEq :
        (inner ℂ endpoint endpoint).re = ‖endpoint‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) endpoint
    rw [endpointInnerEq] at evaluated
    exact evaluated
  have normTendsto :
      Tendsto
        (fun index => ‖sequence index‖)
        atTop
        (nhds (Real.sqrt limit)) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using normSqTendsto.sqrt
  have productTendsto :
      Tendsto
        (fun index => ‖sequence index‖ * ‖endpoint‖)
        atTop
        (nhds (Real.sqrt limit * ‖endpoint‖)) :=
    normTendsto.mul_const ‖endpoint‖
  have endpointSquareLe :
      ‖endpoint‖ ^ 2 ≤ Real.sqrt limit * ‖endpoint‖ :=
    le_of_tendsto_of_tendsto'
      weakRealTendsto productTendsto fun index =>
        re_inner_le_norm (𝕜 := ℂ) (sequence index) endpoint
  by_cases endpointNormZero : ‖endpoint‖ = 0
  · calc
      ‖endpoint‖ ^ 2 = 0 := by rw [endpointNormZero]; norm_num
      _ ≤ limit := limitNonneg
  · have endpointNormPos : 0 < ‖endpoint‖ :=
      lt_of_le_of_ne (norm_nonneg endpoint) (Ne.symm endpointNormZero)
    have sqrtLimitNonneg : 0 ≤ Real.sqrt limit := Real.sqrt_nonneg _
    have sqrtLimitSq : Real.sqrt limit ^ 2 = limit :=
      Real.sq_sqrt limitNonneg
    nlinarith

private theorem tendsto_of_weak_tendsto_of_norm_sq_tendsto_eq
    (sequence : ℕ → WholeRestartKineticEndpointState)
    (endpoint : WholeRestartKineticEndpointState)
    (limit : ℝ)
    (weakTendsto :
      ∀ test : WholeRestartKineticEndpointState,
        Tendsto
          (fun index => inner ℂ (sequence index) test)
          atTop
          (nhds (inner ℂ endpoint test)))
    (normSqTendsto :
      Tendsto (fun index => ‖sequence index‖ ^ 2) atTop (nhds limit))
    (limitEq : limit = ‖endpoint‖ ^ 2) :
    Tendsto sequence atTop (nhds endpoint) := by
  have weakRealTendsto :
      Tendsto
        (fun index => (inner ℂ (sequence index) endpoint).re)
        atTop
        (nhds (‖endpoint‖ ^ 2)) := by
    have evaluated :=
      (Complex.continuous_re.tendsto (inner ℂ endpoint endpoint)).comp
        (weakTendsto endpoint)
    change
      Tendsto
        (fun index => (inner ℂ (sequence index) endpoint).re)
        atTop
        (nhds ((inner ℂ endpoint endpoint).re)) at evaluated
    have endpointInnerEq :
        (inner ℂ endpoint endpoint).re = ‖endpoint‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) endpoint
    rw [endpointInnerEq] at evaluated
    exact evaluated
  have expandedDistanceTendsto :
      Tendsto
        (fun index =>
          ‖sequence index‖ ^ 2 -
            2 * (inner ℂ (sequence index) endpoint).re +
              ‖endpoint‖ ^ 2)
        atTop
        (nhds
          (limit - 2 * ‖endpoint‖ ^ 2 + ‖endpoint‖ ^ 2)) :=
    (normSqTendsto.sub (weakRealTendsto.const_mul 2)).add_const
      (‖endpoint‖ ^ 2)
  have distanceSquareTendsto :
      Tendsto
        (fun index => ‖sequence index - endpoint‖ ^ 2)
        atTop
        (nhds 0) := by
    convert expandedDistanceTendsto using 1
    · funext index
      exact norm_sub_sq (𝕜 := ℂ) (sequence index) endpoint
    · rw [limitEq]
      ring_nf
  have distanceTendsto :
      Tendsto
        (fun index => ‖sequence index - endpoint‖)
        atTop
        (nhds 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      distanceSquareTendsto.sqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr distanceTendsto

/-- The authoritative actual contact sequence generates a bounded kinetic
weak endpoint and a strictly monotone subsequence converging against every
kinetic Hilbert test. -/
theorem exists_wholeRestartContactKineticWeakEndpoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∃ endpoint : WholeRestartKineticEndpointState,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          ‖endpoint‖ ≤
            ‖wholeRestartContactKineticState initial 0‖ ∧
          ∀ test : WholeRestartKineticEndpointState,
            Tendsto
              (fun index =>
                inner ℂ
                  (wholeRestartContactKineticState
                    initial (subsequence index))
                  test)
              atTop
              (nhds (inner ℂ endpoint test)) := by
  let radius := ‖wholeRestartContactKineticState initial 0‖
  let sequence : ℕ → WeakDual ℂ WholeRestartKineticEndpointState :=
    wholeRestartContactKineticWeakDual initial
  have sequenceMem :
      ∀ index,
        sequence index ∈
          WeakDual.toStrongDual ⁻¹'
            Metric.closedBall 0 radius := by
    intro index
    exact wholeRestartContactKineticWeakDual_mem_initialClosedBall
      initial index
  obtain ⟨limitDual, limitMem, subsequence, subsequenceMono,
      dualTendsto⟩ :=
    (WeakDual.isSeqCompact_closedBall
      ℂ WholeRestartKineticEndpointState 0 radius) sequenceMem
  let endpoint : WholeRestartKineticEndpointState :=
    (InnerProductSpace.toDual ℂ WholeRestartKineticEndpointState).symm
      (WeakDual.toStrongDual limitDual)
  have endpointNormLe :
      ‖endpoint‖ ≤
        ‖wholeRestartContactKineticState initial 0‖ := by
    change dist (WeakDual.toStrongDual limitDual) 0 ≤ radius at limitMem
    have dualNormLe :
        ‖WeakDual.toStrongDual limitDual‖ ≤ radius := by
      simpa only [dist_zero_right] using limitMem
    change
      ‖(InnerProductSpace.toDual
          ℂ WholeRestartKineticEndpointState).symm
          (WeakDual.toStrongDual limitDual)‖ ≤
        ‖wholeRestartContactKineticState initial 0‖
    rw [(InnerProductSpace.toDual
      ℂ WholeRestartKineticEndpointState).symm.norm_map]
    simpa only [radius] using dualNormLe
  refine ⟨endpoint, subsequence, subsequenceMono, endpointNormLe, ?_⟩
  intro test
  have evaluated :=
    (WeakDual.eval_continuous test).tendsto limitDual
      |>.comp dualTendsto
  have sourceEq :
      (fun index =>
        sequence (subsequence index) test) =
        (fun index =>
          inner ℂ
            (wholeRestartContactKineticState
              initial (subsequence index)) test) := by
    funext index
    change
      (InnerProductSpace.toDual
        ℂ WholeRestartKineticEndpointState
        (wholeRestartContactKineticState
          initial (subsequence index))) test =
        inner ℂ
          (wholeRestartContactKineticState
            initial (subsequence index)) test
    exact InnerProductSpace.toDual_apply_apply
  have targetEq :
      limitDual test = inner ℂ endpoint test := by
    calc
      limitDual test = (WeakDual.toStrongDual limitDual) test := rfl
      _ = inner ℂ endpoint test := by
        symm
        exact InnerProductSpace.toDual_symm_apply
  change
    Tendsto
      (fun index => sequence (subsequence index) test)
      atTop (nhds (limitDual test)) at evaluated
  rw [sourceEq, targetEq] at evaluated
  exact evaluated

/-- The finite accumulation time generated by the actual native run. -/
def wholeRestartAccumulationTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : ℝ :=
  ⨆ index : ℕ, elapsedTime initial index

/-- Under bounded elapsed time, one source-generated subsequence converges
simultaneously to the kinetic weak endpoint and to the actual accumulation
time. -/
theorem exists_wholeRestartContactKineticWeakEndpoint_at_accumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∃ endpoint : WholeRestartKineticEndpointState,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          ‖endpoint‖ ≤
            ‖wholeRestartContactKineticState initial 0‖ ∧
          Tendsto
            (fun index => elapsedTime initial (subsequence index))
            atTop (nhds (wholeRestartAccumulationTime initial)) ∧
          ∀ test : WholeRestartKineticEndpointState,
            Tendsto
              (fun index =>
                inner ℂ
                  (wholeRestartContactKineticState
                    initial (subsequence index))
                  test)
              atTop
              (nhds (inner ℂ endpoint test)) := by
  obtain ⟨endpoint, subsequence, subsequenceMono, endpointNormLe,
      weakTendsto⟩ :=
    exists_wholeRestartContactKineticWeakEndpoint initial
  have elapsedTendsto :
      Tendsto
        (fun index => elapsedTime initial (subsequence index))
        atTop (nhds (wholeRestartAccumulationTime initial)) := by
    exact
      (tendsto_atTop_ciSup
        (elapsedTime_strictMono initial).monotone elapsedBounded).comp
          subsequenceMono.tendsto_atTop
  exact ⟨endpoint, subsequence, subsequenceMono, endpointNormLe,
    elapsedTendsto, weakTendsto⟩

/-! ## Maximal kinetic endpoint receipt -/

/-- The kinetic mass that remains outside one weak endpoint.  Its two
terms are generated by the same actual contact sequence. -/
def wholeRestartKineticWeakEndpointDefect
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (endpoint : WholeRestartKineticEndpointState) : ℝ :=
  wholeRestartKineticMassLimit initial - ‖endpoint‖ ^ 2

/-- One source-generated kinetic weak endpoint, its exact scalar mass
limit, and the internally exhaustive fate of the endpoint defect. -/
structure GeneratedWholeRestartKineticWeakEndpoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) where
  endpoint : WholeRestartKineticEndpointState
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  endpoint_norm_le_initial :
    ‖endpoint‖ ≤ ‖wholeRestartContactKineticState initial 0‖
  weak_tendsto :
    ∀ test : WholeRestartKineticEndpointState,
      Tendsto
        (fun index =>
          inner ℂ
            (wholeRestartContactKineticState
              initial (subsequence index))
            test)
        atTop
        (nhds (inner ℂ endpoint test))
  mass_tendsto :
    Tendsto
      (fun index =>
        wholeRestartContactKineticMass initial (subsequence index))
      atTop
      (nhds (wholeRestartKineticMassLimit initial))
  defect_nonneg :
    0 ≤ wholeRestartKineticWeakEndpointDefect initial endpoint
  defect_disposition :
    0 < wholeRestartKineticWeakEndpointDefect initial endpoint ∨
      (wholeRestartKineticWeakEndpointDefect initial endpoint = 0 ∧
        Tendsto
          (fun index =>
            wholeRestartContactKineticState
              initial (subsequence index))
          atTop
          (nhds endpoint))

private theorem nonempty_generatedWholeRestartKineticWeakEndpoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Nonempty (GeneratedWholeRestartKineticWeakEndpoint initial) := by
  obtain ⟨endpoint, subsequence, subsequenceMono, endpointNormLe,
      weakTendsto⟩ :=
    exists_wholeRestartContactKineticWeakEndpoint initial
  have massTendsto :
      Tendsto
        (fun index =>
          wholeRestartContactKineticMass initial (subsequence index))
        atTop
        (nhds (wholeRestartKineticMassLimit initial)) :=
    (wholeRestartContactKineticMass_tendsto_limit initial).comp
      subsequenceMono.tendsto_atTop
  have normSqTendsto :
      Tendsto
        (fun index =>
          ‖wholeRestartContactKineticState
            initial (subsequence index)‖ ^ 2)
        atTop
        (nhds (wholeRestartKineticMassLimit initial)) := by
    simpa only [wholeRestartContactKineticMass] using massTendsto
  have endpointSquareLe :
      ‖endpoint‖ ^ 2 ≤ wholeRestartKineticMassLimit initial :=
    norm_sq_le_of_weak_tendsto_of_norm_sq_tendsto
      (fun index =>
        wholeRestartContactKineticState initial (subsequence index))
      endpoint
      (wholeRestartKineticMassLimit initial)
      weakTendsto
      normSqTendsto
      (wholeRestartKineticMassLimit_nonneg initial)
  have defectNonneg :
      0 ≤ wholeRestartKineticWeakEndpointDefect initial endpoint := by
    unfold wholeRestartKineticWeakEndpointDefect
    linarith
  have defectDisposition :
      0 < wholeRestartKineticWeakEndpointDefect initial endpoint ∨
        (wholeRestartKineticWeakEndpointDefect initial endpoint = 0 ∧
          Tendsto
            (fun index =>
              wholeRestartContactKineticState
                initial (subsequence index))
            atTop
            (nhds endpoint)) := by
    by_cases defectZero :
        wholeRestartKineticWeakEndpointDefect initial endpoint = 0
    · right
      refine ⟨defectZero, ?_⟩
      have massLimitEq :
          wholeRestartKineticMassLimit initial = ‖endpoint‖ ^ 2 := by
        unfold wholeRestartKineticWeakEndpointDefect at defectZero
        linarith
      exact tendsto_of_weak_tendsto_of_norm_sq_tendsto_eq
        (fun index =>
          wholeRestartContactKineticState initial (subsequence index))
        endpoint
        (wholeRestartKineticMassLimit initial)
        weakTendsto
        normSqTendsto
        massLimitEq
    · left
      exact lt_of_le_of_ne defectNonneg (Ne.symm defectZero)
  exact
    ⟨{ endpoint := endpoint
       subsequence := subsequence
       subsequence_strictMono := subsequenceMono
       endpoint_norm_le_initial := endpointNormLe
       weak_tendsto := weakTendsto
       mass_tendsto := massTendsto
       defect_nonneg := defectNonneg
       defect_disposition := defectDisposition }⟩

/-- The actual whole restart run generates a kinetic weak endpoint receipt.
If the internally generated mass defect vanishes, the same selected source
subsequence converges strongly; otherwise the receipt exposes a strictly
positive defect.  The selection is noncomputable but accepts no endpoint,
subsequence, bound, limit, or defect branch from a caller. -/
noncomputable def generatedWholeRestartKineticWeakEndpoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeRestartKineticWeakEndpoint initial :=
  Classical.choice
    (nonempty_generatedWholeRestartKineticWeakEndpoint initial)

/-- The maximal kinetic endpoint receipt together with convergence of the
same generated subsequence to the source accumulation time. -/
structure GeneratedWholeRestartKineticWeakEndpointAtAccumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) extends
      GeneratedWholeRestartKineticWeakEndpoint initial where
  elapsed_tendsto :
    Tendsto
      (fun index => elapsedTime initial (subsequence index))
      atTop
      (nhds (wholeRestartAccumulationTime initial))

/-- Bounded elapsed time adds an accumulation-time readout to the same
source-generated maximal kinetic endpoint receipt. -/
noncomputable def generatedWholeRestartKineticWeakEndpointAtAccumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartKineticWeakEndpointAtAccumulation initial := by
  let receipt := generatedWholeRestartKineticWeakEndpoint initial
  refine
    { toGeneratedWholeRestartKineticWeakEndpoint := receipt
      elapsed_tendsto := ?_ }
  exact
    (tendsto_atTop_ciSup
      (elapsedTime_strictMono initial).monotone elapsedBounded).comp
        receipt.subsequence_strictMono.tendsto_atTop

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
end NavierStokes
end SaturationMonoid
