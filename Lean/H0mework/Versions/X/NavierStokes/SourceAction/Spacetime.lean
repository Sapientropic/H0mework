import H0mework.Versions.X.NavierStokes.SourceAction.Mixed
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeSpacetimeControl

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativePhysicalFourier NativeFullOrderAction NativeFullOrderFlux NativeFullOrderSynthesis
open NativeFullOrderTime NativeHigherTimeJetsSource NativeTimeJetCarrier NativeTimeJetRecursion NativeMixedTimeSpace

noncomputable section

theorem hasFDerivWithinAt_tsum_closure {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {openDomain : Set E} (opened : IsOpen openDomain) (convex : Convex ℝ openDomain)
    (nonempty : openDomain.Nonempty) (field : ι → E → F) (next : ι → E → E →L[ℝ] F)
    (fieldBound nextBound : ι → ℝ) (fieldPaid : Summable fieldBound) (nextPaid : Summable nextBound)
    (fieldContinuous : ∀ i, ContinuousOn (field i) (closure openDomain))
    (nextContinuous : ∀ i, ContinuousOn (next i) (closure openDomain))
    (evolves : ∀ i x, x ∈ closure openDomain → HasFDerivWithinAt (field i) (next i x) (closure openDomain) x)
    (fieldBounded : ∀ i x, x ∈ closure openDomain → ‖field i x‖ ≤ fieldBound i)
    (nextBounded : ∀ i x, x ∈ closure openDomain → ‖next i x‖ ≤ nextBound i)
    (x : E) (inside : x ∈ closure openDomain) :
    HasFDerivWithinAt (fun actual => ∑' i, field i actual) (∑' i, next i x) (closure openDomain) x := by
  obtain ⟨anchor, anchorInside⟩ := nonempty
  have interior (actual : E) (member : actual ∈ openDomain) :
      HasFDerivAt (fun actual => ∑' i, field i actual) (∑' i, next i actual) actual :=
    hasFDerivAt_tsum_of_isPreconnected nextPaid opened convex.isPreconnected
      (fun i point pointInside => (evolves i point (subset_closure pointInside)).hasFDerivAt
        (mem_of_superset (opened.mem_nhds pointInside) subset_closure))
      (fun i point pointInside => nextBounded i point (subset_closure pointInside))
      anchorInside (fieldPaid.of_norm_bounded fun i => fieldBounded i anchor (subset_closure anchorInside)) member
  have fieldCont := continuousOn_tsum fieldContinuous fieldPaid fieldBounded
  have nextCont := continuousOn_tsum nextContinuous nextPaid nextBounded
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun actual member => (interior actual member).differentiableAt.differentiableWithinAt)
    convex opened (fun actual member => (fieldCont actual member).mono subset_closure)
  apply ((nextCont x inside).mono_left (nhdsWithin_mono x subset_closure)).congr'
  filter_upwards [self_mem_nhdsWithin] with actual member
  exact (interior actual member).fderiv.symm

theorem contDiffOn_tsum_closure {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {openDomain : Set E} (opened : IsOpen openDomain) (convex : Convex ℝ openDomain)
    (nonempty : openDomain.Nonempty) (unique : UniqueDiffOn ℝ (closure openDomain))
    (field : ι → E → F) (bound : ℕ → ι → ℝ)
    (smooth : ∀ i, ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field i) (closure openDomain))
    (paid : ∀ n, Summable (bound n))
    (bounded : ∀ n i x, x ∈ closure openDomain →
      ‖iteratedFDerivWithin ℝ n (field i) (closure openDomain) x‖ ≤ bound n i) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => ∑' i, field i x) (closure openDomain) := by
  let series (x : E) (n : ℕ) := ∑' i, iteratedFDerivWithin ℝ n (field i) (closure openDomain) x
  have seriesPaid (n : ℕ) (x : E) (inside : x ∈ closure openDomain) :
      Summable fun i => iteratedFDerivWithin ℝ n (field i) (closure openDomain) x :=
    (paid n).of_norm_bounded fun i => bounded n i x inside
  have taylor : HasFTaylorSeriesUpToOn (↑(⊤ : ℕ∞)) (fun x => ∑' i, field i x) series (closure openDomain) := by
    constructor
    · intro x inside
      change (continuousMultilinearCurryFin0 ℝ E F) (series x 0) = _
      dsimp only [series]
      calc
        _ = ∑' i, (continuousMultilinearCurryFin0 ℝ E F)
            (iteratedFDerivWithin ℝ 0 (field i) (closure openDomain) x) :=
          (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.map_tsum
        _ = _ := tsum_congr fun i => ((smooth i).ftaylorSeriesWithin unique).zero_eq x inside
    · intro n below x inside
      have derivative := hasFDerivWithinAt_tsum_closure opened convex nonempty
        (fun i => iteratedFDerivWithin ℝ n (field i) (closure openDomain))
        (fun i x => (iteratedFDerivWithin ℝ (n + 1) (field i) (closure openDomain) x).curryLeft)
        (bound n) (bound (n + 1)) (paid n) (paid (n + 1))
        (fun i => (smooth i).continuousOn_iteratedFDerivWithin (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)) unique)
        (fun i => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).continuous.comp_continuousOn
          ((smooth i).continuousOn_iteratedFDerivWithin (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤)) unique))
        (fun i actual member => ((smooth i).ftaylorSeriesWithin unique).fderivWithin n
          below actual member)
        (bounded n) (fun i actual member => by
          change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F)
            (iteratedFDerivWithin ℝ (n + 1) (field i) (closure openDomain) actual)‖ ≤ _
          rw [LinearIsometryEquiv.norm_map]
          exact bounded (n + 1) i actual member) x inside
      convert! derivative using 1
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).toContinuousLinearEquiv.map_tsum
    · intro n _
      exact continuousOn_tsum (fun i => (smooth i).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)) unique) (paid n) (bounded n)
  exact taylor.contDiffOn

abbrev Spacetime := ℝ × PhysicalSpace

def slab (index : ℕ) : Set Spacetime := Icc (0 : ℝ) (run stackedShortCurrent index).duration ×ˢ univ

def slabInterior (index : ℕ) : Set Spacetime := Ioo (0 : ℝ) (run stackedShortCurrent index).duration ×ˢ univ

theorem slab_unique (index : ℕ) : UniqueDiffOn ℝ (slab index) :=
  (uniqueDiffOn_Icc (run stackedShortCurrent index).receipt.requestedTimePos).prod uniqueDiffOn_univ

theorem slab_closure (index : ℕ) : closure (slabInterior index) = slab index := by
  simp only [slabInterior, slab, closure_prod_eq, closure_Ioo (run stackedShortCurrent index).receipt.requestedTimePos.ne,
    closure_univ]

def coordinateRead (wave : IntegerWavevector) (coordinate : Coordinate) : ComplexVorticityHilbertState →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj coordinate).comp (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave)

variable {index : ℕ} (family : ℕ → Profile index)
  (evolves : ∀ n time, HasDerivWithinAt (readProfile (family n)) (readProfile (family (n + 1)) time.1)
    (Icc (0 : ℝ) (run stackedShortCurrent index).duration) (time : Time index).1)

include evolves in
theorem observed_chain_iterated {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (read : ComplexVorticityHilbertState →L[ℝ] F) (order : ℕ) (time : Time index) :
    iteratedDerivWithin order (fun actual => read (readProfile (family 0) actual))
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 = read (readProfile (family order) time.1) := by
  induction order generalizing time with
  | zero => rw [iteratedDerivWithin_zero]
  | succ order previous =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (f := fun actual => read (readProfile (family order) actual))
        (fun actual inside => previous ⟨actual, inside⟩) (previous time)]
    exact (read.hasFDerivAt.comp_hasDerivWithinAt time.1 (evolves order time)).derivWithin
      (uniqueDiffOn_Icc (run stackedShortCurrent index).receipt.requestedTimePos time.1 time.2)

include evolves in
theorem observed_chain_smooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (read : ComplexVorticityHilbertState →L[ℝ] F) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun actual => read (readProfile (family 0) actual))
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro order _ actual inside
  exact ((read.hasFDerivAt.comp_hasDerivWithinAt actual (evolves order ⟨actual, inside⟩)).congr_of_mem
    (fun sample member => observed_chain_iterated family evolves read order ⟨sample, member⟩)
    inside).differentiableWithinAt

def timeCoefficient (wave : IntegerWavevector) (coordinate : Coordinate) (pair : Spacetime) : ℂ :=
  readProfile (family 0) pair.1 wave coordinate

include evolves in
theorem timeCoefficient_smooth (wave : IntegerWavevector) (coordinate : Coordinate) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (timeCoefficient family wave coordinate) (slab index) :=
  (observed_chain_smooth family evolves (coordinateRead wave coordinate)).comp
    contDiffOn_fst (fun _ inside => inside.1)

include evolves in
theorem timeCoefficient_derivative_bound (wave : IntegerWavevector) (coordinate : Coordinate)
    (order : ℕ) (pair : Spacetime) (inside : pair ∈ slab index) :
    ‖iteratedFDerivWithin ℝ order (timeCoefficient family wave coordinate) (slab index) pair‖ ≤
      ‖readProfile (family order) pair.1 wave coordinate‖ := by
  let projection : Spacetime →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ PhysicalSpace
  have domainEq : projection ⁻¹' Icc (0 : ℝ) (run stackedShortCurrent index).duration = slab index := by
    ext pair
    simp [projection, slab]
  have chainRule := projection.iteratedFDerivWithin_comp_right (i := order)
    (observed_chain_smooth family evolves (coordinateRead wave coordinate))
    (uniqueDiffOn_Icc (run stackedShortCurrent index).receipt.requestedTimePos)
    (by rw [domainEq]; exact slab_unique index) inside.1
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  rw [domainEq] at chainRule
  change iteratedFDerivWithin ℝ order (timeCoefficient family wave coordinate) (slab index) pair = _ at chainRule
  rw [chainRule]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [projection, ContinuousLinearMap.norm_fst, Finset.prod_const_one, mul_one]
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  exact (congrArg norm (observed_chain_iterated family evolves (coordinateRead wave coordinate) order ⟨pair.1, inside.1⟩)).le

def spaceMonomial (wave : IntegerWavevector) (pair : Spacetime) : ℂ := monomial wave pair.2

theorem spaceMonomial_smooth (wave : IntegerWavevector) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spaceMonomial wave) :=
  (monomial_smooth wave).comp contDiff_snd

theorem spaceMonomial_derivative_bound (wave : IntegerWavevector) (order : ℕ)
    (pair : Spacetime) (inside : pair ∈ slab index) :
    ‖iteratedFDerivWithin ℝ order (spaceMonomial wave) (slab index) pair‖ ≤
      (2 * Real.pi * frequencySize wave) ^ order := by
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (slab_unique index)
    ((spaceMonomial_smooth wave).contDiffAt.of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))) inside]
  let projection : Spacetime →L[ℝ] PhysicalSpace := ContinuousLinearMap.snd ℝ ℝ PhysicalSpace
  change ‖iteratedFDeriv ℝ order (monomial wave ∘ projection) pair‖ ≤ _
  rw [projection.iteratedFDeriv_comp_right (monomial_smooth wave) pair
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [projection, ContinuousLinearMap.norm_snd, Finset.prod_const_one, mul_one]
  exact monomial_iterated_bound wave order pair.2

theorem coordinate_decay (profile : Profile index) (order : ℕ) (actual : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    frequencySize wave ^ order * ‖readProfile profile actual wave coordinate‖ ≤
      Real.sqrt (profile.budget (order + 4)) * decay wave := by
  have paid := profile_square_moments profile (order + 4) actual
  have highPaid : Summable fun wave => (frequencySize wave ^ (order + 4)) ^ 2 *
      complexCoordinateAmplitudeSq (readProfile profile actual wave) := by
    simpa only [← pow_mul, Nat.mul_comm (order + 4) 2] using paid.1
  have highBound : (∑' wave, (frequencySize wave ^ (order + 4)) ^ 2 *
      complexCoordinateAmplitudeSq (readProfile profile actual wave)) ≤ profile.budget (order + 4) := by
    simpa only [← pow_mul, Nat.mul_comm (order + 4) 2] using paid.2
  have coordinateBound : ‖readProfile profile actual wave coordinate‖ ≤ rowAmplitude (readProfile profile actual wave) :=
    (norm_le_pi_norm (readProfile profile actual wave) coordinate).trans
      (Real.le_sqrt_of_sq_le (complexCoordinateVector_norm_sq_le_amplitudeSq _))
  exact (mul_le_mul_of_nonneg_left coordinateBound (pow_nonneg (frequencySize_pos wave).le _)).trans
    (weighted_row_decay (fun wave => readProfile profile actual wave) order _ highPaid highBound wave)

def scalarMode (wave : IntegerWavevector) (coordinate : Coordinate) (pair : Spacetime) : ℂ :=
  timeCoefficient family wave coordinate pair * spaceMonomial wave pair

def modeBudget (order : ℕ) : ℝ :=
  ∑ rank ∈ Finset.range (order + 1), (order.choose rank : ℝ) * (2 * Real.pi) ^ (order - rank) *
    Real.sqrt ((family rank).budget (order - rank + 4))

include evolves in
theorem scalarMode_smooth (wave : IntegerWavevector) (coordinate : Coordinate) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (scalarMode family wave coordinate) (slab index) :=
  (timeCoefficient_smooth family evolves wave coordinate).mul (spaceMonomial_smooth wave).contDiffOn

include evolves in
theorem scalarMode_bound (order : ℕ) (wave : IntegerWavevector) (coordinate : Coordinate)
    (pair : Spacetime) (inside : pair ∈ slab index) :
    ‖iteratedFDerivWithin ℝ order (scalarMode family wave coordinate) (slab index) pair‖ ≤
      modeBudget family order * decay wave := by
  have product := norm_iteratedFDerivWithin_mul_le (timeCoefficient_smooth family evolves wave coordinate)
    (spaceMonomial_smooth wave).contDiffOn (slab_unique index) inside
    (n := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  apply product.trans
  rw [modeBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro rank _
  have timeBound := timeCoefficient_derivative_bound family evolves wave coordinate rank pair inside
  have spaceBound := spaceMonomial_derivative_bound wave (order - rank) pair inside
  have source := coordinate_decay (family rank) (order - rank) pair.1 wave coordinate
  calc
    (order.choose rank : ℝ) * ‖iteratedFDerivWithin ℝ rank (timeCoefficient family wave coordinate) (slab index) pair‖ *
        ‖iteratedFDerivWithin ℝ (order - rank) (spaceMonomial wave) (slab index) pair‖ ≤
      (order.choose rank : ℝ) * (2 * Real.pi) ^ (order - rank) *
        (frequencySize wave ^ (order - rank) * ‖readProfile (family rank) pair.1 wave coordinate‖) := by
        have scaled := mul_le_mul_of_nonneg_left
          (mul_le_mul timeBound spaceBound (norm_nonneg _) (norm_nonneg _)) (Nat.cast_nonneg (order.choose rank))
        convert! scaled using 1
        · ring
        · rw [mul_pow]
          ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left source
        (mul_nonneg (Nat.cast_nonneg (order.choose rank)) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _))

include evolves in
theorem scalar_sum_smooth (coordinate : Coordinate) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun pair => ∑' wave, scalarMode family wave coordinate pair) (slab index) := by
  have opened : IsOpen (slabInterior index) := isOpen_Ioo.prod isOpen_univ
  have convex : Convex ℝ (slabInterior index) := (convex_Ioo _ _).prod convex_univ
  have nonempty : (slabInterior index).Nonempty := by
    refine ⟨((run stackedShortCurrent index).duration / 2, 0), ?_, mem_univ _⟩
    have positive := (run stackedShortCurrent index).receipt.requestedTimePos
    constructor <;> linarith
  have generated := contDiffOn_tsum_closure opened convex nonempty
    (by rw [slab_closure]; exact slab_unique index)
    (fun wave => scalarMode family wave coordinate) (fun n wave => modeBudget family n * decay wave)
    (fun wave => by rw [slab_closure]; exact scalarMode_smooth family evolves wave coordinate)
    (fun n => decay_summable.mul_left _)
    (fun n wave pair inside => by
      rw [slab_closure] at inside ⊢
      exact scalarMode_bound family evolves n wave coordinate pair inside)
  rwa [slab_closure] at generated

def jointField (pair : Spacetime) : PhysicalSpace := profileField (family 0) pair.1 pair.2

theorem jointField_coordinate (coordinate : Coordinate) (pair : Spacetime) :
    jointField family pair coordinate = (∑' wave, scalarMode family wave coordinate pair).re := by
  have paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (readProfile (family 0) pair.1 wave)) := by
    simpa only [pow_zero, one_mul, amplitude, vorticityRowAmplitude,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      summable_moment_of_square (readProfile (family 0) pair.1) 0 (profile_square_moments (family 0) 2 pair.1).1
  have source := (ContinuousMap.evalCLM ℂ (circlePoint pair.2)).hasSum
    (NativePhysicalContinuous.scalarSummable (readProfile (family 0) pair.1) coordinate paid).hasSum
  change HasSum (fun wave => scalarMode family wave coordinate pair)
    (NativePhysicalContinuous.scalarContinuous (readProfile (family 0) pair.1) coordinate (circlePoint pair.2)) at source
  exact (congrArg Complex.re source.tsum_eq).symm

include evolves in
theorem joint_contDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (jointField family) (slab index) := by
  have same : jointField family = fun pair => WithLp.toLp 2
      (fun coordinate : Coordinate => (∑' wave, scalarMode family wave coordinate pair).re) := by
    funext pair
    apply PiLp.ext
    intro coordinate
    exact jointField_coordinate family coordinate pair
  rw [same]
  apply PiLp.contDiff_toLp.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro coordinate
  exact Complex.reCLM.contDiff.comp_contDiffOn (scalar_sum_smooth family evolves coordinate)

include evolves in
theorem joint_frechet_Lp (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime}
    (compact : IsCompact domain) (contained : domain ⊆ slab index) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (jointField family) (slab index)) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order (jointField family) (slab index)) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  let differential := iteratedFDerivWithin ℝ order (jointField family) (slab index)
  have continuous : ContinuousOn differential domain :=
    ((joint_contDiffOn family evolves).continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)) (slab_unique index)).mono contained
  have bounded := (compact.image_of_continuousOn continuous.norm).bddAbove
  obtain ⟨ceiling, ceilingBound⟩ := bounded
  let budget := max ceiling 0
  have pointBound (point : Spacetime) (inside : point ∈ domain) : ‖differential point‖ ≤ budget :=
    (ceilingBound ⟨point, inside, rfl⟩).trans (le_max_left _ _)
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have aeBound : ∀ᵐ point ∂volume.restrict domain, ‖differential point‖ ≤ budget := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact pointBound point inside
  refine ⟨budget, le_max_right _ _, MemLp.of_bound (continuous.aestronglyMeasurable compact.measurableSet) budget aeBound, ?_⟩
  simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) aeBound

def sourceField (index : ℕ) (pair : Spacetime) : PhysicalSpace :=
  spatialField (sourceVelocity index pair.1) pair.2

theorem sourceField_receipt (index : ℕ) (time : Time index) (point : PhysicalSpace) :
    sourceField index (time.1, point) =
      spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time)) point := by
  change spatialField (sourceVelocity index time.1) point = _
  rw [sourceVelocity_on_interval]

theorem sourceField_eq_joint (index : ℕ) : sourceField index = jointField (jet index) := by
  funext pair
  exact (congrFun (physicalJet_zero index pair.1) pair.2).symm

theorem sourceField_joint_contDiffOn (index : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (sourceField index) (slab index) := by
  rw [sourceField_eq_joint]
  exact joint_contDiffOn (jet index) (jet_hasDerivWithinAt index)

theorem sourceField_spacetime_Lp (index order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime}
    (compact : IsCompact domain) (contained : domain ⊆ slab index) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (sourceField index) (slab index)) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order (sourceField index) (slab index)) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  rw [sourceField_eq_joint]
  exact joint_frechet_Lp (jet index) (jet_hasDerivWithinAt index) order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeSpacetimeControl
