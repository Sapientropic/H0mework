import H0mework.NavierStokes.ShellSources.InfiniteLineageCarrierCompletion
import H0mework.NavierStokes.Galerkin.AmbientNorm
import H0mework.NavierStokes.Galerkin.CommonTimeExistence
import H0mework.NavierStokes.Fourier.PuncturedCanonicalGalerkinTarget

/-!
# Whole-Hilbert completion of an infinite generated shell lineage

The source lineage already writes every finite coefficient endpoint as the
seed carrier plus a pairwise-disjoint sum of receipt traces.  This module
compiles that exact write-back into the complete ambient Fourier carrier.

The compilation is the literal regrouping of flattened wave-coordinate
coefficients into vector-valued Fourier rows.  Its ambient squared distance
is bounded by the exact source-generated receipt tail.  Consequently, the
common strict-critical margin generates a Cauchy sequence and hence a
whole-state limit in `ℓ²`; every fixed Fourier row converges to the
corresponding row of that same limit.

No limit, convergence witness, support coverage, or silent-tail premise is
stored in the source lineage.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion

open scoped BigOperators Topology

open Set
open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCarrierCompletion.GeneratedIntegerShellInfiniteLineage

noncomputable section

/-! ## The actual flattened-carrier compiler -/

/--
Regroup a finite flattened coefficient carrier into vector-valued Fourier
rows in the common complete `ℓ²` carrier.
-/
def coefficientCarrierComplexState
    (carrier : IntegerShellCoefficientCarrier) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState
    (coefficientWaveSupport carrier)
    (fun wave coordinate => carrier (wave, coordinate))

@[simp] theorem coefficientCarrierComplexState_apply
    (carrier : IntegerShellCoefficientCarrier)
    (wave : IntegerWavevector) :
    coefficientCarrierComplexState carrier wave =
      fun coordinate => carrier (wave, coordinate) := by
  classical
  rw [coefficientCarrierComplexState,
    finiteComplexVorticityState_apply]
  by_cases waveMem : wave ∈ coefficientWaveSupport carrier
  · rw [if_pos waveMem]
  · rw [if_neg waveMem]
    funext coordinate
    symm
    apply Finsupp.notMem_support_iff.mp
    intro coordinateMem
    exact waveMem
      (Finset.mem_image.mpr
        ⟨(wave, coordinate), coordinateMem, rfl⟩)

@[simp] theorem coefficientCarrierComplexState_zero :
    coefficientCarrierComplexState 0 = 0 := by
  apply lp.ext
  funext wave coordinate
  rw [coefficientCarrierComplexState_apply]
  rfl

@[simp] theorem coefficientCarrierComplexState_sub
    (left right : IntegerShellCoefficientCarrier) :
    coefficientCarrierComplexState (left - right) =
        coefficientCarrierComplexState left -
        coefficientCarrierComplexState right := by
  apply lp.ext
  rw [lp.coeFn_sub]
  funext wave coordinate
  simp only [coefficientCarrierComplexState_apply,
    Finsupp.sub_apply, Pi.sub_apply]

private theorem coefficientCarrier_support_subset_wave_product
    (carrier : IntegerShellCoefficientCarrier) :
    carrier.support ⊆
      coefficientWaveSupport carrier ×ˢ
        (Finset.univ : Finset Coordinate) := by
  intro index indexMem
  rw [Finset.mem_product]
  exact
    ⟨Finset.mem_image.mpr ⟨index, indexMem, rfl⟩,
      Finset.mem_univ index.2⟩

/--
The flattened squared mass is exactly the finite coefficient enstrophy of
its regrouped state.
-/
theorem coefficientCarrierNormSq_eq_coefficientEnstrophy
    (carrier : IntegerShellCoefficientCarrier) :
    coefficientCarrierNormSq carrier =
      finiteStateVorticityCoefficientEnstrophy
        (coefficientWaveSupport carrier)
        (coefficientCarrierComplexState carrier) := by
  classical
  rw [coefficientCarrierNormSq]
  rw [Finset.sum_subset
    (coefficientCarrier_support_subset_wave_product carrier)]
  · rw [Finset.sum_product]
    unfold finiteStateVorticityCoefficientEnstrophy
      complexCoordinateAmplitudeSq
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [coefficientCarrierComplexState_apply]
  · intro index indexMem indexNotSupport
    have carrierZero : carrier index = 0 :=
      Finsupp.notMem_support_iff.mp indexNotSupport
    simp [carrierZero]

/--
The common ambient `ℓ²` norm is controlled by the exact flattened
coefficient mass.  The loss is only the existing finite-vector norm
comparison, never a shell-count factor.
-/
theorem coefficientCarrierComplexState_norm_sq_le
    (carrier : IntegerShellCoefficientCarrier) :
    ‖coefficientCarrierComplexState carrier‖ ^ 2 ≤
      coefficientCarrierNormSq carrier := by
  rw [coefficientCarrierNormSq_eq_coefficientEnstrophy]
  apply
    complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      (coefficientWaveSupport carrier)
  intro wave waveNotMem
  rw [coefficientCarrierComplexState,
    finiteComplexVorticityState_apply, if_neg waveNotMem]

/-! ## Exact identification with generated source endpoints -/

private theorem generatedComplexVorticityState_fullSupport_apply
    (source : RawVorticityFourierSource)
    (wave : IntegerWavevector) :
    generatedComplexVorticityState source
        (generatedSupport source) wave =
      generatedVorticityCoefficient source wave := by
  by_cases waveMem : wave ∈ generatedSupport source
  · simp [waveMem]
  · rw [generatedComplexVorticityState_apply,
      if_neg waveMem,
      generatedVorticityCoefficient_eq_zero_of_not_mem
        source waveMem]

/--
The flattened compiler recovers the actual finite source endpoint state,
not a separate observational surrogate.
-/
theorem coefficientCarrierComplexState_generatedCoefficientCarrier
    (source : RawVorticityFourierSource) :
    coefficientCarrierComplexState
        (generatedCoefficientCarrier source) =
      generatedComplexVorticityState source
        (generatedSupport source) := by
  apply lp.ext
  funext wave coordinate
  rw [coefficientCarrierComplexState_apply]
  simpa only [generatedCoefficientCarrier_apply] using
    (congrFun
      (generatedComplexVorticityState_fullSupport_apply
        source wave) coordinate).symm

/--
Arbitrary finite-path crossing theorem: the ambient squared distance between
the actual source endpoints is controlled by the exact accumulated receipt
mass of that `GeneratedIntegerShellReachable` path.
-/
theorem generatedIntegerShellReachable_endpoint_dist_sq_le_receipt_mass
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    dist
        (generatedComplexVorticityState current
          (generatedSupport current))
        (generatedComplexVorticityState seed
          (generatedSupport seed)) ^ 2 ≤
      ((generatedIntegerShellReachableReceipts arrival).map
        (fun receipt =>
          coefficientCarrierNormSq
            (generatedIntegerShellReceiptTrace receipt))).sum := by
  have carrierDifference :
      generatedCoefficientCarrier current -
          generatedCoefficientCarrier seed =
        generatedIntegerShellCumulativeTrace arrival := by
    rw [generatedCoefficientCarrier_eq_seed_add_cumulativeTrace
      arrival]
    abel
  rw [← coefficientCarrierComplexState_generatedCoefficientCarrier,
    ← coefficientCarrierComplexState_generatedCoefficientCarrier,
    dist_eq_norm,
    ← coefficientCarrierComplexState_sub,
    carrierDifference]
  exact
    (coefficientCarrierComplexState_norm_sq_le _).trans_eq
      (generatedIntegerShellCumulativeTrace_normSq arrival)

/-! ## Contractive canonical finite-frequency projections -/

/-- Sharp support projection is contractive on the common `ℓ²` carrier. -/
theorem complexSharpSupportProjection_norm_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ‖complexSharpSupportProjection modes state‖ ≤ ‖state‖ := by
  apply lp.norm_mono (by norm_num)
  intro wave
  by_cases waveMem : wave ∈ modes
  · simp [complexSharpSupportProjection_apply, waveMem]
  · simp [complexSharpSupportProjection_apply, waveMem]

theorem complexSharpSupportProjection_sub
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) :
    complexSharpSupportProjection modes (left - right) =
      complexSharpSupportProjection modes left -
        complexSharpSupportProjection modes right := by
  apply lp.ext
  rw [lp.coeFn_sub]
  funext wave
  by_cases waveMem : wave ∈ modes <;>
    simp [complexSharpSupportProjection_apply, waveMem]

/-- Sharp support projection does not increase ambient distance. -/
theorem complexSharpSupportProjection_dist_le
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) :
    dist
        (complexSharpSupportProjection modes left)
        (complexSharpSupportProjection modes right) ≤
      dist left right := by
  rw [dist_eq_norm, dist_eq_norm,
    ← complexSharpSupportProjection_sub]
  exact
    complexSharpSupportProjection_norm_le
      modes (left - right)

/-- Sharp projection preserves the coefficient enstrophy measured on the
same retained inventory. -/
theorem finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy modes
        (complexSharpSupportProjection modes state) =
      finiteStateVorticityCoefficientEnstrophy modes state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [complexSharpSupportProjection_apply, if_pos waveMem]

/--
For a state supported on `support`, the coefficient enstrophy measured on
any other finite inventory is bounded by its full supported enstrophy.
-/
theorem finiteStateVorticityCoefficientEnstrophy_le_of_supported
    (modes support : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ support → state wave = 0) :
    finiteStateVorticityCoefficientEnstrophy modes state ≤
      finiteStateVorticityCoefficientEnstrophy support state := by
  let active :=
    modes.filter fun wave => wave ∈ support
  have activeSubsetModes : active ⊆ modes :=
    Finset.filter_subset _ _
  have activeSubsetSupport : active ⊆ support := by
    intro wave waveMem
    exact (Finset.mem_filter.mp waveMem).2
  have activeEqModes :
      (∑ wave ∈ active,
          complexCoordinateAmplitudeSq (state wave)) =
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (state wave) := by
    rw [Finset.sum_subset activeSubsetModes]
    intro wave waveMem waveNotActive
    have waveNotSupport : wave ∉ support := by
      intro waveSupport
      exact waveNotActive
        (Finset.mem_filter.mpr
          ⟨waveMem, waveSupport⟩)
    rw [supported wave waveNotSupport]
    simp [complexCoordinateAmplitudeSq]
  unfold finiteStateVorticityCoefficientEnstrophy
  rw [← activeEqModes]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      activeSubsetSupport
      (fun wave waveNotActive waveMem =>
        complexCoordinateAmplitudeSq_nonneg (state wave))

/--
Sharp projection to a finite inventory cannot increase the enstrophy of a
state with known finite support.
-/
theorem finiteStateVorticityCoefficientEnstrophy_sharp_le_of_supported
    (modes support : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ support → state wave = 0) :
    finiteStateVorticityCoefficientEnstrophy modes
        (complexSharpSupportProjection modes state) ≤
      finiteStateVorticityCoefficientEnstrophy support state := by
  rw [
    finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
  exact
    finiteStateVorticityCoefficientEnstrophy_le_of_supported
      modes support state supported

theorem complexSharpSupportProjection_supported
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ∀ wave, wave ∉ modes →
      complexSharpSupportProjection modes state wave = 0 := by
  intro wave waveNotMem
  rw [complexSharpSupportProjection_apply,
    if_neg waveNotMem]

theorem complexSharpSupportProjection_transverse
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (transverse :
      ∀ wave,
        complexWavevector wave ⬝ᵥ state wave = 0) :
    ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ
        complexSharpSupportProjection modes state wave =
      0 := by
  intro wave waveMem
  rw [complexSharpSupportProjection_apply,
    if_pos waveMem]
  exact transverse wave

theorem complexSharpSupportProjection_reality
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (reality : FiniteStateFourierReality state) :
    FiniteStateFourierReality
      (complexSharpSupportProjection modes state) := by
  intro wave
  by_cases waveMem : wave ∈ modes
  · have negWaveMem : waveNeg wave ∈ modes :=
      negClosed wave waveMem
    rw [complexSharpSupportProjection_apply,
      if_pos negWaveMem,
      complexSharpSupportProjection_apply,
      if_pos waveMem]
    exact reality wave
  · have negWaveNotMem : waveNeg wave ∉ modes := by
      intro negWaveMem
      exact waveMem (by
        simpa using negClosed (waveNeg wave) negWaveMem)
    rw [complexSharpSupportProjection_apply,
      if_neg negWaveNotMem,
      complexSharpSupportProjection_apply,
      if_neg waveMem]
    simp

/--
Deleting the zero wave does not change a sharp projection of a state whose
zero Fourier row vanishes.
-/
theorem complexSharpSupportProjection_erase_zero_eq
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    complexSharpSupportProjection (modes.erase 0) state =
      complexSharpSupportProjection modes state := by
  apply lp.ext
  funext wave
  by_cases waveZero : wave = 0
  · subst wave
    simp [complexSharpSupportProjection_apply, zeroRow]
  · by_cases waveMem : wave ∈ modes <;>
      simp [complexSharpSupportProjection_apply,
        waveZero, waveMem]

private theorem contracting_diagonal_tendsto
    {α : Type*}
    [PseudoMetricSpace α]
    (projection : ℕ → α → α)
    (states : ℕ → α)
    (limit : α)
    (contracting :
      ∀ index left right,
        dist
            (projection index left)
            (projection index right) ≤
          dist left right)
    (statesTendsto : Tendsto states atTop (𝓝 limit))
    (limitProjectionTendsto :
      Tendsto
        (fun index => projection index limit)
        atTop (𝓝 limit)) :
    Tendsto
      (fun index => projection index (states index))
      atTop (𝓝 limit) := by
  rw [Metric.tendsto_atTop]
  intro ε εPos
  have halfPos : 0 < ε / 2 := half_pos εPos
  rcases (Metric.tendsto_atTop.mp statesTendsto)
      (ε / 2) halfPos with
    ⟨stateCutoff, stateClose⟩
  rcases
      (Metric.tendsto_atTop.mp
        limitProjectionTendsto)
        (ε / 2) halfPos with
    ⟨projectionCutoff, projectionClose⟩
  refine
    ⟨max stateCutoff projectionCutoff, ?_⟩
  intro radius radiusGe
  have stateRadiusGe : stateCutoff ≤ radius :=
    (le_max_left _ _).trans radiusGe
  have projectionRadiusGe :
      projectionCutoff ≤ radius :=
    (le_max_right _ _).trans radiusGe
  calc
    dist
        (projection radius (states radius))
        limit ≤
      dist
          (projection radius (states radius))
          (projection radius limit) +
        dist
          (projection radius limit)
          limit :=
      dist_triangle _ _ _
    _ ≤
      dist (states radius) limit +
        dist
          (projection radius limit)
          limit :=
      add_le_add
        (contracting radius (states radius) limit)
        le_rfl
    _ < ε / 2 + ε / 2 :=
      add_lt_add
        (stateClose radius stateRadiusGe)
        (projectionClose radius projectionRadiusGe)
    _ = ε := by ring

/--
The canonical frequency cubes with the zero wave punctured still converge
strongly to every whole state whose zero Fourier row is zero.
-/
theorem complexSharpSupportProjection_puncturedFrequencyCube_tendsto
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    Tendsto
      (fun radius =>
        complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube radius)
          state)
      atTop (𝓝 state) := by
  have projectionEquality :
      (fun radius =>
        complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube radius)
          state) =
        (fun radius =>
          complexSharpSupportProjection
            (integerWaveFrequencyCube radius)
            state) := by
    funext radius
    simpa [puncturedIntegerWaveFrequencyCube] using
      complexSharpSupportProjection_erase_zero_eq
        (integerWaveFrequencyCube radius) state zeroRow
  rw [projectionEquality]
  exact
    complexSharpSupportProjection_frequencyCube_tendsto state

/--
If whole states converge to a zero-mean limit, projecting the `n`th state
to the punctured canonical frequency cube of radius `n` converges to the
same limit.
-/
theorem complexSharpSupportProjection_puncturedFrequencyCube_tendsto_of_tendsto
    (states : ℕ → ComplexVorticityHilbertState)
    (limit : ComplexVorticityHilbertState)
    (zeroRow : limit 0 = 0)
    (statesTendsto : Tendsto states atTop (𝓝 limit)) :
    Tendsto
      (fun radius =>
        complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube radius)
          (states radius))
      atTop (𝓝 limit) := by
  exact
    contracting_diagonal_tendsto
      (fun radius state =>
        complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube radius)
          state)
      states limit
      (fun radius =>
        complexSharpSupportProjection_dist_le
          (puncturedIntegerWaveFrequencyCube radius))
      statesTendsto
      (complexSharpSupportProjection_puncturedFrequencyCube_tendsto
        limit zeroRow)

/-! ## Whole-state finite-prefix tail control -/

namespace GeneratedIntegerShellInfiniteLineage

/-- The actual generated source endpoint installed in the common complete
Fourier carrier. -/
def endpointHilbertState
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    ComplexVorticityHilbertState :=
  generatedComplexVorticityState
    (lineage.current index)
    (generatedSupport (lineage.current index))

theorem endpointHilbertState_eq_carrierComplexState
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    endpointHilbertState lineage index =
      coefficientCarrierComplexState
        (generatedCoefficientCarrier
          (lineage.current index)) := by
  exact
    (coefficientCarrierComplexState_generatedCoefficientCarrier
      (lineage.current index)).symm

/-- Every generated endpoint is transverse at every Fourier wave, including
rows outside its finite support. -/
theorem endpointHilbertState_transverse
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ)
    (wave : IntegerWavevector) :
    complexWavevector wave ⬝ᵥ
        endpointHilbertState lineage index wave =
      0 := by
  unfold endpointHilbertState
  rw [generatedComplexVorticityState_fullSupport_apply]
  exact
    generatedVorticityCoefficient_transverse
      (lineage.current index) wave

/-- Every generated endpoint obeys the global Fourier reality involution. -/
theorem endpointHilbertState_reality
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    FiniteStateFourierReality
      (endpointHilbertState lineage index) := by
  intro wave
  unfold endpointHilbertState
  rw [generatedComplexVorticityState_fullSupport_apply,
    generatedComplexVorticityState_fullSupport_apply,
    generatedVorticityCoefficient_waveNeg]

@[simp] theorem endpointHilbertState_zero
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ) :
    endpointHilbertState lineage index 0 = 0 := by
  unfold endpointHilbertState
  rw [generatedComplexVorticityState_fullSupport_apply,
    generatedVorticityCoefficient_zero]

/-! ## Canonical physical Galerkin initial states -/

/--
The radius-`n` physical canonical Galerkin initial state is the punctured
cube projection of the `n`th actual source endpoint.
-/
def puncturedCanonicalInitialState
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (radius : ℕ) :
    ComplexVorticityHilbertState :=
  complexSharpSupportProjection
    (puncturedIntegerWaveFrequencyCube radius)
    (endpointHilbertState lineage radius)

theorem puncturedCanonicalInitialState_supported
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (radius : ℕ) :
    ∀ wave,
      wave ∉ puncturedIntegerWaveFrequencyCube radius →
        puncturedCanonicalInitialState lineage radius wave = 0 := by
  exact
    complexSharpSupportProjection_supported
      (puncturedIntegerWaveFrequencyCube radius)
      (endpointHilbertState lineage radius)

theorem puncturedCanonicalInitialState_transverse
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (radius : ℕ) :
    ∀ wave ∈ puncturedIntegerWaveFrequencyCube radius,
      complexWavevector wave ⬝ᵥ
        puncturedCanonicalInitialState lineage radius wave =
      0 := by
  exact
    complexSharpSupportProjection_transverse
      (puncturedIntegerWaveFrequencyCube radius)
      (endpointHilbertState lineage radius)
      (endpointHilbertState_transverse lineage radius)

theorem puncturedCanonicalInitialState_reality
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (radius : ℕ) :
    FiniteStateFourierReality
      (puncturedCanonicalInitialState lineage radius) := by
  exact
    complexSharpSupportProjection_reality
      (puncturedIntegerWaveFrequencyCube radius)
      (endpointHilbertState lineage radius)
      (fun wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem
          radius waveMem)
      (endpointHilbertState_reality lineage radius)

/--
The canonical projected initial state has no more coefficient enstrophy than
the actual generated endpoint from which it is compiled.
-/
theorem puncturedCanonicalInitialState_enstrophy_le_endpoint
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (radius : ℕ) :
    finiteStateVorticityCoefficientEnstrophy
        (puncturedIntegerWaveFrequencyCube radius)
        (puncturedCanonicalInitialState lineage radius) ≤
      finiteStateVorticityCoefficientEnstrophy
        (generatedSupport (lineage.current radius))
        (endpointHilbertState lineage radius) := by
  apply
    finiteStateVorticityCoefficientEnstrophy_sharp_le_of_supported
  intro wave waveNotMem
  unfold endpointHilbertState
  rw [generatedComplexVorticityState_apply,
    if_neg waveNotMem]

/--
Every projected canonical initial state inherits the same strict-critical
margin from its actual source endpoint.
-/
theorem puncturedCanonicalInitialState_criticalMargin
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (radius : ℕ) :
    criticalEnstrophyLatticeConstant *
        finiteStateVorticityCoefficientEnstrophy
          (puncturedIntegerWaveFrequencyCube radius)
          (puncturedCanonicalInitialState lineage radius) ≤
      θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
  exact
    (mul_le_mul_of_nonneg_left
      (puncturedCanonicalInitialState_enstrophy_le_endpoint
        lineage radius)
      criticalEnstrophyLatticeConstant_pos.le).trans
        (criticalMargin radius)

/--
The squared ambient distance across any actual finite lineage tail is
bounded by the exact sum of the source-generated receipt quanta in that
tail.
-/
theorem endpointHilbertState_dist_sq_le_tail_sum
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (start length : ℕ) :
    dist
        (endpointHilbertState lineage (start + length))
        (endpointHilbertState lineage start) ^ 2 ≤
      ∑ offset ∈ Finset.range length,
        lineage.receiptQuantum (start + offset) := by
  rw [endpointHilbertState_eq_carrierComplexState,
    endpointHilbertState_eq_carrierComplexState,
    dist_eq_norm,
    ← coefficientCarrierComplexState_sub]
  exact
    (coefficientCarrierComplexState_norm_sq_le _).trans_eq
      (generatedCoefficientCarrier_sub_normSq_eq_tail_sum
        lineage start length)

/-! ## Generated Cauchy sequence and complete-carrier limit -/

/--
A common strict-critical margin forces the actual generated endpoint states
to be Cauchy in the whole ambient `ℓ²` carrier.
-/
theorem endpointHilbertState_cauchySeq
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    CauchySeq (endpointHilbertState lineage) := by
  rw [Metric.cauchySeq_iff]
  intro ε εPos
  rcases
      generatedCoefficientCarrier_forwardCauchy
        lineage ν θ criticalMargin
        (ε ^ 2) (sq_pos_of_pos εPos) with
    ⟨cutoff, carrierClose⟩
  refine ⟨cutoff, ?_⟩
  intro left leftGe right rightGe
  rcases le_total left right with leftLeRight | rightLeLeft
  · rw [dist_comm]
    have distanceSqLe :=
      endpointHilbertState_dist_sq_le_tail_sum
        lineage left (right - left)
    rw [Nat.add_sub_of_le leftLeRight] at distanceSqLe
    have carrierSqLt :=
      carrierClose left leftGe (right - left)
    rw [generatedCoefficientCarrier_sub_normSq_eq_tail_sum]
      at carrierSqLt
    exact
      (sq_lt_sq₀ (dist_nonneg)
        (le_of_lt εPos)).mp
        (distanceSqLe.trans_lt carrierSqLt)
  · have distanceSqLe :=
      endpointHilbertState_dist_sq_le_tail_sum
        lineage right (left - right)
    rw [Nat.add_sub_of_le rightLeLeft] at distanceSqLe
    have carrierSqLt :=
      carrierClose right rightGe (left - right)
    rw [generatedCoefficientCarrier_sub_normSq_eq_tail_sum]
      at carrierSqLt
    exact
      (sq_lt_sq₀ (dist_nonneg)
        (le_of_lt εPos)).mp
        (distanceSqLe.trans_lt carrierSqLt)

/--
The whole-state limit is generated from the source lineage and the critical
margin by completeness of the ambient carrier; it is not supplied as data.
-/
theorem endpointHilbertState_tendsto_limit
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ limit : ComplexVorticityHilbertState,
      Tendsto (endpointHilbertState lineage)
        atTop (𝓝 limit) :=
  cauchySeq_tendsto_of_complete
    (endpointHilbertState_cauchySeq
      lineage ν θ criticalMargin)

/--
The same generated whole-state limit controls every fixed Fourier row.
There is one limit and one sequence; no diagonal subsequence or
mode-coverage premise is introduced.
-/
theorem endpointHilbertState_tendsto_limit_with_fixed_waves
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ limit : ComplexVorticityHilbertState,
      Tendsto (endpointHilbertState lineage)
          atTop (𝓝 limit) ∧
        ∀ wave : IntegerWavevector,
          Tendsto
            (fun index =>
              endpointHilbertState lineage index wave)
            atTop (𝓝 (limit wave)) := by
  rcases endpointHilbertState_tendsto_limit
      lineage ν θ criticalMargin with
    ⟨limit, wholeTendsto⟩
  refine ⟨limit, wholeTendsto, ?_⟩
  intro wave
  have evaluated :=
    ((lp.evalCLM ℂ
      (fun _ : IntegerWavevector =>
        ComplexCoordinateVector)
      2 wave).continuous.tendsto limit).comp wholeTendsto
  exact evaluated

/--
The physical canonical cube Galerkin initial states obtained by projecting
the `n`th generated endpoint to the radius-`n` cube with the zero wave
removed converge strongly to the same whole-state limit.  Both endpoint
convergence, zero-mean closure, and cube exhaustion are generated
internally.
-/
theorem endpointHilbertState_puncturedFrequencyCube_tendsto_limit
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ limit : ComplexVorticityHilbertState,
      Tendsto (endpointHilbertState lineage)
          atTop (𝓝 limit) ∧
        Tendsto
          (fun radius =>
            complexSharpSupportProjection
              (puncturedIntegerWaveFrequencyCube radius)
              (endpointHilbertState lineage radius))
          atTop (𝓝 limit) := by
  rcases endpointHilbertState_tendsto_limit_with_fixed_waves
      lineage ν θ criticalMargin with
    ⟨limit, wholeTendsto, fixedWaveTendsto⟩
  have endpointZeroTendsto :
      Tendsto
        (fun index =>
          endpointHilbertState lineage index 0)
        atTop (𝓝 (0 : ComplexCoordinateVector)) := by
    simpa only [endpointHilbertState_zero] using
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℕ => (0 : ComplexCoordinateVector))
          atTop (𝓝 0))
  have limitZero : limit 0 = 0 :=
    tendsto_nhds_unique
      (fixedWaveTendsto 0)
      endpointZeroTendsto
  exact
    ⟨limit, wholeTendsto,
      complexSharpSupportProjection_puncturedFrequencyCube_tendsto_of_tendsto
        (endpointHilbertState lineage) limit
        limitZero wholeTendsto⟩

/-! ## Actual canonical Galerkin trajectory sequence -/

/--
On every requested positive finite interval, the source lineage and common
strict-critical margin generate a whole sequence of actual physical
punctured-cube Galerkin trajectories.  The requested interval is common to
all radii; no trajectory or lifespan is supplied as data.
-/
theorem exists_puncturedCanonicalGalerkinTrajectories_on_Icc
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (targetTime : ℝ)
    (targetTimePos : 0 < targetTime) :
    ∃ trajectories :
        ℕ → ℝ → ComplexVorticityHilbertState,
      ∀ radius,
        trajectories radius 0 =
            puncturedCanonicalInitialState lineage radius ∧
          ∀ t ∈ Icc (0 : ℝ) targetTime,
            HasDerivAt (trajectories radius)
                (finiteStateVorticityGenerator
                  (puncturedIntegerWaveFrequencyCube radius)
                  ν.coeff (trajectories radius t)) t ∧
              (∀ wave,
                wave ∉
                    puncturedIntegerWaveFrequencyCube radius →
                  trajectories radius t wave = 0) ∧
              (∀ wave,
                complexWavevector wave ⬝ᵥ
                  trajectories radius t wave = 0) ∧
              FiniteStateFourierReality
                (trajectories radius t) := by
  have thresholdNonneg :
      0 ≤ ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have thetaThresholdLe :
      θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 ≤
        ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    simpa only [mul_assoc, one_mul] using
      mul_le_mul_of_nonneg_right
        (le_of_lt θLtOne) thresholdNonneg
  have existsAtRadius :
      ∀ radius : ℕ,
        ∃ trajectory :
            ℝ → ComplexVorticityHilbertState,
          trajectory 0 =
              puncturedCanonicalInitialState lineage radius ∧
            ∀ t ∈ Icc (0 : ℝ) targetTime,
              HasDerivAt trajectory
                  (finiteStateVorticityGenerator
                    (puncturedIntegerWaveFrequencyCube radius)
                    ν.coeff (trajectory t)) t ∧
                (∀ wave,
                  wave ∉
                      puncturedIntegerWaveFrequencyCube radius →
                    trajectory t wave = 0) ∧
                (∀ wave,
                  complexWavevector wave ⬝ᵥ
                    trajectory t wave = 0) ∧
                FiniteStateFourierReality
                  (trajectory t) := by
    intro radius
    apply
      exists_finitePhysicalTrajectory_on_Icc_of_criticalSmall
        (puncturedIntegerWaveFrequencyCube radius)
        (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
        (fun wave waveMem =>
          puncturedIntegerWaveFrequencyCube_waveNeg_mem
            radius waveMem)
        ν.coeff ν.coeff_pos
        (puncturedCanonicalInitialState lineage radius)
        (puncturedCanonicalInitialState_supported
          lineage radius)
        (puncturedCanonicalInitialState_transverse
          lineage radius)
        (puncturedCanonicalInitialState_reality
          lineage radius)
        ?_
        targetTime targetTimePos
    exact
      (puncturedCanonicalInitialState_criticalMargin
        lineage ν θ criticalMargin radius).trans
          thetaThresholdLe
  classical
  exact
    ⟨fun radius => Classical.choose (existsAtRadius radius),
      fun radius =>
        Classical.choose_spec (existsAtRadius radius)⟩

/--
The generated canonical trajectory sequence satisfies the genuine
full-lattice infinite nonlinear mild equation at every fixed nonzero wave
for all sufficiently large radii.
-/
theorem exists_puncturedCanonicalGalerkinTrajectories_with_infiniteRow_mild
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (targetTime : ℝ)
    (targetTimePos : 0 < targetTime) :
    ∃ trajectories :
        ℕ → ℝ → ComplexVorticityHilbertState,
      (∀ radius,
        trajectories radius 0 =
            puncturedCanonicalInitialState lineage radius ∧
          ∀ t ∈ Icc (0 : ℝ) targetTime,
            HasDerivAt (trajectories radius)
                (finiteStateVorticityGenerator
                  (puncturedIntegerWaveFrequencyCube radius)
                  ν.coeff (trajectories radius t)) t ∧
              (∀ wave,
                wave ∉
                    puncturedIntegerWaveFrequencyCube radius →
                  trajectories radius t wave = 0) ∧
              (∀ wave,
                complexWavevector wave ⬝ᵥ
                  trajectories radius t wave = 0) ∧
              FiniteStateFourierReality
                (trajectories radius t)) ∧
        ∀ wave : IntegerWavevector,
          wave ≠ 0 →
            ∀ᶠ radius : ℕ in atTop,
              trajectories radius targetTime wave =
                finiteStateVorticityHeatMultiplier
                    ν.coeff targetTime wave •
                  trajectories radius 0 wave +
                ∫ t in (0 : ℝ)..targetTime,
                  finiteStateVorticityHeatMultiplier
                      ν.coeff (targetTime - t) wave •
                    wholeStateVorticityNonlinearCoefficientAt
                      (trajectories radius t) wave := by
  rcases
      exists_puncturedCanonicalGalerkinTrajectories_on_Icc
        lineage ν θ θLtOne criticalMargin
        targetTime targetTimePos with
    ⟨trajectories, trajectoryProperties⟩
  refine ⟨trajectories, trajectoryProperties, ?_⟩
  intro wave waveNe
  simpa only [sub_zero] using
    puncturedCubeWave_eventually_infiniteRow_mild_identity
      ν.coeff trajectories 0 targetTime targetTimePos.le
      (fun radius t timeMem =>
        (trajectoryProperties radius).2 t timeMem |>.1)
      (fun radius t timeMem =>
        (trajectoryProperties radius).2 t timeMem |>.2.1)
      wave waveNe

/--
The generated whole-state limit remains in the physical transverse and real
closed subspace.  These laws are inherited from every actual source
endpoint; they are not added as limit premises.
-/
theorem endpointHilbertState_tendsto_physical_limit
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ limit : ComplexVorticityHilbertState,
      Tendsto (endpointHilbertState lineage)
          atTop (𝓝 limit) ∧
        (∀ wave : IntegerWavevector,
          Tendsto
            (fun index =>
              endpointHilbertState lineage index wave)
            atTop (𝓝 (limit wave))) ∧
        (∀ wave : IntegerWavevector,
          complexWavevector wave ⬝ᵥ limit wave = 0) ∧
        FiniteStateFourierReality limit := by
  rcases
      endpointHilbertState_tendsto_limit_with_fixed_waves
        lineage ν θ criticalMargin with
    ⟨limit, wholeTendsto, fixedWaveTendsto⟩
  refine
    ⟨limit, wholeTendsto, fixedWaveTendsto, ?_, ?_⟩
  · intro wave
    have dotTendsto :
        Tendsto
          (fun index =>
            complexWavevector wave ⬝ᵥ
              endpointHilbertState lineage index wave)
          atTop
          (𝓝 (complexWavevector wave ⬝ᵥ limit wave)) :=
      ((continuous_const.dotProduct continuous_id).tendsto
        (limit wave)).comp
          (fixedWaveTendsto wave)
    have zeroTendsto :
        Tendsto
          (fun _ : ℕ => (0 : ℂ))
          atTop (𝓝 0) :=
      tendsto_const_nhds
    have generatedDotTendsto :
        Tendsto
          (fun index =>
            complexWavevector wave ⬝ᵥ
              endpointHilbertState lineage index wave)
          atTop (𝓝 0) := by
      simpa only [endpointHilbertState_transverse] using
        zeroTendsto
    exact
      tendsto_nhds_unique dotTendsto generatedDotTendsto
  · intro wave
    have vectorConjContinuous :
        Continuous
          (fun vector : ComplexCoordinateVector =>
            vectorConj vector) := by
      apply continuous_pi
      intro coordinate
      exact
        Complex.continuous_conj.comp
          (continuous_apply coordinate)
    have conjugateTendsto :
        Tendsto
          (fun index =>
            vectorConj
              (endpointHilbertState lineage index wave))
          atTop (𝓝 (vectorConj (limit wave))) :=
      (vectorConjContinuous.tendsto (limit wave)).comp
        (fixedWaveTendsto wave)
    have negativeWaveTendsto :
        Tendsto
          (fun index =>
            endpointHilbertState lineage index
              (waveNeg wave))
          atTop (𝓝 (vectorConj (limit wave))) := by
      have generatedReality :
          (fun index =>
            endpointHilbertState lineage index
              (waveNeg wave)) =
          (fun index =>
            vectorConj
              (endpointHilbertState lineage index wave)) := by
        funext index
        exact endpointHilbertState_reality
          lineage index wave
      rw [generatedReality]
      exact conjugateTendsto
    exact
      tendsto_nhds_unique
        (fixedWaveTendsto (waveNeg wave))
        negativeWaveTendsto

end GeneratedIntegerShellInfiniteLineage

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
end NavierStokes
end SaturationMonoid
