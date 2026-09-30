import H0mework.NavierStokes.UnifiedAction.UnifiedCorrectionControl

set_option autoImplicit false
open scoped Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativePhysicalHistory

open Set Filter
open PhysicsCore.ProofFreeRicherAnholonomicSource
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeFullOrderSynthesis NativeSpacetimeControl
open NativeWholeHistoryField (receipt window path_agrees)
open NativeWholeHistoryClock (duration duration_pos duration_strictMono)
open NativeFinitePrefixTimeChart (spatialRead spatialRead_contDiff)

noncomputable section

def domain : Set BasePoint := {point | 0 ≤ point 0 ∧ ∃ length : ℕ, point 0 < duration length}

def index (actual : ℝ) : ℕ := by
  classical
  exact if covered : ∃ length : ℕ, actual < duration length then Nat.find covered else 0

theorem index_spec (point : BasePoint) (inside : point ∈ domain) : point 0 < duration (index (point 0)) := by
  classical
  rw [index, dif_pos inside.2]
  exact Nat.find_spec inside.2

def slab (length : ℕ) : Set BasePoint := {point | point 0 ∈ Icc (0 : ℝ) (duration length)}

theorem slab_subset (length : ℕ) : slab length ⊆ domain := by
  intro point inside
  exact ⟨inside.1, length + 1, inside.2.trans_lt (duration_strictMono (Nat.lt_succ_self length))⟩

def state (actual : ℝ) : ComplexVorticityHilbertState := NativeReceiptSpacetime.state (receipt (index actual)) actual

theorem state_read (length : ℕ) (point : BasePoint) (inside : point ∈ slab length) :
    state (point 0) = NativeReceiptSpacetime.state (receipt length) (point 0) := by
  have covered := slab_subset length inside
  unfold state
  rw [NativeReceiptSpacetime.state_on_interval (receipt (index (point 0)))
      ⟨point 0, inside.1, (index_spec point covered).le⟩,
    NativeReceiptSpacetime.state_on_interval (receipt length) ⟨point 0, inside⟩]
  exact path_agrees _ _ _ _ _

def coordinates (point : BasePoint) : Spacetime := (point 0, spatialRead point)

theorem coordinates_contDiff : ContDiff ℝ ∞ coordinates :=
  (contDiff_piLp_apply 2).prodMk spatialRead_contDiff

def read (observation : ComplexVorticityHilbertState → PhysicalSpace → PhysicalSpace) (point : BasePoint) : PhysicalSpace :=
  observation (state (point 0)) (spatialRead point)

theorem read_locally (observation : ComplexVorticityHilbertState → PhysicalSpace → PhysicalSpace)
    (point : BasePoint) (inside : point ∈ domain) :
    ∀ᶠ sample in 𝓝[domain] point,
      read observation sample = observation
        (NativeReceiptSpacetime.state (receipt (index (point 0))) (sample 0)) (spatialRead sample) := by
  have upper := ((contDiff_piLp_apply 2 : ContDiff ℝ ∞ (fun sample : BasePoint => sample 0)).continuous.tendsto point)
    (Iio_mem_nhds (index_spec point inside))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds upper] with sample belongs before
  unfold read
  rw [state_read _ sample ⟨belongs.1, before.le⟩]

theorem slab_near (point : BasePoint) (inside : point ∈ domain) : slab (index (point 0)) ∈ 𝓝[domain] point := by
  have upper := ((contDiff_piLp_apply 2 : ContDiff ℝ ∞ (fun sample : BasePoint => sample 0)).continuous.tendsto point)
    (Iio_mem_nhds (index_spec point inside))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds upper] with sample belongs before
  exact ⟨belongs.1, before.le⟩

theorem read_contDiffOn (observation : ComplexVorticityHilbertState → PhysicalSpace → PhysicalSpace)
    (controlled : ∀ length : ℕ, ContDiffOn ℝ ∞
      (fun pair : Spacetime => observation (NativeReceiptSpacetime.state (receipt length) pair.1) pair.2)
      (NativeReceiptSpacetime.slab (window length))) :
    ContDiffOn ℝ ∞ (read observation) domain := by
  intro point inside
  let length := index (point 0)
  have pointMember : point ∈ slab length := ⟨inside.1, (index_spec point inside).le⟩
  have original := (controlled length).comp coordinates_contDiff.contDiffOn
    (show MapsTo coordinates (slab length) (NativeReceiptSpacetime.slab (window length)) from
      fun sample member => ⟨member, trivial⟩)
  have nearby := (original point pointMember).mono_of_mem_nhdsWithin (slab_near point inside)
  exact nearby.congr_of_eventuallyEq_of_mem (read_locally observation point inside) inside

def field : BasePoint → PhysicalSpace := read (fun value => spatialField (wholeBiotSavartVelocityState value))

def vorticityField : BasePoint → PhysicalSpace := read spatialField

theorem field_contDiffOn : ContDiffOn ℝ ∞ field domain :=
  read_contDiffOn _ (fun length => NativeReceiptSpacetime.field_contDiffOn (window length))

theorem vorticityField_contDiffOn : ContDiffOn ℝ ∞ vorticityField domain :=
  read_contDiffOn _ (fun length => NativeReceiptSpacetime.vorticityField_contDiffOn (window length))

def correctionField (modes : Finset IntegerWavevector) : BasePoint → PhysicalSpace :=
  read (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw.nativeTurbulenceCorrectionField modes)

theorem correctionField_contDiffOn (modes : Finset IntegerWavevector) :
    ContDiffOn ℝ ∞ (correctionField modes) domain :=
  read_contDiffOn _ (fun length => NativeReceiptSpacetime.correctionField_contDiffOn (window length) modes)

theorem domain_contains_zero (point : BasePoint) (zero : point 0 = 0) : point ∈ domain := by
  change 0 ≤ point 0 ∧ ∃ length : ℕ, point 0 < duration length
  rw [zero]
  exact ⟨le_rfl, 0, duration_pos 0⟩

theorem positive_domain_subset : NativeWholeHistoryPhysical.physicalDomain ⊆ domain := by
  intro point inside
  exact ⟨inside.1.le, _, NativeWholeHistoryPhysicalAction.physical_cover (point 0) inside⟩

theorem domain_positive (point : BasePoint) (inside : point ∈ domain) (positive : 0 < point 0) :
    point ∈ NativeWholeHistoryPhysical.physicalDomain := by
  obtain ⟨length, before⟩ := inside.2
  exact NativeWholeHistoryClock.physicalDomain_of_le_duration length (point 0) positive before.le

theorem field_positive (point : BasePoint) (inside : point ∈ NativeWholeHistoryPhysical.physicalDomain) :
    field point = NativeWholeHistoryField.field (NativeWholeHistoryPhysical.pullback point) := by
  exact (NativeWholeHistoryField.physical_read (index (point 0)) (point 0)
    ⟨inside.1, (index_spec point (positive_domain_subset inside)).le⟩ (spatialRead point)).symm

theorem state_zero : state 0 = RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent.initialState := by
  rw [state, NativeReceiptSpacetime.state_on_interval (receipt (index 0))
    ⟨0, le_rfl, (duration_pos (index 0)).le⟩, (receipt (index 0)).wholePath_initial]

theorem field_initial (space : PhysicalSpace) :
    field (NativeFluidSpatialOperators.slice 0 space) = spatialField
      (wholeBiotSavartVelocityState RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent.initialState) space := by
  have spatial : spatialRead (NativeFluidSpatialOperators.slice 0 space) = space := by
    apply PiLp.ext
    intro direction
    exact NativeFluidSpatialOperators.slice_spatial _ _ direction
  rw [field, read, NativeFluidSpatialOperators.slice_time, state_zero, spatial]

end
end SaturationMonoid.NavierStokes.NativePhysicalHistory
