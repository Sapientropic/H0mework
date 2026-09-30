import H0mework.Versions.X.NavierStokes.CofinalAction.CofinalCurrentResponse
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryDomain

set_option autoImplicit false
open scoped ContDiff ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryUnifiedCurrent

open Set Filter MeasureTheory UnitAddTorus
open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction StageNineFullDiracAdjointMaterial Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryAEWindows NativeRecoveryStrongWindow NativeRecoveryRegularDomain
open NativePhysicalFourier NativeFullOrderSynthesis
open NativePhysicalHistory (coordinates coordinates_contDiff)
open NativeFinitePrefixTimeChart (spatialRead)
open NativeFluidSpatialOperators (slice)

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity}

def receipt (initial : GeneratedWholeRestartCurrent nu) := sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial

def terminal (initial : GeneratedWholeRestartCurrent nu) : ℝ := (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1

def domain (initial : GeneratedWholeRestartCurrent nu) : Set BasePoint :=
  {point | point 0 ∈ regularSet (receipt initial) (terminal initial)}

theorem domain_open (initial : GeneratedWholeRestartCurrent nu) : IsOpen (domain initial) :=
  (regularSet_open _ _).preimage (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0)

theorem regular_window (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) :
    ∃ lower : ℝ, ∃ window : ControlledWindow (receipt initial) lower (terminal initial),
      actual ∈ Ioo window.first window.last := by
  obtain ⟨span, inside⟩ := mem_iUnion.mp member
  let delta := (actual - span.first) / 2
  have positive : 0 < delta := half_pos (sub_pos.mpr inside.1)
  have fits : span.first + delta < span.last := by dsimp [delta]; linarith [inside.1, inside.2]
  refine ⟨span.first, span.toControlledWindow delta positive fits, ?_, inside.2⟩
  change span.first + delta < actual
  dsimp [delta]
  linarith [inside.1]

def velocity (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : ComplexVorticityHilbertState :=
  NativeRecoveryRowAction.velocity (receipt initial) actual

theorem velocity_reality (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) :
    FiniteStateFourierReality (velocity initial actual) := NativeRecoveryPhysical.wholeMild_reality _ _ _

theorem velocity_paid (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) :
    Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity initial actual wave)) := by
  obtain ⟨lower, window, inside⟩ := regular_window initial actual member
  exact NativeRecoveryPhysical.amplitude_summable _ (fun order => window.paid order actual ⟨inside.1.le, inside.2.le⟩)

def field (initial : GeneratedWholeRestartCurrent nu) : BasePoint → PhysicalSpace :=
  NativeRecoveryTimeJets.field (receipt initial) ∘ coordinates

theorem field_on_slice (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (space : PhysicalSpace) :
    field initial (slice actual space) = spatialField (velocity initial actual) space := by
  have spatial : spatialRead (slice actual space) = space := by
    apply PiLp.ext
    intro direction
    exact NativeFluidSpatialOperators.slice_spatial _ _ direction
  change spatialField (velocity initial ((slice actual space) 0)) (spatialRead (slice actual space)) = _
  rw [NativeFluidSpatialOperators.slice_time, spatial]

theorem field_contDiffOn (initial : GeneratedWholeRestartCurrent nu) : ContDiffOn ℝ ∞ (field initial) (domain initial) :=
  (field_regular_contDiffOn (receipt initial) (terminal initial)).comp coordinates_contDiff.contDiffOn
    (fun _ member => ⟨member, trivial⟩)

def matter (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) : DiracExteriorMatterCarrier :=
  NativeCanonicalFluidCoframe.matter (field initial point)

def dual (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  NativeCanonicalFluidCoframe.dual (field initial point)

theorem canonical_pairing (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) :
    FullDiracAdjointPaired (matter initial point) (dual initial point) := NativeCanonicalFluidCoframe.canonical_paired _

theorem spatial_read (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 3) :
    current (matter initial) (dual initial) direction.succ = fun point => field initial point direction := by
  funext point
  exact NativePairedCurrentFourier.value_spatial _ direction

theorem temporal_read (initial : GeneratedWholeRestartCurrent nu) :
    current (matter initial) (dual initial) 0 = fun point => 2 + ‖field initial point‖ ^ 2 / 8 := by
  funext point
  exact NativePairedCurrentFourier.value_temporal _

theorem current_contDiffOn (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) :
    ContDiffOn ℝ ∞ (current (matter initial) (dual initial) direction) (domain initial) := by
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · rw [temporal_read]
    exact contDiffOn_const.add (((field_contDiffOn initial).norm_sq (𝕜 := ℝ)).div_const 8)
  · rw [spatial_read]
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) spatial).contDiff.comp_contDiffOn (field_contDiffOn initial)

theorem source_current_all_order_Lp (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (exponent : ℝ≥0∞)
    {compactDomain : Set BasePoint} (compact : IsCompact compactDomain) (contained : compactDomain ⊆ domain initial) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDeriv ℝ order (current (matter initial) (dual initial) direction)) exponent (volume.restrict compactDomain) ∧
      eLpNorm (iteratedFDeriv ℝ order (current (matter initial) (dual initial) direction)) exponent (volume.restrict compactDomain) ≤
        ENNReal.ofReal bound * volume compactDomain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict compactDomain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  let jets (point : BasePoint) : Fin 4 → ContinuousMultilinearMap ℝ (fun _ : Fin order => BasePoint) ℝ :=
    fun direction => iteratedFDeriv ℝ order (current (matter initial) (dual initial) direction) point
  have component (direction : Fin 4) : ContinuousOn
      (iteratedFDeriv ℝ order (current (matter initial) (dual initial) direction)) compactDomain :=
    (((current_contDiffOn initial direction).continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top)
      (domain_open initial).uniqueDiffOn).congr
        (fun point member => (iteratedFDerivWithin_of_isOpen order (domain_open initial) member).symm)).mono contained
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn (continuousOn_pi.mpr component : ContinuousOn jets compactDomain)
  refine ⟨bound, fun direction => ?_⟩
  have paid : ∀ᵐ point ∂volume.restrict compactDomain,
      ‖iteratedFDeriv ℝ order (current (matter initial) (dual initial) direction) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact (norm_le_pi_norm (jets point) direction).trans (bounded point inside)
  exact ⟨MemLp.of_bound ((component direction).aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

def continuousCurrent (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (point : Torus) : ℝ :=
  NativePairedCurrentFourier.value (NativePhysicalContinuous.continuousField (velocity initial actual) point) direction

theorem current_ae_original (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) :
    NativePairedCurrentFourier.field (velocity initial actual) direction =ᵐ[volume] continuousCurrent initial actual direction :=
  NativePairedCurrentFourier.field_ae_continuous _ (velocity_paid initial actual member) direction

theorem controlled_current_read (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (space : PhysicalSpace) :
    current (matter initial) (dual initial) direction (slice actual space) = continuousCurrent initial actual direction (circlePoint space) := by
  change NativePairedCurrentFourier.value (field initial (slice actual space)) direction = _
  rw [field_on_slice]
  rfl

theorem controlled_current_fourier (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) (wave : IntegerWavevector) :
    mFourierCoeff (fun point => (continuousCurrent initial actual direction point : ℂ)) wave =
      NativePairedCurrentFourier.coefficient (velocity initial actual) (NativeStressSource.quadraticFlux (velocity initial actual)) direction wave := by
  rw [← NativePairedCurrentFourier.current_fourier _ (velocity_reality initial actual)]
  unfold mFourierCoeff
  apply integral_congr_ae
  filter_upwards [current_ae_original initial actual member direction] with point same
  rw [same]

end
end SaturationMonoid.NavierStokes.NativeRecoveryUnifiedCurrent
