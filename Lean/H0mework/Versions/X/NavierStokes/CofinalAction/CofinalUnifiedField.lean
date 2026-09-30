import H0mework.Versions.X.NavierStokes.SourceAction.PhysicalHistoryCurrent
import H0mework.Versions.X.NavierStokes.SourceAction.GeneratedSpacetime
import H0mework.Versions.X.NavierStokes.CofinalAction.CofinalRecovery

set_option autoImplicit false
open scoped ContDiff ENNReal

namespace SaturationMonoid.NavierStokes.NativeCofinalUnifiedField

open Set
open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction StageNineFullDiracAdjointMaterial
open Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open NativeReceiptTimeProfile NativeFullOrderSynthesis
open NativePhysicalHistory (coordinates coordinates_contDiff)
open NativeFluidSpatialOperators (slice slice_time slice_spatial)
open NativeFinitePrefixTimeChart (spatialRead)

noncomputable section

variable {nu : Viscosity}

def target (initial : GeneratedWholeRestartCurrent nu) : GeneratedWholeRestartCurrent nu :=
  sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial

theorem target_from_occurrence (initial : GeneratedWholeRestartCurrent nu) :
    target initial = generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence initial
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence :=
  (nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent initial).symm

def receipt (initial : GeneratedWholeRestartCurrent nu) := (target initial).nextReceipt

def window (initial : GeneratedWholeRestartCurrent nu) : Window (receipt initial) :=
  NativeGeneratedSpacetime.cofinalNextWindow initial

def domain (initial : GeneratedWholeRestartCurrent nu) : Set BasePoint :=
  {point | point 0 ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)}

def field (initial : GeneratedWholeRestartCurrent nu) : BasePoint → PhysicalSpace :=
  NativeReceiptSpacetime.field (receipt initial) ∘ coordinates

def vorticityField (initial : GeneratedWholeRestartCurrent nu) : BasePoint → PhysicalSpace :=
  NativeReceiptSpacetime.vorticityField (receipt initial) ∘ coordinates

def correctionField (initial : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) : BasePoint → PhysicalSpace :=
  NativeReceiptSpacetime.correctionField (receipt initial) modes ∘ coordinates

theorem field_contDiffOn (initial : GeneratedWholeRestartCurrent nu) : ContDiffOn ℝ ∞ (field initial) (domain initial) :=
  (NativeReceiptSpacetime.field_contDiffOn (window initial)).comp coordinates_contDiff.contDiffOn (fun _ member => ⟨member, trivial⟩)

theorem vorticityField_contDiffOn (initial : GeneratedWholeRestartCurrent nu) :
    ContDiffOn ℝ ∞ (vorticityField initial) (domain initial) :=
  (NativeReceiptSpacetime.vorticityField_contDiffOn (window initial)).comp coordinates_contDiff.contDiffOn (fun _ member => ⟨member, trivial⟩)

theorem correctionField_contDiffOn (initial : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) :
    ContDiffOn ℝ ∞ (correctionField initial modes) (domain initial) :=
  (NativeReceiptSpacetime.correctionField_contDiffOn (window initial) modes).comp coordinates_contDiff.contDiffOn (fun _ member => ⟨member, trivial⟩)

def matter (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) : DiracExteriorMatterCarrier :=
  NativeCanonicalFluidCoframe.matter (field initial point)

def dual (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  NativeCanonicalFluidCoframe.dual (field initial point)

theorem canonical_pairing (initial : GeneratedWholeRestartCurrent nu) (point : BasePoint) :
    FullDiracAdjointPaired (matter initial point) (dual initial point) := NativeCanonicalFluidCoframe.canonical_paired _

theorem spatial_read (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 3) :
    current (matter initial) (dual initial) direction.succ = fun point => field initial point direction := by
  funext point
  exact Stage9CU.Fluid.InitialLift.spatialCurrent_eq _ direction

theorem temporal_read (initial : GeneratedWholeRestartCurrent nu) :
    current (matter initial) (dual initial) 0 = fun point => 2 + ‖field initial point‖ ^ 2 / 8 := by
  funext point
  rw [current, dual, matter, NativeCanonicalFluidCoframe.dual, NativeCanonicalFluidCoframe.matter,
    Stage9CU.Fluid.InitialLift.temporalCurrent_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem current_contDiffOn (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) :
    ContDiffOn ℝ ∞ (current (matter initial) (dual initial) direction) (domain initial) := by
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · rw [temporal_read]
    exact contDiffOn_const.add (((field_contDiffOn initial).norm_sq (𝕜 := ℝ)).div_const 8)
  · rw [spatial_read]
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) spatial).contDiff.comp_contDiffOn (field_contDiffOn initial)

theorem field_on_slice (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (space : PhysicalSpace) :
    field initial (slice actual space) = NativeReceiptSpacetime.field (receipt initial) (actual, space) := by
  have spatial : spatialRead (slice actual space) = space := by
    apply PiLp.ext
    intro direction
    exact slice_spatial _ _ direction
  change NativeReceiptSpacetime.field _ ((slice actual space) 0, spatialRead (slice actual space)) = _
  rw [slice_time, spatial]

theorem field_initial (initial : GeneratedWholeRestartCurrent nu) (space : PhysicalSpace) :
    field initial (slice 0 space) = spatialField (wholeBiotSavartVelocityState (target initial).contact.physicalState) space := by
  rw [field_on_slice]
  unfold NativeReceiptSpacetime.field NativeReceiptSpacetime.velocity
  rw [NativeReceiptSpacetime.state_on_interval (receipt initial) ⟨0, le_rfl, (receipt initial).requestedTimePos.le⟩,
    (receipt initial).wholePath_initial]

theorem field_generated_next (initial : GeneratedWholeRestartCurrent nu) (space : PhysicalSpace) :
    field initial (slice (target initial).next.contact.time.1 space) =
      spatialField (wholeBiotSavartVelocityState (target initial).next.contact.physicalState) space := by
  rw [field_on_slice]
  unfold NativeReceiptSpacetime.field NativeReceiptSpacetime.velocity
  rw [NativeReceiptSpacetime.state_on_interval (receipt initial) (target initial).next.contact.time]
  rfl

end
end SaturationMonoid.NavierStokes.NativeCofinalUnifiedField
