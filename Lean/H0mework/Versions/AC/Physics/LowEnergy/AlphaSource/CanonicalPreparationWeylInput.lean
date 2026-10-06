import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylExtension
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylWeakForm
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCore
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarGuard
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompletion
import Mathlib.Analysis.Fourier.LpSpace

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylDomain
open PreparationVacuumWeyl PreparationMeasure PreparationScalarCoordinates PreparationChartGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open CanonicalPreparationCore GaussDensityCore GaussCoreHilbert GaussHistoryHilbert
open SourceQuantumGaugeSliceCoordinates MeasureTheory Filter
open scoped SchwartzMap FourierTransform Distributions ContDiff ENNReal

abbrev FourierHilbert := Lp (α := PhysicalMomentum) ℂ 2 (volume : Measure PhysicalMomentum)

def rawEuclideanCoordinates : FlatRawHilbert →ₗᵢ[ℂ] FourierHilbert :=
  Lp.compMeasurePreservingₗᵢ ℂ flatPosition actual_flatPosition_measure

def sourceEuclideanHalfDensity (N : ℕ) : SectorHilbert N →ₗᵢ[ℂ] FourierHilbert :=
  rawEuclideanCoordinates.comp (sourceRawHalfDensity N)

def sourceFrequencyHalfDensity (N : ℕ) : SectorHilbert N →ₗᵢ[ℂ] FourierHilbert :=
  (Lp.fourierTransformₗᵢ PhysicalMomentum ℂ).toLinearIsometry.comp (sourceEuclideanHalfDensity N)

theorem sourceFrequencyHalfDensity_norm (N : ℕ) (f : SectorHilbert N) :
    ‖sourceFrequencyHalfDensity N f‖=‖f‖ := (sourceFrequencyHalfDensity N).norm_map f

def rawHalfDensityCore (N : ℕ) : ScalarTest →ₗ[ℂ] ScalarTest :=
  (Real.sqrt nativeVolumeFactor : ℂ) • multiply (coreHalfDensity N) (coreHalfDensity_smooth N)

theorem rawHalfDensityCore_apply (N : ℕ) (f : ScalarTest) (z : SourceCoordinateSlice) :
    rawHalfDensityCore N f z=(Real.sqrt nativeVolumeFactor : ℂ)*coreHalfDensity N z*f z := by
  change (Real.sqrt nativeVolumeFactor : ℂ)*(coreHalfDensity N z*f z)=_
  ring

def nativePositionCoordinates : PhysicalMomentum ≃L[ℝ] SourceCoordinateSlice :=
  flatPosition.trans fullCoordinates.symm

def sourcePositionProfile (N : ℕ) (f : ScalarTest) : 𝓢(PhysicalMomentum,ℂ) :=
  ((rawHalfDensityCore N f).hasCompactSupport.comp_homeomorph
    nativePositionCoordinates.toHomeomorph).toSchwartzMap
      ((rawHalfDensityCore N f).contDiff.comp nativePositionCoordinates.contDiff)

theorem sourcePositionProfile_apply (N : ℕ) (f : ScalarTest) (x : PhysicalMomentum) :
    sourcePositionProfile N f x=rawHalfDensityCore N f (fullCoordinates.symm (flatPosition x)) := rfl

theorem raw_zero_extension_core (N : ℕ) (f : ScalarTest) :
    flatZeroExtend (fun z => (rawHalfFactor N (chartCoordinates.symm z) : ℂ)*
      f (fullCoordinates.symm z.val))=
        fun z : FlatConfiguration => rawHalfDensityCore N f (fullCoordinates.symm z) := by
  ext z
  by_cases inside : z∈flatChart
  · rw [flatZeroExtend, dif_pos inside,rawHalfDensityCore_apply]
    change (Real.sqrt nativeVolumeFactor*GaussHalfDensity.halfDensity N
      (chartCoordinates.symm ⟨z,inside⟩) : ℝ) * (f (fullCoordinates.symm z))=_
    have half : coreHalfDensity N (fullCoordinates.symm z)=
        (GaussHalfDensity.halfDensity N (chartCoordinates.symm ⟨z,inside⟩) : ℂ) := by
      have coordinate : (chartCoordinates.symm ⟨z,inside⟩).val=fullCoordinates.symm z := by rfl
      simpa only [coordinate] using coreHalfDensity_on_chart N (chartCoordinates.symm ⟨z,inside⟩)
    rw [Complex.ofReal_mul,half]
  · have zero : f (fullCoordinates.symm z)=0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro support
      exact inside (f.tsupport_subset support)
    rw [flatZeroExtend_outside _ z inside,rawHalfDensityCore_apply,zero,mul_zero]

theorem sourceEuclidean_core_profile (N : ℕ) (f : ScalarTest) :
    sourceEuclideanHalfDensity N (scalarLp N f)=(sourcePositionProfile N f).toLp 2 := by
  have raw : sourceRawHalfDensity N (scalarLp N f)=ᵐ[Measure.map flatPosition volume]
      (fun z => rawHalfDensityCore N f (fullCoordinates.symm z)) := by
    rw [actual_flatPosition_measure.map_eq]
    exact (source_raw_core_readback N f).trans (Eventually.of_forall
      (congrFun (raw_zero_extension_core N f)))
  have pulled := ae_of_ae_map actual_flatPosition_measure.measurable.aemeasurable raw
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (sourceRawHalfDensity N (scalarLp N f))
      actual_flatPosition_measure,pulled,(sourcePositionProfile N f).coeFn_toLp 2 volume]
    with x hc hr hs
  change Lp.compMeasurePreserving flatPosition actual_flatPosition_measure
      (sourceRawHalfDensity N (scalarLp N f)) x= _
  rw [hc]
  simp only [Function.comp_apply]
  rw [hr,hs]
  rfl

def sourceFrequencyProfile (N : ℕ) (f : ScalarTest) : 𝓢(PhysicalMomentum,ℂ) :=
  𝓕 (sourcePositionProfile N f)

theorem sourceFrequency_core_profile (N : ℕ) (f : ScalarTest) :
    sourceFrequencyHalfDensity N (scalarLp N f)=(sourceFrequencyProfile N f).toLp 2 := by
  change 𝓕 (sourceEuclideanHalfDensity N (scalarLp N f))= _
  rw [sourceEuclidean_core_profile,SchwartzMap.toLp_fourier_eq]
  rfl

def sourceVacuumInputCore : ScalarTest →ₗ[ℂ] ScalarTest :=
  CanonicalScalarPreparation.cutCore actualNativeLocalizer

def sourceVacuumInputFrequency (f : ScalarTest) : 𝓢(PhysicalMomentum,ℂ) :=
  sourceFrequencyProfile 0 (sourceVacuumInputCore f)

theorem actual_N0_input_profile (f : ScalarTest) :
    sourceFrequencyHalfDensity 0
      (CanonicalPreparationCore.Completed.zeroCutoff actualNativeLocalizer
        (CanonicalPreparationCore.Completed.zeroCore f))=
      (sourceVacuumInputFrequency f).toLp 2 := by
  rw [CanonicalPreparationCore.Completed.zeroCutoff_core]
  exact sourceFrequency_core_profile 0 _

def actualVacuumFactorPair (g : 𝓢(PhysicalMomentum,ℂ)) (f : ScalarTest) : ℂ :=
  weakWeylForm g (sourceVacuumInputFrequency f)

theorem actualVacuumFactorPair_integrable (g : 𝓢(PhysicalMomentum,ℂ)) (f : ScalarTest) :
    Integrable (weakIntegrand g (sourceVacuumInputFrequency f)) (volume.prod volume) :=
  weakIntegrand_integrable _ _

end LowEnergy.PreparationVacuumWeylDomain
