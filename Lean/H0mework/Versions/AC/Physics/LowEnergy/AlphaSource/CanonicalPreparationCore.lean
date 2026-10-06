import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCreation
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPreparationCore
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussDensityCore GaussHistoryHilbert GaussHalfDensity
open CanonicalPreparationCreation
open MeasureTheory Filter Set
open scoped ContDiff Distributions ENNReal Topology
attribute [local instance] SourceRealScalarFock.branchOrder

def coreHalfDensity (N : ℕ) (z : SourceCoordinateSlice) : ℂ :=
  Real.sqrt (density N z)

theorem coreHalfDensity_smooth (N : ℕ) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coreHalfDensity N) z.val :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    ((density_smooth N z).sqrt (density_pos N z).ne')

theorem coreHalfDensity_on_chart (N : ℕ) (z : physicalChart) :
    coreHalfDensity N z.val = (halfDensity N z : ℂ) := rfl

theorem coreHalfDensity_ne_zero (N : ℕ) (z : physicalChart) :
    coreHalfDensity N z.val ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (halfDensity_pos N z).ne'

def numberRaise (z : SourceCoordinateSlice) : ℂ :=
  coreHalfDensity 0 z * (coreHalfDensity 1 z)⁻¹

theorem numberRaise_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ numberRaise z.val :=
  (coreHalfDensity_smooth 0 z).mul
    ((coreHalfDensity_smooth 1 z).inv (coreHalfDensity_ne_zero 1 z))

def numberRaiseCore : ScalarTest →ₗ[ℂ] ScalarTest :=
  multiply numberRaise numberRaise_smooth

theorem numberRaiseCore_apply (f : ScalarTest) (z : SourceCoordinateSlice) :
    numberRaiseCore f z = numberRaise z * f z := rfl

theorem numberRaise_source : numberRaise sourcePoint.val = 1 := by
  unfold numberRaise
  rw [coreHalfDensity_on_chart,coreHalfDensity_on_chart,
    source_halfDensity_native,source_halfDensity_native]
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr source_jacobian_pos).ne')

theorem numberRaiseCore_source (f : ScalarTest) :
    numberRaiseCore f sourcePoint.val = f sourcePoint.val := by
  rw [numberRaiseCore_apply,numberRaise_source,one_mul]

theorem numberRaise_volume (z : physicalChart) :
    numberRaise z.val = ((Real.sqrt (spatialVolume z) : ℂ))⁻¹ := by
  have weights : numberWeight 1 z = numberWeight 0 z * spatialVolume z := by
    simp only [GaussHistoryHilbert.numberWeight]
    ring
  have halves : halfDensity 1 z = halfDensity 0 z * Real.sqrt (spatialVolume z) := by
    simp only [halfDensity,weights,Real.sqrt_mul (numberWeight_pos 0 z).le]
  unfold numberRaise
  rw [coreHalfDensity_on_chart,coreHalfDensity_on_chart,halves,Complex.ofReal_mul]
  have nonzero : (halfDensity 0 z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfDensity_pos 0 z).ne'
  field_simp

theorem numberRaiseCore_multiply (c : SourceCoordinateSlice → ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f : ScalarTest) :
    numberRaiseCore (multiply c smooth f)=multiply c smooth (numberRaiseCore f) := by
  apply DFunLike.ext
  intro z
  change numberRaise z*(c z*f z)=c z*(numberRaise z*f z)
  ring

theorem halfDensity_numberRaiseCore (f : ScalarTest) :
    halfDensityEquiv 1 (scalarLp 1 (numberRaiseCore f)) =
      halfDensityEquiv 0 (scalarLp 0 f) := by
  apply Lp.ext
  filter_upwards [halfDensityMap_apply 1 (scalarLp 1 (numberRaiseCore f)),
    halfDensityMap_apply 0 (scalarLp 0 f),
    (scalarLp_ae 1 (numberRaiseCore f)).filter_mono (weighted_null_sets 1).ae_le,
    (scalarLp_ae 0 f).filter_mono (weighted_null_sets 0).ae_le] with z h1 h0 hf1 hf0
  change halfDensityMap 1 (scalarLp 1 (numberRaiseCore f)) z =
    halfDensityMap 0 (scalarLp 0 f) z
  rw [h1,h0]
  simp only [multiplyHalf,hf1,hf0,numberRaiseCore_apply,numberRaise,
    coreHalfDensity_on_chart]
  have nonzero : (halfDensity 1 z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfDensity_pos 1 z).ne'
  field_simp

def profile (f : ScalarTest) : GaussComposite.SourceGraph.Profile :=
  GaussComposite.SourceGraph.core (numberRaiseCore f)

def createdCore (f : ScalarTest) : GaussCoreDifferential.QuantumTest :=
  GaussComposite.SourceGraph.seedSection (numberRaiseCore f)

theorem sourceCreated_N1_core (f : ScalarTest) :
    sourceCreated (halfDensityEquiv 1 (scalarLp 1 f)) =
      embed (GaussComposite.SourceGraph.seedSection f) := by
  apply fockHalfDensityEquiv.injective
  apply PiLp.ext
  intro word
  rw [sourceCreated_coordinates]
  change CanonicalCompletedSector.seed word • halfDensityEquiv 1 (scalarLp 1 f) =
    halfDensityEquiv word.card (scalarLp word.card
      (component word (GaussComposite.SourceGraph.seedSection f)))
  rw [GaussComposite.SourceGraph.seedSection_component,
    GaussComposite.SourceGraph.scalarLp_smul,map_smul]
  by_cases hone : word.card=1
  · rw [hone]
  · rw [GaussComposite.SourceGraph.seed_zero_off_one word hone]
    simp

theorem sourceCreated_core (f : ScalarTest) :
    sourceCreated (halfDensityEquiv 0 (scalarLp 0 f)) = embed (createdCore f) := by
  rw [←halfDensity_numberRaiseCore]
  exact sourceCreated_N1_core (numberRaiseCore f)

theorem sourceCreated_prepared (f : ScalarTest) :
    sourceCreated (halfDensityEquiv 0 (scalarLp 0 f)) =
      GaussComposite.SourceGraph.prepared (profile f) := by
  rw [profile,GaussComposite.SourceGraph.prepared_core]
  exact sourceCreated_core f

theorem prepared_norm (f : ScalarTest) :
    ‖GaussComposite.SourceGraph.prepared (profile f)‖=‖scalarLp 0 f‖ := by
  rw [←sourceCreated_prepared,sourceCreated_norm,(halfDensityEquiv 0).norm_map]

theorem prepared_unit (f : ScalarTest) (unit : ‖scalarLp 0 f‖=1) :
    ‖GaussComposite.SourceGraph.prepared (profile f)‖=1 := by
  rw [prepared_norm,unit]

theorem original_eight_legs (f : ScalarTest) (addition : Bool) (a s : Fin 2) :
    GaussComposite.SourceGraph.completedLeg addition a s (profile f)=
      GaussComposite.leg addition a s (createdCore f) :=
  GaussComposite.SourceGraph.completedLeg_core addition a s (numberRaiseCore f)

theorem createdCore_multiply (c : SourceCoordinateSlice → ℂ)
    (smooth : ContDiff ℝ ∞ c) (f : ScalarTest) :
    GaussComposite.scalarMultiplier c smooth (createdCore f)=
      createdCore (multiply c (fun _ => smooth.contDiffAt) f) := by
  rw [createdCore,GaussComposite.SourceGraph.scalar_seedSection,
    ←numberRaiseCore_multiply]
  rfl

theorem annihilation_sourceCreated (a s : Fin 2) (f : ScalarTest) :
    GaussComposite.SourceGraph.completedLeg false a s (profile f)=
      ∑ color : Fin 3, GaussCARHistory.annihilate (GaussComposite.mode s color)
        (sourceCreated (halfDensityEquiv 0 (scalarLp 0
          (multiply (GaussComposite.coefficient a color)
            (fun _ => (GaussComposite.coefficient_smooth a color).contDiffAt) f)))) := by
  rw [original_eight_legs]
  change GaussComposite.annihilationSource a s (createdCore f)=_
  rw [GaussComposite.annihilation_source_apply]
  apply Finset.sum_congr rfl
  intro color _
  rw [createdCore_multiply,←sourceCreated_core]

theorem creation_sourceCreated (a s : Fin 2) (f : ScalarTest) :
    GaussComposite.SourceGraph.completedLeg true a s (profile f)=
      ∑ color : Fin 3, GaussCARHistory.create (GaussComposite.mode s color)
        (sourceCreated (halfDensityEquiv 0 (scalarLp 0
          (multiply (fun z => star (GaussComposite.coefficient a color z))
            (fun _ => (((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff).comp
              (GaussComposite.coefficient_smooth a color)).contDiffAt) f)))) := by
  rw [original_eight_legs]
  change GaussComposite.creationSource a s (createdCore f)=_
  simp only [GaussComposite.creationSource,LinearMap.sum_apply,LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro color _
  rw [createdCore_multiply,←sourceCreated_core]

theorem original_contact (a s : Fin 2) (f : ScalarTest) :
    ‖GaussComposite.SourceGraph.completedLeg true a s (profile f)‖^2+
      ‖GaussComposite.SourceGraph.completedLeg false a s (profile f)‖^2=
      (GaussFockPair.sourcePair (createdCore f)
        (GaussComposite.contactSource a s a s (createdCore f))).re := by
  rw [original_eight_legs,original_eight_legs]
  exact GaussComposite.source_contact_norm a s (createdCore f)

theorem original_bounded_kernel (A : GaussUnitaryHistory.HistorySpace →L[ℂ]
    GaussUnitaryHistory.HistorySpace) (left right : Bool) (a s b t : Fin 2)
    (f g : ScalarTest) :
    GaussComposite.SourceGraph.response A left right a s b t (profile f) (profile g)=
      inner ℂ (GaussUnitaryHistory.inclusion (GaussComposite.leg left a s (createdCore f)))
        (A (GaussUnitaryHistory.inclusion (GaussComposite.leg right b t (createdCore g)))) :=
  GaussComposite.SourceGraph.response_core A left right a s b t (numberRaiseCore f) (numberRaiseCore g)

theorem original_composite_kernel
    (phi : CanonicalGradedSpatial.Localizer)
    (p k ell : CanonicalGradedSpatialSource.PhysicalMomentum)
    (A B : CanonicalGradedSpatialKernel.NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (a s b t : Fin 2) (f g : ScalarTest) :
    GaussComposite.SourceGraph.response
      (GaussComposite.Bilocal.fullResponse phi p k ell A B cut age frequency damping positive)
      left right a s b t (profile f) (profile g)=
      inner ℂ (GaussUnitaryHistory.inclusion (GaussComposite.leg left a s (createdCore f)))
        (CanonicalGradedBilocal.response phi p k ell A B age frequency damping positive
          (GaussUnitaryHistory.inclusion (GaussComposite.leg right b t (createdCore g)))) := by
  rw [GaussComposite.SourceGraph.original_composite_kernel_return]
  exact original_bounded_kernel _ left right a s b t f g

end LowEnergy.CanonicalPreparationCore
