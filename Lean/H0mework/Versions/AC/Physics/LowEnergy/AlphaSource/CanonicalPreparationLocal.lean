import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalar
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! Original compact localization supplies the scalar-Gram moment required
by every prepared composite leg. No near-state, phase or normalization is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalScalarPreparation
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open CanonicalGradedSpatial (Localizer)
open GaussHistoryHilbert (physicalChart)
open MeasureTheory Set Filter
open scoped Topology ContDiff Distributions ENNReal

def weightedCutoff (phi : Localizer) : BoundedContinuousFunction SourceCoordinateSlice ℝ :=
  _root_.ofCompactSupport
    (fun z => Real.sqrt (gramWeight z)*phi z)
    ((Real.continuous_sqrt.comp gramWeight_continuous).mul phi.continuous)
    phi.hasCompactSupport.mul_left

def localBound (phi : Localizer) : ℝ := ‖weightedCutoff phi‖

theorem localBound_nonnegative (phi : Localizer) : 0≤localBound phi := norm_nonneg _

theorem local_square_bound (phi : Localizer) (z : SourceCoordinateSlice) :
    gramWeight z*(phi z)^2≤(localBound phi)^2 := by
  have point := (weightedCutoff phi).norm_coe_le_norm z
  have square := pow_le_pow_left₀ (norm_nonneg _) point 2
  change ‖Real.sqrt (gramWeight z)*phi z‖^2≤(localBound phi)^2 at square
  simpa only [Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt (gramWeight_pos z).le] using square

def cutCore (phi : Localizer) : ScalarTest →ₗ[ℂ] ScalarTest :=
  multiply (fun z => (phi z : ℂ))
    (fun _ => (Complex.ofRealCLM.contDiff.comp phi.contDiff).contDiffAt)

theorem local_eLpNorm (phi : Localizer) (f : physicalChart → ℂ) :
    eLpNorm (fun z : physicalChart => (phi z : ℂ)*f z) 2 graphMeasure≤
      eLpNorm (fun z => (localBound phi : ℂ)*f z) 2
        (GaussHistoryHilbert.numberMeasure 1) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  have measurableWeight : Measurable (fun z : physicalChart => ENNReal.ofReal (gramWeight z)) :=
    (gramWeight_continuous.comp continuous_subtype_val).measurable.ennreal_ofReal
  rw [graphMeasure,lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurableWeight
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono
  intro z
  have point := mul_le_mul_of_nonneg_right (local_square_bound phi z) (sq_nonneg ‖f z‖)
  simp only [Pi.mul_apply,ENNReal.rpow_two,←ofReal_norm]
  rw [←ENNReal.ofReal_pow (norm_nonneg _),←ENNReal.ofReal_pow (norm_nonneg _),
    ←ENNReal.ofReal_mul (gramWeight_pos z).le]
  apply ENNReal.ofReal_le_ofReal
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc] using point

theorem local_core_bound (phi : Localizer) (f : ScalarTest) :
    ‖core (cutCore phi f)‖≤localBound phi*‖scalarCore f‖ := by
  have estimate := local_eLpNorm phi (fun z : physicalChart => f z)
  have right : eLpNorm (fun z : physicalChart => (localBound phi : ℂ)*f z) 2
      (GaussHistoryHilbert.numberMeasure 1)=
      ENNReal.ofReal (localBound phi*‖scalarCore f‖) := by
    rw [show (fun z : physicalChart => (localBound phi : ℂ)*f z)=
      (localBound phi : ℂ) • (fun z : physicalChart => f z) from rfl,
      eLpNorm_const_smul,←ofReal_norm]
    have normRead : eLpNorm (fun z : physicalChart => f z) 2
        (GaussHistoryHilbert.numberMeasure 1)=ENNReal.ofReal ‖scalarCore f‖ := by
      rw [ofReal_norm,Lp.enorm_def]
      exact (eLpNorm_congr_ae (scalarLp_ae 1 f)).symm
    rw [normRead,Complex.norm_real,Real.norm_of_nonneg (localBound_nonnegative phi),
      ENNReal.ofReal_mul (localBound_nonnegative phi)]
  have left : ENNReal.ofReal ‖core (cutCore phi f)‖=
      eLpNorm (fun z : physicalChart => (phi z : ℂ)*f z) 2 graphMeasure := by
    rw [ofReal_norm,Lp.enorm_def]
    exact eLpNorm_congr_ae (coreProfile_ae (cutCore phi f))
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (localBound_nonnegative phi) (norm_nonneg _))).mp
  rw [left]
  exact estimate.trans_eq right

def localProfile (phi : Localizer) : ScalarSpace →L[ℂ] Profile :=
  (core.comp (cutCore phi)).extendOfNorm scalarCore

theorem localProfile_core (phi : Localizer) (f : ScalarTest) :
    localProfile phi (scalarCore f)=core (cutCore phi f) :=
  LinearMap.extendOfNorm_eq scalarCore_dense ⟨localBound phi,local_core_bound phi⟩ f

theorem localProfile_bound (phi : Localizer) (f : ScalarSpace) :
    ‖localProfile phi f‖≤localBound phi*‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le scalarCore_dense _ (local_core_bound phi) f

def scalarCutoff (phi : Localizer) : ScalarSpace →L[ℂ] ScalarSpace :=
  forget.comp (localProfile phi)

theorem scalarCutoff_core (phi : Localizer) (f : ScalarTest) :
    scalarCutoff phi (scalarCore f)=scalarCore (cutCore phi f) := by
  change forget (localProfile phi (scalarCore f))=_
  rw [localProfile_core,forget_core]

theorem localProfile_prepared (phi : Localizer) (f : ScalarSpace) :
    prepared (localProfile phi f)=seedBase (scalarCutoff phi f) := prepared_factors _

theorem localProfile_physical_norm (phi : Localizer) (f : ScalarSpace) :
    ‖prepared (localProfile phi f)‖=‖scalarCutoff phi f‖ := prepared_norm _

theorem localProfile_all_legs_bound (phi : Localizer) (f : ScalarSpace)
    (addition : Bool) (a s : Fin 2) :
    ‖completedLeg addition a s (localProfile phi f)‖≤legBound*localBound phi*‖f‖ := by
  exact (completedLeg_bound addition a s _).trans
    ((mul_le_mul_of_nonneg_left (localProfile_bound phi f) legBound_nonnegative).trans_eq
      (mul_assoc _ _ _).symm)

theorem retained_unit (phi : Localizer) (f : ScalarSpace)
    (retained : scalarCutoff phi f=f) (unit : ‖f‖=1) :
    ‖prepared (localProfile phi f)‖=1 := by
  rw [localProfile_physical_norm,retained,unit]

def complexCutoff (phi : Localizer) : ScalarTest :=
  TestFunction.postcompCLM Complex.ofRealCLM phi

def outerCutoff (phi : Localizer) : Localizer :=
  CanonicalGradedLocalCurrent.coreLocalizer (seedSection (complexCutoff phi))

theorem outerCutoff_retains (phi : Localizer) (z : SourceCoordinateSlice) :
    outerCutoff phi z*phi z=phi z := by
  by_cases zero : phi z=0
  · rw [zero,mul_zero]
  · have seedNonzero : CanonicalCompletedSector.seed≠0 := by
      intro h
      have unit := seed_unit
      rw [h,norm_zero] at unit
      norm_num at unit
    have nonzero : seedSection (complexCutoff phi) z≠0 :=
      smul_ne_zero (Complex.ofReal_ne_zero.mpr zero) seedNonzero
    have atPoint := CanonicalGradedLocalCurrent.coreLocalizer_one
      (seedSection (complexCutoff phi)) z (subset_tsupport _ nonzero)
    change outerCutoff phi z=1 at atPoint
    rw [atPoint,one_mul]

theorem outer_scalarCutoff (phi : Localizer) (f : ScalarSpace) :
    scalarCutoff (outerCutoff phi) (scalarCutoff phi f)=scalarCutoff phi f := by
  refine scalarCore_dense.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [scalarCutoff_core,scalarCutoff_core]
  apply congrArg scalarCore
  apply DFunLike.ext
  intro z
  change (outerCutoff phi z : ℂ)*((phi z : ℂ)*g z)=(phi z : ℂ)*g z
  rw [←mul_assoc,←Complex.ofReal_mul,outerCutoff_retains]

/-- The closed range of the original preparation localizer, in the original
Number1 Hilbert space. This restriction does not choose a state in that range. -/
def localizedSpace (phi : Localizer) : Submodule ℂ ScalarSpace :=
  (LinearMap.range (scalarCutoff phi).toLinearMap).topologicalClosure

theorem outer_retains_localized (phi : Localizer) (f : localizedSpace phi) :
    scalarCutoff (outerCutoff phi) f.val=f.val := by
  have onRange : EqOn (scalarCutoff (outerCutoff phi)) id
      (LinearMap.range (scalarCutoff phi).toLinearMap : Set ScalarSpace) := by
    rintro v ⟨u,rfl⟩
    exact outer_scalarCutoff phi u
  exact onRange.closure (by fun_prop) continuous_id f.property

def localizedProfile (phi : Localizer) : localizedSpace phi →L[ℂ] Profile :=
  (localProfile (outerCutoff phi)).comp (localizedSpace phi).subtypeL

theorem localized_prepared (phi : Localizer) (f : localizedSpace phi) :
    prepared (localizedProfile phi f)=seedBase f.val := by
  change prepared (localProfile (outerCutoff phi) f.val)=_
  rw [localProfile_prepared,outer_retains_localized]

theorem localized_physical_norm (phi : Localizer) (f : localizedSpace phi) :
    ‖prepared (localizedProfile phi f)‖=‖f‖ := by
  rw [localized_prepared,seedBase_norm]
  rfl

theorem localized_profile_bound (phi : Localizer) (f : localizedSpace phi) :
    ‖localizedProfile phi f‖≤localBound (outerCutoff phi)*‖f‖ :=
  localProfile_bound (outerCutoff phi) f.val

theorem localized_eight_legs (phi : Localizer) (f : localizedSpace phi)
    (addition : Bool) (a s : Fin 2) :
    ‖completedLeg addition a s (localizedProfile phi f)‖≤
      legBound*localBound (outerCutoff phi)*‖f‖ :=
  localProfile_all_legs_bound (outerCutoff phi) f.val addition a s

end LowEnergy.CanonicalScalarPreparation
