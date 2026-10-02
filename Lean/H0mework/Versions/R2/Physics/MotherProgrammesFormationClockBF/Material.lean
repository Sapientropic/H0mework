import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence
import H0mework.Versions.R2.Physics.SpinPair.GaugeField
import H0mework.Versions.R2.Physics.Homogeneous.GaugeBalance

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFMaterial

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation SU7MotherLieAlgebra
open StageNineBlockwiseConstitutive StageNineFormNativeGaugeWedge
open StageNineFormNativeGaugeAuxiliaryVariation StageNineDiracDualFormNativeCoframeLocalVariation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous

noncomputable section

/-- The complete primitive first-jet field of the original runtime at the origin. -/
def origin : StageNineContinuumPointField := toContinuumPointField Runtime.configuration 0

theorem source_couplings :
    ((sourceGeneratedUnifiedCouplings Runtime.source).strongCouplingSquared : ℝ) = 1 / 2 ∧
    ((sourceGeneratedUnifiedCouplings Runtime.source).weakCouplingSquared : ℝ) = 1 / 2 ∧
    ((sourceGeneratedUnifiedCouplings Runtime.source).hyperchargeCouplingSquared : ℝ) = 1 / 2 := by
  rw [Runtime.source_eq]
  change sourceCoupling = 1 / 2 ∧ sourceCoupling = 1 / 2 ∧ sourceCoupling = 1 / 2
  exact ⟨sourceCoupling_eq, sourceCoupling_eq, sourceCoupling_eq⟩

theorem connection_origin : Runtime.configuration.gaugeConnection 0 = gaugePotential gaugeScale := by
  rw [Runtime.configuration_eq, actual_gaugeConnection]

theorem origin_coframe : origin.coframe = homogeneousCoframe lapse := by
  change Runtime.configuration.coframe 0 = _
  rw [Runtime.configuration_eq, actual_coframe]

theorem origin_gaugeCurvature : origin.gaugeCurvature = magneticCurvature gaugeScale := by
  change holonomicGaugeCurvature Runtime.configuration 0 = _
  rw [Runtime.configuration_eq, actual_gaugeCurvature]

theorem origin_gaugeAuxiliary : origin.gaugeAuxiliary = electricAuxiliary lapse gaugeScale := by
  change Runtime.configuration.gaugeAuxiliary 0 = _
  rw [Runtime.configuration_eq, actual_gaugeAuxiliary]

theorem gauge_scale_square : gaugeScale ^ 2 = (18 / 25 : ℝ) := by
  rw [gaugeScale, div_pow, mul_pow, spinScale_sq]
  norm_num

theorem auxiliary_coefficient :
    gaugeScale ^ 2 / (sourceCoupling * lapse) = 36 / (25 * lapse) := by
  rw [gauge_scale_square, sourceCoupling_eq]
  ring

theorem origin_curvature_component :
    origin.gaugeCurvature 3 = -(18 / 25 : ℝ) • sourceColorP286Generator 0 := by
  rw [origin_gaugeCurvature]
  change -(gaugeScale ^ 2) • sourceColorP286Generator 0 = _
  rw [gauge_scale_square]

theorem origin_auxiliary_component :
    origin.gaugeAuxiliary 0 = (36 / (25 * lapse) : ℝ) • sourceColorP286Generator 0 := by
  rw [origin_gaugeAuxiliary]
  simp only [electricAuxiliary, Matrix.cons_val_zero, auxiliary_coefficient]

theorem origin_curvature_pairing :
    p286LiePairing (sourceColorP286Generator 0) (origin.gaugeCurvature 3) = -9 / 25 := by
  rw [origin_curvature_component, p286LiePairing_smul_right,
    sourceColorP286Generator_pairing_self]
  norm_num

theorem origin_auxiliary_pairing :
    p286LiePairing (sourceColorP286Generator 0) (origin.gaugeAuxiliary 0) = 18 / (25 * lapse) := by
  rw [origin_auxiliary_component, p286LiePairing_smul_right,
    sourceColorP286Generator_pairing_self]
  ring

def auxiliaryRead : (Fin 6 → P286LieBlockData) →ₗ[ℝ] ℝ where
  toFun form := p286LiePairing (sourceColorP286Generator 0) (form 0)
  map_add' := by intros; exact p286LiePairing_add_right _ _ _
  map_smul' := by intros; exact p286LiePairing_smul_right _ _ _

theorem origin_auxiliary_read : auxiliaryRead origin.gaugeAuxiliary = 18 / (25 * lapse) :=
  origin_auxiliary_pairing

theorem origin_auxiliary_read_pos : 0 < auxiliaryRead origin.gaugeAuxiliary := by
  rw [origin_auxiliary_read]
  exact div_pos (by norm_num) (mul_pos (by norm_num) lapse_pos)

theorem origin_curvature_nonzero : origin.gaugeCurvature ≠ 0 := by
  change holonomicGaugeCurvature Runtime.configuration 0 ≠ 0
  rw [Runtime.configuration_eq]
  exact actual_gaugeCurvature_nonzero 0

theorem origin_auxiliary_nonzero : origin.gaugeAuxiliary ≠ 0 := by
  intro zero
  have entry := congrFun zero 0
  rw [origin_auxiliary_component] at entry
  have coefficient : (36 / (25 * lapse) : ℝ) ≠ 0 :=
    ne_of_gt (div_pos (by norm_num) (mul_pos (by norm_num) lapse_pos))
  exact sourceColorP286Generator_nonzero 0 ((smul_eq_zero.mp entry).resolve_left coefficient)

theorem origin_lapse : origin.coframe 0 0 = Real.sqrt (54 / 125) := by
  rw [origin_coframe]
  rfl

theorem origin_coframe_det : Matrix.det origin.coframe = lapse := by
  rw [origin_coframe, homogeneousCoframe_det]

theorem origin_nondegenerate : Matrix.det origin.coframe ≠ 0 := by
  rw [origin_coframe_det]
  exact ne_of_gt lapse_pos

theorem time_column_shift (u : ℝ) :
    origin.coframe + u • Matrix.single 0 0 1 = homogeneousCoframe (lapse + u) := by
  rw [origin_coframe]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [homogeneousCoframe]

theorem homogeneous_magnetic_trace (clock : ℝ) (nonzero : clock ≠ 0) :
    magneticHodgeTrace (homogeneousCoframe clock) = -3 * clock := by
  simp [magneticHodgeTrace, gaugeOperatorCoefficient, homogeneousHodge clock nonzero]
  ring

theorem origin_auxiliary_quadratic (coframe : LorentzianCoframe) :
    formNativeP286GaugeWedgeCoefficient origin.gaugeAuxiliary
      (formNativeP286BlockwiseConstitutive coframe sourceCoupling sourceCoupling sourceCoupling
        origin.gaugeAuxiliary) =
      sourceCoupling * (gaugeScale ^ 2 / (sourceCoupling * lapse)) ^ 2 / 2 *
        magneticHodgeTrace coframe := by
  have density := actual_gaugeDensity_coframe (0 : BasePoint) coframe
  unfold diracDualFormNativeCoframeGaugeDensity at density
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286] at density
  change formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary 0)
      (holonomicGaugeCurvature actual 0) - (1/2 : ℝ) *
      formNativeP286GaugeWedgeCoefficient (actual.gaugeAuxiliary 0)
        (formNativeP286BlockwiseConstitutive coframe sourceCoupling sourceCoupling sourceCoupling
          (actual.gaugeAuxiliary 0)) = _ at density
  change formNativeP286GaugeWedgeCoefficient (Runtime.configuration.gaugeAuxiliary 0)
      (formNativeP286BlockwiseConstitutive coframe sourceCoupling sourceCoupling sourceCoupling
        (Runtime.configuration.gaugeAuxiliary 0)) = _
  rw [Runtime.configuration_eq]
  nlinarith only [density]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFMaterial
