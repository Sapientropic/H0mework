import H0mework.Physics.LowEnergy.FullQuantum.ScalarGreen.Grading
import H0mework.Physics.LowEnergy.FullQuantum.PerturbedGreen.Inverse

/-! The complete spatial scalar inverse terminates exactly after one insertion at every amplitude. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
open FullSpace SpatialGreen ProofFreeRicherAnholonomicSource
noncomputable section

theorem green_potential_square_zero (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) :
    (green point energy damping positive*potential profile)*(green point energy damping positive*potential profile)=0 := by
  apply ContinuousLinearMap.ext
  intro field
  change green point energy damping positive
    (potential profile (green point energy damping positive (potential profile field)))=0
  rw [two_scalar_insertions_zero,map_zero]

def correctionUnit (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) : PerturbedGreen.SpatialOperatorsˣ := by
  let X := parameter • (green point energy damping positive*potential profile)
  have square : X*X=0 := by
    dsimp only [X]
    rw [smul_mul_smul,green_potential_square_zero,smul_zero]
  refine ⟨1+X,1-X,?_,?_⟩
  · calc
      (1+X)*(1-X)=1-X*X := by noncomm_ring
      _ = 1 := by rw [square,sub_zero]
  · calc
      (1-X)*(1+X)=1-X*X := by noncomm_ring
      _ = 1 := by rw [square,sub_zero]

theorem correction_isUnit (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) :
    IsUnit (PerturbedGreen.correction (green point energy damping positive) (potential profile) parameter) :=
  (correctionUnit point energy damping positive profile parameter).isUnit

def response (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) : PerturbedGreen.SpatialOperators :=
  green point energy damping positive-
    parameter • (green point energy damping positive*potential profile*green point energy damping positive)

theorem response_is_actual_inverse (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) :
    PerturbedGreen.response (green point energy damping positive) (potential profile) parameter=
      response point energy damping positive profile parameter := by
  have inverse : Ring.inverse (PerturbedGreen.correction (green point energy damping positive) (potential profile) parameter)=
      1-parameter • (green point energy damping positive*potential profile) :=
    Ring.inverse_unit (correctionUnit point energy damping positive profile parameter)
  rw [PerturbedGreen.response,inverse,sub_mul,one_mul,smul_mul_assoc]
  rfl

theorem response_solves (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) (source : FullMatterL2) :
    PerturbedGreen.Equation point energy damping (potential profile) parameter
      (response point energy damping positive profile parameter source) source := by
  apply (PerturbedGreen.equation_iff_correction point energy damping positive (potential profile) parameter _ source).mpr
  rw [← response_is_actual_inverse point energy damping positive profile parameter]
  have inverse := Ring.mul_inverse_cancel _ (correction_isUnit point energy damping positive profile parameter)
  exact congrArg (fun A : PerturbedGreen.SpatialOperators => A (green point energy damping positive source)) inverse

theorem response_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) (field source : FullMatterL2)
    (solves : PerturbedGreen.Equation point energy damping (potential profile) parameter field source) :
    field=response point energy damping positive profile parameter source := by
  have generated := (PerturbedGreen.equation_iff_correction point energy damping positive (potential profile) parameter field source).mp solves
  have inverse := Ring.inverse_mul_cancel _ (correction_isUnit point energy damping positive profile parameter)
  have read := congrArg (fun v : FullMatterL2 =>
    (Ring.inverse (PerturbedGreen.correction (green point energy damping positive) (potential profile) parameter) : PerturbedGreen.SpatialOperators) v) generated
  have left := congrArg (fun A : PerturbedGreen.SpatialOperators => A field) inverse
  have original := left.symm.trans read
  rw [← response_is_actual_inverse point energy damping positive profile parameter]
  exact original

theorem response_domain (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) (source : FullMatterL2) :
    MemLp (sourceField point energy damping (response point energy damping positive profile parameter source)) 2 volume :=
  (Lp.memLp (FullSpace.fourier (source-parameter • potential profile
    (response point energy damping positive profile parameter source)))).ae_eq
      (response_solves point energy damping positive profile parameter source).symm

def domainResponse (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) (source : FullMatterL2) : Domain point energy damping :=
  ⟨response point energy damping positive profile parameter source,
    response_domain point energy damping positive profile parameter source⟩

def variedDirac (point : BasePoint) (energy damping : ℝ) (profile : ScalarProfile) (parameter : ℂ)
    (field : Domain point energy damping) : FullMatterL2 :=
  dirac point energy damping field+parameter • potential profile field.val

theorem variedDirac_response (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) (source : FullMatterL2) :
    variedDirac point energy damping profile parameter
      (domainResponse point energy damping positive profile parameter source)=source := by
  have original : dirac point energy damping (domainResponse point energy damping positive profile parameter source)=
      source-parameter • potential profile (response point energy damping positive profile parameter source) := by
    apply FullSpace.fourier.injective
    apply Lp.ext
    exact (dirac_fourier_ae point energy damping
      (domainResponse point energy damping positive profile parameter source)).trans
        (response_solves point energy damping positive profile parameter source)
  change dirac point energy damping (domainResponse point energy damping positive profile parameter source)+
    parameter • potential profile (response point energy damping positive profile parameter source)=source
  rw [original,sub_add_cancel]

theorem response_variedDirac (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : ScalarProfile) (parameter : ℂ) (field : Domain point energy damping) :
    response point energy damping positive profile parameter
      (variedDirac point energy damping profile parameter field)=field.val := by
  have solves : PerturbedGreen.Equation point energy damping (potential profile) parameter field.val
      (variedDirac point energy damping profile parameter field) := by
    unfold PerturbedGreen.Equation variedDirac
    rw [add_sub_cancel_right]
    exact (dirac_fourier_ae point energy damping field).symm
  exact (response_unique point energy damping positive profile parameter field.val _ solves).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
