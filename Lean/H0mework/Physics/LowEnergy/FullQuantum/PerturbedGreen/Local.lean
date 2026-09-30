import H0mework.Physics.LowEnergy.FullQuantum.PerturbedGreen.Native
import Mathlib.MeasureTheory.Function.Holder

/-! Actual bounded field profiles generate full 252-component local perturbations. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PerturbedGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaSpinJurisdiction StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal DiracExteriorMatterAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
noncomputable section

abbrev BoundedProfile := Lp (α := Position) ℂ ⊤ volume

def profileMultiplier (profile : BoundedProfile) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] Hilbert →L[ℂ] Hilbert).holderL volume ⊤ 2 2 profile

theorem profileMultiplier_ae (profile : BoundedProfile) (field : FullMatterL2) :
    profileMultiplier profile field=ᵐ[volume] fun x => profile x • field x :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] Hilbert →L[ℂ] Hilbert).coeFn_holder profile field

def localOperator (profile : BoundedProfile) (A : Mother) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (profileMultiplier profile).comp ((operator A).compLpL 2 volume)

theorem localOperator_ae (profile : BoundedProfile) (A : Mother) (field : FullMatterL2) :
    localOperator profile A field=ᵐ[volume] fun x => profile x • operator A (field x) := by
  filter_upwards [profileMultiplier_ae profile ((operator A).compLpL 2 volume field),
    (operator A).coeFn_compLpL field] with x multiplied applied
  change profileMultiplier profile ((operator A).compLpL 2 volume field) x=_
  rw [multiplied,applied]

def localPotential (profile : BoundedProfile) (gauge : P286GaugeOneForm) (scalar : ScalarCoordinateCarrier) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  localOperator profile (insertion actual (fun _ => gauge) (fun _ => scalar) 0)

def spatialPart (point : BasePoint) : Position := WithLp.toLp 2 (fun j => point j.succ)

def spatialPoint (x : Position) : BasePoint := WithLp.toLp 2 (Fin.cases 0 (fun j => x j))

theorem spatialPart_point (x : Position) : spatialPart (spatialPoint x)=x := by
  ext j
  rfl

def localGauge (profile : BoundedProfile) (gauge : P286GaugeOneForm) : BasePoint → P286GaugeOneForm :=
  fun point => (profile (spatialPart point)).re • gauge

def localScalar (profile : BoundedProfile) (scalar : ScalarCoordinateCarrier) : BasePoint → ScalarCoordinateCarrier :=
  fun point => ((profile (spatialPart point)).re : ℂ) • scalar

theorem source_insertion_local (profile : BoundedProfile) (gauge : P286GaugeOneForm)
    (scalar : ScalarCoordinateCarrier) (x : Position) :
    insertion actual (localGauge profile gauge) (localScalar profile scalar) (spatialPoint x)=
      ((profile x).re : ℂ) • insertion actual (fun _ => gauge) (fun _ => scalar) 0 := by
  apply LinearMap.ext
  intro v
  simp only [insertion,YangMills.Response.Forcing.spatialInsertion,actual_coframe,
    p286GaugeConnectionMotherVariation,localGauge,localScalar,spatialPart_point,
    Pi.smul_apply,map_smul,p286LieBlockEmbed_real_smul,diracExteriorMotherLieAction_real_smul,
    diracDualRightChiralYukawaAction_smul,LinearMap.smul_apply,LinearMap.add_apply,
    LinearMap.comp_apply,LinearMap.sum_apply,map_smul,smul_add,Finset.smul_sum,smul_smul]
  rw [mul_comm Complex.I ((profile x).re : ℂ)]

private theorem real_value (z : ℂ) (real : star z=z) : (z.re : ℂ)=z := by
  have imaginary : z.im=0 := by
    have same := congrArg Complex.im real
    simp only [Complex.star_def,Complex.conj_im] at same
    linarith
  exact Complex.ext rfl (by simpa using imaginary.symm)

theorem localPotential_native_ae (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x)
    (gauge : P286GaugeOneForm) (scalar : ScalarCoordinateCarrier) (field : FullMatterL2) :
    localPotential profile gauge scalar field=ᵐ[volume] fun x =>
      operator (insertion actual (localGauge profile gauge) (localScalar profile scalar) (spatialPoint x)) (field x) := by
  filter_upwards [localOperator_ae profile (insertion actual (fun _ => gauge) (fun _ => scalar) 0) field,real]
    with x read native
  change localOperator profile (insertion actual (fun _ => gauge) (fun _ => scalar) 0) field x=_
  rw [read,source_insertion_local,Triangular.operator_smul,real_value _ native]
  rfl

theorem actual_kernel_constant (point : BasePoint) (momentum : Fin 3 → ℝ) (z : ℂ) :
    Triangular.diracKernel actual point momentum z=Triangular.diracKernel actual 0 momentum z := by
  simp only [Triangular.diracKernel,lowerSymbol,knownSymbol,connection,actual_coframe,
    actual_gravityConnection,actual_gaugeConnection,actual_scalar]

theorem native_kernel_ae (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x)
    (gauge : P286GaugeOneForm) (scalar : ScalarCoordinateCarrier) (epsilon : ℝ)
    (momentum : Fin 3 → ℝ) (z : ℂ) (field : FullMatterL2) :
    (fun x => operator (Triangular.diracKernel (varied actual (localGauge profile gauge)
      (localScalar profile scalar) epsilon) (spatialPoint x) momentum z) (field x))=ᵐ[volume]
      fun x => operator (Triangular.diracKernel actual 0 momentum z) (field x)+
        (epsilon : ℂ) • localPotential profile gauge scalar field x := by
  filter_upwards [localPotential_native_ae profile real gauge scalar field] with x native
  rw [varied_diracKernel,Triangular.operator_add,Triangular.operator_smul,actual_kernel_constant,native]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PerturbedGreen
