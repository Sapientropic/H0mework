import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalMatter
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassReciprocal

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteLowerOperator
open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineHolonomicField StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionVariation
open StageNineLorentzConnectionVariation StageNineCoframeLocalDifferentiability
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeCanonicalFluidCoframe (density density_pos)
open NativePauliCoframeAction (compensation normalizedVelocity normalizedDerivative)
open NativeMaterialJetAction (normalizedJet geometry)
open NativePauliMotherAction (spinActionMatrix gaugePotential)
noncomputable section

def bareColor (coefficients : Fin 4 → Fin 3 → ℝ) : Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 4,(diracMatrixMatterAction (spinActionMatrix direction)).comp
    (diracExteriorMotherLieAction (p286LieBlockEmbed (gaugePotential coefficients direction)))

def color (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) : Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 4,(diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.matrix velocity direction)).comp
    (NativeSourceColorAction.operator velocity coefficients direction)

def spin (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 4,(diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.matrix velocity direction)).comp
    (diracMatrixMatterAction (diracSpinConnectionLift (geometry velocity jet).lorentzSpinConnection direction))

def cartan (velocity : PhysicalSpace) : Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 4,(diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.matrix velocity direction)).comp
    (NativeCartanCompensation.cartanOperator velocity direction)

def cartanControl (velocity : PhysicalSpace) : Fin 4 → Fin 3 → ℝ :=
  NativePauliControl.control (normalizedVelocity velocity) (-NativeCartanMaterialResponse.response velocity)

def static (velocity : PhysicalSpace) : Module.End ℂ DiracExteriorMatterCarrier :=
  cartan velocity+color velocity (cartanControl velocity)+color velocity (NativeConstitutiveColor.coefficients velocity)

theorem matrix_compensation (velocity : PhysicalSpace) (direction : Fin 4) :
    (compensation velocity direction : ℂ) • NativeCanonicalFriedrichsPrincipal.matrix velocity direction=
      (((density velocity)⁻¹ : ℝ) : ℂ) • spinActionMatrix direction := by
  cases direction using Fin.cases with
  | zero =>
    ext row column
    simp [compensation,NativeCanonicalFriedrichsPrincipal.mass,spinActionMatrix,Complex.real_smul]
  | succ j =>
    rw [NativeCanonicalFriedrichsPrincipal.spatial,NativeCanonicalFriedrichsAction.frame_spin]
    simp [compensation,Fin.succ_ne_zero]

theorem color_factor (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) :
    color velocity coefficients=(((density velocity)⁻¹ : ℝ) : ℂ) • bareColor coefficients := by
  apply LinearMap.ext
  intro matter
  simp only [color,bareColor,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    NativeSourceColorAction.operator,NativeSourceColorAction.connection,p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul,map_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  have actual:=congrArg (fun A : DiracMatrix => diracMatrixMatterAction A
      (diracExteriorMotherLieAction (p286LieBlockEmbed (gaugePotential coefficients direction)) matter))
    (matrix_compensation velocity direction)
  simpa only [diracMatrixMatterAction_smul_matrix,RCLike.real_smul_eq_coe_smul,LinearMap.smul_apply] using actual

theorem lower_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    NativeWindowAbsoluteTimePhysicalMatter.lower velocity jet=
      spin velocity jet+color velocity (NativeBalancedMaterialJet.freeCoefficients velocity jet)+static velocity := by
  apply LinearMap.ext
  intro matter
  simp only [NativeWindowAbsoluteTimePhysicalMatter.lower,spin,color,static,cartan,
    LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.add_apply,NativeCanonicalGreenAdjoint.connection_split,
    NativeCanonicalGreenAdjoint.internal,NativeBalancedMaterialJet.gaugeConnection,
    p286LieBlockEmbed_add,diracExteriorMotherLieAction_add,map_add,Finset.sum_add_distrib,
    NativeMaterialAdjointPrincipal.spinOperator,NativeCartanCompensation.cartanOperator,
    NativeSourceColorAction.operator,NativeSourceColorAction.connection,
    NativeCartanCompensation.correction,NativePauliCoframeAction.connection,cartanControl]
  abel

theorem matrix_inverse_normalized (velocity : PhysicalSpace) (direction : Fin 4) :
    NativeCanonicalFriedrichsPrincipal.matrix velocity direction=
      (((density velocity)⁻¹ : ℝ) : ℂ) •
        (((compensation velocity direction)⁻¹ : ℝ) : ℂ) • spinActionMatrix direction := by
  have actual:=congrArg (fun A : DiracMatrix => (((density velocity)⁻¹ : ℝ) : ℂ) • A)
    (NativeCanonicalFriedrichsAction.normalized_spin velocity direction)
  simpa only [NativeCanonicalFriedrichsPrincipal.normalized,smul_smul,← Complex.ofReal_mul,
    Complex.ofReal_inv,inv_mul_cancel₀ (show (density velocity : ℂ)≠0 by exact_mod_cast (density_pos velocity).ne'),one_smul] using actual

theorem spin_scalar (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    spin velocity jet=(((density velocity)⁻¹*(-(3/2:ℝ)*
      NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet jet) 0) : ℝ) : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro matter
  have actual:=NativeCoframeSpin.spin_response velocity
    (NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet jet)) matter
  simp only [normalizedDerivative,← Complex.ofReal_inv] at actual
  simp only [spin,LinearMap.sum_apply,LinearMap.comp_apply,matrix_inverse_normalized,
    diracMatrixMatterAction_smul_matrix,LinearMap.smul_apply,← Finset.smul_sum]
  rw [show (∑ direction : Fin 4,(((compensation velocity direction)⁻¹ : ℝ) : ℂ) •
    diracMatrixMatterAction (spinActionMatrix direction)
      (diracMatrixMatterAction (diracSpinConnectionLift (geometry velocity jet).lorentzSpinConnection direction) matter))=
      (-(3/2:ℝ)*NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet jet) 0 : ℂ) • matter from actual]
  simp only [LinearMap.id_apply,smul_smul,Complex.ofReal_mul,Complex.ofReal_neg]

theorem spin_coefficient (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    (density velocity)⁻¹*(-(3/2:ℝ)*NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet jet) 0)=
      (1/2:ℝ)*NativeWindowMassReciprocal.derivative velocity (jet 0) := by
  rw [NativePauliJet.logDerivative,← NativeMaterialJetAction.source_density,NativeWindowMassReciprocal.derivative_apply]
  simp only [NativeWindowMassReciprocal.value,normalizedJet,normalizedVelocity,PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]
  simp only [Fin.sum_univ_three]
  field_simp [(density_pos velocity).ne']

theorem spin_bound (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    |(density velocity)⁻¹*(-(3/2:ℝ)*NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet jet) 0)|≤‖jet 0‖/16 := by
  rw [spin_coefficient,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  exact (mul_le_mul_of_nonneg_left (NativeWindowMassReciprocal.derivative_bound velocity (jet 0))
    (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)

theorem lower_original (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    NativeWindowAbsoluteTimePhysicalMatter.lower velocity jet=
      (((1/2:ℝ)*NativeWindowMassReciprocal.derivative velocity (jet 0) : ℝ) : ℂ) • LinearMap.id+
        (((density velocity)⁻¹ : ℝ) : ℂ) • bareColor (NativeBalancedMaterialJet.freeCoefficients velocity jet)+static velocity := by
  rw [lower_split,spin_scalar,spin_coefficient,color_factor]

def freeCoefficients (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : Fin 4 → Fin 3 → ℝ :=
  fun direction color => (density velocity)⁻¹*NativeBalancedMaterialJet.freeCoefficients velocity jet direction color

theorem normalized_square (v : PhysicalSpace) : NativeCartanConstitutive.squared (normalizedVelocity v)=‖v‖^2/16 := by
  simp [NativeCartanConstitutive.squared,normalizedVelocity,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_three]
  ring

private theorem damped_square (v : NativePauliControl.Vector) (jet : Fin 4 → NativePauliControl.Vector) :
    (∑ direction : Fin 4,∑ color : Fin 3,
      ((NativePauliJet.density v)⁻¹*NativeBalancedJetCoefficients.coefficients v jet direction color)^2)≤
        6*∑ direction : Fin 4,NativeCartanConstitutive.squared (jet direction) := by
  let s:=NativeCartanConstitutive.squared v
  let r:=NativePauliJet.density v
  have s0:0 ≤ s:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  have r2:2 ≤ r:=by change 2≤2*(1+s); linarith
  have r0:0 < r:=NativePauliJet.density_pos v
  have inverse:r⁻¹≤1/2 := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) r2
  have square:r⁻¹^2≤1/4 := by
    have paid:=pow_le_pow_left₀ (inv_nonneg.mpr r0.le) inverse 2
    norm_num at paid ⊢
    exact paid
  have weighted:r⁻¹^2*s≤1/4 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos r0)).mp
    have same:r^2*(r⁻¹^2*s)=s:=by field_simp
    rw [same]
    change s≤(2*(1+s))^2*(1/4:ℝ)
    nlinarith [sq_nonneg s]
  have temporal:=NativeBalancedJetCoefficients.temporal_bound v jet
  have spatial:=NativeBalancedJetCoefficients.spatial_bound v jet
  have curl:=NativeCovariantMaterialEnergy.curl_energy_bound jet
  let a:=NativeCartanConstitutive.squared (jet 0)
  let b:=NativeCartanConstitutive.squared (NativeBalancedJetCoefficients.curl jet)
  let d:=∑ j : Fin 3,NativeCartanConstitutive.squared (jet j.succ)
  have a0:0≤a:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  have b0:0≤b:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  have d0:0≤d:=Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have complete:(∑ direction : Fin 4,∑ color : Fin 3,NativeBalancedJetCoefficients.coefficients v jet direction color^2)≤
      (3/2:ℝ)*a+4*b+5*s*b := by
    rw [Fin.sum_univ_succ]
    dsimp only [a,b,s]
    linarith only [temporal,spatial]
  have paid:=mul_le_mul_of_nonneg_left complete (sq_nonneg r⁻¹)
  have first:=mul_le_mul_of_nonneg_right square a0
  have last:=mul_le_mul_of_nonneg_right square b0
  have mixed:=mul_le_mul_of_nonneg_right weighted b0
  simp only [mul_pow,← Finset.mul_sum]
  change r⁻¹^2*(∑ direction : Fin 4,∑ color : Fin 3,NativeBalancedJetCoefficients.coefficients v jet direction color^2)≤_
  rw [Fin.sum_univ_succ (fun direction => NativeCartanConstitutive.squared (jet direction))]
  change _≤6*(a+d)
  change b≤2*d at curl
  nlinarith only [paid,first,last,mixed,curl,a0,d0]

theorem free_square (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    (∑ direction : Fin 4,∑ color : Fin 3,(freeCoefficients velocity jet direction color)^2)≤
      (3/8:ℝ)*∑ direction : Fin 4,‖jet direction‖^2 := by
  have paid:=damped_square (normalizedVelocity velocity) (normalizedJet jet)
  simp only [← NativeMaterialJetAction.source_density,normalizedJet,normalized_square,← Finset.sum_div] at paid
  simp only [freeCoefficients,NativeBalancedMaterialJet.freeCoefficients]
  convert paid using 1
  ring

def fixedColor (direction : Fin 4) (color : Fin 3) : Module.End ℂ DiracExteriorMatterCarrier :=
  (diracMatrixMatterAction (spinActionMatrix direction)).comp
    (diracExteriorMotherLieAction (p286LieBlockEmbed (NativePauliMotherAction.generator color)))

theorem bareColor_expansion (coefficients : Fin 4 → Fin 3 → ℝ) :
    bareColor coefficients=∑ direction : Fin 4,∑ color : Fin 3,(coefficients direction color : ℂ) • fixedColor direction color := by
  apply LinearMap.ext
  intro matter
  simp only [bareColor,fixedColor,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    gaugePotential,Fin.sum_univ_three,p286LieBlockEmbed_add,p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_add,diracExteriorMotherLieAction_real_smul,LinearMap.add_apply,map_add,map_smul]

def fixedCartan (direction : Fin 4) (pair : Fin 6) : Module.End ℂ DiracExteriorMatterCarrier :=
  (diracMatrixMatterAction (spinActionMatrix direction)).comp
    (diracMatrixMatterAction (diracGamma (lorentzBivectorFirst pair)*diracGamma (lorentzBivectorSecond pair)))

def cartanCoefficient (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6) : ℝ :=
  NativeCartanCoordinates.profile (NativeCartanCoordinates.currentVector velocity) direction pair/
    (8*NativeCanonicalFluidCoframe.scale velocity)

theorem matrix_diagonal (velocity : PhysicalSpace) (direction : Fin 4) :
    (NativeCanonicalFluidCoframe.diagonal velocity direction : ℂ) • NativeCanonicalFriedrichsPrincipal.matrix velocity direction=
      (((NativeCanonicalFluidCoframe.scale velocity)⁻¹ : ℝ) : ℂ) • spinActionMatrix direction := by
  have left:=congrArg (fun A : DiracMatrix =>
    ((compensation velocity direction)⁻¹*NativeCanonicalFluidCoframe.diagonal velocity direction : ℝ) • A)
      (matrix_compensation velocity direction)
  have nonzero:compensation velocity direction≠0 := by
    unfold compensation
    split_ifs <;> simp [(density_pos velocity).ne']
  have factor:(compensation velocity direction)⁻¹*NativeCanonicalFluidCoframe.diagonal velocity direction*(density velocity)⁻¹=
      (NativeCanonicalFluidCoframe.scale velocity)⁻¹ := by
    rw [NativeCartanConstitutive.inverse_compensation_diagonal,← NativeCanonicalFluidCoframe.scale_cube]
    field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']
  ext row column
  have entry:=congrFun (congrFun left row) column
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul] at entry ⊢
  have real:(compensation velocity direction)⁻¹*NativeCanonicalFluidCoframe.diagonal velocity direction*compensation velocity direction=
      NativeCanonicalFluidCoframe.diagonal velocity direction := by field_simp
  simpa only [← mul_assoc,← Complex.ofReal_mul,real,factor] using entry

theorem cartan_expansion (velocity : PhysicalSpace) :
    cartan velocity=∑ direction : Fin 4,∑ pair : Fin 6,(cartanCoefficient velocity direction pair : ℂ) • fixedCartan direction pair := by
  apply LinearMap.ext
  intro matter
  simp only [cartan,fixedCartan,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    NativeCartanCompensation.cartanOperator,diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,NativeCartanCoordinates.contorsion_eq,
    NativeCartanCoordinates.candidate_component]
  apply Finset.sum_congr rfl
  intro direction _
  simp only [Fin.sum_univ_six,coframeDiracMatrixMatterAction_add_matrix,
    coframeDiracMatrixMatterAction_smul_matrix,map_add,map_smul]
  have each (pair : Fin 6) : diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.matrix velocity direction)
      (((2:ℂ)⁻¹*((NativeCanonicalFluidCoframe.diagonal velocity direction*
        NativeCartanCoordinates.profile (NativeCartanCoordinates.currentVector velocity) direction pair/4 : ℝ) : ℂ)) •
        diracMatrixMatterAction (diracGamma (lorentzBivectorFirst pair)*diracGamma (lorentzBivectorSecond pair)) matter)=
      (cartanCoefficient velocity direction pair : ℂ) •
        diracMatrixMatterAction (spinActionMatrix direction)
          (diracMatrixMatterAction (diracGamma (lorentzBivectorFirst pair)*diracGamma (lorentzBivectorSecond pair)) matter) := by
    have actual:=congrArg (fun A : DiracMatrix => diracMatrixMatterAction A
      (diracMatrixMatterAction (diracGamma (lorentzBivectorFirst pair)*diracGamma (lorentzBivectorSecond pair)) matter))
      (matrix_diagonal velocity direction)
    simp only [diracMatrixMatterAction_smul_matrix] at actual
    have split : (2:ℂ)⁻¹*((NativeCanonicalFluidCoframe.diagonal velocity direction*
        NativeCartanCoordinates.profile (NativeCartanCoordinates.currentVector velocity) direction pair/4 : ℝ) : ℂ)=
      ((NativeCartanCoordinates.profile (NativeCartanCoordinates.currentVector velocity) direction pair/8 : ℝ) : ℂ)*
        (NativeCanonicalFluidCoframe.diagonal velocity direction : ℂ) := by push_cast; ring
    rw [map_smul,split,mul_smul,actual,smul_smul]
    congr 1
    simp only [cartanCoefficient,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_inv]
    ring
  simpa only [map_smul,Fin.sum_univ_six] using congrArg (fun values : Fin 6 → DiracExteriorMatterCarrier => ∑ pair,values pair)
    (funext each)

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteLowerOperator
