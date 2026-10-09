import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedPacketFieldReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedSpatialResponse
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumChargedPacketGreen PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumFullSlowFieldResponse PreparationVacuumObservedPoleTensor
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumNativeSlowCoupling PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumWholeOrigin PreparationVacuumStaticSpatialSource
open CanonicalGradedSpatialSource Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

/-- All three spatial coefficients of the original causal principal, before any detector restriction. -/
def sourceChargedSpatialCoefficient (i : Fin 3) : ℝ :=
  Real.sqrt 2*Real.sqrt 15*(if i=0 then (25/54:ℝ) else if i=1 then 12/335 else 8/15)

def sourceChargedTemporalCoefficient (i : Fin 3) : ℝ :=
  Real.sqrt 2*Real.sqrt 15*(if i=0 then -(25/18:ℝ) else if i=1 then 10/99 else 20/27)

def sourceChargedDenominator (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3) : ℂ :=
  (sourceChargedSpatialCoefficient i:ℂ)*(spatialSquare n:ℂ)+
    (sourceChargedTemporalCoefficient i:ℂ)*zeta^2

theorem sourceChargedSpatialCoefficient_positive (i : Fin 3) : 0<sourceChargedSpatialCoefficient i := by
  fin_cases i <;> norm_num [sourceChargedSpatialCoefficient]

theorem sourceChargedTemporalCoefficient_nonzero (i : Fin 3) : sourceChargedTemporalCoefficient i≠0 := by
  have two : Real.sqrt 2≠0:=by positivity
  have fifteen : Real.sqrt 15≠0:=by positivity
  fin_cases i <;> norm_num [sourceChargedTemporalCoefficient,mul_ne_zero two fifteen,two,fifteen]

private theorem denominator_zero (n : PhysicalMomentum) (zeta : ℂ) :
    sourceChargedDenominator n zeta 0=rootTwo*rootFifteen*(-(25/18:ℂ)*zeta^2+(25/54:ℂ)*(spatialSquare n:ℂ)) := by
  norm_num [sourceChargedDenominator,sourceChargedSpatialCoefficient,sourceChargedTemporalCoefficient,rootTwo,rootFifteen,Fin.ext_iff]
  ring

private theorem denominator_one (n : PhysicalMomentum) (zeta : ℂ) :
    sourceChargedDenominator n zeta 1=rootTwo*rootFifteen*((10/99:ℂ)*zeta^2+(12/335:ℂ)*(spatialSquare n:ℂ)) := by
  norm_num [sourceChargedDenominator,sourceChargedSpatialCoefficient,sourceChargedTemporalCoefficient,rootTwo,rootFifteen,Fin.ext_iff]
  ring

private theorem denominator_two (n : PhysicalMomentum) (zeta : ℂ) :
    sourceChargedDenominator n zeta 2=rootTwo*rootFifteen*((20/27:ℂ)*zeta^2+(8/15:ℂ)*(spatialSquare n:ℂ)) := by
  norm_num [sourceChargedDenominator,sourceChargedSpatialCoefficient,sourceChargedTemporalCoefficient,rootTwo,rootFifteen,Fin.ext_iff]
  ring

private theorem principal_shape (n : PhysicalMomentum) (zeta : ℂ) :
    sourceCausalPrincipal n zeta=
      Matrix.diagonal ![sourceChargedDenominator n zeta 0,sourceChargedDenominator n zeta 1,
        sourceChargedDenominator n zeta 2,0,0]+
      Matrix.single 2 3 (-(40/9:ℂ)*Complex.I*zeta*(n 2:ℂ)-(20/27:ℂ)*rootTwo*rootFifteen*zeta^2)+
      Matrix.single 3 4 (-8*rootTwo*zeta)+Matrix.single 4 3 (8*rootTwo*zeta) := by
  rw [denominator_zero,denominator_one,denominator_two]
  rfl

private theorem charged_det (n : PhysicalMomentum) (zeta : ℂ) :
    (sourceCausalPrincipal n zeta).det=128*zeta^2*
      sourceChargedDenominator n zeta 0*sourceChargedDenominator n zeta 1*sourceChargedDenominator n zeta 2 := by
  rw [denominator_zero,denominator_one,denominator_two]
  exact sourceCausalPrincipal_det n zeta

private theorem denominator_ne (n : PhysicalMomentum) (zeta : sourceCausalDomain n) (i : Fin 3) :
    sourceChargedDenominator n zeta.val i≠0 := by
  have h:=zeta.property.2
  rw [charged_det] at h
  have a:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1).2
  have b:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2
  have c:=(mul_ne_zero_iff.mp h).2
  fin_cases i
  · exact a
  · exact b
  · exact c

/-- The last two input coordinates vanish by the original slow reader; no input condition is supplied. -/
def sourceChargedThreeSolution (n : PhysicalMomentum) (zeta : ℂ) (f : Fin 289→ℂ) : Fin 5→ℂ :=
  fun i=>if i=0 then (sourceChargedDenominator n zeta 0)⁻¹*sourceSlowRead f 0
    else if i=1 then (sourceChargedDenominator n zeta 1)⁻¹*sourceSlowRead f 1
    else if i=2 then (sourceChargedDenominator n zeta 2)⁻¹*sourceSlowRead f 2 else 0

theorem sourceChargedCornerInverse_generated (n : PhysicalMomentum) (zeta : sourceCausalDomain n) (f : Fin 289→ℂ) :
    (sourceCausalPrincipal n zeta.val)⁻¹*ᵥsourceSlowRead f=sourceChargedThreeSolution n zeta.val f := by
  have cancel (i : Fin 3) (x : ℂ) : sourceChargedDenominator n zeta.val i*((sourceChargedDenominator n zeta.val i)⁻¹*x)=x := by
    rw [←mul_assoc,mul_inv_cancel₀ (denominator_ne n zeta i),one_mul]
  have equation : sourceCausalPrincipal n zeta.val*ᵥsourceChargedThreeSolution n zeta.val f=sourceSlowRead f := by
    rw [principal_shape]
    ext i
    fin_cases i <;>
      norm_num [sourceChargedThreeSolution,Matrix.add_mulVec,Matrix.mulVec_diagonal,Matrix.single_mulVec,
        Function.update_apply,Fin.ext_iff,cancel,sourceSlowRead]
    rfl
  rw [←equation,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr zeta.property.2),Matrix.one_mulVec]

theorem sourceChargedFrameInput_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) :
    sourceChargedFrameInput q n zeta.val l r=
      fiveVector (sourceChargedThreeSolution n zeta.val (sourceActualNativeResidue q n zeta.val l r)) := by
  rw [sourceChargedFrameInput,sourceChargedCornerInverse_generated]

private theorem denominator_imaginary (n : PhysicalMomentum) (c eta : ℝ) (i : Fin 3) :
    (sourceChargedDenominator n (sourcePoleSide c eta) i).im=
      2*sourceChargedTemporalCoefficient i*eta*c := by
  simp [sourceChargedDenominator,sourcePoleSide,pow_two,Complex.mul_im,Complex.mul_re]
  ring

theorem sourceChargedDenominator_nonzero (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (i : Fin 3) :
    sourceChargedDenominator n (sourcePoleSide c eta) i≠0 :=
  denominator_ne n ⟨sourcePoleSide c eta,sourcePoleSide_field_domain n c eta frequency positive⟩ i

/-- Fixed positive damping supplies the original imaginary denominator price on every spatial momentum. -/
def sourceChargedDenominatorPrice (c eta : ℝ) (i : Fin 3) : ℝ :=
  |2*sourceChargedTemporalCoefficient i*eta*c|⁻¹

theorem sourceChargedDenominator_bound (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (i : Fin 3) :
    ‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖≤ sourceChargedDenominatorPrice c eta i := by
  have nonzero : 2*sourceChargedTemporalCoefficient i*eta*c≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (sourceChargedTemporalCoefficient_nonzero i)) positive.ne') frequency
  rw [sourceChargedDenominatorPrice,norm_inv]
  apply inv_anti₀ (abs_pos.mpr nonzero)
  rw [←denominator_imaginary n c eta i]
  exact Complex.abs_im_le_norm _

private theorem momentum_square_nonnegative (n : PhysicalMomentum) : 0 ≤ spatialSquare n := by
  unfold spatialSquare
  positivity

private theorem spatial_square_price (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3)
    (nonzero : sourceChargedDenominator n zeta i≠0) :
    spatialSquare n*‖(sourceChargedDenominator n zeta i)⁻¹‖≤
      (sourceChargedSpatialCoefficient i)⁻¹*(1+‖(sourceChargedTemporalCoefficient i:ℂ)*zeta^2‖*
        ‖(sourceChargedDenominator n zeta i)⁻¹‖) := by
  have coefficient:=sourceChargedSpatialCoefficient_positive i
  have numerator : sourceChargedSpatialCoefficient i*spatialSquare n≤
      ‖sourceChargedDenominator n zeta i‖+‖(sourceChargedTemporalCoefficient i:ℂ)*zeta^2‖ := by
    have h:=norm_sub_le (sourceChargedDenominator n zeta i) ((sourceChargedTemporalCoefficient i:ℂ)*zeta^2)
    rw [sourceChargedDenominator,add_sub_cancel_right,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg coefficient.le,Real.norm_of_nonneg (momentum_square_nonnegative n)] at h
    exact h
  have scaled:=mul_le_mul_of_nonneg_right numerator (norm_nonneg ((sourceChargedDenominator n zeta i)⁻¹))
  rw [add_mul,norm_inv,mul_inv_cancel₀ (norm_ne_zero_iff.mpr nonzero)] at scaled
  have divided:=mul_le_mul_of_nonneg_left scaled (inv_nonneg.mpr coefficient.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ coefficient.ne',one_mul,norm_inv] using divided

def sourceChargedQuadraticPrice (c eta : ℝ) (i : Fin 3) : ℝ :=
  2*‖sourcePoleSide c eta‖^2*sourceChargedDenominatorPrice c eta i+
    2*(sourceChargedSpatialCoefficient i)⁻¹*
      (1+‖(sourceChargedTemporalCoefficient i:ℂ)*(sourcePoleSide c eta)^2‖*sourceChargedDenominatorPrice c eta i)

/-- The actual quadratic denominators control the two original linear factors: frame jet and native forcing. -/
theorem sourceChargedQuadratic_bound (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (i : Fin 3) :
    (‖sourcePoleSide c eta‖+‖n‖)^2*‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖≤
      sourceChargedQuadraticPrice c eta i := by
  have nonzero:=denominator_ne n ⟨sourcePoleSide c eta,sourcePoleSide_field_domain n c eta frequency positive⟩ i
  have inverse:=sourceChargedDenominator_bound n c eta frequency positive i
  have square:=spatial_square_price n (sourcePoleSide c eta) i nonzero
  have coefficient:=sourceChargedSpatialCoefficient_positive i
  have nsquare : ‖n‖^2≤ spatialSquare n := by
    simpa [spatialSquare,Fin.sum_univ_three] using SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.GlobalSource.pi_norm_sq_le_sum_sq n
  have quadratic : (‖sourcePoleSide c eta‖+‖n‖)^2≤2*‖sourcePoleSide c eta‖^2+2*spatialSquare n := by
    nlinarith [sq_nonneg (‖sourcePoleSide c eta‖-‖n‖)]
  calc
    _≤(2*‖sourcePoleSide c eta‖^2+2*spatialSquare n)*‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖ :=
      mul_le_mul_of_nonneg_right quadratic (norm_nonneg _)
    _=2*‖sourcePoleSide c eta‖^2*‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖+
      2*(spatialSquare n*‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖) := by ring
    _≤2*‖sourcePoleSide c eta‖^2*sourceChargedDenominatorPrice c eta i+
      2*((sourceChargedSpatialCoefficient i)⁻¹*(1+‖(sourceChargedTemporalCoefficient i:ℂ)*(sourcePoleSide c eta)^2‖*
        ‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖)) := by gcongr
    _≤ sourceChargedQuadraticPrice c eta i := by
      unfold sourceChargedQuadraticPrice
      simp only [mul_assoc]
      gcongr

end LowEnergy.PreparationVacuumChargedSpatialResponse
