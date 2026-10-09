import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPrincipalHistory
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalZeroRead
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumRawJointFeedback
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open FullYSourceCutoffVolterra Filter Set MeasureTheory
open scoped BigOperators Topology InnerProductSpace
attribute [local irreducible] jointGenerator jointResolvent sourcePoleRead rawReader

private theorem prefix_continuous (C A : ZeroReadOp) (n : ℕ) : Continuous (finitePrefix C A n) :=by
  have U : Continuous (SourceFiniteUnitary.time C):=continuous_iff_continuousAt.mpr
    (fun t=>(hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)
  exact (orderedIntegral_continuous C A n).mul U

theorem sourcePrincipalEuler_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (n : Fin 113) (i : Fin 289) :
    Continuous (fun t=>sourcePrincipalEulerSector q pL pR left right n t i) :=by
  unfold sourcePrincipalEulerSector
  apply Continuous.neg
  apply (sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp
  unfold sourcePrincipalSector
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro k _
  by_cases same : j.val+k.val=n.val
  · simp only [if_pos same,sourcePrincipalBlock]
    exact (((((prefix_continuous _ _ _).comp continuous_neg).mul continuous_const).mul
      continuous_const).mul continuous_const).mul (prefix_continuous _ _ _)
  · simp only [if_neg same]
    exact continuous_const

private theorem moment_integrable (n : ℕ) (r : ℝ) (positive : 0<r) :
    IntegrableOn (fun t : ℝ=>t^n*Real.exp (-r*t)) (Ioi (0:ℝ)) :=by
  simpa only [Real.rpow_natCast,Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=(n:ℝ))
      (by have h : 0≤(n:ℝ):=Nat.cast_nonneg n;linarith) (by norm_num) positive

private theorem moment_integral (n : ℕ) (r : ℝ) (positive : 0<r) :
    (∫t : ℝ in Ioi 0,t^n*Real.exp (-r*t))=(n.factorial:ℝ)/r^(n+1) :=by
  have gamma:=Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=(n:ℝ)+1) (r:=r) (by positivity) positive
  simp only [add_sub_cancel_right,Real.rpow_natCast,Real.Gamma_nat_eq_factorial] at gamma
  rw [show ((n:ℝ)+1)=((n+1:ℕ):ℝ) by push_cast; rfl,Real.rpow_natCast] at gamma
  have same : (fun t : ℝ=>t^n*Real.exp (-r*t))=
      (fun t : ℝ=>t^n*Real.exp (-(r*t))):=by ext t; rw [neg_mul]
  rw [same,gamma]
  simp [div_eq_mul_inv,mul_comm]

def sourcePrincipalHalf (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (n : Fin 113) (i : Fin 289) : ℂ:=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t*sourcePrincipalEulerSector q pL pR left right n t i

theorem sourcePrincipalHalf_integrable (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0<lambda.re) (n : Fin 113) (i : Fin 289) :
    IntegrableOn (fun t=>laplaceWeight lambda t*sourcePrincipalEulerSector q pL pR left right n t i)
      (Ioi (0:ℝ)) :=by
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  apply ((moment_integrable n.val lambda.re off).const_mul
    (sourcePrincipalSectorPrice q pL pR (fieldUnit i) n)).mono'
    (weight.mul (sourcePrincipalEuler_continuous q pL pR left right n i)).aestronglyMeasurable.restrict
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  simp only [Pi.mul_apply]
  rw [norm_mul,laplace_norm]
  have actual:=mul_le_mul_of_nonneg_left
    (sourcePrincipalEuler_price q pL pR left right n t i) (Real.exp_pos (-lambda.re*t)).le
  rw [abs_of_pos ht] at actual
  exact actual.trans_eq (by ring)

theorem sourcePrincipalHalf_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0<lambda.re) (n : Fin 113) (i : Fin 289) :
    ‖sourcePrincipalHalf q pL pR left right lambda n i‖≤
      sourcePrincipalSectorPrice q pL pR (fieldUnit i) n*(n.val.factorial:ℝ)/lambda.re^(n.val+1) :=by
  unfold sourcePrincipalHalf
  have paid:=(moment_integrable n.val lambda.re off).const_mul
    (sourcePrincipalSectorPrice q pL pR (fieldUnit i) n)
  apply (norm_integral_le_of_norm_le paid ?_).trans_eq
    ((integral_const_mul _ _).trans (by rw [moment_integral n.val lambda.re off];ring))
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  rw [norm_mul,laplace_norm]
  have actual:=mul_le_mul_of_nonneg_left
    (sourcePrincipalEuler_price q pL pR left right n t i) (Real.exp_pos (-lambda.re*t)).le
  rw [abs_of_pos ht] at actual
  exact actual.trans_eq (by ring)

theorem sourcePrincipalHalf_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0<lambda.re) (i : Fin 289) :
    sourcePoleCurrentHalf q pL pR left right lambda i=
      ∑n : Fin 113,sourcePrincipalHalf q pL pR left right lambda n i :=by
  unfold sourcePoleCurrentHalf sourcePrincipalHalf
  simp_rw [sourcePrincipalEuler_generated,Finset.mul_sum]
  exact integral_finsetSum _ (fun n _=>sourcePrincipalHalf_integrable q pL pR left right lambda off n i)

end LowEnergy.PreparationVacuumPhysicalZeroRead
