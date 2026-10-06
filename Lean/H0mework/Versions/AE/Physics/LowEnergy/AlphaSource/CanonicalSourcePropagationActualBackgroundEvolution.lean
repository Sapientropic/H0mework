import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationFullBackgroundReturn
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNearFieldTime
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open PreparationVacuumPhysicalTailPrice PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
open SourcePropagationSpectralAxis SourcePropagationFieldFeedback
abbrev Op:=SourcePropagationResolvent.Op
abbrev TransferOp:=SourcePropagationResolvent.TransferOp
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ TransferOp:=by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=TransferOp)) using 1
local instance : ContinuousSMul ℝ TransferOp:=by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=TransferOp)) using 1
local instance : ContinuousENorm TransferOp:=by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=TransferOp)) using 1
local instance : AddCommGroup TransferOp:=ContinuousLinearMap.addCommGroup
local instance : IsTopologicalAddGroup TransferOp:=by
  have normal : @IsTopologicalAddGroup TransferOp
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddGroup:=inferInstance
  convert! normal using 1
local instance : IsTopologicalRing TransferOp:=by
  convert! (NonUnitalSeminormedRing.toIsTopologicalRing (α:=TransferOp)) using 1
local instance : IsScalarTower ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  rfl⟩
local instance : SMulCommClass ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  exact (map_smul A c (B X)).symm⟩

open PreparationVacuumFieldPerturbation SourceFiniteUnitary
attribute [local irreducible] jointGenerator physicalTime fieldEvolution factorialBudget
  leftGenerator rightGenerator evolutionGenerator sourceInverse

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev End:=E→L[ℂ] E
local instance : NormedAlgebra ℝ (End (E:=E)):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (End (E:=E)):=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ ((End (E:=E))→L[ℂ] (End (E:=E))):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ ((End (E:=E))→L[ℂ] (End (E:=E))):=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem time_left_derivative (C : End (E:=E)) (t : ℝ) :
    HasDerivAt (time C) (((-Complex.I) • C)*time C t) t :=by
  have h:=time_operator_derivative C t
  rw [←((time_commutes C C (Commute.refl C) t).smul_left (-Complex.I)).eq] at h
  exact h

private theorem map_time_derivative (CL CR : End (E:=E)) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>(ContinuousLinearMap.mul ℂ (End (E:=E)) (time CL (-r)))*(ContinuousLinearMap.mul ℂ (End (E:=E))).flip (time CR r))
      ((ContinuousLinearMap.mul ℂ (End (E:=E)) (-((-Complex.I) • CL))+
        (ContinuousLinearMap.mul ℂ (End (E:=E))).flip ((-Complex.I) • CR))*
        (ContinuousLinearMap.mul ℂ (End (E:=E)) (time CL (-t)))*(ContinuousLinearMap.mul ℂ (End (E:=E))).flip (time CR t)) t :=by
  have TL:=(time_left_derivative CL (-t)).scomp t ((hasDerivAt_id t).neg)
  have TR:=time_operator_derivative CR t
  have L:=(((ContinuousLinearMap.mul ℂ (End (E:=E))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t TL)
  have R:=(((ContinuousLinearMap.mul ℂ (End (E:=E))).flip.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t TR)
  have h:=L.mul R
  refine h.congr_deriv ?_
  apply ContinuousLinearMap.ext
  intro A
  simp only [add_apply,ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.flip_apply,mul_apply_eq_comp,Function.comp_apply,ContinuousLinearMap.coe_restrictScalars',neg_one_smul]
  simp only [neg_mul,mul_assoc]

private theorem map_commutes (CL CR : End (E:=E)) (t : ℝ) :
    Commute (ContinuousLinearMap.mul ℂ (End (E:=E)) (-((-Complex.I) • CL))+
        (ContinuousLinearMap.mul ℂ (End (E:=E))).flip ((-Complex.I) • CR))
      ((ContinuousLinearMap.mul ℂ (End (E:=E)) (time CL (-t)))*(ContinuousLinearMap.mul ℂ (End (E:=E))).flip (time CR t)) :=by
  have left:=((time_commutes CL CL (Commute.refl CL) (-t)).smul_left (-Complex.I)).eq
  have right:=((time_commutes CR CR (Commute.refl CR) t).smul_left (-Complex.I)).eq
  change _*_=_*_
  apply ContinuousLinearMap.ext
  intro A
  simp only [add_apply,ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.flip_apply,mul_apply_eq_comp,map_add]
  simp only [add_mul,mul_add,mul_assoc,neg_mul,mul_neg]
  rw [←mul_assoc ((-Complex.I) • CL) (time CL (-t)),left,mul_assoc]
  rw [←right]

end Algebra

/-- Original inverse/forward physical-time legs at their actual common field background. -/
def physicalBackgroundMap (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) : TransferOp:=
  (ContinuousLinearMap.mul ℂ Op (physicalTime (q.p+q.k) q.F (-t) h))*
    (ContinuousLinearMap.mul ℂ Op).flip (physicalTime q.p q.F t h)

theorem physicalBackgroundMap_apply (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) (A : Op) :
    physicalBackgroundMap q h t A=physicalTime (q.p+q.k) q.F (-t) h*A*physicalTime q.p q.F t h:=rfl

theorem physicalBackgroundMap_initial (q : PhysicalResponsePoint) (h : Field289) :
    physicalBackgroundMap q h 0=1 :=by
  apply ContinuousLinearMap.ext
  intro A
  simp only [physicalBackgroundMap_apply,neg_zero,physicalTime_initial,one_mul,mul_one,one_apply_eq_self]

theorem physicalBackgroundMap_base (q : PhysicalResponsePoint) (t : ℝ) :
    physicalBackgroundMap q 0 t=twoTimeMap q t :=rfl

theorem physicalBackgroundMap_derivative (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) :
    HasDerivAt (physicalBackgroundMap q h) (fieldEvolution q h*physicalBackgroundMap q h t) t :=by
  have generated:=map_time_derivative (jointGenerator (q.p+q.k) q.F 0 h) (jointGenerator q.p q.F 0 h) t
  simp only [mul_assoc] at generated
  convert! generated using 1 <;> first
    | rfl
    | (funext r; unfold physicalBackgroundMap physicalTime; rfl)
    | (unfold fieldEvolution evolutionMap fieldGenerators physicalBackgroundMap physicalTime; rfl)

theorem physicalBackgroundMap_commutes (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) :
    Commute (fieldEvolution q h) (physicalBackgroundMap q h t) :=by
  convert! map_commutes (jointGenerator (q.p+q.k) q.F 0 h) (jointGenerator q.p q.F 0 h) t using 1
  · unfold fieldEvolution evolutionMap fieldGenerators;rfl
  · unfold physicalBackgroundMap physicalTime;rfl

theorem physicalBackgroundMap_right_derivative (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) :
    HasDerivAt (physicalBackgroundMap q h) (physicalBackgroundMap q h t*fieldEvolution q h) t :=by
  rw [←(physicalBackgroundMap_commutes q h t).eq]
  exact physicalBackgroundMap_derivative q h t

section CompleteAlgebra
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
local instance : NormedAlgebra ℚ R:=NormedAlgebra.restrictScalars ℚ ℝ _

private theorem autonomous_unique (L : R) (U : ℝ→R)
    (ode : ∀t,HasDerivAt U (U t*L) t) (initial : U 0=1) (t : ℝ) :
    U t=NormedSpace.exp (t • L) :=by
  let v:=fun s : ℝ=>U s*NormedSpace.exp (s • (-L))
  have derivative (s : ℝ) : HasDerivAt v 0 s:=by
    have generated:=(ode s).mul (hasDerivAt_exp_smul_const (-L) s)
    have commute : L*NormedSpace.exp (s • (-L))=NormedSpace.exp (s • (-L))*L:=
      ((Commute.refl L).neg_right.smul_right s).exp_right.eq
    convert! generated using 1
    simp only [mul_neg,←mul_assoc,←commute,add_neg_cancel]
  have constant:=is_const_of_deriv_eq_zero (fun s=>(derivative s).differentiableAt)
    (fun s=>(derivative s).deriv) t 0
  have value : U t*NormedSpace.exp (t • (-L))=1:=by
    simpa only [v,initial,zero_smul,NormedSpace.exp_zero,mul_one] using constant
  have inverse : NormedSpace.exp (t • (-L))*NormedSpace.exp (t • L)=1:=by
    rw [smul_neg,←NormedSpace.exp_add_of_commute (Commute.refl (t • L)).neg_left,
      neg_add_cancel,NormedSpace.exp_zero]
  calc
    _=U t*(NormedSpace.exp (t • (-L))*NormedSpace.exp (t • L)):=by rw [inverse,mul_one]
    _=(U t*NormedSpace.exp (t • (-L)))*NormedSpace.exp (t • L):=(mul_assoc _ _ _).symm
    _=_:=by rw [value,one_mul]

private theorem exp_product_jet (L0 L1 : R) (t s : ℝ) :
    HasDerivAt (fun r : ℝ=>NormedSpace.exp ((t-r) • L0)*NormedSpace.exp (r • L1))
      (NormedSpace.exp ((t-s) • L0)*(L1-L0)*NormedSpace.exp (s • L1)) s :=by
  have left:=(hasDerivAt_exp_smul_const L0 (t-s)).scomp s ((hasDerivAt_id s).const_sub t)
  have right:=hasDerivAt_exp_smul_const L1 s
  have generated:=left.mul right
  have commute:=((Commute.refl L1).smul_right s).exp_right.eq
  convert! generated using 1
  simp only [neg_one_smul,neg_mul,mul_assoc,mul_sub,Function.comp_apply]
  rw [←commute]
  simp only [sub_mul,mul_assoc]
  abel

private theorem exp_volterra (L0 L1 : R) (t : ℝ) :
    NormedSpace.exp (t • L1)=NormedSpace.exp (t • L0)+
      ∫s in (0:ℝ)..t,NormedSpace.exp ((t-s) • L0)*(L1-L0)*NormedSpace.exp (s • L1) :=by
  have continuous : Continuous (fun s : ℝ=>NormedSpace.exp ((t-s) • L0)*(L1-L0)*NormedSpace.exp (s • L1)):=by
    fun_prop
  have paid:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=t)
    (fun s _=>exp_product_jet L0 L1 t s) (continuous.intervalIntegrable (0:ℝ) t)
  simp only [sub_self,zero_smul,NormedSpace.exp_zero,one_mul,mul_one,sub_zero] at paid
  rw [paid]
  abel

end CompleteAlgebra

theorem physicalBackgroundMap_exp (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) :
    physicalBackgroundMap q h t=NormedSpace.exp (t • fieldEvolution q h) :=by
  have ode (s : ℝ) : HasDerivAt (physicalBackgroundMap q h) (physicalBackgroundMap q h s*fieldEvolution q h) s:=by
    convert! physicalBackgroundMap_right_derivative q h s using 1
  have generated:=autonomous_unique (R:=TransferOp) (fieldEvolution q h) (physicalBackgroundMap q h) ode
    (physicalBackgroundMap_initial q h) t
  convert! generated using 1

/-- Source-owned budget: the same two actual uncut-retainer 57-term prices. -/
def physicalBudget (q : PhysicalResponsePoint) (eta : ℝ) : ℝ:=
  factorialBudget (q.p+q.k) q.F (eta/2)*factorialBudget q.p q.F (eta/2)

theorem physicalBudget_nonnegative (q : PhysicalResponsePoint) (eta : ℝ) (positive : 0<eta) :
    0≤physicalBudget q eta:=mul_nonneg (factorialBudget_nonnegative _ _ _ (by positivity))
      (factorialBudget_nonnegative _ _ _ (by positivity))

theorem physicalBackgroundMap_base_bound (q : PhysicalResponsePoint) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖physicalBackgroundMap q 0 t‖≤physicalBudget q eta*Real.exp (eta*t) :=by
  have normBound:=twoTimeMap_bound q t
  have left:=actualGrowth_envelope (q.p+q.k) q.F (eta/2) t (by positivity) future
  have right:=actualGrowth_envelope q.p q.F (eta/2) t (by positivity) future
  have bound : ‖physicalBackgroundMap q 0 t‖≤
      (factorialBudget (q.p+q.k) q.F (eta/2)*Real.exp ((eta/2)*t))*
      (factorialBudget q.p q.F (eta/2)*Real.exp ((eta/2)*t)):=by
    rw [physicalBackgroundMap_base]
    have base : ‖twoTimeMap q t‖≤actualGrowth (q.p+q.k) q.F t*actualGrowth q.p q.F t:=by
      simpa only [abs_of_nonneg future] using normBound
    exact base.trans (mul_le_mul left right (actualGrowth_nonnegative _ _ _ future)
      (mul_nonneg (factorialBudget_nonnegative (q.p+q.k) q.F (eta/2) (by positivity)) (Real.exp_pos _).le))
  refine bound.trans_eq ?_
  unfold physicalBudget
  rw [mul_mul_mul_comm,←Real.exp_add]
  congr 2
  ring

/-- The actual full background and its original zero-background time obey a source Volterra return. -/
theorem physicalBackgroundMap_volterra (q : PhysicalResponsePoint) (h : Field289) (t : ℝ) :
    physicalBackgroundMap q h t=physicalBackgroundMap q 0 t+
      ∫s in (0:ℝ)..t,physicalBackgroundMap q 0 (t-s)*(fieldEvolution q h-fieldEvolution q 0)*physicalBackgroundMap q h s :=by
  have generated:=exp_volterra (R:=TransferOp) (fieldEvolution q 0) (fieldEvolution q h) t
  simpa only [←physicalBackgroundMap_exp] using generated

end LowEnergy.SourcePropagationNearFieldTime
