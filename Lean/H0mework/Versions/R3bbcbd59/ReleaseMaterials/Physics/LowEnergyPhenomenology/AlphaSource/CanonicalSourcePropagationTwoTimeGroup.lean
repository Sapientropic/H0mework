import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPropagationWholeCurvatureReturn

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationResolvent
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalTailPrice PreparationVacuumPropagationPencil
open PreparationVacuumFieldPerturbation SourceFiniteUnitary
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
abbrev Op:=PreparationVacuumPropagationPencil.Op
abbrev TransferOp:=Op→L[ℂ] Op
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ TransferOp:=by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=TransferOp)) using 1
local instance : ContinuousSMul ℝ TransferOp:=by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=TransferOp)) using 1
attribute [local irreducible] jointGenerator physicalTime actualA actualGrowth factorialBudget
  leftGenerator rightGenerator evolutionGenerator

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

/-- Both actual time legs act on the whole original operator carrier. -/
def twoTimeMap (q : PhysicalResponsePoint) (t : ℝ) : TransferOp:=
  (ContinuousLinearMap.mul ℂ Op (physicalTime (q.p+q.k) q.F (-t) 0))*(ContinuousLinearMap.mul ℂ Op).flip (physicalTime q.p q.F t 0)

theorem twoTimeMap_apply (q : PhysicalResponsePoint) (t : ℝ) (A : Op) :
    twoTimeMap q t A=physicalTime (q.p+q.k) q.F (-t) 0*A*physicalTime q.p q.F t 0 :=rfl

theorem twoTimeMap_initial (q : PhysicalResponsePoint) : twoTimeMap q 0=1 :=by
  apply ContinuousLinearMap.ext
  intro A
  simp only [twoTimeMap_apply,neg_zero,physicalTime_initial,one_mul,mul_one,one_apply_eq_self]

theorem twoTimeMap_derivative (q : PhysicalResponsePoint) (t : ℝ) :
    HasDerivAt (twoTimeMap q) (evolutionGenerator q*twoTimeMap q t) t :=by
  have h:=map_time_derivative (jointGenerator (q.p+q.k) q.F 0 0) (jointGenerator q.p q.F 0 0) t
  simp only [mul_assoc] at h
  convert! h using 1 <;> first
    | rfl
    | (funext r; unfold twoTimeMap physicalTime; rfl)
    | (unfold evolutionGenerator leftGenerator rightGenerator twoTimeMap physicalTime; rfl)

theorem twoTimeMap_commutes (q : PhysicalResponsePoint) (t : ℝ) :
    Commute (evolutionGenerator q) (twoTimeMap q t) :=by
  simpa only [twoTimeMap,physicalTime,evolutionGenerator,leftGenerator,rightGenerator] using
    map_commutes (jointGenerator (q.p+q.k) q.F 0 0) (jointGenerator q.p q.F 0 0) t

theorem twoTimeMap_right_derivative (q : PhysicalResponsePoint) (t : ℝ) :
    HasDerivAt (twoTimeMap q) (twoTimeMap q t*evolutionGenerator q) t :=by
  rw [←(twoTimeMap_commutes q t).eq]
  exact twoTimeMap_derivative q t

private theorem map_norm {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] (A B : R) :
    ‖(ContinuousLinearMap.mul ℂ R A)*(ContinuousLinearMap.mul ℂ R).flip B‖≤‖A‖*‖B‖ :=by
  have right : ‖(ContinuousLinearMap.mul ℂ R).flip B‖≤‖B‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    intro X
    exact (norm_mul_le X B).trans_eq (mul_comm _ _)
  exact (norm_mul_le _ _).trans (mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le ℂ R A)
    right (norm_nonneg _) (norm_nonneg _))

theorem twoTimeMap_bound (q : PhysicalResponsePoint) (t : ℝ) :
    ‖twoTimeMap q t‖≤actualGrowth (q.p+q.k) q.F |t| * actualGrowth q.p q.F |t| :=by
  refine (map_norm _ _).trans ?_
  exact mul_le_mul (by simpa only [abs_neg] using actual_time_bound (q.p+q.k) q.F (-t))
    (actual_time_bound q.p q.F t) (norm_nonneg _) (actualGrowth_nonnegative _ _ _ (abs_nonneg t))

theorem twoTimeMap_subexp (q : PhysicalResponsePoint) : SourceSubexp (twoTimeMap q) :=by
  intro d positive
  have L:=actual_time_subexp (q.p+q.k) q.F (-1) 0
  have R:=actual_time_subexp q.p q.F 1 0
  have bound (t : ℝ) : ‖twoTimeMap q t‖≤‖physicalTime (q.p+q.k) q.F (-t) 0‖*‖physicalTime q.p q.F t 0‖:=
    map_norm _ _
  have weight (t : ℝ) : Real.exp (-d*t)=Real.exp (-(d/2)*t)*Real.exp (-(d/2)*t):=by
    rw [←Real.exp_add];congr 1;ring
  refine squeeze_zero (fun t=>mul_nonneg (Real.exp_pos _).le (show 0≤‖twoTimeMap q t‖ from by convert! norm_nonneg (twoTimeMap q t) using 1))
    (fun t=>(mul_le_mul_of_nonneg_left (bound t) (Real.exp_pos _).le).trans_eq ?_)
    (by simpa only [neg_one_mul,one_mul,add_zero,zero_mul] using
      (L (d/2) (by positivity)).mul (R (d/2) (by positivity)))
  rw [weight]
  ring

theorem twoTimeMap_continuous (q : PhysicalResponsePoint) : Continuous (twoTimeMap q) :=by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h:=twoTimeMap_derivative q t
  have hnorm : @HasDerivAt ℝ _ TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ TransferOp) (twoTimeMap q) (evolutionGenerator q*twoTimeMap q t) t:=by
    convert! h using 1
  convert! hnorm.continuousAt using 1

theorem rawFlow_sameMap (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) :
    rawFlow q reader t=twoTimeMap q t (rawInitial q reader) :=by
  simp only [rawFlow,rawInitial,twoTimeMap_apply,fiveKernel,mul_assoc]

end LowEnergy.SourcePropagationResolvent
