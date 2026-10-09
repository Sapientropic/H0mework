import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationWholeResolvent

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationSpectralAxis
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open PreparationVacuumPhysicalTailPrice PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
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

attribute [local irreducible] physicalTime actualGrowth actualA jointGenerator evolutionGenerator
  propagationPencil twoTimeMap sourceInverse

/-- The original complete two-time source is consumed at its actual negative physical time. -/
def reverseTimeMap (q : PhysicalResponsePoint) (t : ℝ) : TransferOp:=twoTimeMap q (-t)

theorem reverseTimeMap_initial (q : PhysicalResponsePoint) : reverseTimeMap q 0=1 :=by
  simpa only [reverseTimeMap,neg_zero] using twoTimeMap_initial q

theorem reverseTimeMap_derivative (q : PhysicalResponsePoint) (t : ℝ) :
    HasDerivAt (reverseTimeMap q) ((-evolutionGenerator q)*reverseTimeMap q t) t :=by
  have normal : @HasDerivAt ℝ _ TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ TransferOp) (twoTimeMap q) (evolutionGenerator q*twoTimeMap q (-t)) (-t):=by
    convert! twoTimeMap_derivative q (-t) using 1
  have h:=normal.scomp t ((hasDerivAt_id t).neg)
  convert! h using 1
  simp only [reverseTimeMap,neg_one_smul]
  apply ContinuousLinearMap.ext
  intro A
  simp only [mul_apply_eq_comp,neg_apply,map_neg]

theorem reverseTimeMap_right_derivative (q : PhysicalResponsePoint) (t : ℝ) :
    HasDerivAt (reverseTimeMap q) (reverseTimeMap q t*(-evolutionGenerator q)) t :=by
  have normal : @HasDerivAt ℝ _ TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ TransferOp) (twoTimeMap q) (twoTimeMap q (-t)*evolutionGenerator q) (-t):=by
    convert! twoTimeMap_right_derivative q (-t) using 1
  have h:=normal.scomp t ((hasDerivAt_id t).neg)
  convert! h using 1
  simp only [reverseTimeMap,neg_one_smul]
  apply ContinuousLinearMap.ext
  intro A
  simp only [mul_apply_eq_comp,neg_apply,map_neg]

theorem reverseTimeMap_continuous (q : PhysicalResponsePoint) : Continuous (reverseTimeMap q) :=by
  have h:=(twoTimeMap_continuous q).comp continuous_neg
  convert! h using 1

theorem reverseTimeMap_bound (q : PhysicalResponsePoint) (t : ℝ) :
    ‖reverseTimeMap q t‖≤actualGrowth (q.p+q.k) q.F |t| * actualGrowth q.p q.F |t| :=by
  simpa only [reverseTimeMap,abs_neg] using twoTimeMap_bound q (-t)

private theorem two_map_norm {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] (A B : R) :
    ‖(ContinuousLinearMap.mul ℂ R A)*(ContinuousLinearMap.mul ℂ R).flip B‖≤‖A‖*‖B‖ :=by
  have right : ‖(ContinuousLinearMap.mul ℂ R).flip B‖≤‖B‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
    intro X
    exact (norm_mul_le X B).trans_eq (mul_comm _ _)
  exact (norm_mul_le _ _).trans (mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le ℂ R A)
    right (norm_nonneg _) (norm_nonneg _))

theorem reverseTimeMap_subexp (q : PhysicalResponsePoint) : SourceSubexp (reverseTimeMap q) :=by
  intro d positive
  have left:=actual_time_subexp (q.p+q.k) q.F 1 0
  have right:=actual_time_subexp q.p q.F (-1) 0
  have bound (t : ℝ) : ‖reverseTimeMap q t‖≤‖physicalTime (q.p+q.k) q.F t 0‖*‖physicalTime q.p q.F (-t) 0‖:=by
    have h:=two_map_norm (physicalTime (q.p+q.k) q.F t 0) (physicalTime q.p q.F (-t) 0)
    unfold reverseTimeMap twoTimeMap
    rw [neg_neg]
    convert! h using 1
  have weight (t : ℝ) : Real.exp (-d*t)=Real.exp (-(d/2)*t)*Real.exp (-(d/2)*t):=by
    rw [←Real.exp_add];congr 1;ring
  refine squeeze_zero (fun t=>mul_nonneg (Real.exp_pos _).le (show 0≤‖reverseTimeMap q t‖ from by convert! norm_nonneg (reverseTimeMap q t) using 1))
    (fun t=>(mul_le_mul_of_nonneg_left (bound t) (Real.exp_pos _).le).trans_eq ?_)
    (by simpa only [neg_one_mul,one_mul,add_zero,zero_mul] using
      (left (d/2) (by positivity)).mul (right (d/2) (by positivity)))
  rw [weight]
  ring

end LowEnergy.SourcePropagationSpectralAxis
