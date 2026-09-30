import H0mework.Physics.LowEnergy.VertexTensor.Quadratic
import H0mework.Physics.LowEnergy.LightSpace.Frame

/-! The source-generated spatial frame rotates the axial T,T,L tensor. The
fixed A1 probe reads its first diagonal entry, without angular averaging. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
open LightModes LightSpace Stage9C.Material.SpinPair Filter Topology
noncomputable section

def fixedProbeCoupling (same : Bool) (q direction : ℝ) : ℝ :=
  physicalTransverse same q+(physicalLongitudinal same q-physicalTransverse same q)*direction^2

theorem fixedProbe_convex (same : Bool) (q direction : ℝ) :
    fixedProbeCoupling same q direction=(1-direction^2)*physicalTransverse same q+
      direction^2*physicalLongitudinal same q := by
  unfold fixedProbeCoupling
  ring

theorem physical_transverse_positive (same : Bool) (q : ℝ) (small : |q| ≤ LightModes.momentumRadius) :
    0<physicalTransverse same q := by
  rw [physical_transverse_original]
  cases same
  · exact LightInteraction.physical_coupling_positive q small
  · exact DrivenInteraction.physical_growth_coupling_positive q small

theorem fixedProbe_positive (same : Bool) (q direction : ℝ)
    (small : |q| ≤ LightModes.momentumRadius) (unitBound : |direction|≤1) :
    0<fixedProbeCoupling same q direction := by
  have first := physical_transverse_positive same q small
  have second := physical_longitudinal_positive same q small
  have square : direction^2≤1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg direction) unitBound 2
  rw [fixedProbe_convex]
  by_cases edge : direction^2=1
  · rw [edge,sub_self,zero_mul,one_mul,zero_add]
    exact second
  · have weight : 0<1-direction^2 := sub_pos.mpr (lt_of_le_of_ne square edge)
    exact add_pos_of_pos_of_nonneg (mul_pos weight first) (mul_nonneg (sq_nonneg direction) second.le)

def axisSpatialTensor (same : Bool) (q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![0,physicalTransverse same q,physicalTransverse same q,physicalLongitudinal same q]

def transportedSpatialTensor (same : Bool) (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : Matrix (Fin 4) (Fin 4) ℝ :=
  (spatialRotation momentum nonzero).transpose*axisSpatialTensor same (radialMomentum momentum)*
    spatialRotation momentum nonzero

theorem sourceRotation_time_spatial (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) (index : Fin 3) :
    spatialRotation momentum nonzero 0 index.succ=0 := by
  fin_cases index <;>
    simp [spatialRotation,Rotation.rotateY,Rotation.rotateZ]

theorem sourceRotation_column_unit (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) (index : Fin 3) :
    (spatialRotation momentum nonzero 1 index.succ)^2+
      (spatialRotation momentum nonzero 2 index.succ)^2+
      (spatialRotation momentum nonzero 3 index.succ)^2=1 := by
  have generated := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M index.succ index.succ)
    (spatialRotation_generated momentum nonzero).1
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_four,
    sourceRotation_time_spatial,zero_mul,zero_add,Matrix.one_apply_eq,pow_two] using generated

theorem sourceRotation_longitudinal (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) (index : Fin 3) :
    spatialRotation momentum nonzero 3 index.succ=momentum index/Rotation.momentumRadius momentum := by
  have generated := spatialRotation_generated momentum nonzero
  have back : (spatialRotation momentum nonzero).transpose*ᵥ ![0,0,0,Rotation.momentumRadius momentum]=
      ![0,momentum 0,momentum 1,momentum 2] := by
    rw [← generated.2.2,Matrix.mulVec_mulVec,generated.1,Matrix.one_mulVec]
  have coordinate := congrFun back index.succ
  have product : spatialRotation momentum nonzero 3 index.succ*Rotation.momentumRadius momentum=momentum index := by
    fin_cases index <;>
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_four] using coordinate
  exact (eq_div_iff (Rotation.momentumRadius_positive momentum nonzero).ne').mpr product

theorem transportedTensor_probe (same : Bool) (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) (index : Fin 3) :
    transportedSpatialTensor same momentum nonzero index.succ index.succ=
      fixedProbeCoupling same (radialMomentum momentum) (momentum index/Rotation.momentumRadius momentum) := by
  have unit := sourceRotation_column_unit momentum nonzero index
  norm_num [transportedSpatialTensor,axisSpatialTensor,Matrix.mul_apply,
    Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_four,Matrix.vecHead,Matrix.vecTail]
  change spatialRotation momentum nonzero 1 index.succ*physicalTransverse same (radialMomentum momentum)*
      spatialRotation momentum nonzero 1 index.succ+
    spatialRotation momentum nonzero 2 index.succ*physicalTransverse same (radialMomentum momentum)*
      spatialRotation momentum nonzero 2 index.succ+
    spatialRotation momentum nonzero 3 index.succ*physicalLongitudinal same (radialMomentum momentum)*
      spatialRotation momentum nonzero 3 index.succ=_
  rw [fixedProbeCoupling,← sourceRotation_longitudinal momentum nonzero index]
  have weighted := congrArg (fun value : ℝ => physicalTransverse same (radialMomentum momentum)*value) unit
  nlinarith only [weighted]

theorem source_direction_bound (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) (index : Fin 3) :
    |momentum index/Rotation.momentumRadius momentum|≤1 := by
  rw [← sourceRotation_longitudinal momentum nonzero index]
  have unit := sourceRotation_column_unit momentum nonzero index
  have square : (spatialRotation momentum nonzero 3 index.succ)^2≤1 := by
    nlinarith [sq_nonneg (spatialRotation momentum nonzero 1 index.succ),
      sq_nonneg (spatialRotation momentum nonzero 2 index.succ)]
  nlinarith [sq_abs (spatialRotation momentum nonzero 3 index.succ),
    abs_nonneg (spatialRotation momentum nonzero 3 index.succ)]

theorem transported_A1_positive (same : Bool) (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (small : Rotation.momentumRadius momentum≤ spinScale*LightModes.momentumRadius) :
    0<transportedSpatialTensor same momentum nonzero 1 1 := by
  have read := transportedTensor_probe same momentum nonzero 0
  change 0<transportedSpatialTensor same momentum nonzero (0 : Fin 3).succ (0 : Fin 3).succ
  rw [read]
  exact fixedProbe_positive same _ _ (radial_small momentum small) (source_direction_bound momentum nonzero 0)

theorem fixedProbe_difference_bound (same : Bool) (q direction : ℝ)
    (small : |q| ≤ LightModes.momentumRadius) (unitBound : |direction|≤1) :
    |fixedProbeCoupling same q direction-physicalTransverse same q|≤
      (8*(lapse*spinScale)^2*LightInteraction.responseScale*coefficientBound (differenceTerms same))*q^2 := by
  have identity : fixedProbeCoupling same q direction-physicalTransverse same q=
      (physicalLongitudinal same q-physicalTransverse same q)*direction^2 := by
    unfold fixedProbeCoupling
    ring
  rw [identity,abs_mul,abs_of_nonneg (sq_nonneg direction)]
  have square : direction^2≤1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg direction) unitBound 2
  exact (mul_le_mul_of_nonneg_left square (abs_nonneg _)).trans
    (by simpa only [mul_one] using physical_difference_bound same q small)

end
end SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
