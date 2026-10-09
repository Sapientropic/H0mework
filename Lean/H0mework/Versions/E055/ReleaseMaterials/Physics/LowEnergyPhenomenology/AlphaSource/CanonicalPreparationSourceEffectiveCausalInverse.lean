import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedLeadingInverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumQuantumSlowResidue
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalSlowBlock PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumQuantumSlowResponse
open scoped Topology
attribute [local irreducible] sourceEqualProjection sourceOffProjection sourceSlowTransport
  sourceSlowEffective sourceSlowLeading sourceOffgapInverse sourcePinnedLeadingInverse

def sourceOriginInverse (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceSuperOp :=
  sourcePinnedLeadingInverse F n zeta+sourceOffProjection F

def sourceCompletePencil (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) : SourceSuperOp :=
  sourceSlowEffective F n zeta delta+sourceOffProjection F

def sourceOriginPencil (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceSuperOp :=
  sourceSlowLeading F n zeta+sourceOffProjection F

def sourceEffectiveErrorBudget (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : ℝ :=
  1+2*‖sourceEqualProjection F‖^2*‖sourceSlowTransport F n zeta‖^2*‖sourceOffgapInverse F‖

def sourceResidueRadius (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : ℝ :=
  min (sourceSlowRadius F n zeta) (4*(‖sourceOriginInverse F n zeta‖*sourceEffectiveErrorBudget F n zeta+1))⁻¹

def sourceEffectiveInverse (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) : SourceSuperOp :=
  Ring.inverse (sourceCompletePencil F n zeta delta)

theorem sourceEffectiveErrorBudget_positive (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    0<sourceEffectiveErrorBudget F n zeta := by unfold sourceEffectiveErrorBudget;positivity

theorem sourceResidueRadius_positive (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    0<sourceResidueRadius F n zeta := by
  unfold sourceResidueRadius
  apply lt_min (sourceSlowRadius_positive F n zeta)
  have budget:=sourceEffectiveErrorBudget_positive F n zeta
  positivity

theorem sourceResidueRadius_slow (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    sourceResidueRadius F n zeta ≤ sourceSlowRadius F n zeta := min_le_left _ _

theorem sourceOriginInverse_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : sourceOriginInverse F n zeta*sourceOriginPencil F n zeta=1 :=
  sourcePinnedCompleteInverse_left F n zeta positive

theorem sourceOriginInverse_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : sourceOriginPencil F n zeta*sourceOriginInverse F n zeta=1 :=
  sourcePinnedCompleteInverse_right F n zeta positive

theorem sourceCompletePencil_difference (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) :
    sourceCompletePencil F n zeta delta-sourceOriginPencil F n zeta=
      sourceSlowEffective F n zeta delta-sourceSlowLeading F n zeta := by
  unfold sourceCompletePencil sourceOriginPencil
  abel

theorem sourceCompletePencil_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : abs delta ≤ sourceResidueRadius F n zeta) :
    ‖sourceCompletePencil F n zeta delta-sourceOriginPencil F n zeta‖ ≤ sourceEffectiveErrorBudget F n zeta*abs delta := by
  rw [sourceCompletePencil_difference]
  have old:=sourceSlowEffective_error F n zeta delta (small.trans (sourceResidueRadius_slow F n zeta))
  calc
    _≤‖sourceEqualProjection F‖*‖sourceSlowTransport F n zeta‖*
      (2*abs delta*‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖)*‖sourceEqualProjection F‖ := old
    _ ≤ sourceEffectiveErrorBudget F n zeta*abs delta := by
      unfold sourceEffectiveErrorBudget
      nlinarith [abs_nonneg delta]

theorem sourceCompletePencil_neumann (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : abs delta ≤ sourceResidueRadius F n zeta) :
    ‖sourceOriginInverse F n zeta*(sourceCompletePencil F n zeta delta-sourceOriginPencil F n zeta)‖≤(1/4 : ℝ) := by
  have budget:=sourceEffectiveErrorBudget_positive F n zeta
  have scalar : 0<‖sourceOriginInverse F n zeta‖*sourceEffectiveErrorBudget F n zeta+1 := by positivity
  have radius : abs delta≤(4*(‖sourceOriginInverse F n zeta‖*sourceEffectiveErrorBudget F n zeta+1))⁻¹ :=
    small.trans (min_le_right _ _)
  calc
    _≤‖sourceOriginInverse F n zeta‖*‖sourceCompletePencil F n zeta delta-sourceOriginPencil F n zeta‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _≤‖sourceOriginInverse F n zeta‖*(sourceEffectiveErrorBudget F n zeta*abs delta) :=
      mul_le_mul_of_nonneg_left (sourceCompletePencil_error F n zeta delta small) (norm_nonneg (sourceOriginInverse F n zeta))
    _≤(‖sourceOriginInverse F n zeta‖*sourceEffectiveErrorBudget F n zeta+1)*
      (4*(‖sourceOriginInverse F n zeta‖*sourceEffectiveErrorBudget F n zeta+1))⁻¹ := by
      have generated:=mul_le_mul_of_nonneg_left radius
        (mul_nonneg (norm_nonneg (sourceOriginInverse F n zeta)) budget.le)
      have nonnegative : 0≤(4*(‖sourceOriginInverse F n zeta‖*sourceEffectiveErrorBudget F n zeta+1))⁻¹ := by positivity
      nlinarith
    _=1/4 := by field_simp [ne_of_gt scalar]

private theorem nearby_unit {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (A B H : R) (left : H*A=1) (right : A*H=1) (small : ‖H*(B-A)‖<1) : IsUnit B := by
  have origin : IsUnit A:=⟨⟨A,H,right,left⟩,rfl⟩
  have step : IsUnit (1+H*(B-A)) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one (show ‖-(H*(B-A))‖<1 by simpa only [norm_neg] using small)
  have factor : A*(1+H*(B-A))=B := by
    calc
      _=A+(A*H)*(B-A) := by noncomm_ring
      _=B := by rw [right,one_mul];abel
  have result:=origin.mul step
  rwa [factor] at result

theorem sourceCompletePencil_unit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (small : abs delta ≤ sourceResidueRadius F n zeta) :
    IsUnit (sourceCompletePencil F n zeta delta) :=
  nearby_unit (R:=SourceSuperOp) (sourceOriginPencil F n zeta) (sourceCompletePencil F n zeta delta)
    (sourceOriginInverse F n zeta) (sourceOriginInverse_left F n zeta positive) (sourceOriginInverse_right F n zeta positive)
    (lt_of_le_of_lt (sourceCompletePencil_neumann F n zeta delta small) (by norm_num : (1/4:ℝ)<1))

theorem sourceEffectiveInverse_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (small : abs delta ≤ sourceResidueRadius F n zeta) :
    sourceEffectiveInverse F n zeta delta*sourceCompletePencil F n zeta delta=1 :=
  Ring.inverse_mul_cancel _ (sourceCompletePencil_unit F n zeta positive delta small)

theorem sourceEffectiveInverse_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (small : abs delta ≤ sourceResidueRadius F n zeta) :
    sourceCompletePencil F n zeta delta*sourceEffectiveInverse F n zeta delta=1 :=
  Ring.mul_inverse_cancel _ (sourceCompletePencil_unit F n zeta positive delta small)

private theorem inverse_difference {R : Type*} [Ring R] (A B H : R)
    (left : H*A=1) (unit : IsUnit B) : Ring.inverse B=H-(H*(B-A))*Ring.inverse B := by
  calc
    _=(H*A)*Ring.inverse B := by rw [left,one_mul]
    _=H*(B*Ring.inverse B)-(H*(B-A))*Ring.inverse B := by noncomm_ring
    _=_ := by rw [Ring.mul_inverse_cancel B unit,mul_one]

private theorem inverse_price {R : Type*} [NormedRing R] (A B H : R)
    (left : H*A=1) (unit : IsUnit B) (small : ‖H*(B-A)‖≤(1/4:ℝ)) : ‖Ring.inverse B‖≤2*‖H‖ := by
  have triangle : ‖Ring.inverse B‖≤‖H‖+(1/4:ℝ)*‖Ring.inverse B‖ := by
    calc
      _=‖H-(H*(B-A))*Ring.inverse B‖ := congrArg norm (inverse_difference A B H left unit)
      _≤‖H‖+‖(H*(B-A))*Ring.inverse B‖ := norm_sub_le _ _
      _≤_ := add_le_add (le_refl ‖H‖) ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right small (norm_nonneg _)))
  linarith [norm_nonneg H]

theorem sourceEffectiveInverse_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (small : abs delta ≤ sourceResidueRadius F n zeta) :
    ‖sourceEffectiveInverse F n zeta delta‖≤2*‖sourceOriginInverse F n zeta‖ :=
  inverse_price (R:=SourceSuperOp) (sourceOriginPencil F n zeta) (sourceCompletePencil F n zeta delta)
    (sourceOriginInverse F n zeta) (sourceOriginInverse_left F n zeta positive)
    (sourceCompletePencil_unit F n zeta positive delta small) (sourceCompletePencil_neumann F n zeta delta small)

private theorem inverse_error {R : Type*} [NormedRing R] (A B H : R)
    (left : H*A=1) (unit : IsUnit B) :
    ‖Ring.inverse B-H‖≤‖H‖*‖B-A‖*‖Ring.inverse B‖ := by
  have identity : Ring.inverse B-H= -((H*(B-A))*Ring.inverse B) := by
    calc
      _=(H-(H*(B-A))*Ring.inverse B)-H := congrArg (fun Z : R=>Z-H) (inverse_difference A B H left unit)
      _=_ := by abel
  rw [identity,norm_neg]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem sourceEffectiveInverse_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (delta : ℝ) (small : abs delta ≤ sourceResidueRadius F n zeta) :
    ‖sourceEffectiveInverse F n zeta delta-sourceOriginInverse F n zeta‖≤
      2*‖sourceOriginInverse F n zeta‖^2*sourceEffectiveErrorBudget F n zeta*abs delta := by
  have price:=inverse_error (sourceOriginPencil F n zeta) (sourceCompletePencil F n zeta delta)
    (sourceOriginInverse F n zeta) (sourceOriginInverse_left F n zeta positive)
    (sourceCompletePencil_unit F n zeta positive delta small)
  calc
    _≤‖sourceOriginInverse F n zeta‖*‖sourceCompletePencil F n zeta delta-sourceOriginPencil F n zeta‖*
      ‖sourceEffectiveInverse F n zeta delta‖ := price
    _≤‖sourceOriginInverse F n zeta‖*(sourceEffectiveErrorBudget F n zeta*abs delta)*
      (2*‖sourceOriginInverse F n zeta‖) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (sourceCompletePencil_error F n zeta delta small)
          (norm_nonneg (sourceOriginInverse F n zeta)))
        (sourceEffectiveInverse_price F n zeta positive delta small)
        (norm_nonneg (sourceEffectiveInverse F n zeta delta))
        (mul_nonneg (norm_nonneg (sourceOriginInverse F n zeta))
          (mul_nonneg (sourceEffectiveErrorBudget_positive F n zeta).le (abs_nonneg delta)))
    _=_ := by ring

end LowEnergy.PreparationVacuumQuantumSlowResidue
