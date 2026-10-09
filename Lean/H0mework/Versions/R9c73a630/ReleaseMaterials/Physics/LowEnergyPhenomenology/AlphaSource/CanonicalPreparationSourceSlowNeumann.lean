import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceOffgapInverse
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFullN1Sylvester

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumQuantumSlowResponse
open GaussCoreHilbert PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumGaugeSlowFrequency PreparationVacuumPhysicalFeedback
open CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis
open scoped Topology
attribute [local irreducible] actualC actualA sourceVelocityLinear sourceOffgapInverse
  sourceEqualProjection sourceOffProjection sourceStaticLiouvillian

def sourceSlowTransport (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceSuperOp :=
  zeta • (1 : SourceSuperOp)+Complex.I • ContinuousLinearMap.mul ℂ SourceOp (sourceVelocityLinear F n)

def sourceSlowRadius (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : ℝ :=
  (4*(‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖+1))⁻¹

def sourceSlowPerturbation (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) : SourceSuperOp :=
  (delta : ℂ) • (sourceOffgapInverse F*sourceSlowTransport F n zeta)

def sourceSlowReturn (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) : SourceSuperOp :=
  Ring.inverse (1+sourceSlowPerturbation F n zeta delta)

theorem sourceSlowTransport_apply (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (X : SourceOp) :
    sourceSlowTransport F n zeta X=zeta • X+Complex.I • (sourceVelocityLinear F n*X) := rfl

theorem sourceSlowReturn_origin (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    sourceSlowReturn F n zeta 0=1 := by
  have zero : (0 : ℂ) • (sourceOffgapInverse F*sourceSlowTransport F n zeta)=0 := by
    apply ContinuousLinearMap.ext
    intro X
    apply ContinuousLinearMap.ext
    intro x
    exact zero_smul ℂ (sourceOffgapInverse F (sourceSlowTransport F n zeta X) x)
  simp only [sourceSlowReturn,sourceSlowPerturbation,Complex.ofReal_zero,zero,add_zero (1 : SourceSuperOp),Ring.inverse_one (M₀:=SourceSuperOp)]

theorem sourceSlowRadius_positive (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    0<sourceSlowRadius F n zeta := by unfold sourceSlowRadius; positivity

theorem sourceSlowPerturbation_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) :
    ‖sourceSlowPerturbation F n zeta delta‖ ≤ (abs delta)*‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖ := by
  unfold sourceSlowPerturbation
  calc
    _≤‖(delta:ℂ)‖*‖sourceOffgapInverse F*sourceSlowTransport F n zeta‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _≤‖(delta:ℂ)‖*(‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _=_ := by rw [Complex.norm_real,Real.norm_eq_abs];ring

theorem sourceSlowPerturbation_small (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) : ‖sourceSlowPerturbation F n zeta delta‖ ≤ (1/4 : ℝ) := by
  have budget : 0<‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖+1 := by positivity
  calc
    _≤(abs delta)*‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖ := sourceSlowPerturbation_price F n zeta delta
    _ ≤ sourceSlowRadius F n zeta*(‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖+1) := by
      have h:=mul_le_mul_of_nonneg_right small (mul_nonneg (norm_nonneg (sourceOffgapInverse F)) (norm_nonneg (sourceSlowTransport F n zeta)))
      have radius:0 ≤ sourceSlowRadius F n zeta := (sourceSlowRadius_positive F n zeta).le
      nlinarith
    _=1/4 := by unfold sourceSlowRadius;field_simp [ne_of_gt budget]

theorem sourceSlowReturn_unit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) : IsUnit (1+sourceSlowPerturbation F n zeta delta) := by
  have h:‖-sourceSlowPerturbation F n zeta delta‖<1 := by
    rw [norm_neg (sourceSlowPerturbation F n zeta delta)];linarith [sourceSlowPerturbation_small F n zeta delta small]
  simpa only [sub_neg_eq_add (1 : SourceSuperOp) (sourceSlowPerturbation F n zeta delta)] using isUnit_one_sub_of_norm_lt_one (R:=SourceSuperOp) h

theorem sourceSlowReturn_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) :
    sourceSlowReturn F n zeta delta*(1+sourceSlowPerturbation F n zeta delta)=1 :=
  Ring.inverse_mul_cancel _ (sourceSlowReturn_unit F n zeta delta small)

theorem sourceSlowReturn_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) :
    (1+sourceSlowPerturbation F n zeta delta)*sourceSlowReturn F n zeta delta=1 :=
  Ring.mul_inverse_cancel _ (sourceSlowReturn_unit F n zeta delta small)

private theorem return_identity {R : Type*} [Ring R] (P W : R) (inverse : (1+P)*W=1) :
    W=1-P*W := by
  rw [add_mul,one_mul] at inverse
  exact eq_sub_of_add_eq inverse

theorem sourceSlowReturn_identity (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) :
    sourceSlowReturn F n zeta delta=1-sourceSlowPerturbation F n zeta delta*sourceSlowReturn F n zeta delta := by
  exact return_identity (sourceSlowPerturbation F n zeta delta) (sourceSlowReturn F n zeta delta)
    (sourceSlowReturn_right F n zeta delta small)

theorem sourceSlowReturn_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) : ‖sourceSlowReturn F n zeta delta‖≤2 := by
  have triangle : ‖sourceSlowReturn F n zeta delta‖≤1+(1/4:ℝ)*‖sourceSlowReturn F n zeta delta‖ := by
    calc
      _=‖1-sourceSlowPerturbation F n zeta delta*sourceSlowReturn F n zeta delta‖ := congrArg norm (sourceSlowReturn_identity F n zeta delta small)
      _≤‖(1 : SourceSuperOp)‖+‖sourceSlowPerturbation F n zeta delta*sourceSlowReturn F n zeta delta‖ := norm_sub_le (1 : SourceSuperOp) (sourceSlowPerturbation F n zeta delta*sourceSlowReturn F n zeta delta)
      _≤1+(1/4:ℝ)*‖sourceSlowReturn F n zeta delta‖ := add_le_add ContinuousLinearMap.norm_id_le
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (sourceSlowPerturbation_small F n zeta delta small) (norm_nonneg _)))
  linarith

theorem sourceSlowReturn_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) :
    ‖sourceSlowReturn F n zeta delta-1‖≤2*(abs delta)*‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖ := by
  have identity : sourceSlowReturn F n zeta delta-1=
      -(sourceSlowPerturbation F n zeta delta*sourceSlowReturn F n zeta delta) := by
    calc
      _=(1-sourceSlowPerturbation F n zeta delta*sourceSlowReturn F n zeta delta)-1 :=
        congrArg (fun A : SourceSuperOp=>A-1) (sourceSlowReturn_identity F n zeta delta small)
      _=_ := by abel
  rw [identity,norm_neg (sourceSlowPerturbation F n zeta delta*sourceSlowReturn F n zeta delta)]
  calc
    _≤‖sourceSlowPerturbation F n zeta delta‖*‖sourceSlowReturn F n zeta delta‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _≤((abs delta)*‖sourceOffgapInverse F‖*‖sourceSlowTransport F n zeta‖)*2 :=
      mul_le_mul (sourceSlowPerturbation_price F n zeta delta) (sourceSlowReturn_price F n zeta delta small) (norm_nonneg (sourceSlowReturn F n zeta delta)) (by positivity)
    _=_ := by ring

end LowEnergy.PreparationVacuumQuantumSlowResponse
