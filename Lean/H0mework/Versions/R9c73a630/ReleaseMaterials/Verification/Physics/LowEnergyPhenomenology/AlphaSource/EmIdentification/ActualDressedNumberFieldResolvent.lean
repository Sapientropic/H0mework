import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldLeft

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberField
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open ActualDressedNumberSector
open Filter
open scoped Topology
attribute [local irreducible] jointCompression jointY jointGenerator jointResolvent numberTwoGrade numberTwoProjection jointCResolvent

private theorem inverse_preserves (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (h : Field289) (free : IsUnit (jointCompression p F h-z • (1:ActualDressedNumberZero.Op))) (g : Fin 57) :
    Commute (numberTwoGrade g) (jointCResolvent p F z h) := by
  unfold jointCResolvent
  exact PreparationVacuumYukawaTransport.inverse_commuting _ _ free
    ((show Commute (numberTwoGrade g) (jointCompression p F h) from
      by simpa only [numberTwoGrade] using actual_joint_compression_blocks p F h (2,g)).sub_right
      ((Commute.one_right _).smul_right z))

private theorem inverse_range {R : Type*} [Ring R] (P Q A U : R)
    (PU : Commute P U) (range : Q*A*P=A*P) : Q*(A*U)*P=(A*U)*P := by
  calc
    _=(Q*A)*(U*P) := by noncomm_ring
    _=(Q*A)*(P*U) := by rw [PU.symm.eq]
    _=(Q*A*P)*U := by noncomm_ring
    _=(A*P)*U := by rw [range]
    _=A*(P*U) := by rw [mul_assoc]
    _=A*(U*P) := by rw [PU.eq]
    _=_ := by rw [mul_assoc]

private theorem inverse_terminal {R : Type*} [Ring R] (P A U : R)
    (PU : Commute P U) (terminal : A*P=0) : (A*U)*P=0 := by
  rw [mul_assoc,PU.symm.eq,←mul_assoc,terminal,zero_mul]

private theorem three_step_nilpotent {R : Type*} [Ring R] (P Q T B : R)
    (first : Q*B*P=B*P) (second : T*B*Q=B*Q) (terminal : B*T=0) :
    B*B*B*(P+Q+T)=0 := by
  have one : B*B*B*P=0 := by
    calc
      _=B*B*(B*P) := by noncomm_ring
      _=B*B*(Q*B*P) := by rw [first]
      _=B*(B*Q)*B*P := by noncomm_ring
      _=B*(T*B*Q)*B*P := by rw [second]
      _=(B*T)*B*Q*B*P := by noncomm_ring
      _=0 := by rw [terminal,zero_mul,zero_mul,zero_mul,zero_mul]
  have two : B*B*B*Q=0 := by
    calc
      _=B*B*(B*Q) := by noncomm_ring
      _=B*B*(T*B*Q) := by rw [second]
      _=B*(B*T)*B*Q := by noncomm_ring
      _=0 := by rw [terminal,mul_zero,zero_mul,zero_mul]
  have three : B*B*B*T=0 := by rw [mul_assoc (B*B) B T,terminal,mul_zero]
  rw [mul_add,mul_add,one,two,three,add_zero,add_zero]

private theorem inverse_three_return {R : Type*} [Ring R] (P D A U V : R)
    (free : D*U=1) (full : V*(D+A)=1) (terminal : A*U*A*U*A*U*P=0) :
    V*P=(U-U*A*U+U*A*U*A*U)*P := by
  have generated : (D+A)*(U-U*A*U+U*A*U*A*U)*P=P := by
    calc
      _=(D*U)*P+A*U*P-((D*U)*A*U*P+A*U*A*U*P)+
        ((D*U)*A*U*A*U*P+A*U*A*U*A*U*P) := by noncomm_ring
      _=P := by rw [free,terminal]; noncomm_ring
  calc
    _=V*((D+A)*(U-U*A*U+U*A*U*A*U)*P) := by rw [generated]
    _=(V*(D+A))*((U-U*A*U+U*A*U*A*U)*P) := by noncomm_ring
    _=_ := by rw [full,one_mul]

/-- The three words are read from the original C(h) inverse and actual Y(h) on the same field carrier. -/
def jointN2GreenWords (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (h : Field289) : ActualDressedNumberZero.Op :=
  let U:=jointCResolvent p F z h
  let A:=jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h
  U-U*A*U+U*A*U*A*U

/-- The original full N2 Green returns its own three words throughout its source-generated field neighbourhood. -/
theorem actual_joint_N2_resolvent_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    ∀ᶠh : Field289 in 𝓝 0,jointResolvent p F z h*numberTwoProjection=
      jointN2GreenWords p F z h*numberTwoProjection := by
  filter_upwards [actual_joint_free_units_near_zero p F z nonreal,actual_joint_full_units_near_zero p F z nonreal]
    with h free full
  let U:=jointCResolvent p F z h
  let A:=jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h
  have terminal : A*U*A*U*A*U*numberTwoProjection=0 := by
    have computed:=three_step_nilpotent (numberTwoGrade 0) (numberTwoGrade 1) (numberTwoGrade 2) (A*U)
      (inverse_range _ _ _ _ (inverse_preserves p F z h free 0)
        (actual_joint_Y_N2G0_range h (PreparationVacuumYukawaTransport.finiteRetainer p F)))
      (inverse_range _ _ _ _ (inverse_preserves p F z h free 1)
        (actual_joint_Y_N2G1_range h (PreparationVacuumYukawaTransport.finiteRetainer p F)))
      (inverse_terminal _ _ _ (inverse_preserves p F z h free 2)
        (actual_joint_Y_N2G2_zero h (PreparationVacuumYukawaTransport.finiteRetainer p F)))
    simpa only [numberTwoProjection,mul_assoc] using computed
  have free_inverse : (jointCompression p F h-z • (1:ActualDressedNumberZero.Op))*U=1 := by
    unfold U jointCResolvent
    exact Ring.mul_inverse_cancel _ free
  have full_inverse : jointResolvent p F z h*((jointCompression p F h-z • (1:ActualDressedNumberZero.Op))+A)=1 := by
    have original:=Ring.inverse_mul_cancel _ full
    simpa only [A,jointResolvent,jointGenerator,sub_add_eq_add_sub] using original
  simpa only [jointN2GreenWords] using inverse_three_return numberTwoProjection
    (jointCompression p F h-z • (1:ActualDressedNumberZero.Op)) A U (jointResolvent p F z h)
    free_inverse full_inverse terminal

end LowEnergy.GaussComposite.ActualDressedNumberField
