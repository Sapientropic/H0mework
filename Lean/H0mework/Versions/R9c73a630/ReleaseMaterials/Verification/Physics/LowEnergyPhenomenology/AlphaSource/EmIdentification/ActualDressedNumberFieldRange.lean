import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberJointField

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberField
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open ActualDressedNumberSector ActualDressedNumberZero
open scoped Topology InnerProductSpace
attribute [local irreducible] numberTwoGrade numberTwoProjection jointCompression jointY jointGenerator

private theorem number_two_accepts (g : Fin 57) (supported : g=0 ∨ g=1 ∨ g=2) :
    numberTwoProjection*numberTwoGrade g=numberTwoGrade g := by
  rcases supported with rfl|rfl|rfl
  all_goals simp [numberTwoProjection,numberTwoGrade,add_mul,
    NativeHistoryGrade.projection_product,Prod.ext_iff,Fin.ext_iff]

private theorem projection_expansion : numberTwoProjection=numberTwoGrade 0+numberTwoGrade 1+numberTwoGrade 2 := by
  rw [numberTwoProjection]

private theorem projection_sum_square {R : Type*} [Ring R] (P Q S T : R)
    (expansion : P=Q+S+T) (q : P*Q=Q) (s : P*S=S) (t : P*T=T) : P*P=P := by
  calc
    _=P*(Q+S+T) := congrArg (fun X : R=>P*X) expansion
    _=Q+S+T := by rw [mul_add,mul_add,q,s,t]
    _=P := expansion.symm

private theorem sum_range {R : Type*} [Ring R] (P Q S T A : R)
    (expansion : P=Q+S+T) (s : P*S=S) (t : P*T=T)
    (first : S*A*Q=A*Q) (second : T*A*S=A*S) (terminal : A*T=0) : P*A*P=A*P := by
  have qrange : P*A*Q=A*Q := by
    calc
      _=P*(A*Q) := by rw [mul_assoc]
      _=P*(S*A*Q) := by rw [first]
      _=(P*S)*A*Q := by noncomm_ring
      _=S*A*Q := by rw [s]
      _=A*Q := first
  have srange : P*A*S=A*S := by
    calc
      _=P*(A*S) := by rw [mul_assoc]
      _=P*(T*A*S) := by rw [second]
      _=(P*T)*A*S := by noncomm_ring
      _=T*A*S := by rw [t]
      _=A*S := second
  have trange : P*A*T=A*T := by rw [mul_assoc,terminal,mul_zero]
  calc
    _=P*A*(Q+S+T) := congrArg (fun X : R=>P*A*X) expansion
    _=A*Q+A*S+A*T := by rw [mul_add,mul_add,qrange,srange,trange]
    _=A*(Q+S+T) := by rw [mul_add,mul_add]
    _=A*P := congrArg (fun X : R=>A*X) expansion.symm

/-- The original all-field compression keeps the actual complete N2 carrier. -/
theorem actual_joint_C_number_two (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    Commute numberTwoProjection (jointCompression p F h) := by
  simpa only [numberTwoProjection,numberTwoGrade] using
    ((actual_joint_compression_blocks p F h (2,0)).add_left (actual_joint_compression_blocks p F h (2,1))).add_left
      (actual_joint_compression_blocks p F h (2,2))

theorem actual_joint_Y_number_two (h : Field289) (phi : CanonicalGradedSpatial.Localizer) :
    numberTwoProjection*jointY phi h*numberTwoProjection=jointY phi h*numberTwoProjection :=
  sum_range _ _ _ _ _ projection_expansion (number_two_accepts 1 (Or.inr (Or.inl rfl)))
    (number_two_accepts 2 (Or.inr (Or.inr rfl))) (actual_joint_Y_N2G0_range h phi)
    (actual_joint_Y_N2G1_range h phi) (actual_joint_Y_N2G2_zero h phi)

private theorem shifted_range {R : Type*} [Ring R] [Algebra ℂ R] (P C A : R) (z : ℂ)
    (idem : P*P=P) (blocks : Commute P C) (range : P*A*P=A*P) :
    P*(C+A-z • 1)*P=(C+A-z • 1)*P := by
  have c : P*C*P=C*P := by rw [blocks.eq,mul_assoc,idem]
  have scalar : P*(z • (1:R))*P=(z • (1:R))*P := by
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,idem]
  simp only [mul_sub,sub_mul,mul_add,add_mul,c,range,scalar]

/-- Every original source field value retains the same N2 generator range, including the original spectral shift. -/
theorem actual_joint_generator_number_two (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (h : Field289) : numberTwoProjection*jointGenerator p F z h*numberTwoProjection=
      jointGenerator p F z h*numberTwoProjection := by
  unfold jointGenerator
  exact shifted_range _ _ _ z actual_number_two_square (actual_joint_C_number_two p F h)
    (actual_joint_Y_number_two h (PreparationVacuumYukawaTransport.finiteRetainer p F))

local instance fieldRealAlgebra : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- Differentiate the actual all-field range, rather than the zero-field read identity. -/
theorem actual_joint_current_number_two (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (force : Field289) :
    numberTwoProjection*(jointCurrent p F z 0 force)*numberTwoProjection=
      (jointCurrent p F z 0 force)*numberTwoProjection := by
  have source:=(jointGenerator_C2 p F z).differentiableAt (by norm_num) |>.hasFDerivAt
  have derivative:=source.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have left:=(derivative.const_mul numberTwoProjection).mul_const numberTwoProjection
  have right:=derivative.mul_const numberTwoProjection
  simpa only [jointCurrent] using (left.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun r=>(actual_joint_generator_number_two p F z (r • force)).symm))).unique right

end LowEnergy.GaussComposite.ActualDressedNumberField
