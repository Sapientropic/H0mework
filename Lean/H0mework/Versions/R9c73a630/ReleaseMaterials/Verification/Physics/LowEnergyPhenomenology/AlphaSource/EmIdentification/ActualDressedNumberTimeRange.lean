import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberResolvent

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberZero
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse
open ActualDressedSourcePreparation ActualDressedNumberSector
open FullYSourceCutoffVolterra
attribute [local irreducible] numberTwoGrade numberTwoProjection actualA actualC physicalTime

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

theorem actual_number_two_square : numberTwoProjection*numberTwoProjection=numberTwoProjection :=
  projection_sum_square _ _ _ _ projection_expansion
    (number_two_accepts 0 (Or.inl rfl)) (number_two_accepts 1 (Or.inr (Or.inl rfl)))
    (number_two_accepts 2 (Or.inr (Or.inr rfl)))

theorem actualC_number_two (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute numberTwoProjection (actualC p F) :=
  by simpa only [numberTwoProjection] using
    ((actualC_numberTwoGrade p F 0).add_left (actualC_numberTwoGrade p F 1)).add_left (actualC_numberTwoGrade p F 2)

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

theorem actualA_number_two_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    numberTwoProjection*actualA p F*numberTwoProjection=actualA p F*numberTwoProjection :=
  sum_range _ _ _ _ _ projection_expansion (number_two_accepts 1 (Or.inr (Or.inl rfl)))
    (number_two_accepts 2 (Or.inr (Or.inr rfl))) (actualA_N2G0_range p F) (actualA_N2G1_range p F)
    (actualA_N2G2_zero p F)

private theorem generator_range {R : Type*} [Ring R] (P C A : R)
    (idem : P*P=P) (blocks : Commute P C) (range : P*A*P=A*P) : P*(C+A)*P=(C+A)*P := by
  simp only [mul_add,add_mul]
  rw [range]
  exact congrArg (fun X=>X+A*P) (calc
    P*C*P=C*(P*P) := by rw [blocks.eq,mul_assoc]
    _=C*P := by rw [idem])

local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem exp_range {B : Type*} [NormedRing B] [NormedAlgebra ℚ B] [CompleteSpace B]
    (P X : B) (idem : P*P=P) (range : P*X*P=X*P) : P*NormedSpace.exp X*P=NormedSpace.exp X*P := by
  have source : SemiconjBy P (P*X*P) X := by
    change P*(P*X*P)=X*P
    calc
      _=(P*P)*X*P := by noncomm_ring
      _=P*X*P := by rw [idem]
      _=X*P := range
  have generated:=source.exp_right.eq
  calc
    _=P*(NormedSpace.exp X*P) := by rw [mul_assoc]
    _=P*(P*NormedSpace.exp (P*X*P)) := by rw [←generated]
    _=(P*P)*NormedSpace.exp (P*X*P) := (mul_assoc P P _).symm
    _=P*NormedSpace.exp (P*X*P) := by rw [idem]
    _=NormedSpace.exp X*P := generated

private theorem scalar_range {B : Type*} [Ring B] [Algebra ℂ B] [Algebra ℝ B]
    (P X : B) (c : ℂ) (t : ℝ) (range : P*X*P=X*P) : P*(t • (c • X))*P=(t • (c • X))*P := by
  simp only [mul_smul_comm,smul_mul_assoc]
  exact congrArg (fun Y : B=>t • (c • Y)) range

/-- The original full time stays inside the computed N2 carrier for every physical time. -/
theorem actual_time_number_two_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    numberTwoProjection*physicalTime p F t 0*numberTwoProjection=physicalTime p F t 0*numberTwoProjection := by
  have generator : numberTwoProjection*jointGenerator p F 0 0*numberTwoProjection=
      jointGenerator p F 0 0*numberTwoProjection := by
    simpa only [actualGenerator_source] using
      generator_range numberTwoProjection (actualC p F) (actualA p F) actual_number_two_square
        (actualC_number_two p F) (actualA_number_two_range p F)
  unfold physicalTime SourceFiniteUnitary.time
  apply exp_range _ _ actual_number_two_square
  exact scalar_range (B:=Op) _ _ (-Complex.I) t generator

/-- The generated N2 range lets the actual right Green and time use their three original words together. -/
theorem actual_created_resolvent_time_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (t epsilon : ℝ) (precision : 0<epsilon) :
    jointResolvent p F z 0 (physicalTime p F t 0 (sourceDressedUnit epsilon precision))=
      (CanonicalPhysicalResolvent.finiteResolvent p F z-
        CanonicalPhysicalResolvent.finiteResolvent p F z*actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z+
        CanonicalPhysicalResolvent.finiteResolvent p F z*actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z*
          actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z)
        (partialEvolution (actualC p F) (actualA p F) 2 t (sourceDressedUnit epsilon precision)) := by
  have time_range:=congrArg (fun A : Op=>A (sourceDressedUnit epsilon precision)) (actual_time_number_two_range p F t)
  simp only [mul_apply_eq_comp,actual_created_unit_N2] at time_range
  have returned:=congrArg (fun A : Op=>A (physicalTime p F t 0 (sourceDressedUnit epsilon precision)))
    (actual_resolvent_N2_return p F z nonreal)
  simp only [mul_apply_eq_comp] at returned
  rw [time_range] at returned
  simpa only [actual_time_created_unit] using returned

end LowEnergy.GaussComposite.ActualDressedNumberZero
