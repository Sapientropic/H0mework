import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedN1SlopePrice

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedGradedPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumYukawaTransport
open ActualDressedNumberField ActualDressedNumberSector ActualDressedNumberZero
open FullYSourceCutoffVolterra MeasureTheory
open scoped Topology Interval
attribute [local irreducible] jointCompression jointY jointGenerator jointCurrent numberTwoGrade
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _

def upperOne : H→L[ℂ]H := numberTwoGrade 1 + numberTwoGrade 2
def upperTwo : H→L[ℂ]H := numberTwoGrade 2
attribute [local irreducible] upperOne upperTwo

private theorem upper_algebra {R : Type*} [Ring R] (P Q S A : R)
    (qq : Q*Q=Q) (ss : S*S=S) (qs : Q*S=0) (sq : S*Q=0)
    (first : Q*A*P=A*P) (second : S*A*Q=A*Q) (last : A*S=0) :
    (Q+S)*A*(P+Q+S)=A*(P+Q+S) ∧ S*A*(Q+S)=A*(Q+S) := by
  have qfirst : (Q+S)*A*P=A*P := by
    calc
      _=(Q+S)*(Q*A*P) := by rw [first]; noncomm_ring
      _=((Q+S)*Q)*A*P := by noncomm_ring
      _=Q*A*P := by rw [add_mul,qq,sq,add_zero]
      _=A*P := first
  have qsecond : (Q+S)*A*Q=A*Q := by
    calc
      _=(Q+S)*(S*A*Q) := by rw [second]; noncomm_ring
      _=((Q+S)*S)*A*Q := by noncomm_ring
      _=S*A*Q := by rw [add_mul,qs,ss,zero_add]
      _=A*Q := second
  constructor
  · rw [mul_add,mul_add,qfirst,qsecond,mul_assoc,last,mul_zero,add_zero,
      mul_add,mul_add,last,add_zero]
  · rw [mul_add,second,mul_assoc,last,mul_zero,add_zero,mul_add,last,add_zero]

private theorem shifted_range {R : Type*} [Ring R] [Algebra ℂ R] (P C A : R) (z : ℂ)
    (idem : P*P=P) (blocks : Commute P C) (range : P*A*P=A*P) :
    P*(C+A-z • 1)*P=(C+A-z • 1)*P := by
  have c : P*C*P=C*P := by rw [blocks.eq,mul_assoc,idem]
  have scalar : P*(z • (1:R))*P=(z • (1:R))*P := by
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,idem]
  simp only [mul_sub,sub_mul,mul_add,add_mul,c,range,scalar]

private theorem super_range {R : Type*} [Ring R] (P Q A : R)
    (accept : P*Q=Q) (range : Q*A*P=A*P) : P*A*P=A*P := by
  calc
    _=P*(Q*A*P) := by rw [range]; rw [mul_assoc]
    _=(P*Q)*A*P := by simp only [mul_assoc]
    _=Q*A*P := by rw [accept]
    _=A*P := range

private theorem terminal_range {R : Type*} [Ring R] (P A : R) (zero : A*P=0) : P*A*P=A*P := by
  rw [mul_assoc,zero,mul_zero]

private theorem upper_square : upperOne*upperOne=upperOne ∧ upperTwo*upperTwo=upperTwo := by
  simp [upperOne,upperTwo,numberTwoGrade,add_mul,mul_add,
    NativeHistoryGrade.projection_product,Prod.ext_iff,Fin.ext_iff]

theorem actual_joint_Y_upper (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    upperOne*jointY (finiteRetainer p F) h*numberTwoProjection=jointY (finiteRetainer p F) h*numberTwoProjection ∧
    upperTwo*jointY (finiteRetainer p F) h*upperOne=jointY (finiteRetainer p F) h*upperOne := by
  have prod (i j : Fin 57) : numberTwoGrade i*numberTwoGrade j=
      if i=j then numberTwoGrade i else 0 := by
    simp [numberTwoGrade,NativeHistoryGrade.projection_product,Prod.ext_iff]
  simpa only [upperOne,upperTwo,numberTwoProjection] using upper_algebra
    (numberTwoGrade 0) (numberTwoGrade 1) (numberTwoGrade 2) (jointY (finiteRetainer p F) h)
    (by simp [prod]) (by simp [prod]) (by simp [prod]) (by simp [prod])
    (actual_joint_Y_N2G0_range h _) (actual_joint_Y_N2G1_range h _) (actual_joint_Y_N2G2_zero h _)

theorem actual_interaction_upper (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    upperOne*interaction (PreparationVacuumPhysicalHalfAxis.actualC p F) (PreparationVacuumPhysicalHalfAxis.actualA p F) t*numberTwoProjection=
      interaction (PreparationVacuumPhysicalHalfAxis.actualC p F) (PreparationVacuumPhysicalHalfAxis.actualA p F) t*numberTwoProjection ∧
    upperTwo*interaction (PreparationVacuumPhysicalHalfAxis.actualC p F) (PreparationVacuumPhysicalHalfAxis.actualA p F) t*upperOne=
      interaction (PreparationVacuumPhysicalHalfAxis.actualC p F) (PreparationVacuumPhysicalHalfAxis.actualA p F) t*upperOne := by
  have prod (i j : Fin 57) : numberTwoGrade i*numberTwoGrade j=
      if i=j then numberTwoGrade i else 0 := by
    simp [numberTwoGrade,NativeHistoryGrade.projection_product,Prod.ext_iff]
  simpa only [upperOne,upperTwo,numberTwoProjection] using upper_algebra
    (numberTwoGrade 0) (numberTwoGrade 1) (numberTwoGrade 2)
    (interaction (PreparationVacuumPhysicalHalfAxis.actualC p F) (PreparationVacuumPhysicalHalfAxis.actualA p F) t)
    (by simp [prod]) (by simp [prod]) (by simp [prod]) (by simp [prod])
    (actual_interaction_N2G0_range p F t) (actual_interaction_N2G1_range p F t) (actual_interaction_N2G2_zero p F t)

theorem actual_joint_C_upper (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    Commute upperOne (jointCompression p F h) ∧ Commute upperTwo (jointCompression p F h) := by
  simpa only [upperOne,upperTwo,numberTwoGrade] using
    And.intro ((actual_joint_compression_blocks p F h (2,1)).add_left
      (actual_joint_compression_blocks p F h (2,2))) (actual_joint_compression_blocks p F h (2,2))

theorem actual_joint_generator_upper (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (h : Field289) :
    upperOne*jointGenerator p F z h*upperOne=jointGenerator p F z h*upperOne ∧
    upperTwo*jointGenerator p F z h*upperTwo=jointGenerator p F z h*upperTwo := by
  have y:=actual_joint_Y_upper p F h
  have y1 : upperOne*jointY (finiteRetainer p F) h*upperOne=jointY (finiteRetainer p F) h*upperOne := by
    have accept : upperOne*upperTwo=upperTwo := by
      simp [upperOne,upperTwo,numberTwoGrade,add_mul,NativeHistoryGrade.projection_product,
        Prod.ext_iff,Fin.ext_iff]
    exact super_range _ _ _ accept y.2
  have y2 : jointY (finiteRetainer p F) h*upperTwo=0 := by
    simpa only [upperTwo] using actual_joint_Y_N2G2_zero h (finiteRetainer p F)
  unfold jointGenerator
  exact ⟨shifted_range _ _ _ z upper_square.1 (actual_joint_C_upper p F h).1 y1,
    shifted_range _ _ _ z upper_square.2 (actual_joint_C_upper p F h).2 (terminal_range _ _ y2)⟩

theorem actual_joint_current_upper (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (force : Field289) :
    upperOne*(jointCurrent p F z 0 force)*upperOne=(jointCurrent p F z 0 force)*upperOne ∧
    upperTwo*(jointCurrent p F z 0 force)*upperTwo=(jointCurrent p F z 0 force)*upperTwo := by
  have source:=(jointGenerator_C2 p F z).differentiableAt (by norm_num) |>.hasFDerivAt
  have derivative:=source.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  constructor
  · have left:=(derivative.const_mul upperOne).mul_const upperOne
    have right:=derivative.mul_const upperOne
    simpa only [jointCurrent] using (left.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun r=>((actual_joint_generator_upper p F z (r • force)).1).symm))).unique right
  · have left:=(derivative.const_mul upperTwo).mul_const upperTwo
    have right:=derivative.mul_const upperTwo
    simpa only [jointCurrent] using (left.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun r=>((actual_joint_generator_upper p F z (r • force)).2).symm))).unique right

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem integral_range (f : ℝ→E→L[ℂ]E) (ct : Continuous f)
    (P Q : E→L[ℂ]E) (t : ℝ) (range : ∀s,Q*f s*P=f s*P) :
    Q*(∫s in (0:ℝ)..t,f s)*P=(∫s in (0:ℝ)..t,f s)*P := by
  let right := (ContinuousLinearMap.mul ℂ (E→L[ℂ]E)).flip P
  let both := (ContinuousLinearMap.mul ℂ (E→L[ℂ]E) Q).comp right
  have hr:=right.intervalIntegral_comp_comm (ct.intervalIntegrable (μ:=volume) 0 t)
  have hb:=both.intervalIntegral_comp_comm (ct.intervalIntegrable (μ:=volume) 0 t)
  change (∫s in (0:ℝ)..t,f s*P)=(∫s in (0:ℝ)..t,f s)*P at hr
  change (∫s in (0:ℝ)..t,Q*(f s*P))=Q*((∫s in (0:ℝ)..t,f s)*P) at hb
  simp_rw [←mul_assoc,range] at hb
  exact hb.symm.trans hr

theorem ordered_one_range (C A P Q : E→L[ℂ]E)
    (shift : ∀s,Q*interaction C A s*P=interaction C A s*P) (t : ℝ) :
    Q*orderedIntegral C A 1 t*P=orderedIntegral C A 1 t*P := by
  simpa only [orderedIntegral,one_mul] using
    integral_range (interaction C A) (interaction_continuous C A) P Q t shift

theorem prefix_one_range (C A P Q : E→L[ℂ]E) (comm : Commute P C)
    (shift : ∀s,Q*interaction C A s*P=interaction C A s*P) (t : ℝ) :
    Q*finitePrefix C A 1 t*P=finitePrefix C A 1 t*P := by
  have ordered := ordered_one_range C A P Q shift t
  have time:=(SourceFiniteUnitary.time_commutes C P comm t).eq
  simp only [finitePrefix]
  calc
    _=(Q*orderedIntegral C A 1 t*P)*SourceFiniteUnitary.time C t := by noncomm_ring [time]
    _=orderedIntegral C A 1 t*P*SourceFiniteUnitary.time C t := by rw [ordered]
    _=_ := by noncomm_ring [time]

theorem prefix_two_range (C A P Q R : E→L[ℂ]E) (comm : Commute P C)
    (shift : ∀s,Q*interaction C A s*P=interaction C A s*P)
    (next : ∀s,R*orderedIntegral C A 1 s*Q=orderedIntegral C A 1 s*Q) (t : ℝ) :
    R*finitePrefix C A 2 t*P=finitePrefix C A 2 t*P := by
  have ordered : R*orderedIntegral C A 2 t*P=orderedIntegral C A 2 t*P := by
    apply integral_range _ ((orderedIntegral_continuous C A 1).mul (interaction_continuous C A))
    intro s
    calc
      _=R*orderedIntegral C A 1 s*(Q*interaction C A s*P) := by rw [shift s]; noncomm_ring
      _=(R*orderedIntegral C A 1 s*Q)*interaction C A s*P := by noncomm_ring
      _=orderedIntegral C A 1 s*(Q*interaction C A s*P) := by rw [next s]; noncomm_ring
      _=_ := by rw [shift s]; rfl
  have time:=(SourceFiniteUnitary.time_commutes C P comm t).eq
  simp only [finitePrefix]
  calc
    _=(R*orderedIntegral C A 2 t*P)*SourceFiniteUnitary.time C t := by noncomm_ring [time]
    _=orderedIntegral C A 2 t*P*SourceFiniteUnitary.time C t := by rw [ordered]
    _=_ := by noncomm_ring [time]
end Generic
end LowEnergy.GaussComposite.ActualDressedGradedPrice
