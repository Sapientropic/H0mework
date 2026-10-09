import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeFull

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFieldTime
open GaussCoreHilbert CanonicalGradedSpatialSource GaussComposite.SourceGraph
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumYukawaTransport
open ActualDressedNumberSector ActualDressedNumberField FullYSourceCutoffVolterra MeasureTheory
open PreparationVacuumRawJointFeedback PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumPhysicalNumberOneRead
open CanonicalGradedCurrent PreparationVacuumSourcePreparedResponse ActualDressedSourcePreparation
open scoped BigOperators
attribute [local irreducible] jointCompression jointY numberTwoGrade

private theorem field_C_numberTwoGrade (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (g : Fin 57) : Commute (numberTwoGrade g) (jointCompression p F h) := by
  simpa only [numberTwoGrade] using actual_joint_compression_blocks p F h (2,g)

private theorem interaction_range {R : Type*} [Ring R] [Algebra ℂ R]
    (P Q U V A : R) (QU : Commute Q U) (PV : Commute P V) (range : Q*A*P=A*P) :
    Q*(U*((-Complex.I) • A)*V)*P=U*((-Complex.I) • A)*V*P := by
  have paid : Q*(U*A*V)*P=U*A*V*P := by
    calc
      _=(Q*U)*A*(V*P) := by noncomm_ring
      _=(U*Q)*A*(P*V) := by rw [QU.eq,PV.symm.eq]
      _=U*(Q*A*P)*V := by noncomm_ring
      _=U*A*P*V := by rw [range];noncomm_ring
      _=U*A*V*P := by noncomm_ring [PV.eq]
  simpa only [mul_smul_comm,smul_mul_assoc] using congrArg (fun B : R=>(-Complex.I) • B) paid

private theorem interaction_zero {R : Type*} [Ring R] [Algebra ℂ R]
    (Q U V A : R) (QV : Commute Q V) (zero : A*Q=0) : (U*((-Complex.I) • A)*V)*Q=0 := by
  have paid : (U*A*V)*Q=0 := by
    calc
      _=U*(A*Q)*V := by noncomm_ring [QV.symm.eq]
      _=0 := by rw [zero,mul_zero,zero_mul]
  simpa only [mul_smul_comm,smul_mul_assoc,smul_zero] using congrArg (fun B : R=>(-Complex.I) • B) paid

theorem actual_field_interaction_N2G0_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) (t : ℝ) :
    numberTwoGrade 1*interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*numberTwoGrade 0=
      interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*numberTwoGrade 0 :=
  interaction_range _ _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (field_C_numberTwoGrade p F h 1) t)
    (SourceFiniteUnitary.time_commutes _ _ (field_C_numberTwoGrade p F h 0) (-t))
    (actual_joint_Y_N2G0_range h (finiteRetainer p F))

theorem actual_field_interaction_N2G1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) (t : ℝ) :
    numberTwoGrade 2*interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*numberTwoGrade 1=
      interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*numberTwoGrade 1 :=
  interaction_range _ _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (field_C_numberTwoGrade p F h 2) t)
    (SourceFiniteUnitary.time_commutes _ _ (field_C_numberTwoGrade p F h 1) (-t))
    (actual_joint_Y_N2G1_range h (finiteRetainer p F))

theorem actual_field_interaction_N2G2_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) (t : ℝ) :
    interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*numberTwoGrade 2=0 :=
  interaction_zero _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (field_C_numberTwoGrade p F h 2) (-t))
    (actual_joint_Y_N2G2_zero h (finiteRetainer p F))



private theorem integral_zero_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f : ℝ→E→L[ℂ]E) (continuous : Continuous f) (P : E→L[ℂ]E) (t : ℝ)
    (zero : ∀s,f s*P=0) : (∫s in (0:ℝ)..t,f s)*P=0 := by
  let read : (E→L[ℂ]E)→L[ℂ](E→L[ℂ]E):=(ContinuousLinearMap.mul ℂ (E→L[ℂ]E)).flip P
  have paid:=read.intervalIntegral_comp_comm (continuous.intervalIntegrable (μ:=volume) 0 t)
  change (∫s in (0:ℝ)..t,f s*P)=(∫s in (0:ℝ)..t,f s)*P at paid
  simp_rw [zero] at paid
  simpa only [intervalIntegral.integral_zero] using paid.symm

theorem actual_field_ordered_N2G2_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 0<n) :
    orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*numberTwoGrade 2=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n s*interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) s)*numberTwoGrade 2=0
    rw [mul_assoc,actual_field_interaction_N2G2_zero,mul_zero]

theorem actual_field_ordered_N2G1_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 1<n) :
    orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*numberTwoGrade 1=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n s*interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) s)*numberTwoGrade 1=0
    rw [mul_assoc,←actual_field_interaction_N2G1_range p F h s,←mul_assoc,←mul_assoc,
      actual_field_ordered_N2G2_zero p F h n s (by omega),zero_mul,zero_mul]

theorem actual_field_ordered_N2G0_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 2<n) :
    orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*numberTwoGrade 0=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n s*interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) s)*numberTwoGrade 0=0
    rw [mul_assoc,←actual_field_interaction_N2G0_range p F h s,←mul_assoc,←mul_assoc,
      actual_field_ordered_N2G1_high_zero p F h n s (by omega),zero_mul,zero_mul]

/-- Original homogeneous grade resolutions turn every higher Dyson word into zero on all three N2 grades. -/
theorem actual_field_prefix_N2_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 2<n) (g : Fin 3) :
    finitePrefix (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*numberTwoGrade (g.castLE (by decide))=0 := by
  unfold finitePrefix
  have time:=SourceFiniteUnitary.time_commutes _ _ (field_C_numberTwoGrade p F h (g.castLE (by decide))) t
  rw [mul_assoc,←time.eq,←mul_assoc]
  have word : orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*numberTwoGrade (g.castLE (by decide))=0 := by
    fin_cases g
    · exact actual_field_ordered_N2G0_high_zero p F h n t high
    · exact actual_field_ordered_N2G1_high_zero p F h n t (by omega)
    · exact actual_field_ordered_N2G2_zero p F h n t (by omega)
  rw [word,zero_mul]

theorem actual_field_time_N2_grade_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) (g : Fin 3) :
    physicalTime p F t h*numberTwoGrade (g.castLE (by decide))=
      partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 2 t*numberTwoGrade (g.castLE (by decide)) := by
  rw [actual_field_time_finitePrefix]
  have truncate (k : ℕ) :
      partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) (k+2) t*numberTwoGrade (g.castLE (by decide))=
        partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 2 t*numberTwoGrade (g.castLE (by decide)) := by
    induction k with
    | zero=>rfl
    | succ k ih=>
      rw [show k+1+2=k+2+1 from by omega,partialEvolution,add_mul,
        actual_field_prefix_N2_high_zero p F h (k+2+1) t (by omega) g,add_zero,ih]
  exact truncate 54


theorem actual_field_time_N2_projection_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) : physicalTime p F t h*numberTwoProjection=
      partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 2 t*numberTwoProjection := by
  have zero:=actual_field_time_N2_grade_return p F h t 0
  have one:=actual_field_time_N2_grade_return p F h t 1
  have two:=actual_field_time_N2_grade_return p F h t 2
  have generated:=congrArg₂ (fun A B : H→L[ℂ]H=>A+B)
    (congrArg₂ (fun A B : H→L[ℂ]H=>A+B) zero one) two
  simpa only [numberTwoProjection,mul_add] using! generated

/-- Three original all-field prefixes act on the unchanged norm-one source creation. -/
theorem actual_field_time_created_unit (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t epsilon : ℝ) (precision : 0<epsilon) :
    physicalTime p F t h (sourceDressedUnit epsilon precision)=
      partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 2 t
        (sourceDressedUnit epsilon precision) := by
  have generated:=congrArg (fun A : H→L[ℂ]H=>A (sourceDressedUnit epsilon precision))
    (actual_field_time_N2_projection_return p F h t)
  simpa only [mul_apply_eq_comp,actual_created_unit_N2] using! generated

theorem actual_field_interaction_N1G0_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) :
    sourceExcitedProjection*interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*sourceProjection=
      interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*sourceProjection :=
  interaction_range _ _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (actual_joint_compression_blocks p F h sourceExcitedLabel) t)
    (SourceFiniteUnitary.time_commutes _ _ (actual_joint_compression_blocks p F h sourceLabel) (-t))
    (actual_joint_Y_N1G0_range h (finiteRetainer p F))

theorem actual_field_interaction_N1G1_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) :
    interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) t*sourceExcitedProjection=0 :=
  interaction_zero _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (actual_joint_compression_blocks p F h sourceExcitedLabel) (-t))
    (actual_joint_Y_N1G1_zero h (finiteRetainer p F))

theorem actual_field_ordered_N1G1_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 0<n) :
    orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*sourceExcitedProjection=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n s*
      interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) s)*sourceExcitedProjection=0
    rw [mul_assoc,actual_field_interaction_N1G1_zero,mul_zero]

theorem actual_field_ordered_N1G0_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 1<n) :
    orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*sourceProjection=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (jointCompression p F h) (jointY (finiteRetainer p F) h) n s*
      interaction (jointCompression p F h) (jointY (finiteRetainer p F) h) s)*sourceProjection=0
    rw [mul_assoc,←actual_field_interaction_N1G0_range p F h s,←mul_assoc,←mul_assoc,
      actual_field_ordered_N1G1_zero p F h n s (by omega),zero_mul,zero_mul]

theorem actual_field_prefix_N1G0_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 1<n) :
    finitePrefix (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*sourceProjection=0 := by
  unfold finitePrefix
  have time : Commute sourceProjection (SourceFiniteUnitary.time (jointCompression p F h) t) := by
    simpa only [sourceProjection] using
      SourceFiniteUnitary.time_commutes _ _ (actual_joint_compression_blocks p F h sourceLabel) t
  rw [mul_assoc,←time.eq,←mul_assoc,actual_field_ordered_N1G0_high_zero p F h n t high,zero_mul]

theorem actual_field_prefix_N1G1_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 0<n) :
    finitePrefix (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*sourceExcitedProjection=0 := by
  unfold finitePrefix
  have time : Commute sourceExcitedProjection (SourceFiniteUnitary.time (jointCompression p F h) t) := by
    simpa only [sourceExcitedProjection] using
      SourceFiniteUnitary.time_commutes _ _ (actual_joint_compression_blocks p F h sourceExcitedLabel) t
  rw [mul_assoc,←time.eq,←mul_assoc,actual_field_ordered_N1G1_zero p F h n t high,zero_mul]

theorem actual_field_prefix_N1_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (n : ℕ) (t : ℝ) (high : 1<n) :
    finitePrefix (jointCompression p F h) (jointY (finiteRetainer p F) h) n t*sourceN1Projection=0 := by
  rw [sourceN1Projection,mul_add,actual_field_prefix_N1G0_high_zero p F h n t high,
    actual_field_prefix_N1G1_high_zero p F h n t (by omega),add_zero]

theorem actual_field_time_N1_projection_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) : physicalTime p F t h*sourceN1Projection=
      partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 1 t*sourceN1Projection := by
  rw [actual_field_time_finitePrefix]
  have truncate (k : ℕ) :
      partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) (k+1) t*sourceN1Projection=
        partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 1 t*sourceN1Projection := by
    induction k with
    | zero=>rfl
    | succ k ih=>
      rw [partialEvolution,add_mul,actual_field_prefix_N1_high_zero p F h (k+1+1) t (by omega),add_zero,ih]
  exact truncate 55

/-- Two original all-field prefixes act on the original prepared background. -/
theorem actual_field_time_background (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) (profile : GaussComposite.SourceGraph.Profile) :
    physicalTime p F t h (prepared profile)=
      partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 1 t (prepared profile) := by
  have original:=congrArg (fun A : H→L[ℂ]H=>A (prepared profile)) (actual_field_time_N1_projection_return p F h t)
  simpa only [mul_apply_eq_comp,ActualDressedNumberZero.actual_background_number_one] using original

end LowEnergy.GaussComposite.ActualDressedFieldTime
