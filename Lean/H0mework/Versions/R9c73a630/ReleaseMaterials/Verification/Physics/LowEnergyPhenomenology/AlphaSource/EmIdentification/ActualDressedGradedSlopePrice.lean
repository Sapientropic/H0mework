import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.FiniteFlagVariationPrice

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedGradedPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open ActualDressedNumberField ActualDressedNumberSector ActualDressedNumberZero ActualDressedPreparedPrice
open ActualDressedSourcePreparation FullYSourceCutoffVolterra
open ActualDressedN1Price PreparationVacuumPhysicalN1WardCollapse
open scoped Topology
attribute [local irreducible] numberTwoGrade numberTwoProjection upperOne upperTwo physicalTime timeSlope
  jointGenerator jointCurrent actualC actualA sourceDressedUnit

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
private theorem prefix_zero (C A P : E→L[ℂ]E) (comm : Commute P C) (n : ℕ) (t : ℝ)
    (zero : orderedIntegral C A n t*P=0) : finitePrefix C A n t*P=0 := by
  have time:=(SourceFiniteUnitary.time_commutes C P comm t).eq
  simp only [finitePrefix]
  rw [mul_assoc,←time,←mul_assoc,zero,zero_mul]
end Generic

private theorem shorten {R : Type*} [Ring R] (T U A B P Q : R)
    (first : T*P=(U+A+B)*P) (second : T*Q=(U+A+B)*Q)
    (bp : B*P=0) (bq : B*Q=0) (aq : A*Q=0) :
    T*(P+Q)=(U+A)*(P+Q) ∧ T*Q=U*Q := by
  constructor
  · simp only [mul_add,first,second,add_mul,bp,bq,aq,add_zero]
  · rw [second,add_mul,add_mul,aq,bq,add_zero,add_zero]

theorem actual_time_upper_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    physicalTime p F t 0*upperOne=partialEvolution (actualC p F) (actualA p F) 1 t*upperOne ∧
    physicalTime p F t 0*upperTwo=SourceFiniteUnitary.time (actualC p F) t*upperTwo := by
  have zero21:=prefix_zero _ _ _ (actualC_numberTwoGrade p F 1) 2 t
    (actual_ordered_N2G1_high_zero p F 2 t (by norm_num))
  have zero22:=prefix_zero _ _ _ (actualC_numberTwoGrade p F 2) 2 t
    (actual_ordered_N2G2_zero p F 2 t (by norm_num))
  have zero12:=prefix_zero _ _ _ (actualC_numberTwoGrade p F 2) 1 t
    (actual_ordered_N2G2_zero p F 1 t (by norm_num))
  have r1:=actual_time_N2_grade_return p F t (1:Fin 3)
  have r2:=actual_time_N2_grade_return p F t (2:Fin 3)
  have one : (1:Fin 3).castLE (by decide)=(1:Fin 57) := by decide
  have two : (2:Fin 3).castLE (by decide)=(2:Fin 57) := by decide
  rw [one] at r1
  rw [two] at r2
  simpa only [upperOne,upperTwo,partialEvolution] using shorten
    (physicalTime p F t 0) (SourceFiniteUnitary.time (actualC p F) t)
    (finitePrefix (actualC p F) (actualA p F) 1 t) (finitePrefix (actualC p F) (actualA p F) 2 t)
    (numberTwoGrade 1) (numberTwoGrade 2)
    (by simpa only [partialEvolution,Nat.reduceAdd] using r1)
    (by simpa only [partialEvolution,Nat.reduceAdd] using r2) zero21 zero22 zero12

private theorem upper_time_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (s T : ℝ) (st : |s| ≤T) (v : H) :
    (upperOne v=v→‖physicalTime p F s 0 v‖≤(1+T*‖actualA p F‖)*‖v‖) ∧
    (upperTwo v=v→‖physicalTime p F s 0 v‖≤‖v‖) := by
  have ret:=actual_time_upper_return p F s
  constructor
  · intro sector
    have eq:=congrArg (fun A : H→L[ℂ]H=>A v) ret.1
    simp only [mul_apply_eq_comp,sector] at eq
    have price:=((partialEvolution (actualC p F) (actualA p F) 1 s).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (partialEvolution_bound _ _ (actualC_symmetric p F) 1 s) (norm_nonneg v))
    have poly : (∑ j ∈ Finset.range (1+1),(|s| *‖actualA p F‖)^j)=1+|s| *‖actualA p F‖ := by
      simp [Finset.sum_range_succ]
    exact (congrArg norm eq).le.trans ((price.trans_eq (by rw [poly])).trans
      (mul_le_mul_of_nonneg_right (add_le_add_right
        (mul_le_mul_of_nonneg_right st (norm_nonneg _)) 1) (norm_nonneg v)))
  · intro sector
    have eq:=congrArg (fun A : H→L[ℂ]H=>A v) ret.2
    simp only [mul_apply_eq_comp,sector] at eq
    exact (congrArg norm eq).le.trans_eq (SourceFiniteUnitary.time_norm _ (actualC_symmetric p F) s v)

theorem actual_timeSlope_N2_cubic_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) (v : H) (sector : numberTwoProjection v=v) :
    ‖timeSlope force p F t v‖ ≤ |t| *‖jointCurrent p F 0 0 force‖*
      (1+2*(|t| *‖actualA p F‖)+3*(|t| *‖actualA p F‖)^2)*‖v‖ := by
  have first := actual_interaction_upper p F
  have prefix1 := prefix_one_range (actualC p F) (actualA p F) numberTwoProjection upperOne
    (actualC_number_two p F) (fun s=>(first s).1)
  have prefix2 := prefix_two_range (actualC p F) (actualA p F) numberTwoProjection upperOne upperTwo
    (actualC_number_two p F) (fun s=>(first s).1)
    (ordered_one_range _ _ _ _ (fun s=>(first s).2))
  have current:=actual_joint_current_upper p F 0 force
  have ret : ∀s x,numberTwoProjection x=x→SourceFiniteUnitary.time (jointGenerator p F 0 0) s x=
      partialEvolution (actualC p F) (actualA p F) 2 s x := by
    intro s x hx
    simpa only [physicalTime] using actual_time_N2_return p F s x hx
  have price0 : ∀s,|s| ≤|t|→∀x,numberTwoProjection x=x→
      ‖SourceFiniteUnitary.time (jointGenerator p F 0 0) s x‖≤
        (1+|t| *‖actualA p F‖+(|t| *‖actualA p F‖)^2)*‖x‖ := by
    intro s hs x hx
    have h:=(actual_time_N2_price p F s x hx).trans
      (mul_le_mul_of_nonneg_right (occupationPrice_mono 2 _ _ _ (norm_nonneg _) (abs_nonneg s) hs) (norm_nonneg x))
    simpa only [physicalTime,occupationPrice,Finset.sum_range_succ,Finset.sum_range_zero,
      zero_add,pow_zero,pow_one,Nat.reduceAdd] using h
  have price1 : ∀s,|s| ≤|t|→∀x,upperOne x=x→
      ‖SourceFiniteUnitary.time (jointGenerator p F 0 0) s x‖≤(1+|t| *‖actualA p F‖)*‖x‖ := by
    intro s hs x hx
    simpa only [physicalTime] using (upper_time_price p F s |t| hs x).1 hx
  have price2 : ∀s,|s| ≤|t|→∀x,upperTwo x=x→
      ‖SourceFiniteUnitary.time (jointGenerator p F 0 0) s x‖≤‖x‖ := by
    intro s hs x hx
    simpa only [physicalTime] using (upper_time_price p F s |t| hs x).2 hx
  simpa only [timeSlope] using finite_flag_variation_price (jointGenerator p F 0 0) (actualC p F)
    (actualA p F) (jointCurrent p F 0 0 force) numberTwoProjection upperOne upperTwo
    (actualC_symmetric p F) (actualC_number_two p F) ret prefix1 prefix2
    (actual_joint_current_number_two p F 0 force) current.1 current.2 t price0 price1 price2 v sector

theorem actual_created_timeSlope_cubic_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t epsilon : ℝ) (precision : 0<epsilon) :
    ‖timeSlope force p F t (sourceDressedUnit epsilon precision)‖ ≤ |t| *‖jointCurrent p F 0 0 force‖*
      (1+2*(|t| *‖actualA p F‖)+3*(|t| *‖actualA p F‖)^2) := by
  simpa only [source_dressed_unit_norm,mul_one] using actual_timeSlope_N2_cubic_price p F force t
    (sourceDressedUnit epsilon precision) (actual_created_unit_N2 epsilon precision)

private theorem cubic_growth (a j v t : ℝ) (ha : 0≤a) (hj : 0≤j) (hv : 0≤v) (ht : 0≤t) :
    t*j*(1+2*(t*a)+3*(t*a)^2)*v ≤ (3*j*(1+a)^2*v)*(1+t)^3 := by
  have x : 0≤t*a := mul_nonneg ht ha
  have b : 1+t*a≤(1+a)*(1+t) := by nlinarith
  have poly : 1+2*(t*a)+3*(t*a)^2≤3*(1+t*a)^2 := by nlinarith
  have square := pow_le_pow_left₀ (by positivity : 0≤1+t*a) b 2
  calc
    _≤((1+t)*j)*(3*((1+a)*(1+t))^2)*v := by
      apply mul_le_mul_of_nonneg_right _ hv
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hj)
        (poly.trans (mul_le_mul_of_nonneg_left square (by norm_num))) (by positivity) (by positivity)
    _=_ := by ring

theorem actual_timeSlope_N2_cubic_growth (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (v : H) (sector : numberTwoProjection v=v) (t : ℝ) :
    ‖timeSlope force p F t v‖ ≤
      (3*‖jointCurrent p F 0 0 force‖*(1+‖actualA p F‖)^2*‖v‖)*(1+|t|)^3 :=
  (actual_timeSlope_N2_cubic_price p F force t v sector).trans
    (cubic_growth _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (abs_nonneg t))

private theorem n1_cubic_growth (a j v t : ℝ) (ha : 0≤a) (hj : 0≤j) (hv : 0≤v) (ht : 0≤t) :
    t*j*(occupationPrice 1 a t)^2*v ≤ (3*j*(1+a)^2*v)*(1+t)^3 := by
  have square : (occupationPrice 1 a t)^2≤1+2*(t*a)+3*(t*a)^2 := by
    simp only [occupationPrice,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one]
    nlinarith [sq_nonneg (t*a)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left square (mul_nonneg ht hj)) hv).trans
    (cubic_growth a j v t ha hj hv ht)

theorem actual_timeSlope_N1_cubic_growth (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (v : H) (sector : sourceN1Projection v=v) (t : ℝ) :
    ‖timeSlope force p F t v‖ ≤
      (3*‖jointCurrent p F 0 0 force‖*(1+‖actualA p F‖)^2*‖v‖)*(1+|t|)^3 :=
  (actual_timeSlope_N1_price p F force t v sector).trans
    (n1_cubic_growth _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (abs_nonneg t))
end LowEnergy.GaussComposite.ActualDressedGradedPrice
