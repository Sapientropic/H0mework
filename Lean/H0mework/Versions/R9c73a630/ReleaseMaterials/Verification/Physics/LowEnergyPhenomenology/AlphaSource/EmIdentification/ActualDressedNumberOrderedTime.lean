import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberInteraction

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberSector
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open FullYSourceCutoffVolterra MeasureTheory
open scoped BigOperators Interval
attribute [local irreducible] actualC actualA numberTwoGrade physicalTime

private theorem integral_zero_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f : ℝ→E→L[ℂ]E) (continuous : Continuous f) (P : E→L[ℂ]E) (t : ℝ)
    (zero : ∀s,f s*P=0) : (∫s in (0:ℝ)..t,f s)*P=0 := by
  let read : (E→L[ℂ]E)→L[ℂ](E→L[ℂ]E):=(ContinuousLinearMap.mul ℂ (E→L[ℂ]E)).flip P
  have paid:=read.intervalIntegral_comp_comm (continuous.intervalIntegrable (μ:=volume) 0 t)
  change (∫s in (0:ℝ)..t,f s*P)=(∫s in (0:ℝ)..t,f s)*P at paid
  simp_rw [zero] at paid
  simpa only [intervalIntegral.integral_zero] using paid.symm

theorem actual_ordered_N2G2_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (high : 0<n) :
    orderedIntegral (actualC p F) (actualA p F) n t*numberTwoGrade 2=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (actualC p F) (actualA p F) n s*interaction (actualC p F) (actualA p F) s)*numberTwoGrade 2=0
    rw [mul_assoc,actual_interaction_N2G2_zero,mul_zero]

theorem actual_ordered_N2G1_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (high : 1<n) :
    orderedIntegral (actualC p F) (actualA p F) n t*numberTwoGrade 1=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (actualC p F) (actualA p F) n s*interaction (actualC p F) (actualA p F) s)*numberTwoGrade 1=0
    rw [mul_assoc,←actual_interaction_N2G1_range p F s,←mul_assoc,←mul_assoc,
      actual_ordered_N2G2_zero p F n s (by omega),zero_mul,zero_mul]

theorem actual_ordered_N2G0_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (high : 2<n) :
    orderedIntegral (actualC p F) (actualA p F) n t*numberTwoGrade 0=0 := by
  cases n with
  | zero=>omega
  | succ n=>
    apply integral_zero_right _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (actualC p F) (actualA p F) n s*interaction (actualC p F) (actualA p F) s)*numberTwoGrade 0=0
    rw [mul_assoc,←actual_interaction_N2G0_range p F s,←mul_assoc,←mul_assoc,
      actual_ordered_N2G1_high_zero p F n s (by omega),zero_mul,zero_mul]

/-- Original homogeneous grade resolutions turn every higher Dyson word into zero on all three N2 grades. -/
theorem actual_prefix_N2_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (high : 2<n) (g : Fin 3) :
    finitePrefix (actualC p F) (actualA p F) n t*numberTwoGrade (g.castLE (by decide))=0 := by
  unfold finitePrefix
  have time:=SourceFiniteUnitary.time_commutes _ _ (actualC_numberTwoGrade p F (g.castLE (by decide))) t
  rw [mul_assoc,←time.eq,←mul_assoc]
  have word : orderedIntegral (actualC p F) (actualA p F) n t*numberTwoGrade (g.castLE (by decide))=0 := by
    fin_cases g
    · exact actual_ordered_N2G0_high_zero p F n t high
    · exact actual_ordered_N2G1_high_zero p F n t (by omega)
    · exact actual_ordered_N2G2_zero p F n t (by omega)
  rw [word,zero_mul]

theorem actual_time_N2_grade_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (g : Fin 3) :
    physicalTime p F t 0*numberTwoGrade (g.castLE (by decide))=
      partialEvolution (actualC p F) (actualA p F) 2 t*numberTwoGrade (g.castLE (by decide)) := by
  rw [actual_time_finitePrefix]
  have truncate (k : ℕ) :
      partialEvolution (actualC p F) (actualA p F) (k+2) t*numberTwoGrade (g.castLE (by decide))=
        partialEvolution (actualC p F) (actualA p F) 2 t*numberTwoGrade (g.castLE (by decide)) := by
    induction k with
    | zero=>rfl
    | succ k ih=>
      rw [show k+1+2=k+2+1 from by omega,partialEvolution,add_mul,
        actual_prefix_N2_high_zero p F (k+2+1) t (by omega) g,add_zero,ih]
  exact truncate 54

end LowEnergy.GaussComposite.ActualDressedNumberSector
