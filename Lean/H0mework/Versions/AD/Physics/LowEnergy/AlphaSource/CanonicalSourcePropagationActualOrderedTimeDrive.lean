import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedMeromorphicResponse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationTimeDependentFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPropagationPencil PreparationVacuumFieldPerturbation
open PreparationVacuumRawJointFeedback PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalTailPrice
open SourceFiniteUnitary CanonicalGradedVariation PreparationVacuumSourcePreparedResponse
open MeasureTheory Filter
open scoped Topology BigOperators Interval
abbrev Op:=PreparationVacuumPropagationPencil.Op
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator jointCurrent physicalTime leftCurrent rightCurrent

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev End:=E→L[ℂ] E
local instance : NormedAlgebra ℝ (End (E:=E)):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (End (E:=E)):=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem left_time_derivative (C : End (E:=E)) (t : ℝ) :
    HasDerivAt (time C) (((-Complex.I) • C)*time C t) t:=by
  have h:=time_operator_derivative C t
  rw [←((time_commutes C C (Commute.refl C) t).smul_left (-Complex.I)).eq] at h
  exact h

private def primalPrimitive (C : End (E:=E)) (D : ℝ→End (E:=E)) (t : ℝ) : End (E:=E):=
  ∫s in (0:ℝ)..t,time C (-s)*D s*time C s

private def primalDrive (C : End (E:=E)) (D : ℝ→End (E:=E)) (t : ℝ) : End (E:=E):=
  time C t*primalPrimitive C D t

private theorem primalDrive_derivative (C : End (E:=E)) (D : ℝ→End (E:=E))
    (continuousD : Continuous D) (t : ℝ) :
    HasDerivAt (primalDrive C D)
      (((-Complex.I) • C)*primalDrive C D t+D t*time C t) t:=by
  have integrand : Continuous (fun s : ℝ=>time C (-s)*D s*time C s):=
    (((time_continuous C).comp continuous_neg).mul continuousD).mul (time_continuous C)
  have primitive : HasDerivAt (primalPrimitive C D) (time C (-t)*D t*time C t) t:=
    (integrand.integral_hasStrictDerivAt 0 t).hasDerivAt
  have derivative:=(left_time_derivative C t).mul primitive
  have inverse : time C t*time C (-t)=1:=by rw [←SourceFiniteUnitary.time_add,add_neg_cancel,SourceFiniteUnitary.time_zero]
  convert! derivative using 1
  unfold primalDrive
  simp only [mul_assoc]
  rw [←mul_assoc (time C t) (time C (-t)),inverse,one_mul]

private def dualPrimitive (C : End (E:=E)) (D : ℝ→End (E:=E)) (t : ℝ) : End (E:=E):=
  ∫s in (0:ℝ)..t,time C (-s)*(-D s)*time C s

private def dualDrive (C : End (E:=E)) (D : ℝ→End (E:=E)) (t : ℝ) : End (E:=E):=
  dualPrimitive C D t*time C (-t)

private theorem dualDrive_derivative (C : End (E:=E)) (D : ℝ→End (E:=E))
    (continuousD : Continuous D) (t : ℝ) :
    HasDerivAt (dualDrive C D)
      (dualDrive C D t*(-((-Complex.I) • C))+time C (-t)*(-D t)) t:=by
  have integrand : Continuous (fun s : ℝ=>time C (-s)*(-D s)*time C s):=
    (((time_continuous C).comp continuous_neg).mul continuousD.neg).mul (time_continuous C)
  have primitive : HasDerivAt (dualPrimitive C D) (time C (-t)*(-D t)*time C t) t:=
    (integrand.integral_hasStrictDerivAt 0 t).hasDerivAt
  have reverse:=(time_operator_derivative C (-t)).scomp t ((hasDerivAt_id t).neg)
  have derivative:=primitive.mul reverse
  have inverse : time C t*time C (-t)=1:=by rw [←SourceFiniteUnitary.time_add,add_neg_cancel,SourceFiniteUnitary.time_zero]
  convert! derivative using 1
  unfold dualDrive
  simp only [Function.comp_apply,Function.comp_def,neg_one_smul,mul_neg,neg_mul,mul_assoc,inverse,mul_one]
  abel

end Calculus

/-- The instantaneous generator variation comes from the actual common field derivative. -/
theorem physicalDrive_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ→Field289) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>(-Complex.I) • jointGenerator p F 0 (r • history t))
      ((-Complex.I) • jointCurrent p F 0 0 (history t)) 0:=by
  have h:=(jointGenerator_C2 p F 0).differentiableAt (by norm_num) |>.hasFDerivAt
  have generated:=h.comp_hasDerivAt_of_eq 0 (fieldRay_derivative (history t) 0) (by simp)
  unfold jointCurrent
  exact generated.const_smul (-Complex.I)

private theorem current_history_continuous (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ→Field289) (continuousHistory : Continuous history) :
    Continuous (fun t : ℝ=>(-Complex.I) • jointCurrent p F 0 0 (history t)):=
  ((jointCurrent p F 0 0).continuous.comp continuousHistory).const_smul (-Complex.I)

def orderedPrimal (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) : Op:=
  primalDrive (jointGenerator q.p q.F 0 0) (fun s=>rightCurrent q (history s)) t

def orderedDual (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) : Op:=
  dualDrive (jointGenerator (q.p+q.k) q.F 0 0) (fun s=>leftCurrent q (history s)) t

theorem orderedPrimal_initial (q : PhysicalResponsePoint) (history : ℝ→Field289) :
    orderedPrimal q history 0=0:=by
  simp only [orderedPrimal,primalDrive,primalPrimitive,intervalIntegral.integral_same,mul_zero]

theorem orderedDual_initial (q : PhysicalResponsePoint) (history : ℝ→Field289) :
    orderedDual q history 0=0:=by
  simp only [orderedDual,dualDrive,dualPrimitive,intervalIntegral.integral_same,zero_mul]

theorem orderedPrimal_derivative (q : PhysicalResponsePoint) (history : ℝ→Field289)
    (continuousHistory : Continuous history) (t : ℝ) :
    HasDerivAt (orderedPrimal q history)
      (rightGenerator q*orderedPrimal q history t+rightCurrent q (history t)*physicalTime q.p q.F t 0) t:=by
  have actual:=primalDrive_derivative (jointGenerator q.p q.F 0 0)
    (fun s=>rightCurrent q (history s)) (by simpa only [rightCurrent] using current_history_continuous q.p q.F history continuousHistory) t
  unfold orderedPrimal rightGenerator physicalTime
  exact actual

theorem orderedDual_derivative (q : PhysicalResponsePoint) (history : ℝ→Field289)
    (continuousHistory : Continuous history) (t : ℝ) :
    HasDerivAt (orderedDual q history)
      (orderedDual q history t*(-leftGenerator q)+physicalTime (q.p+q.k) q.F (-t) 0*(-leftCurrent q (history t))) t:=by
  have actual:=dualDrive_derivative (jointGenerator (q.p+q.k) q.F 0 0)
    (fun s=>leftCurrent q (history s)) (by simpa only [leftCurrent] using current_history_continuous (q.p+q.k) q.F history continuousHistory) t
  unfold orderedDual leftGenerator physicalTime
  exact actual

end LowEnergy.SourcePropagationTimeDependentFeedback
