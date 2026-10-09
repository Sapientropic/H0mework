import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalFullHalfAxis
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationDampedWeightedTime

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalTailPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumDampedFieldPerturbation
open scoped BigOperators Topology Matrix InnerProductSpace
abbrev Index:=GaussUnitaryHistory.Index
abbrev Op:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] actualA actualC actualGrowth jointGenerator jointCurrent physicalTime timeSlope

/-- Every atom is the norm of the actual uncut retainer operator. -/
def factorialBudget (p : PhysicalMomentum) (F : Index) (eta : ℝ) : ℝ:=
  ∑j∈Finset.range 57,(j.factorial:ℝ)*(‖actualA p F‖/eta)^j

theorem factorialBudget_nonnegative (p : PhysicalMomentum) (F : Index) (eta : ℝ) (positive : 0<eta) :
    0≤factorialBudget p F eta :=by
  unfold factorialBudget
  apply Finset.sum_nonneg
  intro j _
  positivity

theorem actualGrowth_envelope (p : PhysicalMomentum) (F : Index) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    actualGrowth p F t≤factorialBudget p F eta*Real.exp (eta*t) :=by
  unfold actualGrowth factorialBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  exact polynomial_term_envelope ‖actualA p F‖ eta t (norm_nonneg _) positive future j

theorem actualTime_envelope (p : PhysicalMomentum) (F : Index) (eta t : ℝ) (positive : 0<eta) :
    ‖physicalTime p F t 0‖≤factorialBudget p F eta*Real.exp (eta*|t|) :=
  (actual_time_bound p F t).trans (actualGrowth_envelope p F eta |t| positive (abs_nonneg t))

def variationBudget (p : PhysicalMomentum) (F : Index) (B : Op) (eta : ℝ) : ℝ:=
  (factorialBudget p F eta)^2*‖B‖/eta

theorem variationBudget_nonnegative (p : PhysicalMomentum) (F : Index) (B : Op) (eta : ℝ)
    (positive : 0<eta) : 0≤variationBudget p F B eta :=by
  unfold variationBudget
  positivity

theorem actualVariation_envelope (p : PhysicalMomentum) (F : Index) (B : Op) (eta t : ℝ)
    (positive : 0<eta) :
    ‖CanonicalGradedVariation.variation (jointGenerator p F 0 0) B t‖≤
      variationBudget p F B eta*Real.exp (3*eta*|t|) :=by
  have timeBound:=actualGrowth_envelope p F eta |t| positive (abs_nonneg t)
  have argument : |t|≤eta⁻¹*Real.exp (eta*|t|):=by
    have h:=polynomial_term_envelope 1 eta |t| zero_le_one positive (abs_nonneg t) 1
    simpa only [mul_one,Nat.factorial_one,Nat.cast_one,pow_one,one_div,one_mul] using h
  have budget:=factorialBudget_nonnegative p F eta positive
  have multiplication : ‖CanonicalGradedVariation.variation (jointGenerator p F 0 0) B t‖≤
      (eta⁻¹*Real.exp (eta*|t|))*(factorialBudget p F eta*Real.exp (eta*|t|))^2*‖B‖ :=by
    refine (actual_variation_bound p F B t).trans ?_
    unfold actualVariationBound
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg B)
    exact mul_le_mul argument (pow_le_pow_left₀ (actualGrowth_nonnegative p F _ (abs_nonneg t)) timeBound 2)
      (sq_nonneg _) (by positivity)
  have exponential : Real.exp (eta*|t|)*Real.exp (eta*|t|)^2=Real.exp (3*eta*|t|):=by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  refine multiplication.trans_eq ?_
  unfold variationBudget
  rw [mul_pow,div_eq_mul_inv]
  calc
    _=(factorialBudget p F eta^2*‖B‖*eta⁻¹)*(Real.exp (eta*|t|)*Real.exp (eta*|t|)^2):=by ac_rfl
    _=_:=by rw [exponential]

theorem actualTime_future (p : PhysicalMomentum) (F : Index) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖physicalTime p F t 0‖≤factorialBudget p F eta*Real.exp (eta*t) :=by
  simpa only [abs_of_nonneg future] using actualTime_envelope p F eta t positive

theorem actualTime_past (p : PhysicalMomentum) (F : Index) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖physicalTime p F (-t) 0‖≤factorialBudget p F eta*Real.exp (eta*t) :=by
  simpa only [abs_neg,abs_of_nonneg future] using actualTime_envelope p F eta (-t) positive

theorem actualSlope_future (force : Field289) (p : PhysicalMomentum) (F : Index) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖timeSlope force p F t‖≤variationBudget p F (jointCurrent p F 0 0 force) eta*Real.exp (3*eta*t) :=by
  simpa only [timeSlope,abs_of_nonneg future] using actualVariation_envelope p F (jointCurrent p F 0 0 force) eta t positive

theorem actualSlope_past (force : Field289) (p : PhysicalMomentum) (F : Index) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖timeSlope force p F (-t)‖≤variationBudget p F (jointCurrent p F 0 0 force) eta*Real.exp (3*eta*t) :=by
  simpa only [timeSlope,abs_neg,abs_of_nonneg future] using actualVariation_envelope p F (jointCurrent p F 0 0 force) eta (-t) positive

end LowEnergy.PreparationVacuumPhysicalTailPrice
