import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalBinaryRounding

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalRadii
open PreparationVacuumCentralBudget PreparationVacuumArenaRows
open scoped BigOperators

abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound

-- Python coefficient_exponents uses the maximum of the four clock arrays and
-- the energy array, without the counting factor used by upper_sum.
def upperMaximum (xs : List UpperExponent) : UpperExponent :=
  let nonzero:=xs.filterMap id
  if nonzero=[] then none else some (maximumExponent nonzero)

theorem upperMaximum_mem (xs : List UpperExponent) (e : UpperExponent) (mem : e∈xs) :
    exponentValue e≤ exponentValue (upperMaximum xs) := by
  cases e with
  | none=>exact exponentValue_nonnegative _
  | some e=>
    have present : e∈xs.filterMap id := List.mem_filterMap.mpr ⟨some e,mem,rfl⟩
    have nonempty : xs.filterMap id≠[] := by
      intro empty
      rw [empty] at present
      exact List.not_mem_nil present
    simp only [upperMaximum,if_neg nonempty,exponentValue]
    exact pow_le_pow_right₀ (by norm_num) (maximumExponent_mem _ e present)

def coefficientEnvelope (B : ℕ → Fin 5 → ArrayBound) (k m : ℕ) : UpperExponent :=
  upperMaximum (List.ofFn (fun i : Fin 5=>roundExponent (B k i m)))

theorem coefficientEnvelope_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i m,0 ≤ B k i m) (k m : ℕ) (i : Fin 5) :
    B k i m≤ exponentValue (coefficientEnvelope B k m) :=
  (roundExponent_upper _ (positive k i m)).trans
    (upperMaximum_mem _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

def localizedCutoff (B : ℕ → Fin 5 → ArrayBound) (theta radial : ArrayBound) (k : ℕ) : UpperArray :=
  upperProduct (upperProduct (coefficientEnvelope B k) (fun m=>roundExponent (theta m)))
    (fun m=>roundExponent (radial m))

def stageLargest (cutoff : ℕ → UpperArray) (k : ℕ) : ℕ :=
  maximumExponent (((List.range (k+1)).map (cutoff k)).filterMap id)

def radiusLog (cutoff : ℕ → UpperArray) (k : ℕ) : ℕ :=
  Nat.rec 0 (fun order previous=>max (previous+1) (order+1+stageLargest cutoff (order+1))) k

def originalRadius (cutoff : ℕ → UpperArray) (k : ℕ) : ℝ :=
  (2 : ℝ)^radiusLog cutoff k

@[simp] theorem radiusLog_zero (cutoff : ℕ → UpperArray) : radiusLog cutoff 0=0 := rfl

theorem radiusLog_succ (cutoff : ℕ → UpperArray) (k : ℕ) :
    radiusLog cutoff (k+1)=max (radiusLog cutoff k+1) (k+1+stageLargest cutoff (k+1)) := rfl

theorem radiusLog_increases (cutoff : ℕ → UpperArray) (k : ℕ) :
    radiusLog cutoff k+1≤ radiusLog cutoff (k+1) := by rw [radiusLog_succ];exact le_max_left _ _

theorem radiusLog_order (cutoff : ℕ → UpperArray) (k : ℕ) : k≤ radiusLog cutoff k := by
  induction k with
  | zero=>exact le_refl 0
  | succ k ih=>exact (Nat.add_le_add_right ih 1).trans (radiusLog_increases cutoff k)

theorem radiusLog_largest (cutoff : ℕ → UpperArray) (k : ℕ) (positive : 0<k) :
    k+stageLargest cutoff k≤ radiusLog cutoff k := by
  cases k with
  | zero=>omega
  | succ k=>rw [radiusLog_succ];exact le_max_right _ _

theorem stageLargest_mem (cutoff : ℕ → UpperArray) (k m e : ℕ)
    (order : m≤ k) (actual : cutoff k m=some e) : e≤ stageLargest cutoff k := by
  apply maximumExponent_mem
  apply List.mem_filterMap.mpr
  refine ⟨some e,?_,rfl⟩
  apply List.mem_map.mpr
  exact ⟨m,List.mem_range.mpr (by omega),actual⟩

theorem originalRadius_positive (cutoff : ℕ → UpperArray) (k : ℕ) :
    0<originalRadius cutoff k := by unfold originalRadius;positivity

theorem originalRadius_order (cutoff : ℕ → UpperArray) (k : ℕ) :
    (2 : ℝ)^k≤ originalRadius cutoff k :=
  pow_le_pow_right₀ (by norm_num) (radiusLog_order cutoff k)

theorem originalRadius_doubles (cutoff : ℕ → UpperArray) (k : ℕ) :
    2*originalRadius cutoff k≤ originalRadius cutoff (k+1) := by
  have next : (2 : ℝ)^(radiusLog cutoff k+1)≤(2 : ℝ)^radiusLog cutoff (k+1) :=
    pow_le_pow_right₀ (by norm_num) (radiusLog_increases cutoff k)
  simpa only [originalRadius,pow_succ,mul_comm] using next

theorem originalRadius_dyadic_bound (cutoff : ℕ → UpperArray) (k m : ℕ)
    (positive : 0<k) (order : m≤ k) :
    exponentValue (cutoff k m)≤ originalRadius cutoff k*(1/2 : ℝ)^k := by
  cases actual : cutoff k m with
  | none=>rw [exponentValue];exact mul_nonneg (originalRadius_positive cutoff k).le (by positivity)
  | some e=>
    have largest:=stageLargest_mem cutoff k m e order actual
    have paid:=radiusLog_largest cutoff k positive
    have relation : e+k≤ radiusLog cutoff k := by omega
    have budget : (2 : ℝ)^(e+k)≤(2 : ℝ)^radiusLog cutoff k :=
      pow_le_pow_right₀ (by norm_num) relation
    change (2 : ℝ)^e≤(2 : ℝ)^radiusLog cutoff k*(1/2 : ℝ)^k
    rw [show (1/2 : ℝ)=(2 : ℝ)⁻¹ by norm_num,inv_pow,←div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0<(2 : ℝ)^k)).mpr
    simpa only [←pow_add] using budget

end LowEnergy.PreparationVacuumOriginalRadii
