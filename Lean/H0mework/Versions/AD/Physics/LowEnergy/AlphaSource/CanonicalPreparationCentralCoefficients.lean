import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCentralPolynomials
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationReciprocalActual
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGInverseEntries

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCentralBudget
open PreparationVacuumDAGCoefficient PreparationVacuumEngineBudget PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumEngineSmooth
open PreparationVacuumReciprocalBudget PreparationVacuumClockGuard PreparationVacuumClockPole
open PreparationActualFactor PreparationScalarCoordinates PreparationPhaseSource
open PreparationVacuumEnergyTail PreparationVacuumEngineSource
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff GaussNativeEnergy
open scoped BigOperators ContDiff Topology Matrix

def fieldArrays (C S : ArrayBound) (i : CentralVariable) : ArrayBound :=
  if i=0 then C else if i=1 then (fun n => 3*S n) else S

/-- Only the original seven finite primitive jets and the original A zero-order responsibility. -/
structure PrimitiveInputs (x : SourcePhase) (N : ℕ) where
  clock : ArrayBound
  spatial : ArrayBound
  clock_nonnegative : ∀ n,0 ≤ clock n
  spatial_nonnegative : ∀ n,0 ≤ spatial n
  fields : ∀ i,FiniteBound (fieldFunction i) N (fieldArrays clock spatial i) x
  A0 : ℝ
  actualA_zero : actualA x ≤ A0

def qArray {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) (n : ℕ) : ℝ :=
  3*input.spatial n+input.spatial n

def detArray {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) (n : ℕ) : ℝ :=
  6*powerArray (qArray input) 3 n

def clockInverseZero {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) : ℝ := max 1 (30*input.A0)

def inverseArrays {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) (i : Fin 3) : ArrayBound :=
  if i=0 then inverseBudget input.clock (clockInverseZero input) else
  if i=1 then sourceTInverseBudget (fun n => 3*input.spatial n) else sourceDetInverseBudget (detArray input)

def sourceCoefficientArray {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N)
    (c : NormalizedCoefficient) : ArrayBound :=
  coefficientArray (fieldArrays input.clock input.spatial) (inverseArrays input) c

theorem fieldArrays_nonnegative {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) (i : CentralVariable) (n : ℕ) :
    0 ≤ fieldArrays input.clock input.spatial i n := by
  unfold fieldArrays
  split_ifs
  · exact input.clock_nonnegative n
  · exact mul_nonneg (by norm_num) (input.spatial_nonnegative n)
  · exact input.spatial_nonnegative n

theorem qArray_nonnegative {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) (n : ℕ) : 0 ≤ qArray input n := by
  unfold qArray
  exact add_nonneg (mul_nonneg (by norm_num) (input.spatial_nonnegative n)) (input.spatial_nonnegative n)

theorem detArray_nonnegative {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) (n : ℕ) : 0 ≤ detArray input n :=
  mul_nonneg (by norm_num) (powerArray_nonnegative (qArray input) (qArray_nonnegative input) 3 n)

def qFields : Matrix (Fin 3) (Fin 3) RealSymbol :=
  !![fieldFunction 1-fieldFunction 2,-fieldFunction 4,-fieldFunction 5;
     -fieldFunction 4,fieldFunction 1-fieldFunction 3,-fieldFunction 6;
     -fieldFunction 5,-fieldFunction 6,fieldFunction 2+fieldFunction 3]

theorem sourceQ_fields (i j : Fin 3) : (fun x => sourceM x i j)=qFields i j := by
  funext x
  have native := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) (centralQ_source x).symm
  fin_cases i <;> fin_cases j <;>
    simpa [qFields,centralQ,evalAt,fieldFunction,sourceVariables,Matrix.map_apply] using native

theorem finite_Q (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain) (input : PrimitiveInputs x N) (i j : Fin 3) :
    FiniteBound (fun y => sourceM y i j) N (qArray input) x := by
  have t : FiniteBound (fieldFunction 1) N (fun n => 3*input.spatial n) x := by
    simpa [fieldArrays] using! input.fields 1
  have spatial (i : CentralVariable) (h0 : i≠0) (h1 : i≠1) :
      FiniteBound (fieldFunction i) N input.spatial x := by simpa [fieldArrays,h0,h1] using input.fields i
  have difference (k : CentralVariable) (h0 : k≠0) (h1 : k≠1) :
      FiniteBound (fieldFunction 1-fieldFunction k) N (qArray input) x :=
    finite_sub _ _ (fieldFunction_smooth 1) (fieldFunction_smooth k) _ _ N x hx t (spatial k h0 h1)
  have negative (k : CentralVariable) (h0 : k≠0) (h1 : k≠1) :
      FiniteBound (-fieldFunction k) N (qArray input) x := by
    apply finite_dominate _ input.spatial _ N x
      (finite_neg _ (fieldFunction_smooth k) input.spatial N x hx (spatial k h0 h1))
    intro n
    unfold qArray
    linarith [input.spatial_nonnegative n]
  have last : FiniteBound (fieldFunction 2+fieldFunction 3) N (qArray input) x := by
    apply finite_dominate _ (fun n => input.spatial n+input.spatial n) _ N x
      (finite_add _ _ (fieldFunction_smooth 2) (fieldFunction_smooth 3) _ _ N x hx
        (spatial 2 (by decide) (by decide)) (spatial 3 (by decide) (by decide)))
    intro n
    unfold qArray
    linarith [input.spatial_nonnegative n]
  rw [sourceQ_fields]
  fin_cases i <;> fin_cases j
  · exact difference 2 (by decide) (by decide)
  · exact negative 4 (by decide) (by decide)
  · exact negative 5 (by decide) (by decide)
  · exact negative 4 (by decide) (by decide)
  · exact difference 3 (by decide) (by decide)
  · exact negative 6 (by decide) (by decide)
  · exact negative 5 (by decide) (by decide)
  · exact negative 6 (by decide) (by decide)
  · exact last

/-- Exactly determinant_bound(Q,3)=3! * Q.power(3), over the same actual source determinant. -/
theorem finite_det (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain) (input : PrimitiveInputs x N) :
    FiniteBound sourceDet N (detArray input) x := by
  let term (s : Equiv.Perm (Fin 3)) : RealSymbol := fun y =>
    (Equiv.Perm.sign s : ℝ)*(∏ i : Fin 3,sourceM y (s i) i)
  have smooth (s : Equiv.Perm (Fin 3)) : SmoothSymbol (fun y => ∏ i : Fin 3,sourceM y (s i) i) := by
    intro y hy
    exact (contDiffAt_prod (fun i _ => sourceM_entry_smooth y hy.1.1 (s i) i)).contDiffWithinAt
  have bound (s : Equiv.Perm (Fin 3)) : FiniteBound (term s) N (powerArray (qArray input) 3) x := by
    have product := finite_common_product (qArray input) (qArray_nonnegative input) N x hx 3
      (fun i y => sourceM y (s i) i) (fun i y hy => (sourceM_entry_smooth y hy.1.1 (s i) i).contDiffWithinAt)
      (fun i => finite_Q N x hx input (s i) i)
    have result := finite_scale (Equiv.Perm.sign s : ℝ) _ (smooth s) _ N x hx product
    have signAbsolute : |(Equiv.Perm.sign s : ℝ)|=1 := by exact_mod_cast Equiv.Perm.sign_abs s
    simpa [term,signAbsolute] using result
  have result := finite_sum Finset.univ term (fun s _ => contDiffOn_const.mul (smooth s))
    (fun _ => powerArray (qArray input) 3) N x hx (fun s _ => bound s)
  have source : sourceDet=(fun y => ∑ s : Equiv.Perm (Fin 3),term s y) := by
    funext y
    exact Matrix.det_apply' (sourceM y)
  rw [source]
  intro m hm w
  have value := result m hm w
  simpa [detArray,Fintype.card_perm,Nat.factorial] using value

private theorem unit_admitted (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|  ≤  sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|  ≤  sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) : (z,WithLp.toLp 2 u)∈poleDomain := by
  refine ⟨actual_closed_phase_cone z u zbox ubox unit,?_⟩
  have determinant := actual_clockMatrix_det_j15 z u zbox ubox
  have positive : 0<(clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).det := by linarith
  simpa only [sourceM,actualT,actualS,nativePhase,clockMatrix] using positive.ne'

theorem clock_inverse_zero (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain) (input : PrimitiveInputs x N)
    (Tlower : (1/15 : ℝ) ≤ actualT x) : |(actualC x)⁻¹| ≤ clockInverseZero input := by
  have cpositive : 0<actualC x := C_positive hx.1
  have tpositive : 0<actualT x := hx.1.2.2
  have apositive : 0<actualA x := hx.1.2.1
  have a0positive : 0 ≤ input.A0 := apositive.le.trans input.actualA_zero
  have relation : 2*actualA x*actualC x^2=actualT x := C_equation hx.1
  have square : ((actualC x)⁻¹)^2=2*actualA x/actualT x := by
    field_simp [cpositive.ne',tpositive.ne']
    nlinarith [relation]
  have estimate : 2*actualA x/actualT x ≤ 30*input.A0 := by
    apply (div_le_iff₀ tpositive).mpr
    have product := mul_le_mul_of_nonneg_left Tlower (show 0 ≤ 30*input.A0 by positivity)
    nlinarith [input.actualA_zero]
  have one : 1 ≤ clockInverseZero input := le_max_left _ _
  have original : 30*input.A0 ≤ clockInverseZero input := le_max_right _ _
  have sqbound : ((actualC x)⁻¹)^2 ≤ clockInverseZero input := by rw [square]; exact estimate.trans original
  rw [abs_of_pos (inv_pos.mpr cpositive)]
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) one]

theorem inverseArrays_nonnegative {x : SourcePhase} {N : ℕ} (input : PrimitiveInputs x N) (i : Fin 3) (n : ℕ) :
    0 ≤ inverseArrays input i n := by
  unfold inverseArrays
  split_ifs
  · exact inverseBudget_nonnegative _ _ (le_trans (by norm_num) (le_max_left _ _)) input.clock_nonnegative n
  · exact inverseBudget_nonnegative _ _ (by norm_num) (fun m => mul_nonneg (by norm_num) (input.spatial_nonnegative m)) n
  · exact inverseBudget_nonnegative _ _ (by norm_num) (detArray_nonnegative input) n

theorem actual_inverse_fields (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|  ≤  sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|  ≤  sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (i : Fin 3) : FiniteBound (fun y => (poleFunction i y)⁻¹) N (inverseArrays input i) (z,WithLp.toLp 2 u) := by
  have hx := unit_admitted z u zbox ubox unit
  fin_cases i
  · have Tlower : (1/15 : ℝ) ≤ actualT (z,WithLp.toLp 2 u) := by
      have floor := actual_T_j15 z u zbox ubox
      change (1/15 : ℝ) ≤ T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
      linarith
    have cb : FiniteBound actualC N input.clock (z,WithLp.toLp 2 u) := by
      simpa [fieldFunction,sourceVariables,fieldArrays] using! input.fields 0
    intro m hm w
    simpa [inverseArrays,poleFunction] using! primitive_inverse_canonical_budget 0 _ hx input.clock N
      (clockInverseZero input) (le_trans (by norm_num) (le_max_left _ _)) input.clock_nonnegative
      (clock_inverse_zero N _ hx input Tlower) cb m hm w
  · have tb : FiniteBound actualT N (fun n => 3*input.spatial n) (z,WithLp.toLp 2 u) := by
      simpa [fieldFunction,sourceVariables,fieldArrays] using! input.fields 1
    intro m hm w
    simpa [inverseArrays,poleFunction] using actual_T_inverse_budget z u zbox ubox unit _ N
      (fun n => mul_nonneg (by norm_num) (input.spatial_nonnegative n)) tb m hm w
  · intro m hm w
    simpa [inverseArrays,poleFunction] using actual_det_inverse_budget z u zbox ubox unit _ N
      (detArray_nonnegative input) (finite_det N _ hx input) m hm w

/-- The original coefficient algorithm returns finite budgets for the same normalized source function. -/
theorem actual_coefficient_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|  ≤  sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|  ≤  sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (c : NormalizedCoefficient) :
    FiniteBound (coefficientValue c) N (sourceCoefficientArray input c) (z,WithLp.toLp 2 u) :=
  finite_coefficient _ _ (fieldArrays_nonnegative input) (inverseArrays_nonnegative input) N _
    (unit_admitted z u zbox ubox unit) input.fields (actual_inverse_fields z u zbox ubox unit N input) c

theorem actual_inverseCoefficient_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|  ≤  sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|  ≤  sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (a b : Fin 4) : FiniteBound (fun y => (principalForceJacobian y)⁻¹ a b) N
      (sourceCoefficientArray input (inverseCoefficient a b)) (z,WithLp.toLp 2 u) := by
  have hx := unit_admitted z u zbox ubox unit
  intro m hm w
  have germ : coefficientValue (inverseCoefficient a b)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun y => (principalForceJacobian y)⁻¹ a b) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact inverseCoefficient_native a b y hy
  have read := (germ.iteratedFDeriv ℝ m).eq_of_nhds
  have result := actual_coefficient_budget z u zbox ubox unit N input (inverseCoefficient a b) m hm w
  simpa only [jet,read] using result

theorem actual_principalCoefficient_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|  ≤  sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|  ≤  sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (i : Fin 13) : FiniteBound (engineSource 0 i) N
      (sourceCoefficientArray input (principalCoefficient i)) (z,WithLp.toLp 2 u) := by
  have same : coefficientValue (principalCoefficient i)=engineSource 0 i := funext (principalCoefficient_native i)
  simpa only [same] using actual_coefficient_budget z u zbox ubox unit N input (principalCoefficient i)

end LowEnergy.PreparationVacuumCentralBudget
