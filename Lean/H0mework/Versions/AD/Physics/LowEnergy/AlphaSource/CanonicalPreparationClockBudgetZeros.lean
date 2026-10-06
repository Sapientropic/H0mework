import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCentralArrays
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationReciprocalActual
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalFloor

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockBudget
open PreparationVacuumCentralBudget PreparationVacuumEngineBudget PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumClockPole
open PreparationVacuumClockGuard PreparationVacuumReciprocalBudget PreparationVacuumEngineSmooth
open PreparationActualFactor PreparationScalarCoordinates PreparationPhaseSource PreparationPhaseBounds
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff GaussNativeEnergy
open scoped BigOperators ContDiff Topology

/-- The only primitive scalar derivative inputs of the original implicit clock algorithm. -/
structure ATInputs (x : SourcePhase) (N : ℕ) where
  A : ArrayBound
  T : ArrayBound
  A_nonnegative : ∀ n,0 ≤ A n
  T_nonnegative : ∀ n,0 ≤ T n
  A_bound : FiniteBound actualA N A x
  T_bound : FiniteBound actualT N T x

def actualRatio : RealSymbol := fun x => (1/2 : ℝ)*actualT x*(actualA x)⁻¹

def aInverseArray {x : SourcePhase} {N : ℕ} (input : ATInputs x N) : ArrayBound := inverseBudget input.A 15

def ratioArray {x : SourcePhase} {N : ℕ} (input : ATInputs x N) (n : ℕ) : ℝ :=
  (1/2 : ℝ)*productArray input.T (aInverseArray input) n

def clockZero {x : SourcePhase} {N : ℕ} (input : ATInputs x N) : ℝ := max 1 (ratioArray input 0)
def inverseClockZero {x : SourcePhase} {N : ℕ} (input : ATInputs x N) : ℝ := max 1 (30*input.A 0)

theorem sourceUnit_admitted (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) : (z,WithLp.toLp 2 u)∈poleDomain := by
  refine ⟨actual_closed_phase_cone z u zbox ubox unit,?_⟩
  have determinant := actual_clockMatrix_det_j15 z u zbox ubox
  have positive : 0<(clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).det := by linarith
  simpa only [sourceM,actualT,actualS,nativePhase,clockMatrix] using positive.ne'

theorem actual_A_inverse_zero (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) : |(actualA (z,WithLp.toLp 2 u))⁻¹| ≤ 15 := by
  have floor : (1/15 : ℝ)<actualA (z,WithLp.toLp 2 u) := actual_closed_phase_A_floor z u zbox ubox unit
  have positive : 0<actualA (z,WithLp.toLp 2 u) := by linarith
  rw [abs_of_pos (inv_pos.mpr positive)]
  have estimate := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/15) floor.le
  simpa using estimate

theorem actualRatio_smooth : SmoothSymbol actualRatio := by
  intro x hx
  exact ((contDiffAt_const.mul (actualT_smooth x hx.1.1)).mul
    ((actualA_smooth x hx.1.1).inv hx.1.2.1.ne')).contDiffWithinAt

theorem actualRatio_square (x : SourcePhase) (hx : x∈poleDomain) : actualC x^2=actualRatio x := by
  have relation : 2*actualA x*actualC x^2=actualT x := C_equation hx.1
  have a : actualA x≠0 := hx.1.2.1.ne'
  unfold actualRatio
  field_simp [a]
  nlinarith [relation]

theorem ratioArray_nonnegative {x : SourcePhase} {N : ℕ} (input : ATInputs x N) (n : ℕ) : 0 ≤ ratioArray input n :=
  mul_nonneg (by norm_num) (productArray_nonnegative _ _ input.T_nonnegative
    (inverseBudget_nonnegative _ _ (by norm_num) input.A_nonnegative) n)

theorem ratioArray_zero {x : SourcePhase} {N : ℕ} (input : ATInputs x N) :
    ratioArray input 0=(1/2 : ℝ)*input.T 0*15 := by
  simp [ratioArray,productArray,aInverseArray,inverseBudget_zero]
  ring

theorem actual_ratio_zero (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N) :
    |actualRatio (z,WithLp.toLp 2 u)| ≤ ratioArray input 0 := by
  have tb : |actualT (z,WithLp.toLp 2 u)| ≤ input.T 0 := by
    simpa [jet] using input.T_bound 0 (Nat.zero_le N) (fun i => Fin.elim0 i)
  have ai := actual_A_inverse_zero z u zbox ubox unit
  rw [abs_inv] at ai
  rw [actualRatio,ratioArray_zero,abs_mul,abs_mul]
  norm_num
  exact mul_le_mul (mul_le_mul_of_nonneg_left tb (by norm_num)) ai (inv_nonneg.mpr (abs_nonneg _)) (mul_nonneg (by norm_num) (input.T_nonnegative 0))

theorem actual_clock_zero (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N) :
    |actualC (z,WithLp.toLp 2 u)| ≤ clockZero input := by
  have hx := sourceUnit_admitted z u zbox ubox unit
  have positive : 0<actualC (z,WithLp.toLp 2 u) := C_positive hx.1
  have squared : actualC (z,WithLp.toLp 2 u)^2 ≤ ratioArray input 0 := by
    rw [actualRatio_square _ hx]
    exact (le_abs_self _).trans (actual_ratio_zero z u zbox ubox unit N input)
  rw [abs_of_pos positive]
  by_cases low : actualC (z,WithLp.toLp 2 u) ≤ 1
  · exact low.trans (le_max_left _ _)
  · have self : actualC (z,WithLp.toLp 2 u) ≤ actualC (z,WithLp.toLp 2 u)^2 := by nlinarith
    exact (self.trans squared).trans (le_max_right _ _)

theorem actual_inverseClock_zero (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N) :
    |(actualC (z,WithLp.toLp 2 u))⁻¹| ≤ inverseClockZero input := by
  let x : SourcePhase := (z,WithLp.toLp 2 u)
  have hx := sourceUnit_admitted z u zbox ubox unit
  have positive : 0<actualC x := C_positive hx.1
  have tpositive : 0<actualT x := hx.1.2.2
  have ab : actualA x ≤ input.A 0 := by
    apply (le_abs_self _).trans
    simpa [jet,x] using input.A_bound 0 (Nat.zero_le N) (fun i => Fin.elim0 i)
  have floor : (1/15 : ℝ) ≤ actualT x := by
    have original := actual_T_j15 z u zbox ubox
    change (1/15 : ℝ) ≤ T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
    linarith
  have relation : 2*actualA x*actualC x^2=actualT x := C_equation hx.1
  have square : ((actualC x)⁻¹)^2=2*actualA x/actualT x := by
    field_simp [positive.ne',tpositive.ne']
    nlinarith [relation]
  have estimate : 2*actualA x/actualT x ≤ 30*input.A 0 := by
    apply (div_le_iff₀ tpositive).mpr
    have product := mul_le_mul_of_nonneg_left floor
      (show 0 ≤ 30*input.A 0 from mul_nonneg (by norm_num) (input.A_nonnegative 0))
    nlinarith [ab]
  have one : 1 ≤ inverseClockZero input := le_max_left _ _
  have original : 30*input.A 0 ≤ inverseClockZero input := le_max_right _ _
  have bound : ((actualC x)⁻¹)^2 ≤ inverseClockZero input := by rw [square]; exact estimate.trans original
  change |(actualC x)⁻¹| ≤ _
  rw [abs_of_pos (inv_pos.mpr positive)]
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) one]

end LowEnergy.PreparationVacuumClockBudget
