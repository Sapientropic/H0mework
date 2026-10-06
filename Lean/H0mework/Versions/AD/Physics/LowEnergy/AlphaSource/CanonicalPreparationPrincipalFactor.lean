import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativePrincipal

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace LowEnergy.PreparationActualFactor
open GaussNativeEnergy GaussHistoryHilbert GaussCoreDifferential GaussNativeForm
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open scoped BigOperators ContDiff Topology

theorem principal_shift_line (z : SourceCoordinateSlice) (p : Cotangent) (n s : ℝ)
    (i : Fin 3) :
    timelikePrincipal z p n (Pi.single i s) = n * A z p +
      (n^2 * T z p - s^2 * S z p i i) / (2*n*(n^2-s^2)) := by
  fin_cases i <;> simp [timelikePrincipal,Pi.single_apply,pow_two] <;> ring

theorem principal_shift_force (z : SourceCoordinateSlice) (p : Cotangent)
    (n : ℝ) (nonzero : n ≠ 0) (i : Fin 3) :
    HasDerivAt (fun s => timelikePrincipal z p n (Pi.single i s)) 0 0 := by
  have square : HasDerivAt (fun s : ℝ => s^2) 0 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).pow 2
  have numerator := (hasDerivAt_const (0 : ℝ) (n^2*T z p)).sub (square.mul_const (S z p i i))
  have denominator := (hasDerivAt_const (0 : ℝ) (2*n)).mul
    ((hasDerivAt_const (0 : ℝ) (n^2)).sub square)
  have nz : 2*n*(n^2-(0 : ℝ)^2) ≠ 0 := by
    simpa using mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) nonzero)
      (pow_ne_zero 2 nonzero)
  have result := (hasDerivAt_const (0 : ℝ) (n*A z p)).add (numerator.div denominator nz)
  have normalized : HasDerivAt (fun s : ℝ => n*A z p +
      (n^2*T z p-s^2*S z p i i)/(2*n*(n^2-s^2))) 0 0 := by
    simpa only [zero_mul,mul_zero,sub_zero,zero_div,add_zero,Pi.mul_apply] using! result
  have same : (fun s => timelikePrincipal z p n (Pi.single i s)) =
      (fun s => n*A z p+(n^2*T z p-s^2*S z p i i)/(2*n*(n^2-s^2))) :=
    funext (fun s => principal_shift_line z p n s i)
  rw [same]
  exact normalized

theorem all_four_principal_forces {zp : SourceCoordinateSlice × Cotangent}
    (cone : zp ∈ positiveCone) :
    HasDerivAt (fun n => timelikePrincipal zp.1 zp.2 n 0) 0 (C zp.1 zp.2) ∧
      ∀ i : Fin 3, HasDerivAt (fun s => timelikePrincipal zp.1 zp.2 (C zp.1 zp.2)
        (Pi.single i s)) 0 0 :=
  ⟨principal_clock_force cone, fun i => principal_shift_force _ _ _ (C_positive cone).ne' i⟩

theorem scalarNormSquare_smul (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) :
    scalarNormSquare z (r • p) = r^2*scalarNormSquare z p := by
  simp only [scalarNormSquare,scalarMomentum,smul_apply,smul_eq_mul,
    mul_pow,Finset.mul_sum]

theorem electricGram_smul (z : SourceCoordinateSlice) (p : Cotangent)
    (r : ℝ) (i j : Fin 3) : electricGram z (r • p) i j = r^2*electricGram z p i j := by
  simp only [electricGram,electricMomentum,smul_apply,smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem coframeQuadratic_smul (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) :
    coframeQuadratic z (r • p) = r^2*coframeQuadratic z p := by
  simp only [coframeQuadratic,coframeMomentum,smul_apply,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem A_smul (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) :
    A z (r • p) = r^2*A z p := by
  rw [A,coframeQuadratic_smul,scalarNormSquare_smul,A]
  ring

theorem S_smul (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) (k l : Fin 3) :
    S z (r • p) k l = r^2*S z p k l := by
  simp only [S,electricGram_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem T_smul (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) :
    T z (r • p) = r^2*T z p := by
  simp only [T,S_smul,Finset.mul_sum]

theorem C_smul (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) (nonzero : r ≠ 0) :
    C z (r • p) = C z p := by
  rw [C,C,T_smul,A_smul]
  congr 1
  by_cases zero : A z p=0
  · simp [zero]
  · field_simp

theorem h2_smul (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) (nonzero : r ≠ 0) :
    h2 z (r • p) = r^2*h2 z p := by
  rw [h2,h2,T_smul,C_smul z p r nonzero]
  ring

theorem principalFactor_order_one (z : SourceCoordinateSlice) (p : Cotangent)
    (r : ℝ) (positive : 0 < r) : principalFactor z (r • p) = r*principalFactor z p := by
  rw [principalFactor,principalFactor,h2_smul z p r positive.ne',
    Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq positive.le]

theorem scalarMomentum_smooth (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1 ∈ physicalChart) (a : ScalarIndex) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => scalarMomentum q.1 q.2 a) zp := by
  have hp : ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => q.2) zp := contDiffAt_snd
  have hd : ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent =>
      direction (scalarDirection a) q.1) zp :=
    ContDiffAt.comp (g := direction (scalarDirection a)) (f := Prod.fst) zp
      (direction_smooth (scalarDirection a) ⟨zp.1,physical⟩) contDiffAt_fst
  exact hp.clm_apply hd

theorem electricMomentum_smooth (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1 ∈ physicalChart) (i : Fin 3) (a : LieIndex) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => electricMomentum q.1 q.2 i a) zp := by
  have hp : ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => q.2) zp := contDiffAt_snd
  have hd : ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent =>
      direction (gaugeDirection i a) q.1) zp :=
    ContDiffAt.comp (g := direction (gaugeDirection i a)) (f := Prod.fst) zp
      (direction_smooth (gaugeDirection i a) ⟨zp.1,physical⟩) contDiffAt_fst
  exact hp.clm_apply hd

theorem scalarNormSquare_smooth (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1 ∈ physicalChart) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => scalarNormSquare q.1 q.2) zp := by
  unfold scalarNormSquare
  exact ContDiffAt.sum (fun a _ => (scalarMomentum_smooth zp physical a).pow 2)

theorem electricGram_smooth (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1 ∈ physicalChart) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => electricGram q.1 q.2 i j) zp := by
  unfold electricGram
  exact ContDiffAt.sum (fun a _ =>
    (electricMomentum_smooth zp physical i a).mul (electricMomentum_smooth zp physical j a))

theorem coframeQuadratic_smooth (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1 ∈ physicalChart) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => coframeQuadratic q.1 q.2) zp := by
  unfold coframeQuadratic
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((GaussCoframeKinetic.coefficient_smooth i j ⟨zp.1,physical⟩).comp zp contDiffAt_fst).mul
    (contDiffAt_snd.clm_apply contDiffAt_const)).mul (contDiffAt_snd.clm_apply contDiffAt_const)

theorem A_smooth (zp : SourceCoordinateSlice × Cotangent) (physical : zp.1 ∈ physicalChart) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => A q.1 q.2) zp := by
  unfold A
  exact (coframeQuadratic_smooth zp physical).div_const _ |>.sub
    ((scalarNormSquare_smooth zp physical).div
      (contDiffAt_const.mul (volume_smooth.contDiffAt.comp zp contDiffAt_fst))
      (mul_ne_zero (by norm_num) (volume_pos ⟨zp.1,physical⟩).ne'))

theorem S_smooth (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1 ∈ physicalChart) (k l : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => S q.1 q.2 k l) zp := by
  unfold S
  apply (contDiffAt_const.mul (volume_smooth.contDiffAt.comp zp contDiffAt_fst)).mul
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((triadInverse_smooth i k ⟨zp.1,physical⟩).comp zp contDiffAt_fst).mul
    (electricGram_smooth zp physical i j)).mul
      ((triadInverse_smooth j l ⟨zp.1,physical⟩).comp zp contDiffAt_fst)

theorem T_smooth (zp : SourceCoordinateSlice × Cotangent) (physical : zp.1 ∈ physicalChart) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => T q.1 q.2) zp := by
  unfold T
  exact ContDiffAt.sum (fun k _ => S_smooth zp physical k k)

theorem C_smooth (zp : SourceCoordinateSlice × Cotangent) (cone : zp ∈ positiveCone) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => C q.1 q.2) zp := by
  unfold C
  exact ((T_smooth zp cone.1).div (contDiffAt_const.mul (A_smooth zp cone.1))
    (mul_ne_zero (by norm_num) cone.2.1.ne')).sqrt
      (div_pos cone.2.2 (mul_pos (by norm_num) cone.2.1)).ne'

theorem principalFactor_smooth (zp : SourceCoordinateSlice × Cotangent) (cone : zp ∈ positiveCone) :
    ContDiffAt ℝ ∞ (fun q : SourceCoordinateSlice × Cotangent => principalFactor q.1 q.2) zp := by
  unfold principalFactor h2
  exact ((T_smooth zp cone.1).div (C_smooth zp cone) (C_positive cone).ne').sqrt
    (h2_positive cone).ne'

end LowEnergy.PreparationActualFactor
