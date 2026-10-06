import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockGaugeFrame

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockPole
open PreparationActualFactor PreparationPhaseGuard PreparationPhaseBounds
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussNativeEnergy GaussHistoryHilbert CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open GaussLiveMomentum GaussNativeForm GaussCoreDifferential
open scoped BigOperators Matrix

def clockMatrix (z : SourceCoordinateSlice) (p : Cotangent) : Matrix (Fin 3) (Fin 3) ℝ :=
  T z p • (1 : Matrix (Fin 3) (Fin 3) ℝ)-(show Matrix (Fin 3) (Fin 3) ℝ from fun i k => S z p i k)

def clockForm (z : SourceCoordinateSlice) (p : Cotangent) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3,∑ k : Fin 3,v i*clockMatrix z p i k*v k

def coloredRotated (z : SourceCoordinateSlice) (p : Cotangent) (j : Fin 2) (k : Fin 3) : ℝ :=
  ∑ a : LieIndex,lieBasis.repr (frameLie j) a*rotatedElectric z p a k

theorem S_original_gram (z : SourceCoordinateSlice) (p : Cotangent) (i k : Fin 3) :
    S z p i k=sourceSigma*volume z*
      ∑ a : LieIndex,rotatedElectric z p a i*rotatedElectric z p a k := by
  unfold S electricGram rotatedElectric
  simp only [Fin.sum_univ_three,Finset.mul_sum,Finset.sum_mul]
  simp only [←Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem clockForm_native (z : SourceCoordinateSlice) (p : Cotangent) (v : Fin 3 → ℝ) :
    clockForm z p v=T z p*(∑ i : Fin 3,v i^2)-
      ∑ i : Fin 3,∑ k : Fin 3,v i*S z p i k*v k := by
  unfold clockForm clockMatrix
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_sub,sub_mul,
    Finset.sum_sub_distrib,mul_ite,ite_mul,mul_zero,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem reorder (f : Fin 3 → Fin 3 → LieIndex → ℝ) :
    (∑ i : Fin 3,∑ k : Fin 3,∑ a : LieIndex,f i k a)=
      ∑ a : LieIndex,∑ i : Fin 3,∑ k : Fin 3,f i k a := by
  calc
    _=∑ i : Fin 3,∑ a : LieIndex,∑ k : Fin 3,f i k a := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _=_ := by rw [Finset.sum_comm]

private theorem wedge_square (v e : Fin 3 → ℝ) :
    (1/2 : ℝ)*(∑ i : Fin 3,∑ k : Fin 3,(v i*e k-v k*e i)^2)=
      (∑ i : Fin 3,v i^2)*(∑ k : Fin 3,e k^2)-(∑ i : Fin 3,v i*e i)^2 := by
  simp only [Fin.sum_univ_three]
  ring

theorem clockForm_squares (z : SourceCoordinateSlice) (p : Cotangent) (v : Fin 3 → ℝ) :
    clockForm z p v=(sourceSigma*volume z/2)*
      ∑ a : LieIndex,∑ i : Fin 3,∑ k : Fin 3,
        (v i*rotatedElectric z p a k-v k*rotatedElectric z p a i)^2 := by
  have quadratic : (∑ i : Fin 3,∑ k : Fin 3,v i*S z p i k*v k)=
      sourceSigma*volume z*∑ a : LieIndex,(∑ i : Fin 3,v i*rotatedElectric z p a i)^2 := by
    simp only [S_original_gram,Finset.mul_sum,Finset.sum_mul]
    rw [reorder]
    simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have folded : (1/2 : ℝ)*(∑ a : LieIndex,∑ i : Fin 3,∑ k : Fin 3,
      (v i*rotatedElectric z p a k-v k*rotatedElectric z p a i)^2)=
      ∑ a : LieIndex,((∑ i : Fin 3,v i^2)*(∑ k : Fin 3,rotatedElectric z p a k^2)-
        (∑ i : Fin 3,v i*rotatedElectric z p a i)^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => wedge_square v (rotatedElectric z p a))
  rw [clockForm_native,T_original_squares,quadratic]
  calc
    _=sourceSigma*volume z*(∑ a : LieIndex,
        ((∑ i : Fin 3,v i^2)*(∑ k : Fin 3,rotatedElectric z p a k^2)-
          (∑ i : Fin 3,v i*rotatedElectric z p a i)^2)) := by
      rw [Finset.sum_sub_distrib,←Finset.mul_sum]
      ring
    _=_ := by rw [←folded]; ring

theorem clockForm_nonnegative (z : physicalChart) (p : Cotangent) (v : Fin 3 → ℝ) :
    0≤clockForm z.val p v := by
  rw [clockForm_squares]
  apply mul_nonneg (div_nonneg (mul_pos sourceSigma_positive (volume_pos z)).le (by norm_num))
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem clockForm_zero_cross (z : physicalChart) (p : Cotangent) (v : Fin 3 → ℝ)
    (zero : clockForm z.val p v=0) :
    ∀ a : LieIndex,∀ i k : Fin 3,v i*rotatedElectric z.val p a k=v k*rotatedElectric z.val p a i := by
  have prefactor : 0<sourceSigma*volume z.val/2 :=
    div_pos (mul_pos sourceSigma_positive (volume_pos z)) (by norm_num)
  have sumZero : (∑ a : LieIndex,∑ i : Fin 3,∑ k : Fin 3,
      (v i*rotatedElectric z.val p a k-v k*rotatedElectric z.val p a i)^2)=0 := by
    rw [clockForm_squares] at zero
    exact (mul_eq_zero.mp zero).resolve_left prefactor.ne'
  have outer := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a∈(Finset.univ : Finset LieIndex)) => Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg
        (v i*rotatedElectric z.val p a k-v k*rotatedElectric z.val p a i))))).mp sumZero
  intro a i k
  have middle := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) => Finset.sum_nonneg (fun k _ =>
      sq_nonneg (v i*rotatedElectric z.val p a k-v k*rotatedElectric z.val p a i)))).mp
        (outer a (Finset.mem_univ a))
  have inner := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k∈(Finset.univ : Finset (Fin 3))) =>
      sq_nonneg (v i*rotatedElectric z.val p a k-v k*rotatedElectric z.val p a i))).mp
        (middle i (Finset.mem_univ i))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (inner k (Finset.mem_univ k)))

theorem coloredRotated_cross (z : physicalChart) (p : Cotangent) (v : Fin 3 → ℝ)
    (zero : clockForm z.val p v=0) (j : Fin 2) (i k : Fin 3) :
    v i*coloredRotated z.val p j k=v k*coloredRotated z.val p j i := by
  unfold coloredRotated
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _=lieBasis.repr (frameLie j) a*(v i*rotatedElectric z.val p a k) := by ring
    _=lieBasis.repr (frameLie j) a*(v k*rotatedElectric z.val p a i) := by
      rw [clockForm_zero_cross z p v zero a i k]
    _=_ := by ring

theorem coloredRotated_recover (z : physicalChart) (u : FlatConfiguration) (i : Fin 3) (j : Fin 2) :
    (∑ k : Fin 3,triad z.val.1 k i*
      coloredRotated z.val (nativeCovector (WithLp.toLp 2 u)) j k)=
      u (PreparationPhaseScalar.gaugeSlot (frameFree i j)) := by
  calc
    _=∑ a : LieIndex,lieBasis.repr (frameLie j) a*
        electricMomentum z.val (nativeCovector (WithLp.toLp 2 u)) i a := by
      simp only [coloredRotated,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [original_electric_recover z _ i a,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _=ambientMomentum z.val (nativeCovector (WithLp.toLp 2 u)) (0,(frameGauge i j).val) :=
      (frameGauge_electric z _ i j).symm
    _=_ := frameGauge_momentum z u i j

theorem parallel_matrix_mul (B : Matrix (Fin 3) (Fin 3) ℝ) (v w : Fin 3 → ℝ)
    (parallel : ∀ i k : Fin 3,v i*w k=v k*w i) (i k : Fin 3) :
    (B*ᵥv) i*(B*ᵥw) k=(B*ᵥv) k*(B*ᵥw) i := by
  simp only [Matrix.mulVec,dotProduct]
  rw [Finset.sum_mul,Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _=B i a*B k b*(v a*w b) := by ring
    _=B i a*B k b*(v b*w a) := by rw [parallel a b]
    _=_ := by ring

theorem coloredGamma_parallel (z : physicalChart) (u : FlatConfiguration) (v : Fin 3 → ℝ)
    (zero : clockForm z.val (nativeCovector (WithLp.toLp 2 u)) v=0)
    (j : Fin 2) (i k : Fin 3) :
    ((triad z.val.1).transpose*ᵥv) i*u (PreparationPhaseScalar.gaugeSlot (frameFree k j))=
      ((triad z.val.1).transpose*ᵥv) k*u (PreparationPhaseScalar.gaugeSlot (frameFree i j)) := by
  have actual := parallel_matrix_mul (triad z.val.1).transpose v
    (coloredRotated z.val (nativeCovector (WithLp.toLp 2 u)) j)
    (fun a b => coloredRotated_cross z _ v zero j a b) i k
  change ((triad z.val.1).transpose*ᵥv) i*
      (∑ a : Fin 3,triad z.val.1 a k*coloredRotated z.val (nativeCovector (WithLp.toLp 2 u)) j a)=
    ((triad z.val.1).transpose*ᵥv) k*
      (∑ a : Fin 3,triad z.val.1 a i*coloredRotated z.val (nativeCovector (WithLp.toLp 2 u)) j a) at actual
  simpa only [coloredRotated_recover] using actual

end LowEnergy.PreparationVacuumClockPole
