import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockSourceFrame
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockGuard
open PreparationActualFactor PreparationVacuumClockPole PreparationVacuumClockJacobian
open PreparationPhaseBounds PreparationPhaseSource PreparationVacuumWeyl
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open GaussHistoryHilbert GaussNativeEnergy GaussLiveMomentum GaussNativeForm GaussCoreDifferential
open SourceQuantumConfigurationHilbert PreparationCoordinates PreparationScalarCoordinates
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open scoped BigOperators Matrix

private def crossEnergy (R : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3,∑ i : Fin 3,∑ k : Fin 3,(v i*R j k-v k*R j i)^2

private theorem square_perturb (a d : ℝ) : (99/100 : ℝ)*a^2-100*d^2≤(a+d)^2 := by
  nlinarith [sq_nonneg (a/10+10*d),sq_nonneg d]

private theorem cross_error (vi vk e1 e2 : ℝ)
    (h1 : |e1|≤1/1000) (h2 : |e2|≤1/1000) :
    (vi*e1-vk*e2)^2≤2*(1/1000 : ℝ)^2*(vi^2+vk^2) := by
  have e1square : e1^2≤(1/1000 : ℝ)^2 := by
    have h := abs_le.mp h1
    nlinarith
  have e2square : e2^2≤(1/1000 : ℝ)^2 := by
    have h := abs_le.mp h2
    nlinarith
  have b1 := mul_le_mul_of_nonneg_left e1square (sq_nonneg vi)
  have b2 := mul_le_mul_of_nonneg_left e2square (sq_nonneg vk)
  nlinarith [sq_nonneg (vi*e1+vk*e2)]

private theorem ideal_cross (b : ℝ) (v : Fin 3 → ℝ) :
    crossEnergy (fun j k => if k=j then b else 0) v=4*b^2*(∑ i : Fin 3,v i^2) := by
  simp [crossEnergy,Fin.sum_univ_three]
  ring

private theorem frame_cross_stable (R : Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ) (v : Fin 3 → ℝ)
    (near : ∀ j k,|R j k-(if k=j then b else 0)|≤1/1000) :
    (99/100 : ℝ)*4*b^2*(∑ i : Fin 3,v i^2)-(9/2500 : ℝ)*(∑ i : Fin 3,v i^2)≤crossEnergy R v := by
  let D : Matrix (Fin 3) (Fin 3) ℝ := fun j k => if k=j then b else 0
  have pointwise (j i k : Fin 3) :
      (99/100 : ℝ)*(v i*D j k-v k*D j i)^2-
        100*(2*(1/1000 : ℝ)^2*(v i^2+v k^2))≤(v i*R j k-v k*R j i)^2 := by
    have error := cross_error (v i) (v k) (R j k-D j k) (R j i-D j i) (near j k) (near j i)
    have stable := square_perturb (v i*D j k-v k*D j i)
      (v i*(R j k-D j k)-v k*(R j i-D j i))
    have identity : v i*D j k-v k*D j i+(v i*(R j k-D j k)-v k*(R j i-D j i))=
        v i*R j k-v k*R j i := by ring
    rw [identity] at stable
    linarith
  have total := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
    Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
      Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => pointwise j i k)))
  calc
    _=(∑ j : Fin 3,∑ i : Fin 3,∑ k : Fin 3,
        ((99/100 : ℝ)*(v i*D j k-v k*D j i)^2-
          100*(2*(1/1000 : ℝ)^2*(v i^2+v k^2)))) := by
      simp [D,Fin.sum_univ_three]
      ring
    _≤_ := total

private theorem determinant_j15 (M : Matrix (Fin 3) (Fin 3) ℝ) (hermitian : M.IsHermitian)
    (guard : ∀ v : Fin 3 → ℝ, (1/15 : ℝ)*(∑ i : Fin 3,v i^2)≤
      ∑ i : Fin 3,∑ k : Fin 3,v i*M i k*v k) : (1/15 : ℝ)^3≤M.det := by
  let N := M-(1/15 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
  have hN : N.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hermitian.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])))
    intro v
    convert! sub_nonneg.mpr (guard v) using 1
    simp [dotProduct,Matrix.mulVec,Fin.sum_univ_three]
    ring
  have h01 := (hN.submatrix (![0,1] : Fin 2 → Fin 3)).det_nonneg
  have h02 := (hN.submatrix (![0,2] : Fin 2 → Fin 3)).det_nonneg
  have h12 := (hN.submatrix (![1,2] : Fin 2 → Fin 3)).det_nonneg
  simp only [Matrix.det_fin_two,Matrix.submatrix_apply,Matrix.cons_val_zero,Matrix.cons_val_one] at h01 h02 h12
  have expansion : M.det=N.det+(1/15 : ℝ)*
      ((N 0 0*N 1 1-N 0 1*N 1 0)+(N 0 0*N 2 2-N 0 2*N 2 0)+(N 1 1*N 2 2-N 1 2*N 2 1))+
      (1/15 : ℝ)^2*(N 0 0+N 1 1+N 2 2)+(1/15 : ℝ)^3 := by
    simp [N,Matrix.det_fin_three]
    ring
  rw [expansion]
  linarith [hN.det_nonneg,hN.diag_nonneg (i:=0),hN.diag_nonneg (i:=1),hN.diag_nonneg (i:=2)]

private theorem inverse_entry_j15 (M : Matrix (Fin 3) (Fin 3) ℝ) (regular : M.det≠0)
    (guard : ∀ v : Fin 3 → ℝ, (1/15 : ℝ)*(∑ i : Fin 3,v i^2)≤
      ∑ i : Fin 3,∑ k : Fin 3,v i*M i k*v k) (i k : Fin 3) : |M⁻¹ i k|≤15 := by
  let v : Fin 3 → ℝ := fun l => M⁻¹ l k
  have solve (l : Fin 3) : (∑ a : Fin 3,M l a*v a)=if l=k then 1 else 0 := by
    have identity := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ => B l k)
      (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr regular))
    simpa only [Matrix.mul_apply,Matrix.one_apply,v] using identity
  have quadratic : (∑ l : Fin 3,∑ a : Fin 3,v l*M l a*v a)=v k := by
    simp_rw [mul_assoc,←Finset.mul_sum,solve,mul_ite,mul_one,mul_zero]
    simp
  have coercive := guard v
  rw [quadratic] at coercive
  have squares : ∀ l : Fin 3,v l^2≤∑ a : Fin 3,v a^2 := fun l =>
    Finset.single_le_sum (fun a _ => sq_nonneg (v a)) (Finset.mem_univ l)
  have normnonnegative : 0≤∑ a : Fin 3,v a^2 := Finset.sum_nonneg (fun a _ => sq_nonneg (v a))
  have diagonal : v k≤15 := by nlinarith [squares k]
  have normupper : (∑ a : Fin 3,v a^2)≤225 := by nlinarith
  have entry : |v i|≤15 := by
    apply abs_le.mpr
    constructor <;> nlinarith [squares i]
  exact entry

private theorem weighted_frame_j15 (R : Matrix (Fin 3) (Fin 3) ℝ) (b V : ℝ) (v : Fin 3 → ℝ)
    (near : ∀ j k,|R j k-(if k=j then b else 0)|≤1/1000)
    (sharp : (3/8 : ℝ)<b) (volumeLower : (99/100 : ℝ)^3≤V) :
    (1/15 : ℝ)*(∑ i : Fin 3,v i^2)≤(V/8)*crossEnergy R v := by
  have stable := frame_cross_stable R b v near
  have amplitude : (3/8 : ℝ)^2≤b^2 := by
    nlinarith [sq_nonneg (b-3/8)]
  have nonnegative : 0≤∑ i : Fin 3,v i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have amplitudeWeighted := mul_le_mul_of_nonneg_right amplitude nonnegative
  have crossLower : (110655/200000 : ℝ)*(∑ i : Fin 3,v i^2)≤crossEnergy R v := by nlinarith
  have volumeNonnegative : 0≤V := by nlinarith
  have weighted := mul_le_mul_of_nonneg_left crossLower (show 0≤V/8 from by positivity)
  have volumeWeighted := mul_le_mul_of_nonneg_right volumeLower nonnegative
  nlinarith


theorem actual_clockForm_j15 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius) (v : Fin 3 → ℝ) :
    (1/15 : ℝ)*(∑ i : Fin 3,v i^2)≤
      clockForm (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) v := by
  let R : Matrix (Fin 3) (Fin 3) ℝ :=
    sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
  calc
    _≤(volume (fullCoordinates.symm z)/8)*crossEnergy R v :=
      weighted_frame_j15 R (sourceUnitMomentum 67) (volume (fullCoordinates.symm z)) v
        (source_frame_rotated_near z u zbox ubox) source_gauge_momentum_sharp.1
        (actual_volume_product_bounds z zbox).1
    _=(sourceSigma*volume (fullCoordinates.symm z)/4)*crossEnergy R v := by
      rw [actual_sourceSigma_half]
      ring
    _≤_ := by
      simpa only [crossEnergy,R] using source_clockForm_frame_lower z u zbox v

theorem actual_clockMatrix_det_j15 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius) :
    (1/15 : ℝ)^3≤(clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).det := by
  apply determinant_j15 _ (clockMatrix_isHermitian _ _)
  intro v
  exact actual_clockForm_j15 z u zbox ubox v

private theorem clockForm_radial (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) (v : Fin 3 → ℝ) :
    clockForm z (r • p) v=r^2*clockForm z p v := by
  simp only [clockForm,clockMatrix_radial,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_three]
  ring

theorem sourceM_j15 (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z∈thetaPositionClosed) (ubox : normalizedMomentum p∈thetaDirectionClosed)
    (nonzero : p≠0) (v : Fin 3 → ℝ) :
    (‖p‖^2/15)*(∑ i : Fin 3,v i^2)≤∑ i : Fin 3,∑ k : Fin 3,v i*sourceM (z,p) i k*v k := by
  have lower := actual_clockForm_j15 z (normalizedMomentum p) zbox ubox v
  have radialLower := mul_le_mul_of_nonneg_left lower (sq_nonneg ‖p‖)
  have original := original_radial_cotangent p nonzero
  have form : clockForm (fullCoordinates.symm z) (nativeCovector p) v=
      ‖p‖^2*clockForm (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 (normalizedMomentum p))) v := by
    rw [←original,clockForm_radial]
  rw [←form] at radialLower
  simpa only [sourceM,actualT,actualS,nativePhase,clockForm,clockMatrix,div_eq_mul_inv,mul_assoc,one_mul] using! radialLower

theorem sourceM_det_j15 (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z∈thetaPositionClosed) (ubox : normalizedMomentum p∈thetaDirectionClosed)
    (nonzero : p≠0) : ‖p‖^6*(1/15 : ℝ)^3≤(sourceM (z,p)).det := by
  have floor := actual_clockMatrix_det_j15 z (normalizedMomentum p) zbox ubox
  have scaled := mul_le_mul_of_nonneg_left floor (pow_nonneg (norm_nonneg p) 6)
  have original := original_radial_cotangent p nonzero
  have determinant : (clockMatrix (fullCoordinates.symm z) (nativeCovector p)).det=
      ‖p‖^6*(clockMatrix (fullCoordinates.symm z)
        (nativeCovector (WithLp.toLp 2 (normalizedMomentum p)))).det := by
    rw [←original,clockMatrix_radial,Matrix.det_smul]
    simp only [Fintype.card_fin]
    ring
  rw [←determinant] at scaled
  simpa only [sourceM,actualT,actualS,nativePhase,clockMatrix] using scaled

theorem actual_T_j15 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius) :
    (1/10 : ℝ)≤T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) := by
  have h0 := actual_clockForm_j15 z u zbox ubox (Pi.single (0 : Fin 3) 1)
  have h1 := actual_clockForm_j15 z u zbox ubox (Pi.single (1 : Fin 3) 1)
  have h2 := actual_clockForm_j15 z u zbox ubox (Pi.single (2 : Fin 3) 1)
  simp [clockForm,clockMatrix,Pi.single_apply] at h0 h1 h2
  have trace : T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))=
      S (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 0 0+
      S (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 1 1+
      S (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 2 2 := by
    simp [T,Fin.sum_univ_three]
  linarith

theorem actual_T_inverse_j15 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius) :
    |(T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)))⁻¹|≤15 := by
  have floor := actual_T_j15 z u zbox ubox
  have positive : 0<T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) := by linarith
  rw [abs_of_pos (inv_pos.mpr positive)]
  have estimate := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/15) (show (1/15 : ℝ)≤T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) from by linarith)
  norm_num [one_div] at estimate
  exact estimate

theorem actual_det_inverse_j15 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius) :
    |((clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).det)⁻¹|≤3375 := by
  have floor := actual_clockMatrix_det_j15 z u zbox ubox
  have positive : 0<(clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).det := by linarith
  rw [abs_of_pos (inv_pos.mpr positive)]
  have estimate := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<(1/15)^3) floor
  norm_num [one_div] at estimate ⊢
  exact estimate

theorem actual_M_inverse_entry_j15 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius) (i k : Fin 3) :
    |(clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)))⁻¹ i k|≤15 := by
  apply inverse_entry_j15
    _ (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ)<(1/15)^3)
      (actual_clockMatrix_det_j15 z u zbox ubox)))
    (actual_clockForm_j15 z u zbox ubox) i k

theorem actual_M_inverse_matrix_budget_j15 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius) (i : Fin 3) :
    (∑ k : Fin 3,|(clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)))⁻¹ i k|)≤45 ∧
    (∑ k : Fin 3,|(clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)))⁻¹ k i|)≤45 := by
  constructor
  · calc
      _≤∑ k : Fin 3,(15 : ℝ) := Finset.sum_le_sum (fun k _ => actual_M_inverse_entry_j15 z u zbox ubox i k)
      _=45 := by norm_num
  · calc
      _≤∑ k : Fin 3,(15 : ℝ) := Finset.sum_le_sum (fun k _ => actual_M_inverse_entry_j15 z u zbox ubox k i)
      _=45 := by norm_num

end LowEnergy.PreparationVacuumClockGuard
