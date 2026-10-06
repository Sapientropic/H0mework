import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationBorelPrincipal
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarGuard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhaseGuard
open SaturationMonoid.PhysicsCore
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumScalarChart
open GaussNativeEnergy GaussNativeForm GaussCoreDifferential GaussLiveMomentum GaussHistoryHilbert
open scoped BigOperators Matrix

def rotatedElectric (z : SourceCoordinateSlice) (p : Cotangent) (a : LieIndex) (k : Fin 3) : ℝ :=
  ∑ i : Fin 3, triadInverse z.1 i k * electricMomentum z p i a

theorem T_original_squares (z : SourceCoordinateSlice) (p : Cotangent) :
    T z p=sourceSigma*volume z*∑ a : LieIndex, ∑ k : Fin 3, rotatedElectric z p a k^2 := by
  unfold T S electricGram rotatedElectric
  simp only [Fin.sum_univ_three,Finset.mul_sum,Finset.sum_mul]
  simp only [←Finset.sum_add_distrib]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem sourceSigma_positive : 0 < sourceSigma := by
  exact StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource.legacy.sigma_pos

theorem T_nonnegative (z : physicalChart) (p : Cotangent) : 0 ≤ T z.val p := by
  rw [T_original_squares]
  exact mul_nonneg (mul_pos sourceSigma_positive (volume_pos z)).le
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem T_zero_electric (z : physicalChart) (p : Cotangent) (zero : T z.val p=0) :
    ∀ i a, electricMomentum z.val p i a=0 := by
  have sumZero : (∑ a : LieIndex, ∑ k : Fin 3, rotatedElectric z.val p a k^2)=0 := by
    rw [T_original_squares] at zero
    exact (mul_eq_zero.mp zero).resolve_left (mul_pos sourceSigma_positive (volume_pos z)).ne'
  have outer := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a∈(Finset.univ : Finset LieIndex)) =>
      Finset.sum_nonneg (fun k _ => sq_nonneg (rotatedElectric z.val p a k)))).mp sumZero
  have allZero : ∀ a k, rotatedElectric z.val p a k=0 := by
    intro a k
    have innerSum := outer a (Finset.mem_univ a)
    have terms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k∈(Finset.univ : Finset (Fin 3))) => sq_nonneg (rotatedElectric z.val p a k))).mp innerSum
    exact sq_eq_zero_iff.mp (terms k (Finset.mem_univ k))
  intro i a
  have vectorZero : (triadInverse z.val.1).transpose *ᵥ
      (fun j => electricMomentum z.val p j a)=0 := by
    funext k
    change rotatedElectric z.val p a k=0
    exact allZero a k
  have recover := congrArg (fun x : Fin 3 → ℝ => (triad z.val.1).transpose *ᵥ x) vectorZero
  rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,triad_inverse_left z,
    Matrix.transpose_one,Matrix.one_mulVec,Matrix.mulVec_zero] at recover
  exact congrFun recover i

def ambientMomentum (z : SourceCoordinateSlice) (p : Cotangent) : Ambient →ₗ[ℝ] ℝ where
  toFun v := p (direction v z)
  map_add' v w := by
    simp only [direction,map_add,Prod.snd_add]
    simpa only [Prod.mk_add_mk,zero_add] using
      map_add p (0,(inverseL z v).2) (0,(inverseL z w).2)
  map_smul' r v := by
    simp only [direction,map_smul]
    have pair : ((0,(r • inverseL z v).2) : SourceCoordinateSlice) =
        r • ((0,(inverseL z v).2) : SourceCoordinateSlice) := by
      apply Prod.ext
      · simp
      · rfl
    rw [pair]
    simpa only [Prod.smul_mk,smul_zero,RingHom.id_apply] using
      map_smul p r (0,(inverseL z v).2)

theorem original_gauge_decomposition (g : Gauge) :
    ((0,g) : Ambient)=∑ i : Fin 3, ∑ a : LieIndex,
      lieBasis.repr (gaugeCoordinates g i) a • gaugeDirection i a := by
  apply Prod.ext
  · simp only [gaugeDirection,Prod.smul_mk,Prod.fst_sum,
      smul_zero,Finset.sum_const_zero]
  · apply gaugeCoordinates.injective
    funext k
    simp only [Prod.snd_sum,Prod.smul_mk,gaugeDirection,map_sum,map_smul,
      Finset.sum_apply,Pi.smul_apply]
    change gaugeCoordinates g k=∑ i : Fin 3, ∑ a : LieIndex,
      lieBasis.repr (gaugeCoordinates g i) a • (Pi.single i (lieBasis a) : Fin 3 → NativeLie) k
    simp only [Pi.single_apply]
    simp only [smul_ite,smul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact (lieBasis.sum_repr (gaugeCoordinates g k)).symm

theorem T_zero_on_gauge (z : physicalChart) (p : Cotangent) (zero : T z.val p=0)
    (g : Gauge) : ambientMomentum z.val p (0,g)=0 := by
  rw [original_gauge_decomposition,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul]
  have fields := T_zero_electric z p zero
  change (∑ i : Fin 3, ∑ a : LieIndex,
    lieBasis.repr (gaugeCoordinates g i) a*electricMomentum z.val p i a)=0
  simp only [fields,mul_zero,Finset.sum_const_zero]

def gaugeSlot0 : coordinateSlice := gaugeFree.symm (Pi.single 0 1)

theorem original_gauge_slot0_coordinates :
    fullCoordinates (0,(0,gaugeSlot0))=Pi.single (67 : Fin 100) 1 := by
  rw [full_blocks]
  simp only [gaugeSlot0,gaugeFree.apply_symm_apply,map_zero]
  ext i
  fin_cases i <;> simp [joinCoordinates,read61,scalarRealify,scalarRead]

theorem original_gauge_slot0_momentum (z : physicalChart) (u : FlatConfiguration) :
    ambientMomentum z.val (nativeCovector (WithLp.toLp 2 u)) (0,gaugeSlot0.val)=u 67 := by
  have splice : ((0,gaugeSlot0.val) : Ambient)=splitMap z.val (0,(0,gaugeSlot0)) := by
    simp [splitMap,sliceMap]
  change nativeCovector (WithLp.toLp 2 u) (direction (0,gaugeSlot0.val) z.val)=_
  rw [splice]
  simp only [direction,inverse_left]
  rw [nativeCovector_apply,original_gauge_slot0_coordinates]
  simp [Pi.single_apply]

theorem actual_angular_gauge_nonzero (u : FlatConfiguration)
    (box : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) : 0 < u 67 := by
  have root : 1 ≤ Real.sqrt 3563 := by
    have square := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3563)
    have nonneg := Real.sqrt_nonneg (3563 : ℝ)
    nlinarith
  have center : 1/200 < sourceUnitMomentum 67 := by
    rw [sourceUnitMomentum,if_neg (by decide),if_pos (by decide)]
    nlinarith
  have lower := (abs_le.mp (box 67)).1
  linarith [radius_small.2]

theorem actual_closed_phase_T (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) :
    0 < T (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) := by
  have chart : fullCoordinates.symm z ∈ physicalChart := by
    apply actual_source_chart_guard z
    intro i
    exact (zbox i).trans (by linarith [radius_small.1])
  let native : physicalChart := ⟨fullCoordinates.symm z,chart⟩
  have nonneg := T_nonnegative native (nativeCovector (WithLp.toLp 2 u))
  apply lt_of_le_of_ne nonneg
  intro equal
  have zero := T_zero_on_gauge native (nativeCovector (WithLp.toLp 2 u)) equal.symm gaugeSlot0.val
  rw [original_gauge_slot0_momentum native u] at zero
  exact (actual_angular_gauge_nonzero u ubox).ne' zero

end LowEnergy.PreparationPhaseGuard
