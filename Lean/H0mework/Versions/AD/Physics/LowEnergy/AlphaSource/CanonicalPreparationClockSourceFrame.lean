import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockResidualMomentum
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawGram
import Mathlib.Analysis.InnerProductSpace.Orthonormal

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockGuard
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates
open PreparationMeasure PreparationChartGuard PreparationPhaseScalar PreparationPhaseSource
open PreparationPhaseGuard PreparationPhaseBounds PreparationVacuumClockPole
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumNativeDimensions
open SourceQuantumResidualFlow SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open GaussLiveMomentum GaussNativeEnergy GaussNativeForm GaussHistoryHilbert
open scoped BigOperators Matrix RealInnerProductSpace

def sourceFrameRaw (j : Fin 3) : Fin 12 → ℝ :=
  ![Pi.single 1 1,Pi.single 3 1,Pi.single 6 1-(1/2 : ℝ) • Pi.single 7 1] j

def sourceFrameLie (j : Fin 3) : NativeLie := rawCoordinates.symm (sourceFrameRaw j)

def sourceFrameWeight (j : Fin 3) : ℝ := ![2,2,3/2] j

theorem sourceFrameWeight_bounds (j : Fin 3) :
    0 < sourceFrameWeight j ∧ sourceFrameWeight j ≤ 2 := by
  fin_cases j <;> norm_num [sourceFrameWeight]

theorem sourceFrame_inner (j k : Fin 3) :
    inner ℝ (sourceFrameLie j) (sourceFrameLie k)=if j=k then sourceFrameWeight j else 0 := by
  rw [sourceFrameLie,sourceFrameLie,original_raw_inner]
  fin_cases j <;> fin_cases k <;>
    norm_num [sourceFrameRaw,sourceFrameWeight,Pi.single_apply,Fin.ext_iff]

def sourceNormalLie (j : Fin 3) : NativeLie :=
  (Real.sqrt (sourceFrameWeight j))⁻¹ • sourceFrameLie j

theorem sourceNormalLie_orthonormal : Orthonormal ℝ sourceNormalLie := by
  rw [orthonormal_iff_ite]
  intro j k
  simp only [sourceNormalLie,real_inner_smul_left,real_inner_smul_right,sourceFrame_inner]
  by_cases same : j=k
  · subst k
    simp only [if_true]
    have positive := sourceFrameWeight_bounds j |>.1
    have square := Real.sq_sqrt positive.le
    have regular := (Real.sqrt_pos.mpr positive).ne'
    field_simp [regular]
    nlinarith [square]
  · simp [same]

theorem sourceFrame_pair (E : LieIndex → ℝ) (j : Fin 3) :
    inner ℝ (sourceFrameLie j) (lieBasis.repr.symm (WithLp.toLp 2 E)) =
      ∑ a : LieIndex, lieBasis.repr (sourceFrameLie j) a*E a := by
  rw [←lieBasis.repr.inner_map_map (sourceFrameLie j)
    (lieBasis.repr.symm (WithLp.toLp 2 E)),lieBasis.repr.apply_symm_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem sourceFrame_bessel (E : LieIndex → ℝ) :
    (∑ j : Fin 3, (∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*E a)^2) ≤
      2*∑ a : LieIndex, E a^2 := by
  let w := lieBasis.repr.symm (WithLp.toLp 2 E)
  have pair (j : Fin 3) : ‖inner ℝ (sourceNormalLie j) w‖^2 =
      (∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*E a)^2/sourceFrameWeight j := by
    rw [sourceNormalLie,real_inner_smul_left,sourceFrame_pair]
    simp only [Real.norm_eq_abs,sq_abs,mul_pow,inv_pow]
    rw [Real.sq_sqrt (sourceFrameWeight_bounds j).1.le]
    rw [div_eq_mul_inv,mul_comm]
  have square : ‖w‖^2=∑ a : LieIndex,E a^2 := by
    rw [LinearIsometryEquiv.norm_map,EuclideanSpace.real_norm_sq_eq]
  have weighted := sourceNormalLie_orthonormal.sum_inner_products_le w (s:=Finset.univ)
  simp_rw [pair] at weighted
  rw [square] at weighted
  have term (j : Fin 3) : (∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*E a)^2 ≤
      2*((∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*E a)^2/sourceFrameWeight j) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (sourceFrameWeight_bounds j).1).2
    nlinarith [sq_nonneg (∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*E a),
      (sourceFrameWeight_bounds j).2]
  calc
    _ ≤ ∑ j : Fin 3, 2*((∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*E a)^2/
        sourceFrameWeight j) := Finset.sum_le_sum (fun j _ => term j)
    _ = 2*∑ j : Fin 3,(∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*E a)^2/
        sourceFrameWeight j := by rw [Finset.mul_sum]
    _ ≤ 2*∑ a : LieIndex,E a^2 := mul_le_mul_of_nonneg_left weighted (by norm_num)

def sourceFrameElectric (z : SourceCoordinateSlice) (p : Cotangent) (j i : Fin 3) : ℝ :=
  ∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*electricMomentum z p i a

def sourceFrameRotated (z : SourceCoordinateSlice) (p : Cotangent) (j k : Fin 3) : ℝ :=
  ∑ a : LieIndex,lieBasis.repr (sourceFrameLie j) a*rotatedElectric z p a k

theorem sourceFrameRotated_native (z : SourceCoordinateSlice) (p : Cotangent) (j k : Fin 3) :
    sourceFrameRotated z p j k=
      ∑ i : Fin 3,triadInverse z.1 i k*sourceFrameElectric z p j i := by
  simp only [sourceFrameRotated,sourceFrameElectric,rotatedElectric,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem sourceFrame_cross_bound (z : SourceCoordinateSlice) (p : Cotangent)
    (v : Fin 3 → ℝ) (i k : Fin 3) :
    (∑ j : Fin 3,(v i*sourceFrameRotated z p j k-v k*sourceFrameRotated z p j i)^2) ≤
      2*∑ a : LieIndex,(v i*rotatedElectric z p a k-v k*rotatedElectric z p a i)^2 := by
  have bessel := sourceFrame_bessel
    (fun a => v i*rotatedElectric z p a k-v k*rotatedElectric z p a i)
  convert! bessel using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [sourceFrameRotated,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem source_clockForm_frame_lower (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius) (v : Fin 3 → ℝ) :
    (sourceSigma*volume (fullCoordinates.symm z)/4)*
      (∑ j : Fin 3,∑ i : Fin 3,∑ k : Fin 3,
        (v i*sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j k-
          v k*sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j i)^2) ≤
      clockForm (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) v := by
  rw [clockForm_squares]
  have sums := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 3) _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun (k : Fin 3) _ => sourceFrame_cross_bound
      (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) v i k))
  simp only [←Finset.mul_sum] at sums
  have frameSwap :
      (∑ j : Fin 3,∑ i : Fin 3,∑ k : Fin 3,
        (v i*sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j k-
          v k*sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j i)^2)=
      ∑ i : Fin 3,∑ k : Fin 3,∑ j : Fin 3,
        (v i*sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j k-
          v k*sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have electricSwap :
      (∑ a : LieIndex,∑ i : Fin 3,∑ k : Fin 3,
        (v i*rotatedElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) a k-
          v k*rotatedElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) a i)^2)=
      ∑ i : Fin 3,∑ k : Fin 3,∑ a : LieIndex,
        (v i*rotatedElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) a k-
          v k*rotatedElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) a i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [←frameSwap,←electricSwap] at sums
  have positive := mul_pos sourceSigma_positive (volume_pos (phaseChart z zbox))
  change 0 < sourceSigma*volume (fullCoordinates.symm z) at positive
  nlinarith

theorem source_gauge_momentum_sharp :
    (3/8 : ℝ)<sourceUnitMomentum 67 ∧ sourceUnitMomentum 67 ≤ 2/5 := by
  refine ⟨?_,source_gauge_momentum_bounds.2⟩
  rw [sourceUnitMomentum,if_neg (by decide),if_pos (by decide)]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3563),Real.sqrt_nonneg (3563 : ℝ)]

def seventhFree (i : Fin 3) : Fin 33 := ![5,16,28] i

def seventhGauge (i : Fin 3) : coordinateSlice := gaugeFree.symm (Pi.single (seventhFree i) 1)

theorem seventhGauge_native (i k : Fin 3) :
    gaugeCoordinates (seventhGauge i).val k=
      if k=i then rawCoordinates.symm (Pi.single (7 : Fin 12) 1) else 0 := by
  change rawCoordinates.symm (fun a => insertFree (Pi.single (seventhFree i) 1)
    (combinedRow k a))=_
  fin_cases i <;> fin_cases k <;> apply rawCoordinates.injective <;> ext a <;> fin_cases a <;>
    norm_num [seventhFree,insertFree,combinedRow,Pi.single_apply,Fin.ext_iff]

theorem seventhGauge_momentum (z : physicalChart) (u : FlatConfiguration) (i : Fin 3) :
    ambientMomentum z.val (nativeCovector (WithLp.toLp 2 u)) (0,(seventhGauge i).val)=
      u (gaugeSlot (seventhFree i)) := by
  have splice : ((0,(seventhGauge i).val) : Ambient)=splitMap z.val (0,(0,seventhGauge i)) := by
    simp [splitMap,sliceMap]
  change nativeCovector (WithLp.toLp 2 u) (GaussCoreDifferential.direction (0,(seventhGauge i).val) z.val)=_
  rw [splice]
  simp only [GaussCoreDifferential.direction,inverse_left]
  rw [nativeCovector_apply]
  unfold seventhGauge
  rw [gaugeTest_coordinates]
  simp [Pi.single_apply]

theorem sourceFrameElectric_first (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius) (j : Fin 2) (i : Fin 3) :
    sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j.castSucc i=
      u (gaugeSlot (frameFree i j)) := by
  have same : sourceFrameLie j.castSucc=frameLie j := by fin_cases j <;> rfl
  let native := phaseChart z zbox
  change (∑ a : LieIndex,lieBasis.repr (sourceFrameLie j.castSucc) a*
    electricMomentum native.val (nativeCovector (WithLp.toLp 2 u)) i a)=_
  rw [same,←frameGauge_electric native (nativeCovector (WithLp.toLp 2 u)) i j,
    frameGauge_momentum native u i j]

theorem sourceFrameElectric_third (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i : Fin 3) :
    sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 2 i=
      ambientMomentum (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
        (0,cartanGauge i)-(1/2)*u (gaugeSlot (seventhFree i)) := by
  let g := cartanGauge i-(1/2 : ℝ) • (seventhGauge i).val
  let native := phaseChart z zbox
  let p := nativeCovector (WithLp.toLp 2 u)
  have coordinates (k : Fin 3) : gaugeCoordinates g k=
      if k=i then sourceFrameLie 2 else 0 := by
    apply rawCoordinates.injective
    ext a
    simp only [g,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [cartanGauge_coordinates,seventhGauge_native]
    by_cases same : k=i
    · simp [same,sourceFrameLie,sourceFrameRaw,Pi.single_apply]
    · simp [same]
  have read : ambientMomentum native.val p (0,g)=sourceFrameElectric native.val p 2 i := by
    rw [original_gauge_decomposition,map_sum]
    simp only [map_sum,map_smul,smul_eq_mul]
    change (∑ k : Fin 3,∑ a : LieIndex,lieBasis.repr (gaugeCoordinates g k) a*
      electricMomentum native.val p k a)=_
    have column (k : Fin 3) :
        (∑ a : LieIndex,lieBasis.repr (gaugeCoordinates g k) a*electricMomentum native.val p k a)=
          if k=i then sourceFrameElectric native.val p 2 i else 0 := by
      by_cases same : k=i
      · rw [coordinates,if_pos same,if_pos same,same]
        rfl
      · rw [coordinates,if_neg same,if_neg same]
        simp
    simp_rw [column]
    simp
  have pair : ((0,g) : Ambient)=
      (0,cartanGauge i)-(1/2 : ℝ) • ((0,(seventhGauge i).val) : Ambient) := by
    simp [g,Prod.smul_mk]
  rw [pair,map_sub,map_smul,smul_eq_mul,seventhGauge_momentum native u i] at read
  exact read.symm

theorem sourceFrameElectric_near (z u : FlatConfiguration)
    (zbox : ∀ k, |z k-flatSource k| ≤ sourceRadius)
    (ubox : ∀ k, |u k-sourceUnitMomentum k| ≤ sourceRadius) (j i : Fin 3) :
    |sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j i-
      (if i=j then sourceUnitMomentum 67 else 0)| ≤ 1000000000000000*sourceRadius := by
  have nonnegative := radius_small.1
  have first (a : Fin 2) : sourceUnitMomentum (gaugeSlot (frameFree i a))=
      if i=a.castSucc then sourceUnitMomentum 67 else 0 := by
    fin_cases i <;> fin_cases a <;>
      norm_num [gaugeSlot,frameFree,sourceUnitMomentum,Fin.ext_iff]
  have seventh : sourceUnitMomentum (gaugeSlot (seventhFree i))=0 := by
    fin_cases i <;> norm_num [gaugeSlot,seventhFree,sourceUnitMomentum,Fin.ext_iff]
  have seventhBound : |u (gaugeSlot (seventhFree i))| ≤ sourceRadius := by
    simpa only [seventh,sub_zero] using ubox (gaugeSlot (seventhFree i))
  fin_cases j
  · change |sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 0 i-
      (if i=0 then sourceUnitMomentum 67 else 0)| ≤ _
    have equation := sourceFrameElectric_first z u zbox 0 i
    change sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 0 i=_ at equation
    rw [equation]
    have bound := ubox (gaugeSlot (frameFree i 0))
    rw [first 0] at bound
    change |u (gaugeSlot (frameFree i 0))-(if i=0 then sourceUnitMomentum 67 else 0)| ≤ sourceRadius at bound
    exact bound.trans (by nlinarith)
  · change |sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 1 i-
      (if i=1 then sourceUnitMomentum 67 else 0)| ≤ _
    have equation := sourceFrameElectric_first z u zbox 1 i
    change sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 1 i=_ at equation
    rw [equation]
    have bound := ubox (gaugeSlot (frameFree i 1))
    rw [first 1] at bound
    change |u (gaugeSlot (frameFree i 1))-(if i=1 then sourceUnitMomentum 67 else 0)| ≤ sourceRadius at bound
    exact bound.trans (by nlinarith)
  · change |sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) 2 i-
      (if i=2 then sourceUnitMomentum 67 else 0)| ≤ _
    rw [sourceFrameElectric_third z u zbox i]
    have actual := cartan_momentum_source_error z u zbox ubox i
    rw [sourceGaugeRead_cartan] at actual
    have triangle := real_abs_sub_le_sum
      (ambientMomentum (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
        (0,cartanGauge i)-(if i=2 then sourceUnitMomentum 67 else 0))
      ((1/2)*u (gaugeSlot (seventhFree i)))
    simp only [abs_mul] at triangle
    norm_num at triangle
    have target : |ambientMomentum (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
        (0,cartanGauge i)-(if i=2 then sourceUnitMomentum 67 else 0)-
        (1/2)*u (gaugeSlot (seventhFree i))| ≤ 1000000000000000*sourceRadius := by
      nlinarith
    convert! target using 1
    congr 1
    ring

theorem actual_triad_inverse_near (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i k : Fin 3) :
    |triadInverse (fullCoordinates.symm z).1 i k-(if i=k then 1 else 0)| ≤ 100*sourceRadius := by
  let q := (fullCoordinates.symm z).1
  have q0 := actual_diagonal_coframe_bounds z zbox 0 (by decide)
  have q2 := actual_diagonal_coframe_bounds z zbox 2 (by decide)
  have q5 := actual_diagonal_coframe_bounds z zbox 5 (by decide)
  change 99/100 ≤ q 0 ∧ q 0 ≤ 101/100 at q0
  change 99/100 ≤ q 2 ∧ q 2 ≤ 101/100 at q2
  change 99/100 ≤ q 5 ∧ q 5 ≤ 101/100 at q5
  have off1 : |q 1| ≤ sourceRadius := by simpa [q,qCenter,Fin.ext_iff] using coframe_box z zbox 1
  have off3 : |q 3| ≤ sourceRadius := by simpa [q,qCenter,Fin.ext_iff] using coframe_box z zbox 3
  have off4 : |q 4| ≤ sourceRadius := by simpa [q,qCenter,Fin.ext_iff] using coframe_box z zbox 4
  have near (a : Fin 6) (diagonal : diagonalIndex a) : |(q a)⁻¹-1| ≤ 100*sourceRadius := by
    have bounds := actual_diagonal_coframe_bounds z zbox a diagonal
    change 99/100 ≤ q a ∧ q a ≤ 101/100 at bounds
    have positive : 0 < q a := by linarith
    have same : (q a)⁻¹-1=(1-q a)/(q a) := by field_simp
    have center := coframe_box z zbox a
    have unit : qCenter a=1 := if_pos diagonal
    rw [unit] at center
    change |q a-1| ≤ sourceRadius at center
    rw [same,abs_div,abs_sub_comm,abs_of_pos positive]
    exact (div_le_iff₀ positive).2 (by nlinarith [radius_small.1])
  have division (a d : ℝ) (numerator : |a| ≤ 10*sourceRadius) (denominator : 1/2 ≤ d) :
      |a/d| ≤ 100*sourceRadius := by
    have positive : 0 < d := by linarith
    rw [abs_div,abs_of_pos positive]
    exact (div_le_iff₀ positive).2 (by nlinarith [radius_small.1])
  have denominator02 : (1/2 : ℝ) ≤ q 0*q 2 := by
    have product := mul_le_mul q0.1 q2.1 (by norm_num) (by linarith : 0 ≤ q 0)
    norm_num at product
    linarith
  have denominator25 : (1/2 : ℝ) ≤ q 2*q 5 := by
    have product := mul_le_mul q2.1 q5.1 (by norm_num) (by linarith : 0 ≤ q 2)
    norm_num at product
    linarith
  have denominator025 : (1/2 : ℝ) ≤ q 0*q 2*q 5 := by
    have original := actual_volume_product_bounds z zbox
    change (99/100 : ℝ)^3 ≤ q 0*q 2*q 5 ∧ q 0*q 2*q 5 ≤ (101/100 : ℝ)^3 at original
    norm_num at original
    linarith [original.1]
  have numerator : |q 1*q 4-q 2*q 3| ≤ 10*sourceRadius := by
    have first := mul_le_mul off1 off4 (abs_nonneg _) radius_small.1.le
    have second := mul_le_mul (coframe_box_abs z zbox 2) off3 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have triangle := real_abs_sub_le_sum (q 1*q 4) (q 2*q 3)
    rw [abs_mul,abs_mul] at triangle
    change |q 2| * |q 3| ≤ 2*sourceRadius at second
    nlinarith [radius_small.1,radius_small.2]
  fin_cases i <;> fin_cases k
  · change |(q 0)⁻¹-1| ≤ _
    exact near 0 (by decide)
  · change |0-0| ≤ _
    simp only [sub_zero,abs_zero]
    linarith [radius_small.1]
  · change |0-0| ≤ _
    simp only [sub_zero,abs_zero]
    linarith [radius_small.1]
  · change |-(q 1)/(q 0*q 2)-0| ≤ _
    simpa only [sub_zero,neg_div,abs_neg] using division (q 1) (q 0*q 2)
      (by nlinarith [radius_small.1]) denominator02
  · change |(q 2)⁻¹-1| ≤ _
    exact near 2 (by decide)
  · change |0-0| ≤ _
    simp only [sub_zero,abs_zero]
    linarith [radius_small.1]
  · change |(q 1*q 4-q 2*q 3)/(q 0*q 2*q 5)-0| ≤ _
    simpa only [sub_zero] using division (q 1*q 4-q 2*q 3) (q 0*q 2*q 5) numerator denominator025
  · change |-(q 4)/(q 2*q 5)-0| ≤ _
    simpa only [sub_zero,neg_div,abs_neg] using division (q 4) (q 2*q 5)
      (by nlinarith [radius_small.1]) denominator25
  · change |(q 5)⁻¹-1| ≤ _
    exact near 5 (by decide)

theorem sourceFrameElectric_bound (z u : FlatConfiguration)
    (zbox : ∀ k, |z k-flatSource k| ≤ sourceRadius)
    (ubox : ∀ k, |u k-sourceUnitMomentum k| ≤ sourceRadius) (j i : Fin 3) :
    |sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j i| ≤ 1 := by
  let G := sourceFrameElectric (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j i
  let D : ℝ := if i=j then sourceUnitMomentum 67 else 0
  have nearby := sourceFrameElectric_near z u zbox ubox j i
  change |G-D| ≤ 1000000000000000*sourceRadius at nearby
  have diagonal : |D| ≤ 2/5 := by
    by_cases same : i=j
    · simp only [D,if_pos same,abs_of_nonneg source_gauge_momentum_bounds.1]
      exact source_gauge_momentum_bounds.2
    · norm_num [D,same]
  have triangle := real_abs_sub_le_sum (G-D) (-D)
  rw [abs_neg] at triangle
  have bound : |G| ≤ |G-D|+|D| := by
    convert! triangle using 1
    congr 1
    ring
  change |G| ≤ 1
  nlinarith [phase_radius]

theorem source_frame_rotated_near (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) (j k : Fin 3) :
    |sourceFrameRotated (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) j k-
      (if k=j then sourceUnitMomentum 67 else 0)| ≤ 1/1000 := by
  let native := fullCoordinates.symm z
  let p := nativeCovector (WithLp.toLp 2 u)
  let G := sourceFrameElectric native p j
  let D : ℝ := if k=j then sourceUnitMomentum 67 else 0
  let error : ℝ := ∑ i : Fin 3,
    (triadInverse native.1 i k-(if i=k then 1 else 0))*G i
  have identity : sourceFrameRotated native p j k-D=(G k-D)+error := by
    rw [sourceFrameRotated_native]
    change (∑ i : Fin 3,triadInverse native.1 i k*G i)-D=(G k-D)+
      ∑ i : Fin 3,(triadInverse native.1 i k-(if i=k then 1 else 0))*G i
    simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring
  have each (i : Fin 3) : |(triadInverse native.1 i k-(if i=k then 1 else 0))*G i| ≤
      100*sourceRadius := by
    rw [abs_mul]
    have product := mul_le_mul (actual_triad_inverse_near z zbox i k)
      (sourceFrameElectric_bound z u zbox ubox j i) (abs_nonneg _) (by nlinarith [radius_small.1])
    simpa only [mul_one] using product
  have errorBound : |error| ≤ 300*sourceRadius := by
    calc
      _ ≤ ∑ i : Fin 3, |(triadInverse native.1 i k-(if i=k then 1 else 0))*G i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3,100*sourceRadius := Finset.sum_le_sum (fun i _ => each i)
      _ = 300*sourceRadius := by norm_num; ring
  have original := sourceFrameElectric_near z u zbox ubox j k
  change |G k-D| ≤ 1000000000000000*sourceRadius at original
  change |sourceFrameRotated native p j k-D| ≤ 1/1000
  rw [identity]
  have triangle := abs_add_le (G k-D) error
  nlinarith [phase_radius]

end LowEnergy.PreparationVacuumClockGuard
