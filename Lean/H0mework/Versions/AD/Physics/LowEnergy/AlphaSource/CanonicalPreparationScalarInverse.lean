import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoframeCone
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLieBounds
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentum

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhaseScalar
open SaturationMonoid.PhysicsCore
open StageNineCoframeGravityGaugeRegularity StageNineP286GaugeConnectionVariationDensity
open SourceQuantumResidualFlow
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open GaussNativeEnergy GaussNativeForm GaussCoreDifferential GaussLiveMomentum GaussHistoryHilbert
open scoped BigOperators Matrix RealInnerProductSpace

theorem closed_box_outer (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) : z ∈ sourceClosedBox := by
  intro i
  exact (box i).trans (by linarith [radius_small.1])

def phaseChart (z : FlatConfiguration) (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) : physicalChart :=
  ⟨fullCoordinates.symm z,actual_source_chart_guard z (closed_box_outer z box)⟩

def inverseLie (z : SourceCoordinateSlice) (xi : Scalar) : NativeLie :=
  (inverseL z (xi,0)).1

def inverseScalar (z : SourceCoordinateSlice) (xi : Scalar) : scalarSlice :=
  (inverseL z (xi,0)).2.1

def inverseGauge (z : SourceCoordinateSlice) (xi : Scalar) : coordinateSlice :=
  (inverseL z (xi,0)).2.2

theorem original_scalar_inverse_equation (z : physicalChart) (xi : Scalar) :
    action (vacuum+(z.val.2.1 : Scalar)) (inverseLie z.val xi)+(inverseScalar z.val xi : Scalar)=xi :=
  congrArg Prod.fst (inverse_right z (xi,0))

theorem original_gauge_inverse_equation (z : physicalChart) (xi : Scalar) :
    nativeGauge (inverseLie z.val xi) z.val.2.2.val+(inverseGauge z.val xi : Gauge)=0 :=
  congrArg Prod.snd (inverse_right z (xi,0))

theorem original_inverse_normal_pairing (z : physicalChart) (xi : Scalar) :
    ‖orbit (normalBuild (normalRead (inverseLie z.val xi)))‖^2+
      inner ℝ (orbit (normalBuild (normalRead (inverseLie z.val xi))))
        (action (z.val.2.1 : Scalar) (normalBuild (normalRead (inverseLie z.val xi))))=
      inner ℝ (orbit (normalBuild (normalRead (inverseLie z.val xi)))) xi := by
  let a:=inverseLie z.val xi
  let x:=normalRead a
  have equation:=congrArg (fun y : Scalar => inner ℝ (orbit (normalBuild x)) y)
    (original_scalar_inverse_equation z xi)
  have split : action (vacuum+(z.val.2.1 : Scalar)) a=
      orbit (normalBuild x)+action (z.val.2.1 : Scalar) (normalBuild x)+
        action (vacuum+(z.val.2.1 : Scalar)) (stabilizerPart a).val := by
    nth_rw 1 [native_decomposition a]
    rw [map_add]
    have phase : action (vacuum+(z.val.2.1 : Scalar)) (normalBuild x)=
        orbit (normalBuild x)+action (z.val.2.1 : Scalar) (normalBuild x) := by
      change StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
        (normalBuild x) (vacuum+(z.val.2.1 : Scalar))=_
      exact map_add _ _ _
    rw [phase]
  have residual : inner ℝ (orbit (normalBuild x))
      (action (vacuum+(z.val.2.1 : Scalar)) (stabilizerPart a).val)=0 :=
    (Submodule.mem_orthogonal _ _).mp (stabilizer_affine_action (stabilizerPart a) z.val.2.1)
      (orbit (normalBuild x)) ⟨_,rfl⟩
  have scalarResidual : inner ℝ (orbit (normalBuild x)) (inverseScalar z.val xi : Scalar)=0 :=
    (Submodule.mem_orthogonal _ _).mp (inverseScalar z.val xi).property
      (orbit (normalBuild x)) ⟨_,rfl⟩
  change inner ℝ (orbit (normalBuild x))
    (action (vacuum+(z.val.2.1 : Scalar)) a+(inverseScalar z.val xi : Scalar))=_ at equation
  rw [split,inner_add_right,inner_add_right,inner_add_right,residual,scalarResidual,
    add_zero,add_zero,real_inner_self_eq_norm_sq] at equation
  exact equation

theorem original_inverse_normal_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (xi : Scalar) :
    ‖normalRead (inverseLie (fullCoordinates.symm z) xi)‖ ≤ 4*‖xi‖ := by
  let native:=phaseChart z box
  let sigma:=native.val.2.1
  let x:=normalRead (inverseLie native.val xi)
  have pairing:=original_inverse_normal_pairing native xi
  change ‖orbit (normalBuild x)‖^2+
    inner ℝ (orbit (normalBuild x)) (action (sigma : Scalar) (normalBuild x))=
      inner ℝ (orbit (normalBuild x)) xi at pairing
  have error:=norm_inner_le_norm (𝕜:=ℝ) (orbit (normalBuild x)) (action (sigma : Scalar) (normalBuild x))
  change |inner ℝ (orbit (normalBuild x)) (action (sigma : Scalar) (normalBuild x))| ≤
    ‖orbit (normalBuild x)‖*‖action (sigma : Scalar) (normalBuild x)‖ at error
  have actionBound:=normal_action_bound x (sigma : Scalar)
  have sigmaBound:=scalar_box_norm z (closed_box_outer z box)
  have orbitBound:=normal_orbit_upper x
  have lower:=normal_orbit_lower x
  have perturb : ‖orbit (normalBuild x)‖*‖action (sigma : Scalar) (normalBuild x)‖ ≤
      33868800*sourceRadius*‖x‖^2 := by
    calc
      _ ≤ (2*‖x‖)*(1058400*‖x‖*(16*sourceRadius)) := by
        apply mul_le_mul orbitBound ?_ (norm_nonneg _) (by positivity)
        exact actionBound.trans (mul_le_mul_of_nonneg_left sigmaBound (by positivity))
      _ = _ := by ring
  have right:=norm_inner_le_norm (𝕜:=ℝ) (orbit (normalBuild x)) xi
  change |inner ℝ (orbit (normalBuild x)) xi| ≤ ‖orbit (normalBuild x)‖*‖xi‖ at right
  have rhs : inner ℝ (orbit (normalBuild x)) xi ≤ 2*‖x‖*‖xi‖ :=
    (le_abs_self _).trans (right.trans (mul_le_mul_of_nonneg_right orbitBound (norm_nonneg _)))
  have lhs:= (abs_le.mp (error.trans perturb)).1
  have tiny : 33868800*sourceRadius < 1/2 := by nlinarith [radius_strong]
  change ‖x‖ ≤ 4*‖xi‖
  nlinarith [norm_nonneg x,norm_nonneg xi,sq_nonneg ‖x‖]

theorem original_scalar_Parseval_bound (z : SourceCoordinateSlice) (p : Cotangent)
    (c : ℝ) (positive : 0 ≤ c)
    (bound : ∀ xi : Scalar, |PreparationPhaseGuard.ambientMomentum z p (xi,0)| ≤ c*‖xi‖) :
    scalarNormSquare z p ≤ c^2 := by
  let f : Scalar →ₗ[ℝ] ℝ := (PreparationPhaseGuard.ambientMomentum z p).comp
    (LinearMap.inl ℝ Scalar Gauge)
  let w : Scalar := ∑ a : ScalarIndex, f (scalarBasis a) • scalarBasis a
  have value : f w=∑ a : ScalarIndex, f (scalarBasis a)^2 := by
    simp [w,map_sum,map_smul,pow_two]
  have gram : ‖w‖^2=∑ a : ScalarIndex, f (scalarBasis a)^2 := by
    have representation : w=scalarBasis.repr.symm (WithLp.toLp 2 (fun a => f (scalarBasis a))) :=
      scalarBasis.sum_repr_symm (WithLp.toLp 2 (fun a => f (scalarBasis a)))
    rw [representation,LinearIsometryEquiv.norm_map,EuclideanSpace.real_norm_sq_eq]
  have estimate:=bound w
  change |f w|≤ c*‖w‖ at estimate
  rw [value,← gram,abs_of_nonneg (sq_nonneg ‖w‖)] at estimate
  have normBound : ‖w‖ ≤ c := by nlinarith [norm_nonneg w]
  change (∑ a : ScalarIndex, f (scalarBasis a)^2)≤ c^2
  rw [← gram]
  nlinarith [norm_nonneg w]

theorem phase_radius : sourceRadius < 1/(10 : ℝ)^100 := by
  norm_num [sourceRadius]

def gaugeSlot (i : Fin 33) : Fin 100 := ⟨67+i.val,by omega⟩

theorem original_gauge_free_decode (z : FlatConfiguration) (i : Fin 33) :
    gaugeFree (fullCoordinates.symm z).2.2 i=z (gaugeSlot i) := by
  change gaugeFree (gaugeFree.symm (fun j => z ⟨67+j.val,by omega⟩)) i=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem original_gauge_raw_decode (z : FlatConfiguration) :
    gaugeRaw (fullCoordinates.symm z).2.2.val=insertFree (fun i => z (gaugeSlot i)) := by
  change gaugeRaw (gaugeFree.symm (fun j => z ⟨67+j.val,by omega⟩)).val=_
  exact decode_original_rows _

theorem flat_source_bound (i : Fin 100) : |flatSource i| ≤ 1 := by
  have root : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg (2 : ℝ)]
  unfold flatSource
  split_ifs <;> simp -failIfUnchanged only [abs_one,abs_neg,abs_zero]
  all_goals solve
    | norm_num
    | (rw [abs_of_nonneg (by positivity)]; nlinarith [Real.sqrt_nonneg (2 : ℝ)])

theorem flat_box_bound (z : FlatConfiguration) (box : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (i : Fin 100) : |z i| ≤ 2 := by
  have bound:=abs_le.mp (box i)
  have center:=abs_le.mp (flat_source_bound i)
  rw [abs_le]
  constructor <;> linarith [radius_small.2]

theorem actual_gauge_raw_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i : Fin 3) (j : Fin 12) :
    |rawCoordinates (gaugeCoordinates (fullCoordinates.symm z).2.2.val i) j| ≤ 2 := by
  have all (k : Fin 36) : |gaugeRaw (fullCoordinates.symm z).2.2.val k| ≤ 2 := by
    rw [original_gauge_raw_decode]
    fin_cases k <;> simp only [insertFree]
    all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
    all_goals solve | norm_num | exact flat_box_bound z box _
  have value:=all (combinedRow i j)
  change |gaugeRead (fullCoordinates.symm z).2.2.val (combinedRow i j)| ≤ 2 at value
  unfold gaugeRead at value
  rw [spatial_combined,native_combined] at value
  exact value

theorem actual_gauge_raw_difference (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i : Fin 3) (j : Fin 12) :
    |rawCoordinates (gaugeCoordinates
      ((fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge) i) j| ≤ sourceRadius := by
  have source : SourceQuantumConfigurationHilbert.sourceGauge=(fullCoordinates.symm flatSource).2.2.val := by
    rw [← actual_flat_source,ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have all (k : Fin 36) : |gaugeRaw
      ((fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge) k| ≤ sourceRadius := by
    rw [source,map_sub]
    simp only [Pi.sub_apply]
    rw [original_gauge_raw_decode,original_gauge_raw_decode]
    fin_cases k <;> simp only [insertFree]
    all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
    all_goals solve | simpa using radius_small.1.le | exact box _
  have value:=all (combinedRow i j)
  change |gaugeRead ((fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge)
    (combinedRow i j)| ≤ sourceRadius at value
  unfold gaugeRead at value
  rw [spatial_combined,native_combined] at value
  exact value

theorem actual_normal_raw_bound (x : NormalCoordinates) (i : Fin 12) :
    |rawCoordinates (normalBuild x) i| ≤ ‖x‖ := by
  change |rawRead (normalBuild x) i| ≤ ‖x‖
  unfold rawRead
  simp only [normalBuild,LinearEquiv.apply_symm_apply]
  fin_cases i
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals solve
    | (simpa only [Real.norm_eq_abs,sub_zero] using PiLp.norm_apply_le x _)
    | simp

theorem actual_minor_lower (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) :
    1/4 ≤ firstGauge (fullCoordinates.symm z).2.2.val ∧
      1/4 ≤ secondGauge (fullCoordinates.symm z).2.2.val := by
  have root : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg (2 : ℝ)]
  have first:= (abs_le.mp (box 67)).1
  have second:= (abs_le.mp (box 77)).1
  norm_num [flatSource,Fin.ext_iff] at first second
  rw [decoded_firstGauge,decoded_secondGauge]
  constructor <;> nlinarith [radius_small.2]

def stabilizerCoefficients (a : NativeLie) : Fin 3 → ℝ :=
  ![2*(nativeCoordinates a).1 1,2*(nativeCoordinates a).1 0,2*(nativeCoordinates a).1 6]

theorem actual_inverse_rows (z : physicalChart) (xi : Scalar) :
    orbitRows (nativeGauge (normalBuild (normalRead (inverseLie z.val xi))) z.val.2.2.val)+
      ![-secondGauge z.val.2.2.val*stabilizerCoefficients (inverseLie z.val xi) 0+
          (nativeCoordinates (gaugeCoordinates z.val.2.2.val 1)).1 1*stabilizerCoefficients (inverseLie z.val xi) 1,
        firstGauge z.val.2.2.val*stabilizerCoefficients (inverseLie z.val xi) 1,
        -(nativeCoordinates (gaugeCoordinates z.val.2.2.val 0)).1 7/2*stabilizerCoefficients (inverseLie z.val xi) 0-
          firstGauge z.val.2.2.val*stabilizerCoefficients (inverseLie z.val xi) 2]=0 := by
  have rows:=congrArg orbitRows (original_gauge_inverse_equation z xi)
  rw [map_add,map_zero] at rows
  have tangent : orbitRows (inverseGauge z.val xi).val=0 := (inverseGauge z.val xi).property
  rw [tangent,add_zero] at rows
  nth_rw 1 [native_decomposition (inverseLie z.val xi)] at rows
  rw [map_add,LinearMap.add_apply,map_add] at rows
  change orbitRows (nativeGauge (normalBuild (normalRead (inverseLie z.val xi))) z.val.2.2.val)+
    orbitRows (gaugeAction (colorStabilizer (stabilizerCoefficients (inverseLie z.val xi))) z.val.2.2.val)=0 at rows
  rw [variable_rows] at rows
  exact rows

theorem normal_gauge_rows_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (x : NormalCoordinates) (i : Fin 3) :
    |orbitRows (nativeGauge (normalBuild x) (fullCoordinates.symm z).2.2.val) i| ≤ 200*‖x‖ := by
  have bound (j : Fin 3) (k : Fin 12) :
      |rawCoordinates (gaugeCoordinates
        (nativeGauge (normalBuild x) (fullCoordinates.symm z).2.2.val) j) k| ≤ 200*‖x‖ := by
    change |rawCoordinates (jointP286CoordinateLieBracket (normalBuild x)
      (gaugeCoordinates (fullCoordinates.symm z).2.2.val j)) k| ≤ _
    have primitive:=actual_raw_bracket_bound (normalBuild x)
      (gaugeCoordinates (fullCoordinates.symm z).2.2.val j) ‖x‖ 2 (norm_nonneg _) (by norm_num)
        (actual_normal_raw_bound x) (actual_gauge_raw_bound z box j) k
    nlinarith
  fin_cases i
  · exact bound 1 6
  · exact bound 0 6
  · exact bound 0 0

theorem actual_inverse_stabilizer_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (xi : Scalar) (i : Fin 3) :
    |stabilizerCoefficients (inverseLie (fullCoordinates.symm z) xi) i| ≤
      60000*‖normalRead (inverseLie (fullCoordinates.symm z) xi)‖ := by
  let native:=phaseChart z box
  let x:=normalRead (inverseLie native.val xi)
  let r:=stabilizerCoefficients (inverseLie native.val xi)
  let B:=native.val.2.2.val
  have rows:=actual_inverse_rows native xi
  have h0:=congrFun rows 0
  have h1:=congrFun rows 1
  have h2:=congrFun rows 2
  change orbitRows (nativeGauge (normalBuild x) B) 0+(-secondGauge B*r 0+
    (nativeCoordinates (gaugeCoordinates B 1)).1 1*r 1)=0 at h0
  change orbitRows (nativeGauge (normalBuild x) B) 1+firstGauge B*r 1=0 at h1
  change orbitRows (nativeGauge (normalBuild x) B) 2+
    (-(nativeCoordinates (gaugeCoordinates B 0)).1 7/2*r 0-firstGauge B*r 2)=0 at h2
  have small:=normal_gauge_rows_bound z box x
  change ∀ j : Fin 3, |orbitRows (nativeGauge (normalBuild x) B) j|≤200*‖x‖ at small
  have lower:=actual_minor_lower z box
  change 1/4≤ firstGauge B ∧ 1/4≤ secondGauge B at lower
  have b11 : |(nativeCoordinates (gaugeCoordinates B 1)).1 1|≤2 :=
    actual_gauge_raw_bound z box 1 1
  have b07 : |(nativeCoordinates (gaugeCoordinates B 0)).1 7|≤4 := by
    have first:=actual_gauge_raw_bound z box 0 6
    have second:=actual_gauge_raw_bound z box 0 7
    change |(nativeCoordinates (gaugeCoordinates B 0)).1 6|≤2 at first
    change |(nativeCoordinates (gaugeCoordinates B 0)).1 7-(nativeCoordinates (gaugeCoordinates B 0)).1 6|≤2 at second
    have sum:=abs_le.mp first
    have difference:=abs_le.mp second
    rw [abs_le]
    constructor <;> linarith
  have r1 : |r 1|≤800*‖x‖ := by
    have product : firstGauge B*|r 1|≤200*‖x‖ := by
      rw [← abs_of_pos (by linarith : 0 < firstGauge B),← abs_mul]
      have equal : firstGauge B*r 1=-orbitRows (nativeGauge (normalBuild x) B) 1 := by linarith
      rw [equal,abs_neg]
      exact small 1
    nlinarith [abs_nonneg (r 1)]
  have r0 : |r 0|≤7200*‖x‖ := by
    have product : secondGauge B*|r 0|≤1800*‖x‖ := by
      rw [← abs_of_pos (by linarith : 0 < secondGauge B),← abs_mul]
      have equal : secondGauge B*r 0=orbitRows (nativeGauge (normalBuild x) B) 0+
          (nativeCoordinates (gaugeCoordinates B 1)).1 1*r 1 := by linarith
      rw [equal]
      have pair:=mul_le_mul b11 r1 (abs_nonneg _) (by norm_num : (0 : ℝ)≤2)
      have sum:=abs_add_le (orbitRows (nativeGauge (normalBuild x) B) 0)
        ((nativeCoordinates (gaugeCoordinates B 1)).1 1*r 1)
      rw [abs_mul] at sum
      nlinarith [small 0]
    nlinarith [abs_nonneg (r 0)]
  have r2 : |r 2|≤58400*‖x‖ := by
    have product : firstGauge B*|r 2|≤14600*‖x‖ := by
      rw [← abs_of_pos (by linarith : 0 < firstGauge B),← abs_mul]
      have equal : firstGauge B*r 2=orbitRows (nativeGauge (normalBuild x) B) 2-
          (nativeCoordinates (gaugeCoordinates B 0)).1 7/2*r 0 := by linarith
      rw [equal]
      have pair:=mul_le_mul b07 r0 (abs_nonneg _) (by norm_num : (0 : ℝ)≤4)
      have sum:=real_abs_sub_le_sum (orbitRows (nativeGauge (normalBuild x) B) 2)
        ((nativeCoordinates (gaugeCoordinates B 0)).1 7/2*r 0)
      simp only [abs_mul,abs_div] at sum
      norm_num at sum
      nlinarith [small 2]
    nlinarith [abs_nonneg (r 2)]
  change |r i|≤60000*‖x‖
  fin_cases i
  · change |r 0|≤60000*‖x‖; nlinarith [norm_nonneg x]
  · change |r 1|≤60000*‖x‖; nlinarith [norm_nonneg x]
  · change |r 2|≤60000*‖x‖; nlinarith [norm_nonneg x]

theorem stabilizer_raw_coefficients_bound (r : Fin 3 → ℝ) (B : ℝ) (positive : 0 ≤ B)
    (bound : ∀ i,|r i|≤ B) (j : Fin 12) : |rawCoordinates (colorCombination r) j|≤ B := by
  change |rawRead (colorCombination r) j|≤ B
  unfold rawRead
  rw [colorCombination_coordinates]
  fin_cases j
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num only [zero_sub,abs_neg,abs_div,abs_zero]
  all_goals linarith [bound 0,bound 1,bound 2]

theorem actual_inverse_lie_raw_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i|≤ sourceRadius) (xi : Scalar) (i : Fin 12) :
    |rawCoordinates (inverseLie (fullCoordinates.symm z) xi) i|≤1000000*‖xi‖ := by
  let a:=inverseLie (fullCoordinates.symm z) xi
  let x:=normalRead a
  have normal:=actual_normal_raw_bound x i
  have stabilizer:=stabilizer_raw_coefficients_bound (stabilizerCoefficients a) (60000*‖x‖)
    (by positivity) (actual_inverse_stabilizer_bound z box xi) i
  have coefficient : rawCoordinates a i=rawCoordinates (normalBuild x) i+
      rawCoordinates (colorCombination (stabilizerCoefficients a)) i := by
    nth_rw 1 [native_decomposition a]
    rw [map_add]
    rfl
  have sum:=abs_add_le (rawCoordinates (normalBuild x) i)
    (rawCoordinates (colorCombination (stabilizerCoefficients a)) i)
  rw [coefficient]
  have original:=original_inverse_normal_bound z box xi
  change ‖x‖≤4*‖xi‖ at original
  nlinarith [norm_nonneg xi]

theorem actual_inverse_action_perturbation (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i|≤ sourceRadius) (xi : Scalar) :
    ‖action ((fullCoordinates.symm z).2.1 : Scalar) (inverseLie (fullCoordinates.symm z) xi)‖≤
      30000000000000*sourceRadius*‖xi‖ := by
  have primitive:=actual_full_scalar_action_bound (inverseLie (fullCoordinates.symm z) xi)
    ((fullCoordinates.symm z).2.1 : Scalar)
  have total : (∑ i : Fin 12,|rawCoordinates (inverseLie (fullCoordinates.symm z) xi) i|)≤12000000*‖xi‖ := by
    have sum:=Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 12) _ => actual_inverse_lie_raw_bound z box xi i)
    norm_num at sum
    nlinarith
  have sigma:=scalar_box_norm z (closed_box_outer z box)
  have actionBound:=primitive.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left total (by norm_num : (0 : ℝ)≤117600)) (norm_nonneg _))
  have product:=mul_le_mul_of_nonneg_left sigma (by positivity : (0 : ℝ)≤117600*(12000000*‖xi‖))
  have small:=radius_small.1
  nlinarith [norm_nonneg xi]

theorem actual_inverse_scalar_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i|≤ sourceRadius) (xi : Scalar) :
    ‖(inverseScalar (fullCoordinates.symm z) xi : Scalar)‖≤10*‖xi‖ := by
  let native:=phaseChart z box
  let a:=inverseLie native.val xi
  have split : action (vacuum+(native.val.2.1 : Scalar)) a=
      orbit a+action (native.val.2.1 : Scalar) a := by
    change StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear a
      (vacuum+(native.val.2.1 : Scalar))=_
    exact map_add _ _ _
  have sameOrbit : orbit a=orbit (normalBuild (normalRead a)) := by
    nth_rw 1 [native_decomposition a]
    rw [map_add,show orbit (stabilizerPart a).val=0 from (stabilizerPart a).property,add_zero]
  have equation:=original_scalar_inverse_equation native xi
  rw [split,sameOrbit] at equation
  have value : (inverseScalar native.val xi : Scalar)=
      xi-(orbit (normalBuild (normalRead a))+action (native.val.2.1 : Scalar) a) := by
    exact eq_sub_of_add_eq' equation
  have normal:=original_inverse_normal_bound z box xi
  have orbitBound:=(normal_orbit_upper (normalRead a)).trans (mul_le_mul_of_nonneg_left normal (by norm_num))
  have perturb:=actual_inverse_action_perturbation z box xi
  change ‖action (native.val.2.1 : Scalar) a‖≤30000000000000*sourceRadius*‖xi‖ at perturb
  have small : 30000000000000*sourceRadius<1 := by nlinarith [phase_radius]
  change ‖(inverseScalar native.val xi : Scalar)‖≤10*‖xi‖
  rw [value]
  have triangle:=(norm_sub_le xi (orbit (normalBuild (normalRead a))+action (native.val.2.1 : Scalar) a)).trans
    (add_le_add le_rfl (norm_add_le _ _))
  nlinarith [norm_nonneg xi]

theorem scalar_real_coordinate_bound (phi : Scalar) (i : Fin 70) : |scalarRealify phi i|≤ ‖phi‖ := by
  change |scalarRead phi i|≤ ‖phi‖
  unfold scalarRead
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le phi _)
  · exact (Complex.abs_im_le_norm _).trans (PiLp.norm_apply_le phi _)

theorem actual_scalar_slice_read_bound (s : scalarSlice) (i : Fin 61) : |scalarFree s i|≤4*‖s.val‖ := by
  rw [scalar_free_read]
  have one (j : Fin 70) : |scalarRealify s.val j|≤4*‖s.val‖ :=
    (scalar_real_coordinate_bound s.val j).trans (by nlinarith [norm_nonneg s.val])
  have pair (j k : Fin 70) : |scalarRealify s.val j-scalarRealify s.val k|≤4*‖s.val‖ :=
    (real_abs_sub_le_sum _ _).trans (by
      nlinarith [scalar_real_coordinate_bound s.val j,scalar_real_coordinate_bound s.val k,norm_nonneg s.val])
  have four (j k l m : Fin 70) :
      |scalarRealify s.val j-scalarRealify s.val k-scalarRealify s.val l+scalarRealify s.val m|≤4*‖s.val‖ := by
    have a:=abs_le.mp (scalar_real_coordinate_bound s.val j)
    have b:=abs_le.mp (scalar_real_coordinate_bound s.val k)
    have c:=abs_le.mp (scalar_real_coordinate_bound s.val l)
    have d:=abs_le.mp (scalar_real_coordinate_bound s.val m)
    rw [abs_le]
    constructor <;> linarith
  fin_cases i <;> simp only [read61]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals solve | exact one _ | exact pair _ _ | exact four _ _ _ _

theorem actual_inverse_gauge_raw_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i|≤ sourceRadius) (xi : Scalar) (i : Fin 3) (j : Fin 12) :
    |rawCoordinates (gaugeCoordinates (inverseGauge (fullCoordinates.symm z) xi).val i) j|≤200000000*‖xi‖ := by
  let native:=phaseChart z box
  have relation:=original_gauge_inverse_equation native xi
  have gauge : (inverseGauge native.val xi : Gauge)=-nativeGauge (inverseLie native.val xi) native.val.2.2.val :=
    eq_neg_of_add_eq_zero_right relation
  change |rawCoordinates (gaugeCoordinates (inverseGauge native.val xi).val i) j|≤200000000*‖xi‖
  rw [gauge,map_neg,Pi.neg_apply,map_neg]
  simp only [Pi.neg_apply,abs_neg]
  change |rawCoordinates (jointP286CoordinateLieBracket (inverseLie native.val xi)
    (gaugeCoordinates native.val.2.2.val i)) j|≤ _
  have primitive:=actual_raw_bracket_bound (inverseLie native.val xi)
    (gaugeCoordinates native.val.2.2.val i) (1000000*‖xi‖) 2 (by positivity) (by norm_num)
      (actual_inverse_lie_raw_bound z box xi) (actual_gauge_raw_bound z box i) j
  nlinarith

theorem actual_inverse_coordinate_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i|≤ sourceRadius) (xi : Scalar) (k : Fin 100) :
    |fullCoordinates (0,(inverseScalar (fullCoordinates.symm z) xi,inverseGauge (fullCoordinates.symm z) xi)) k|≤
      200000000*‖xi‖ := by
  rw [full_blocks,map_zero,← scalar_free_read]
  change |joinCoordinates (0,scalarFree (inverseScalar (fullCoordinates.symm z) xi),
    gaugeFree (inverseGauge (fullCoordinates.symm z) xi)) k|≤ _
  unfold joinCoordinates
  split_ifs with coframe scalar
  · simp only [Pi.zero_apply,abs_zero]; positivity
  · have bound:=actual_scalar_slice_read_bound (inverseScalar (fullCoordinates.symm z) xi)
      ⟨k.val-6,by omega⟩
    have original:=actual_inverse_scalar_bound z box xi
    nlinarith [norm_nonneg xi]
  · let i : Fin 33 := ⟨k.val-67,by omega⟩
    have bound:=actual_inverse_gauge_raw_bound z box xi (spatialRow (freeRow i)) (nativeRow (freeRow i))
    change |gaugeFree (inverseGauge (fullCoordinates.symm z) xi) i|≤ _ at bound
    exact bound

theorem actual_scalar_cotangent_box_error (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) (xi : Scalar) :
    |PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) (xi,0)-
      PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z) (nativeCovector sourceMomentum) (xi,0)|≤
      20000000000*sourceRadius*‖xi‖ := by
  change |nativeCovector (WithLp.toLp 2 u)
      (0,(inverseL (fullCoordinates.symm z) (xi,0)).2)-nativeCovector sourceMomentum
      (0,(inverseL (fullCoordinates.symm z) (xi,0)).2)|≤ _
  simp only [nativeCovector_apply]
  change |(∑ i : Fin 100,u i*fullCoordinates
      (0,(inverseScalar (fullCoordinates.symm z) xi,inverseGauge (fullCoordinates.symm z) xi)) i)-
    ∑ i : Fin 100,sourceUnitMomentum i*fullCoordinates
      (0,(inverseScalar (fullCoordinates.symm z) xi,inverseGauge (fullCoordinates.symm z) xi)) i|≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have term (i : Fin 100) : |(u i-sourceUnitMomentum i)*fullCoordinates
      (0,(inverseScalar (fullCoordinates.symm z) xi,inverseGauge (fullCoordinates.symm z) xi)) i|≤
      sourceRadius*(200000000*‖xi‖) := by
    rw [abs_mul]
    exact mul_le_mul (ubox i) (actual_inverse_coordinate_bound z zbox xi i)
      (abs_nonneg _) radius_small.1.le
  calc
    _ ≤ ∑ i : Fin 100, |(u i-sourceUnitMomentum i)*fullCoordinates
        (0,(inverseScalar (fullCoordinates.symm z) xi,inverseGauge (fullCoordinates.symm z) xi)) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 100, sourceRadius*(200000000*‖xi‖) :=
      Finset.sum_le_sum (fun i _ => term i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

def scalarPairRead : Scalar →ₗ[ℝ] ℝ where
  toFun phi := (phi (lexIndex 13)).im+(phi (lexIndex 15)).im
  map_add' x y := by simp [PiLp.add_apply]; ring
  map_smul' r x := by simp [PiLp.smul_apply,smul_eq_mul,mul_add]

theorem scalar_pair_orbit (a : NativeLie) :
    scalarPairRead (orbit a)=2*(nativeCoordinates a).1 5 := by
  let c:=(nativeCoordinates a).1
  let w:=(nativeCoordinates a).2.1
  let h:=(nativeCoordinates a).2.2
  have restore : a=nativeCoordinates.symm (c,w,h) := by
    rw [← LinearEquiv.symm_apply_apply nativeCoordinates a]
  nth_rw 1 [restore]
  change (orbit (nativeCoordinates.symm (c,w,h)) (lexIndex 13)).im+
    (orbit (nativeCoordinates.symm (c,w,h)) (lexIndex 15)).im=2*c 5
  rw [sourceOrbit_all,sourceOrbit_all]
  simp only [sourceOrbit35]
  dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  simp
  ring

theorem scalar_pair_inner (xi : Scalar) : scalarPairRead xi=
    inner ℝ (orbit (normalBuild (PiLp.single 2 (3 : Fin 9) 1))) xi := by
  rw [scalar_inner_lex]
  simp_rw [normalBuild,sourceOrbit_all]
  simp [Fin.sum_univ_succ,sourceOrbit35,scalarPairRead]

theorem scalar_pair_slice_zero (s : scalarSlice) : scalarPairRead s.val=0 := by
  rw [scalar_pair_inner]
  exact (Submodule.mem_orthogonal _ _).mp s.property
    (orbit (normalBuild (PiLp.single 2 (3 : Fin 9) 1))) ⟨_,rfl⟩

theorem scalar_pair_bound (xi : Scalar) : |scalarPairRead xi|≤2*‖xi‖ := by
  change |(xi (lexIndex 13)).im+(xi (lexIndex 15)).im|≤ _
  exact (abs_add_le _ _).trans (show |(xi (lexIndex 13)).im|+|(xi (lexIndex 15)).im|≤2*‖xi‖ by
    have first:=(Complex.abs_im_le_norm _).trans (PiLp.norm_apply_le xi (lexIndex 13))
    have second:=(Complex.abs_im_le_norm _).trans (PiLp.norm_apply_le xi (lexIndex 15))
    linarith)

theorem actual_inverse_scalar_pair (z : physicalChart) (xi : Scalar) :
    scalarPairRead xi=2*(nativeCoordinates (inverseLie z.val xi)).1 5+
      scalarPairRead (action (z.val.2.1 : Scalar) (inverseLie z.val xi)) := by
  have original:=congrArg scalarPairRead (original_scalar_inverse_equation z xi)
  have split : action (vacuum+(z.val.2.1 : Scalar)) (inverseLie z.val xi)=
      orbit (inverseLie z.val xi)+action (z.val.2.1 : Scalar) (inverseLie z.val xi) := by
    change StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (inverseLie z.val xi)
      (vacuum+(z.val.2.1 : Scalar))=_
    exact map_add _ _ _
  rw [split,map_add,map_add,scalar_pair_orbit,scalar_pair_slice_zero,add_zero] at original
  exact original.symm

theorem source_gauge_momentum_bounds :
    0 ≤ sourceUnitMomentum 67 ∧ sourceUnitMomentum 67 ≤ 2/5 := by
  rw [sourceUnitMomentum,if_neg (by decide),if_pos (by decide)]
  have root : Real.sqrt 3563≤60 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤3563),Real.sqrt_nonneg (3563 : ℝ)]
  constructor
  · positivity
  · nlinarith

theorem source_gauge_scale_bounds : 0 ≤ Stage9C.Material.SpinPair.gaugeScale ∧
    Stage9C.Material.SpinPair.gaugeScale ≤ 9/10 := by
  have original:=source_gauge_scale
  have root : Real.sqrt 2≤3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg (2 : ℝ)]
  constructor <;> nlinarith [Real.sqrt_nonneg (2 : ℝ)]

def sourceScalarRead : Scalar →ₗ[ℝ] ℝ :=
  (Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/4) • scalarPairRead

theorem sourceScalarRead_bound (xi : Scalar) : |sourceScalarRead xi|≤ (1/5)*‖xi‖ := by
  have g:=source_gauge_scale_bounds
  have b:=source_gauge_momentum_bounds
  have coefficientNonneg : 0≤ Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/4 :=
    div_nonneg (mul_nonneg g.1 b.1) (by norm_num)
  have coefficient : Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/4≤1/10 := by
    have product:=mul_le_mul g.2 b.2 b.1 (by norm_num : (0 : ℝ)≤9/10)
    nlinarith
  change |(Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/4)*scalarPairRead xi|≤ _
  rw [abs_mul,abs_of_nonneg coefficientNonneg]
  have bound:=mul_le_mul coefficient (scalar_pair_bound xi) (abs_nonneg _) (by norm_num : (0 : ℝ)≤1/10)
  nlinarith

theorem actual_source_scalar_read_error (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (xi : Scalar) :
    |sourceScalarRead (action ((fullCoordinates.symm z).2.1 : Scalar)
      (inverseLie (fullCoordinates.symm z) xi))| ≤ 6000000000000*sourceRadius*‖xi‖ := by
  have read:=sourceScalarRead_bound (action ((fullCoordinates.symm z).2.1 : Scalar)
    (inverseLie (fullCoordinates.symm z) xi))
  have original:=actual_inverse_action_perturbation z box xi
  nlinarith

theorem actual_source_gauge_read_error (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (xi : Scalar) :
    |sourceUnitMomentum 67*(gaugeRaw (nativeGauge (inverseLie (fullCoordinates.symm z) xi)
      ((fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge)) 1+
      gaugeRaw (nativeGauge (inverseLie (fullCoordinates.symm z) xi)
        ((fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge)) 15+
      gaugeRaw (nativeGauge (inverseLie (fullCoordinates.symm z) xi)
        ((fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge)) 30)| ≤
      120000000*sourceRadius*‖xi‖ := by
  let a:=inverseLie (fullCoordinates.symm z) xi
  let d:=(fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge
  let g:=nativeGauge a d
  have each (j : Fin 36) : |gaugeRaw g j| ≤ 100000000*sourceRadius*‖xi‖ := by
    change |rawCoordinates (jointP286CoordinateLieBracket a (gaugeCoordinates d (spatialRow j))) (nativeRow j)| ≤ _
    have primitive:=actual_raw_bracket_bound a (gaugeCoordinates d (spatialRow j))
      (1000000*‖xi‖) sourceRadius (by positivity) radius_small.1.le
        (actual_inverse_lie_raw_bound z box xi) (actual_gauge_raw_difference z box (spatialRow j)) (nativeRow j)
    nlinarith
  have sum : |gaugeRaw g 1+gaugeRaw g 15+gaugeRaw g 30| ≤ 300000000*sourceRadius*‖xi‖ := by
    have first:=abs_add_le (gaugeRaw g 1) (gaugeRaw g 15)
    have second:=abs_add_le (gaugeRaw g 1+gaugeRaw g 15) (gaugeRaw g 30)
    nlinarith [each 1,each 15,each 30]
  change |sourceUnitMomentum 67*(gaugeRaw g 1+gaugeRaw g 15+gaugeRaw g 30)| ≤ _
  rw [abs_mul,abs_of_nonneg source_gauge_momentum_bounds.1]
  have product:=mul_le_mul source_gauge_momentum_bounds.2 sum (abs_nonneg _) (by norm_num : (0 : ℝ)≤2/5)
  nlinarith

def sourceGaugeRead : Gauge →ₗ[ℝ] ℝ where
  toFun g := sourceUnitMomentum 67*(gaugeRaw g 1+gaugeRaw g 15+gaugeRaw g 30)
  map_add' g h := by simp only [map_add,Pi.add_apply]; ring
  map_smul' r g := by simp only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem actual_reference_scalar_identity (z : physicalChart) (xi : Scalar) :
    PreparationPhaseGuard.ambientMomentum z.val (nativeCovector sourceMomentum) (xi,0)=
      sourceScalarRead xi-sourceScalarRead (action (z.val.2.1 : Scalar) (inverseLie z.val xi))-
        sourceGaugeRead (nativeGauge (inverseLie z.val xi)
          (z.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge)) := by
  let a:=inverseLie z.val xi
  let n:=nativeGauge a z.val.2.2.val
  let s:=nativeGauge a SourceQuantumConfigurationHilbert.sourceGauge
  have original : PreparationPhaseGuard.ambientMomentum z.val (nativeCovector sourceMomentum) (xi,0)=
      sourceGaugeRead (inverseGauge z.val xi).val := by
    change nativeCovector sourceMomentum (0,(inverseScalar z.val xi,inverseGauge z.val xi))=_
    exact PreparationPhaseSource.original_source_covector _ _
  have gamma : (inverseGauge z.val xi : Gauge)=-n :=
    eq_neg_of_add_eq_zero_right (original_gauge_inverse_equation z xi)
  rw [gamma,map_neg] at original
  have delta : sourceGaugeRead (nativeGauge a (z.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge))=
      sourceGaugeRead n-sourceGaugeRead s := by
    rw [map_sub,map_sub]
  have source : sourceGaugeRead s=-Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/2*
      (nativeCoordinates a).1 5 := by
    have rows:=PreparationPhaseSource.original_source_gauge_bracket a
    change gaugeRaw s 1=0 ∧ gaugeRaw s 15=-Stage9C.Material.SpinPair.gaugeScale/2*
      (nativeCoordinates a).1 5 ∧ gaugeRaw s 30=0 at rows
    change sourceUnitMomentum 67*(gaugeRaw s 1+gaugeRaw s 15+gaugeRaw s 30)=_
    rw [rows.1,rows.2.1,rows.2.2]
    ring
  have pair:=actual_inverse_scalar_pair z xi
  have scalar : sourceScalarRead xi=Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/2*
      (nativeCoordinates a).1 5+sourceScalarRead (action (z.val.2.1 : Scalar) a) := by
    change (Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/4)*scalarPairRead xi=_
    rw [pair]
    change (Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/4)*
      (2*(nativeCoordinates a).1 5+scalarPairRead (action (z.val.2.1 : Scalar) a))=
      Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/2*(nativeCoordinates a).1 5+
        (Stage9C.Material.SpinPair.gaugeScale*sourceUnitMomentum 67/4)*scalarPairRead (action (z.val.2.1 : Scalar) a)
    ring
  change PreparationPhaseGuard.ambientMomentum z.val (nativeCovector sourceMomentum) (xi,0)=
    sourceScalarRead xi-sourceScalarRead (action (z.val.2.1 : Scalar) a)-
      sourceGaugeRead (nativeGauge a (z.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge))
  linarith

theorem actual_reference_scalar_error (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (xi : Scalar) :
    |PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z) (nativeCovector sourceMomentum) (xi,0)-
      sourceScalarRead xi| ≤ 10000000000000*sourceRadius*‖xi‖ := by
  let native:=phaseChart z box
  have original:=actual_reference_scalar_identity native xi
  have scalar:=actual_source_scalar_read_error z box xi
  have gauge:=actual_source_gauge_read_error z box xi
  change |sourceGaugeRead (nativeGauge (inverseLie (fullCoordinates.symm z) xi)
    ((fullCoordinates.symm z).2.2.val-SourceQuantumConfigurationHilbert.sourceGauge))|≤
      120000000*sourceRadius*‖xi‖ at gauge
  change |PreparationPhaseGuard.ambientMomentum native.val (nativeCovector sourceMomentum) (xi,0)-
    sourceScalarRead xi|≤ _
  rw [original]
  have triangle:=real_abs_sub_le_sum
    (-sourceScalarRead (action (native.val.2.1 : Scalar) (inverseLie native.val xi)))
    (sourceGaugeRead (nativeGauge (inverseLie native.val xi)
      (native.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge)))
  rw [abs_neg] at triangle
  have algebra : sourceScalarRead xi-sourceScalarRead (action (native.val.2.1 : Scalar) (inverseLie native.val xi))-
      sourceGaugeRead (nativeGauge (inverseLie native.val xi)
        (native.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge))-sourceScalarRead xi=
    -sourceScalarRead (action (native.val.2.1 : Scalar) (inverseLie native.val xi))-
      sourceGaugeRead (nativeGauge (inverseLie native.val xi)
        (native.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge)) := by ring
  rw [algebra]
  change |sourceScalarRead (action (native.val.2.1 : Scalar) (inverseLie native.val xi))|≤
    6000000000000*sourceRadius*‖xi‖ at scalar
  change |sourceGaugeRead (nativeGauge (inverseLie native.val xi)
    (native.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge))|≤120000000*sourceRadius*‖xi‖ at gauge
  nlinarith [mul_nonneg radius_small.1.le (norm_nonneg xi)]

theorem actual_scalar_functional_bound (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) (xi : Scalar) :
    |PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) (xi,0)|≤
      (1/4)*‖xi‖ := by
  let f:=PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) (xi,0)
  let g:=PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z) (nativeCovector sourceMomentum) (xi,0)
  have momentum:=actual_scalar_cotangent_box_error z u zbox ubox xi
  have reference:=actual_reference_scalar_error z zbox xi
  have source:=sourceScalarRead_bound xi
  have triangle:=abs_sub_le f g (sourceScalarRead xi)
  have value:=abs_sub_le f (sourceScalarRead xi) 0
  simp only [sub_zero] at value
  have margin : 10020000000000*sourceRadius≤1/20 := by nlinarith [phase_radius]
  have scaled:=mul_le_mul_of_nonneg_right margin (norm_nonneg xi)
  change |f|≤ (1/4)*‖xi‖
  change |f-g|≤20000000000*sourceRadius*‖xi‖ at momentum
  change |g-sourceScalarRead xi|≤10000000000000*sourceRadius*‖xi‖ at reference
  nlinarith

theorem actual_closed_phase_scalarNorm (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) :
    scalarNormSquare (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))≤1/16 := by
  have original:=original_scalar_Parseval_bound (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
    (1/4) (by norm_num) (actual_scalar_functional_bound z u zbox ubox)
  norm_num at original
  exact original

theorem actual_closed_phase_A (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1) :
    0 < A (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) := by
  let native:=phaseChart z zbox
  have coframe:=coframe_polynomial_positive z u zbox ubox unit
  have scalar:=actual_closed_phase_scalarNorm z u zbox ubox
  change 0 < A native.val (nativeCovector (WithLp.toLp 2 u))
  rw [A_original_numerator]
  apply div_pos
  · change 0 < polynomialPrincipal (fullCoordinates.symm z).1 (fun i => u (coframeSlot i))-
      2*scalarNormSquare (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))
    linarith
  · exact mul_pos (by norm_num) (volume_pos native)

end LowEnergy.PreparationPhaseScalar
