import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockPoleSupport

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockGuard
open SaturationMonoid.PhysicsCore StageNineP286GaugeConnectionVariationDensity StageNineHolonomicField
open StageNineCoframeGravityGaugeRegularity
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates
open PreparationChartGuard PreparationPhaseScalar PreparationPhaseSource PreparationPhaseBounds
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumNativeDimensions
open SourceQuantumResidualFlow SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open GaussLiveMomentum GaussCoreDifferential GaussNativeEnergy GaussNativeForm GaussHistoryHilbert
open scoped BigOperators Matrix RealInnerProductSpace

def residualLie (z : physicalChart) (g : Gauge) : stabilizer :=
  ((residualEquiv z).symm g).1

def residualGauge (z : physicalChart) (g : Gauge) : coordinateSlice :=
  ((residualEquiv z).symm g).2

def residualScalar (z : physicalChart) (g : Gauge) : scalarSlice :=
  -scalarAction (residualLie z g) z.val.2.1

theorem residual_gauge_equation (z : physicalChart) (g : Gauge) :
    gaugeAction (residualLie z g) z.val.2.2.val + (residualGauge z g).val = g := by
  simpa only [residualLie,residualGauge,residualEquiv_apply] using
    (residualEquiv z).apply_symm_apply g

theorem residual_slice_inverse (z : physicalChart) (g : Gauge) :
    inverseL z.val (0,g) =
      ((residualLie z g).val,(residualScalar z g,residualGauge z g)) := by
  have split : splitMap z.val
      ((residualLie z g).val,(residualScalar z g,residualGauge z g)) = (0,g) := by
    apply Prod.ext
    · change action (vacuum+(z.val.2.1 : Scalar)) (residualLie z g).val +
        (residualScalar z g : Scalar) = 0
      change scalarP286ActionBilinear (residualLie z g).val (vacuum+(z.val.2.1 : Scalar)) +
        -(scalarP286ActionBilinear (residualLie z g).val (z.val.2.1 : Scalar)) = 0
      rw [map_add,show scalarP286ActionBilinear (residualLie z g).val vacuum=0 from
        (residualLie z g).property,zero_add,add_neg_cancel]
    · change nativeGauge (residualLie z g).val z.val.2.2.val + (residualGauge z g).val = g
      rw [nativeGauge_stabilizer]
      exact residual_gauge_equation z g
  rw [←split,inverse_left]

theorem residual_momentum_readback (z : physicalChart) (g : Gauge) (u : FlatConfiguration) :
    PreparationPhaseGuard.ambientMomentum z.val
        (nativeCovector (WithLp.toLp 2 u)) (0,g) =
      nativeCovector (WithLp.toLp 2 u) (0,(residualScalar z g,residualGauge z g)) := by
  change nativeCovector (WithLp.toLp 2 u) (0,(inverseL z.val (0,g)).2) = _
  rw [residual_slice_inverse]

def residualCoefficients (z : physicalChart) (g : Gauge) : Fin 3 → ℝ :=
  colorStabilizerEquiv.symm (residualLie z g)

theorem residualLie_coefficients (z : physicalChart) (g : Gauge) :
    residualLie z g = colorStabilizer (residualCoefficients z g) :=
  (colorStabilizerEquiv.apply_symm_apply _).symm

theorem residual_rows (z : physicalChart) (g : Gauge) :
    ![-secondGauge z.val.2.2.val*residualCoefficients z g 0+
          (nativeCoordinates (gaugeCoordinates z.val.2.2.val 1)).1 1*residualCoefficients z g 1,
        firstGauge z.val.2.2.val*residualCoefficients z g 1,
        -(nativeCoordinates (gaugeCoordinates z.val.2.2.val 0)).1 7/2*residualCoefficients z g 0-
          firstGauge z.val.2.2.val*residualCoefficients z g 2] = orbitRows g := by
  have rows := congrArg orbitRows (residual_gauge_equation z g)
  rw [map_add,(residualGauge z g).property,add_zero,residualLie_coefficients,
    variable_rows] at rows
  exact rows

def cartanGauge (i : Fin 3) : Gauge :=
  gaugeCoordinates.symm (Pi.single i (rawCoordinates.symm (Pi.single (6 : Fin 12) 1)))

theorem cartanGauge_coordinates (i k : Fin 3) (a : Fin 12) :
    rawCoordinates (gaugeCoordinates (cartanGauge i) k) a =
      if k=i then if a=6 then 1 else 0 else 0 := by
  by_cases selected : k=i <;> simp [cartanGauge,Pi.single_apply,selected]

theorem cartanGauge_raw_bound (i : Fin 3) (k : Fin 36) :
    |gaugeRaw (cartanGauge i) k| ≤ 1 := by
  change |rawCoordinates (gaugeCoordinates (cartanGauge i) (spatialRow k)) (nativeRow k)| ≤ 1
  rw [cartanGauge_coordinates]
  split_ifs <;> norm_num

theorem cartanGauge_rows_bound (i : Fin 3) (k : Fin 3) :
    |orbitRows (cartanGauge i) k| ≤ 1 := by
  fin_cases k
  · change |rawCoordinates (gaugeCoordinates (cartanGauge i) 1) 6| ≤ 1
    rw [cartanGauge_coordinates]
    split_ifs <;> norm_num
  · change |rawCoordinates (gaugeCoordinates (cartanGauge i) 0) 6| ≤ 1
    rw [cartanGauge_coordinates]
    split_ifs <;> norm_num
  · change |rawCoordinates (gaugeCoordinates (cartanGauge i) 0) 0| ≤ 1
    rw [cartanGauge_coordinates]
    split_ifs <;> norm_num

theorem residual_coefficients_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i k : Fin 3) :
    |residualCoefficients (phaseChart z box) (cartanGauge i) k| ≤ 300 := by
  let native := phaseChart z box
  let r := residualCoefficients native (cartanGauge i)
  let B := native.val.2.2.val
  have rows := residual_rows native (cartanGauge i)
  have h0 := congrFun rows 0
  have h1 := congrFun rows 1
  have h2 := congrFun rows 2
  change -secondGauge B*r 0+(nativeCoordinates (gaugeCoordinates B 1)).1 1*r 1 =
    orbitRows (cartanGauge i) 0 at h0
  change firstGauge B*r 1 = orbitRows (cartanGauge i) 1 at h1
  change -(nativeCoordinates (gaugeCoordinates B 0)).1 7/2*r 0-firstGauge B*r 2 =
    orbitRows (cartanGauge i) 2 at h2
  have lower := actual_minor_lower z box
  change 1/4 ≤ firstGauge B ∧ 1/4 ≤ secondGauge B at lower
  have b11 : |(nativeCoordinates (gaugeCoordinates B 1)).1 1| ≤ 2 :=
    actual_gauge_raw_bound z box 1 1
  have b07 : |(nativeCoordinates (gaugeCoordinates B 0)).1 7| ≤ 4 := by
    have first := actual_gauge_raw_bound z box 0 6
    have second := actual_gauge_raw_bound z box 0 7
    change |(nativeCoordinates (gaugeCoordinates B 0)).1 6| ≤ 2 at first
    change |(nativeCoordinates (gaugeCoordinates B 0)).1 7-
      (nativeCoordinates (gaugeCoordinates B 0)).1 6| ≤ 2 at second
    have sum := abs_le.mp first
    have difference := abs_le.mp second
    rw [abs_le]
    constructor <;> linarith
  have r1 : |r 1| ≤ 4 := by
    have product : firstGauge B*|r 1| ≤ 1 := by
      rw [←abs_of_pos (by linarith : 0 < firstGauge B),←abs_mul,h1]
      exact cartanGauge_rows_bound i 1
    nlinarith [abs_nonneg (r 1)]
  have r0 : |r 0| ≤ 36 := by
    have product : secondGauge B*|r 0| ≤ 9 := by
      have equal : secondGauge B*r 0 =
          (nativeCoordinates (gaugeCoordinates B 1)).1 1*r 1-orbitRows (cartanGauge i) 0 := by
        linarith
      rw [←abs_of_pos (by linarith : 0 < secondGauge B),←abs_mul,equal]
      have pair := mul_le_mul b11 r1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      have sum := real_abs_sub_le_sum ((nativeCoordinates (gaugeCoordinates B 1)).1 1*r 1)
        (orbitRows (cartanGauge i) 0)
      rw [abs_mul] at sum
      nlinarith [cartanGauge_rows_bound i 0]
    nlinarith [abs_nonneg (r 0)]
  have r2 : |r 2| ≤ 292 := by
    have product : firstGauge B*|r 2| ≤ 73 := by
      have equal : firstGauge B*r 2 =
          -(nativeCoordinates (gaugeCoordinates B 0)).1 7/2*r 0-orbitRows (cartanGauge i) 2 := by
        linarith
      rw [←abs_of_pos (by linarith : 0 < firstGauge B),←abs_mul,equal]
      have pair := mul_le_mul b07 r0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
      have sum := real_abs_sub_le_sum (-(nativeCoordinates (gaugeCoordinates B 0)).1 7/2*r 0)
        (orbitRows (cartanGauge i) 2)
      simp only [abs_mul,abs_div,abs_neg] at sum
      norm_num at sum
      nlinarith [cartanGauge_rows_bound i 2]
    nlinarith [abs_nonneg (r 2)]
  change |r k| ≤ 300
  fin_cases k
  · change |r 0| ≤ 300; linarith
  · change |r 1| ≤ 300; linarith
  · change |r 2| ≤ 300; linarith

theorem residual_lie_raw_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i : Fin 3) (k : Fin 12) :
    |rawCoordinates (residualLie (phaseChart z box) (cartanGauge i)).val k| ≤ 300 := by
  rw [residualLie_coefficients]
  exact stabilizer_raw_coefficients_bound _ 300 (by norm_num)
    (residual_coefficients_bound z box i) k

theorem sourceGaugeRead_stabilizer (a : stabilizer) :
    sourceGaugeRead (nativeGauge a.val SourceQuantumConfigurationHilbert.sourceGauge)=0 := by
  have rows := original_source_gauge_bracket a.val
  have zero : (nativeCoordinates a.val).1 5=0 := by
    obtain ⟨r,rfl⟩ := colorStabilizerEquiv.surjective a
    change (nativeCoordinates (colorCombination r)).1 5=0
    rw [colorCombination_coordinates]
    rfl
  change gaugeRaw (nativeGauge a.val SourceQuantumConfigurationHilbert.sourceGauge) 1=0 ∧
    gaugeRaw (nativeGauge a.val SourceQuantumConfigurationHilbert.sourceGauge) 15=
      -Stage9C.Material.SpinPair.gaugeScale/2*(nativeCoordinates a.val).1 5 ∧
    gaugeRaw (nativeGauge a.val SourceQuantumConfigurationHilbert.sourceGauge) 30=0 at rows
  change sourceUnitMomentum 67*(gaugeRaw (nativeGauge a.val
    SourceQuantumConfigurationHilbert.sourceGauge) 1+gaugeRaw (nativeGauge a.val
    SourceQuantumConfigurationHilbert.sourceGauge) 15+gaugeRaw (nativeGauge a.val
    SourceQuantumConfigurationHilbert.sourceGauge) 30)=0
  rw [rows.1,rows.2.1,rows.2.2,zero]
  ring

theorem residual_scalar_norm_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i : Fin 3) :
    ‖(residualScalar (phaseChart z box) (cartanGauge i) : Scalar)‖ ≤
      7000000000*sourceRadius := by
  let native := phaseChart z box
  let a := residualLie native (cartanGauge i)
  have total : (∑ k : Fin 12, |rawCoordinates a.val k|) ≤ 3600 := by
    have sum := Finset.sum_le_sum (s:=Finset.univ)
      (fun (k : Fin 12) _ => residual_lie_raw_bound z box i k)
    norm_num at sum
    exact sum
  change ‖-action (native.val.2.1 : Scalar) a.val‖ ≤ _
  rw [norm_neg]
  calc
    _ ≤ 117600*(∑ k : Fin 12, |rawCoordinates a.val k|)*‖(native.val.2.1 : Scalar)‖ :=
      actual_full_scalar_action_bound a.val (native.val.2.1 : Scalar)
    _ ≤ 117600*3600*(16*sourceRadius) := by
      gcongr
      exact scalar_box_norm z (closed_box_outer z box)
    _ ≤ 7000000000*sourceRadius := by nlinarith [radius_small.1]

theorem residual_gauge_raw_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i : Fin 3) (k : Fin 36) :
    |gaugeRaw (residualGauge (phaseChart z box) (cartanGauge i)).val k| ≤ 60001 := by
  let native := phaseChart z box
  let a := residualLie native (cartanGauge i)
  have current : |gaugeRaw (gaugeAction a native.val.2.2.val) k| ≤ 60000 := by
    change |rawCoordinates (jointP286CoordinateLieBracket a.val
      (gaugeCoordinates native.val.2.2.val (spatialRow k))) (nativeRow k)| ≤ _
    have primitive := actual_raw_bracket_bound a.val
      (gaugeCoordinates native.val.2.2.val (spatialRow k)) 300 2
      (by norm_num) (by norm_num) (residual_lie_raw_bound z box i)
      (actual_gauge_raw_bound z box (spatialRow k)) (nativeRow k)
    norm_num at primitive
    exact primitive
  have equation : (residualGauge native (cartanGauge i)).val =
      cartanGauge i-gaugeAction a native.val.2.2.val := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact residual_gauge_equation native (cartanGauge i)
  change |gaugeRaw (residualGauge native (cartanGauge i)).val k| ≤ _
  rw [equation,map_sub,Pi.sub_apply]
  exact (real_abs_sub_le_sum _ _).trans (by linarith [cartanGauge_raw_bound i k])

theorem residual_coordinate_bound (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i| ≤ sourceRadius) (i : Fin 3) (k : Fin 100) :
    |fullCoordinates (0,(residualScalar (phaseChart z box) (cartanGauge i),
      residualGauge (phaseChart z box) (cartanGauge i))) k| ≤ 100000000000 := by
  rw [full_blocks,map_zero,←scalar_free_read]
  change |joinCoordinates (0,
    scalarFree (residualScalar (phaseChart z box) (cartanGauge i)),
    gaugeFree (residualGauge (phaseChart z box) (cartanGauge i))) k| ≤ _
  unfold joinCoordinates
  split_ifs with coframe scalar
  · simp
  · have scalarRead := actual_scalar_slice_read_bound
      (residualScalar (phaseChart z box) (cartanGauge i)) ⟨k.val-6,by omega⟩
    have bound := residual_scalar_norm_bound z box i
    nlinarith [radius_small.2]
  · exact (residual_gauge_raw_bound z box i
      (freeRow ⟨k.val-67,by omega⟩)).trans (by norm_num)

theorem residual_cotangent_box_error (z u : FlatConfiguration)
    (zbox : ∀ k, |z k-flatSource k| ≤ sourceRadius)
    (ubox : ∀ k, |u k-sourceUnitMomentum k| ≤ sourceRadius) (i : Fin 3) :
    |PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z)
        (nativeCovector (WithLp.toLp 2 u)) (0,cartanGauge i)-
      PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z)
        (nativeCovector sourceMomentum) (0,cartanGauge i)| ≤ 10000000000000*sourceRadius := by
  let native := phaseChart z zbox
  change |PreparationPhaseGuard.ambientMomentum native.val (nativeCovector (WithLp.toLp 2 u))
      (0,cartanGauge i)-PreparationPhaseGuard.ambientMomentum native.val
      (nativeCovector (WithLp.toLp 2 sourceUnitMomentum)) (0,cartanGauge i)| ≤ _
  rw [residual_momentum_readback native (cartanGauge i) u,
    residual_momentum_readback native (cartanGauge i) sourceUnitMomentum]
  simp only [nativeCovector_apply]
  change |(∑ k : Fin 100, u k*fullCoordinates
      (0,(residualScalar native (cartanGauge i),residualGauge native (cartanGauge i))) k)-
    ∑ k : Fin 100, sourceUnitMomentum k*fullCoordinates
      (0,(residualScalar native (cartanGauge i),residualGauge native (cartanGauge i))) k| ≤ _
  rw [←Finset.sum_sub_distrib]
  simp_rw [←sub_mul]
  calc
    _ ≤ ∑ k : Fin 100, |(u k-sourceUnitMomentum k)*fullCoordinates
        (0,(residualScalar native (cartanGauge i),residualGauge native (cartanGauge i))) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 100, sourceRadius*100000000000 := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (ubox k) (residual_coordinate_bound z zbox i k)
        (abs_nonneg _) radius_small.1.le
    _ = 10000000000000*sourceRadius := by simp; ring

theorem residual_source_current_error (z : FlatConfiguration)
    (box : ∀ k, |z k-flatSource k| ≤ sourceRadius) (i : Fin 3) :
    |sourceGaugeRead (gaugeAction (residualLie (phaseChart z box) (cartanGauge i))
      (phaseChart z box).val.2.2.val)| ≤ 36000*sourceRadius := by
  let native := phaseChart z box
  let a := residualLie native (cartanGauge i)
  let d := native.val.2.2.val-SourceQuantumConfigurationHilbert.sourceGauge
  have each (k : Fin 36) : |gaugeRaw (gaugeAction a d) k| ≤ 30000*sourceRadius := by
    change |rawCoordinates (jointP286CoordinateLieBracket a.val
      (gaugeCoordinates d (spatialRow k))) (nativeRow k)| ≤ _
    have primitive := actual_raw_bracket_bound a.val (gaugeCoordinates d (spatialRow k))
      300 sourceRadius (by norm_num) radius_small.1.le
      (residual_lie_raw_bound z box i) (actual_gauge_raw_difference z box (spatialRow k))
      (nativeRow k)
    nlinarith
  have equal : sourceGaugeRead (gaugeAction a native.val.2.2.val)=
      sourceGaugeRead (gaugeAction a d) := by
    have zero : sourceGaugeRead (gaugeAction a SourceQuantumConfigurationHilbert.sourceGauge)=0 :=
      sourceGaugeRead_stabilizer a
    unfold d
    rw [map_sub,map_sub,zero,sub_zero]
  change |sourceGaugeRead (gaugeAction a native.val.2.2.val)| ≤ _
  rw [equal]
  change |sourceUnitMomentum 67*(gaugeRaw (gaugeAction a d) 1+
    gaugeRaw (gaugeAction a d) 15+gaugeRaw (gaugeAction a d) 30)| ≤ _
  have sum : |gaugeRaw (gaugeAction a d) 1+gaugeRaw (gaugeAction a d) 15+
      gaugeRaw (gaugeAction a d) 30| ≤ 90000*sourceRadius := by
    have first := abs_add_le (gaugeRaw (gaugeAction a d) 1) (gaugeRaw (gaugeAction a d) 15)
    have second := abs_add_le (gaugeRaw (gaugeAction a d) 1+gaugeRaw (gaugeAction a d) 15)
      (gaugeRaw (gaugeAction a d) 30)
    nlinarith [each 1,each 15,each 30]
  rw [abs_mul,abs_of_nonneg source_gauge_momentum_bounds.1]
  have product := mul_le_mul source_gauge_momentum_bounds.2 sum
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2/5)
  nlinarith

theorem cartan_momentum_source_error (z u : FlatConfiguration)
    (zbox : ∀ k, |z k-flatSource k| ≤ sourceRadius)
    (ubox : ∀ k, |u k-sourceUnitMomentum k| ≤ sourceRadius) (i : Fin 3) :
    |PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z)
      (nativeCovector (WithLp.toLp 2 u)) (0,cartanGauge i)-
      sourceGaugeRead (cartanGauge i)| ≤ 100000000000000*sourceRadius := by
  let native := phaseChart z zbox
  have reference : PreparationPhaseGuard.ambientMomentum native.val
      (nativeCovector sourceMomentum) (0,cartanGauge i)=
      sourceGaugeRead (residualGauge native (cartanGauge i)).val := by
    change PreparationPhaseGuard.ambientMomentum native.val
      (nativeCovector (WithLp.toLp 2 sourceUnitMomentum)) (0,cartanGauge i)=_
    rw [residual_momentum_readback native (cartanGauge i) sourceUnitMomentum]
    exact original_source_covector _ _
  have relation := congrArg sourceGaugeRead (residual_gauge_equation native (cartanGauge i))
  rw [map_add] at relation
  have center : |PreparationPhaseGuard.ambientMomentum native.val
      (nativeCovector sourceMomentum) (0,cartanGauge i)-sourceGaugeRead (cartanGauge i)| ≤
      36000*sourceRadius := by
    rw [reference,show sourceGaugeRead (residualGauge native (cartanGauge i)).val-
      sourceGaugeRead (cartanGauge i) =
        -sourceGaugeRead (gaugeAction (residualLie native (cartanGauge i)) native.val.2.2.val)
      from by linarith,abs_neg]
    exact residual_source_current_error z zbox i
  have angular := residual_cotangent_box_error z u zbox ubox i
  change |PreparationPhaseGuard.ambientMomentum native.val (nativeCovector (WithLp.toLp 2 u))
    (0,cartanGauge i)-PreparationPhaseGuard.ambientMomentum native.val
    (nativeCovector sourceMomentum) (0,cartanGauge i)| ≤ 10000000000000*sourceRadius at angular
  change |PreparationPhaseGuard.ambientMomentum native.val (nativeCovector (WithLp.toLp 2 u))
    (0,cartanGauge i)-sourceGaugeRead (cartanGauge i)| ≤ _
  have triangle := real_abs_sub_le_sum
    (PreparationPhaseGuard.ambientMomentum native.val (nativeCovector (WithLp.toLp 2 u))
      (0,cartanGauge i)-PreparationPhaseGuard.ambientMomentum native.val
      (nativeCovector sourceMomentum) (0,cartanGauge i))
    (sourceGaugeRead (cartanGauge i)-PreparationPhaseGuard.ambientMomentum native.val
      (nativeCovector sourceMomentum) (0,cartanGauge i))
  rw [abs_sub_comm (sourceGaugeRead _) _] at triangle
  have sumBound :
      |PreparationPhaseGuard.ambientMomentum native.val (nativeCovector (WithLp.toLp 2 u))
        (0,cartanGauge i)-PreparationPhaseGuard.ambientMomentum native.val
        (nativeCovector sourceMomentum) (0,cartanGauge i)|+
      |PreparationPhaseGuard.ambientMomentum native.val (nativeCovector sourceMomentum)
        (0,cartanGauge i)-sourceGaugeRead (cartanGauge i)| ≤ 100000000000000*sourceRadius := by
    linarith [radius_small.1]
  convert! triangle.trans sumBound using 1
  congr 1
  ring

theorem sourceGaugeRead_cartan (i : Fin 3) :
    sourceGaugeRead (cartanGauge i)=if i=2 then sourceUnitMomentum 67 else 0 := by
  change sourceUnitMomentum 67*(rawCoordinates (gaugeCoordinates (cartanGauge i) 0) 1+
    rawCoordinates (gaugeCoordinates (cartanGauge i) 1) 3+
    rawCoordinates (gaugeCoordinates (cartanGauge i) 2) 6)=_
  rw [cartanGauge_coordinates,cartanGauge_coordinates,cartanGauge_coordinates]
  fin_cases i <;> norm_num [Fin.ext_iff]

theorem cartan_locked_momentum_bound (z u : FlatConfiguration)
    (zbox : ∀ k, |z k-flatSource k| ≤ sourceRadius)
    (ubox : ∀ k, |u k-sourceUnitMomentum k| ≤ sourceRadius) (i : Fin 2) :
    |PreparationPhaseGuard.ambientMomentum (fullCoordinates.symm z)
      (nativeCovector (WithLp.toLp 2 u)) (0,cartanGauge i.castSucc)| < 1/10000 := by
  have source := cartan_momentum_source_error z u zbox ubox i.castSucc
  have locked : i.castSucc ≠ (2 : Fin 3) := by
    intro same
    have values := congrArg Fin.val same
    have bound := i.isLt
    change i.val=2 at values
    omega
  rw [sourceGaugeRead_cartan,if_neg locked,sub_zero] at source
  have margin : 100000000000000*sourceRadius < 1/10000 := by
    nlinarith [phase_radius]
  exact source.trans_lt margin

end LowEnergy.PreparationVacuumClockGuard
