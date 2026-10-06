import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussHistoryHilbert
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.GaussLiveMomentum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumResidualFlow
open SourceQuantumNativeDimensions SourceQuantumScalarOrbitDimensions GaussHistoryHilbert
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeConnectionVariationDensity
open scoped RealInnerProductSpace ContDiff Topology

abbrev Slice := scalarSlice × coordinateSlice
abbrev Ambient := Scalar × Gauge
abbrev Split := NativeLie × Slice

def nativeGauge : NativeLie →ₗ[ℝ] Gauge →ₗ[ℝ] Gauge where
  toFun a :=
    { toFun v := WithLp.toLp 2 (fun i => jointP286CoordinateLieBracket a (gaugeCoordinates v i))
      map_add' v w := by
        apply gaugeCoordinates.injective
        funext i
        exact jointP286CoordinateLieBracket_add_right (gaugeCoordinates v i) (gaugeCoordinates w i) a
      map_smul' r v := by
        apply gaugeCoordinates.injective
        funext i
        exact jointP286CoordinateLieBracket_smul_right r (gaugeCoordinates v i) a }
  map_add' a b := by
    ext v
    apply gaugeCoordinates.injective
    funext i
    exact jointP286CoordinateLieBracket_add_left a b (gaugeCoordinates v i)
  map_smul' r a := by
    ext v
    apply gaugeCoordinates.injective
    funext i
    exact jointP286CoordinateLieBracket_smul_left r a (gaugeCoordinates v i)

theorem nativeGauge_stabilizer (a : stabilizer) (A : Gauge) :
    nativeGauge (a : NativeLie) A = gaugeAction a A := rfl

def sourceNormal : Scalar →ₗ[ℝ] broken := brokenOrbit.adjoint

theorem sourceNormal_slice (x : scalarSlice) : sourceNormal (x : Scalar) = 0 := by
  apply ext_inner_left ℝ
  intro a
  rw [inner_zero_right]
  change ⟪a, brokenOrbit.adjoint (x : Scalar)⟫ = 0
  rw [LinearMap.adjoint_inner_right]
  exact (Submodule.mem_orthogonal _ _).1 x.property (orbit (a : NativeLie)) ⟨_, rfl⟩

theorem scalar_stabilizer (x : scalarSlice) (a : stabilizer) :
    action (vacuum + (x : Scalar)) (a : NativeLie) = (scalarAction a x : Scalar) := by
  change scalarP286ActionBilinear (a : NativeLie) (vacuum + (x : Scalar)) = _
  rw [map_add, show scalarP286ActionBilinear (a : NativeLie) vacuum = 0 from a.property,
    zero_add]
  rfl

theorem sourceNormal_stabilizer (x : scalarSlice) (a : stabilizer) :
    sourceNormal (action (vacuum + (x : Scalar)) (a : NativeLie)) = 0 := by
  rw [scalar_stabilizer]
  exact sourceNormal_slice _

def orbitMap (z : SourceCoordinateSlice) : NativeLie →ₗ[ℝ] Ambient :=
  (action (vacuum + (z.2.1 : Scalar))).prod (nativeGauge.flip (z.2.2 : Gauge))

def sliceMap : Slice →ₗ[ℝ] Ambient := scalarSlice.subtype.prodMap coordinateSlice.subtype

def splitMap (z : SourceCoordinateSlice) : Split →ₗ[ℝ] Ambient :=
  (orbitMap z).comp (LinearMap.fst ℝ NativeLie Slice) +
    sliceMap.comp (LinearMap.snd ℝ NativeLie Slice)

theorem residual_relative_det (z : physicalChart) : (relative (z.val.2.2 : Gauge)).det ≠ 0 := by
  have hp := z.property.2.2.2.2.2.2
  have hd : (relativeMatrix (z.val.2.2 : Gauge)).det ≠ 0 := by
    intro hz
    simp only [jacobian, hz, abs_zero, mul_zero, lt_self_iff_false] at hp
  simpa only [relativeMatrix, LinearMap.det_toMatrix] using hd

def residualEquiv (z : physicalChart) : (stabilizer × coordinateSlice) ≃ₗ[ℝ] Gauge :=
  (LinearMap.equivOfDetNeZero (relative (z.val.2.2 : Gauge)) (residual_relative_det z)).trans
    sourceSplitEquiv

theorem residualEquiv_apply (z : physicalChart) (av : stabilizer × coordinateSlice) :
    residualEquiv z av = gaugeAction av.1 (z.val.2.2 : Gauge) + (av.2 : Gauge) := by
  change sourceSplitEquiv (sourceSplitEquiv.symm (combined (z.val.2.2 : Gauge) av)) = _
  rw [sourceSplitEquiv.apply_symm_apply]
  rfl

theorem splitMap_injective (z : physicalChart) : Function.Injective (splitMap z.val) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro u hu
    have hscalar : action (vacuum + (z.val.2.1 : Scalar)) u.1 + (u.2.1 : Scalar) = 0 :=
      congrArg Prod.fst hu
    have hgauge : nativeGauge u.1 (z.val.2.2 : Gauge) + (u.2.2 : Gauge) = 0 :=
      congrArg Prod.snd hu
    let a : stabilizer := stabilizer.orthogonalProjectionOnto u.1
    let b : broken := broken.orthogonalProjectionOnto u.1
    have hab : (a : NativeLie) + (b : NativeLie) = u.1 :=
      stabilizer.starProjection_add_starProjection_orthogonal u.1
    have hn := congrArg sourceNormal hscalar
    rw [map_add, sourceNormal_slice, add_zero, map_zero, ← hab, map_add, map_add,
      sourceNormal_stabilizer, zero_add] at hn
    have hb : b = 0 := by
      let x : scalarChart := ⟨z.val.2.1, z.property.2.2.2.1⟩
      apply (chartConsistencyEquiv x).injective
      change consistency (vacuum + (z.val.2.1 : Scalar)) b = chartConsistencyEquiv x 0
      rw [map_zero]
      exact hn
    have ha : (a : NativeLie) = u.1 := by simpa [hb] using hab
    have hres : residualEquiv z (a, u.2.2) = 0 := by
      rw [residualEquiv_apply, ← nativeGauge_stabilizer, ha]
      exact hgauge
    have hzero : (a, u.2.2) = 0 := (residualEquiv z).injective (by simpa using hres)
    have hu1 : u.1 = 0 := by
      rw [← ha, show a = 0 from congrArg Prod.fst hzero]
      rfl
    have hu21 : u.2.1 = 0 := by
      apply Subtype.ext
      simpa [hu1] using hscalar
    have hu22 : u.2.2 = 0 := congrArg Prod.snd hzero
    change u = 0
    exact Prod.ext hu1 (Prod.ext hu21 hu22)
  · exact bot_le

theorem coordinateSlice_finrank : Module.finrank ℝ coordinateSlice = 33 := by
  rw [sliceEquiv.finrank_eq]
  exact gaugeSlice_finrank

theorem split_finrank : Module.finrank ℝ Split = Module.finrank ℝ Ambient := by
  simp only [Split, Slice, Ambient, Module.finrank_prod, nativeLie_finrank,
    scalarSlice_finrank, coordinateSlice_finrank, scalar_finrank,
    SourceQuantumNativeDimensions.gauge_finrank]

def splitEquiv (z : physicalChart) : Split ≃ₗ[ℝ] Ambient :=
  (splitMap z.val).linearEquivOfInjective (splitMap_injective z) split_finrank

theorem splitEquiv_apply (z : physicalChart) (u : Split) :
    splitEquiv z u = (action (vacuum + (z.val.2.1 : Scalar)) u.1 + (u.2.1 : Scalar),
      nativeGauge u.1 (z.val.2.2 : Gauge) + (u.2.2 : Gauge)) := rfl

theorem split_left_inverse (z : physicalChart) (u : Split) :
    (splitEquiv z).symm (splitMap z.val u) = u := (splitEquiv z).symm_apply_apply u

theorem split_right_inverse (z : physicalChart) (v : Ambient) :
    splitMap z.val ((splitEquiv z).symm v) = v := (splitEquiv z).apply_symm_apply v

def variation : SourceCoordinateSlice →ₗ[ℝ] Split →ₗ[ℝ] Ambient where
  toFun h :=
    { toFun u := (scalarP286ActionBilinear u.1 (h.2.1 : Scalar),
        nativeGauge u.1 (h.2.2 : Gauge))
      map_add' u v := by
        apply Prod.ext
        · exact LinearMap.congr_fun (map_add scalarP286ActionBilinear u.1 v.1) _
        · exact LinearMap.congr_fun (map_add nativeGauge u.1 v.1) _
      map_smul' r u := by
        apply Prod.ext
        · exact LinearMap.congr_fun (map_smul scalarP286ActionBilinear r u.1) _
        · exact LinearMap.congr_fun (map_smul nativeGauge r u.1) _ }
  map_add' h k := by
    apply LinearMap.ext
    intro u
    exact Prod.ext (map_add (scalarP286ActionBilinear u.1) _ _) (map_add (nativeGauge u.1) _ _)
  map_smul' r h := by
    apply LinearMap.ext
    intro u
    exact Prod.ext (map_smul (scalarP286ActionBilinear u.1) r _) (map_smul (nativeGauge u.1) r _)

def variationL : SourceCoordinateSlice →L[ℝ] Split →L[ℝ] Ambient :=
  variation.toContinuousBilinearMap

def splitL (z : SourceCoordinateSlice) : Split →L[ℝ] Ambient := (splitMap z).toContinuousLinearMap

theorem split_affine (z : SourceCoordinateSlice) : splitL z = splitL 0 + variationL z := by
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext
  · change scalarP286ActionBilinear u.1 (vacuum + (z.2.1 : Scalar)) + (u.2.1 : Scalar) =
      (scalarP286ActionBilinear u.1 (vacuum + 0) + (u.2.1 : Scalar)) +
        scalarP286ActionBilinear u.1 (z.2.1 : Scalar)
    rw [map_add, add_zero]
    abel
  · change nativeGauge u.1 (z.2.2 : Gauge) + (u.2.2 : Gauge) =
      (nativeGauge u.1 0 + (u.2.2 : Gauge)) + nativeGauge u.1 (z.2.2 : Gauge)
    rw [map_zero, zero_add, add_comm]

set_option backward.isDefEq.respectTransparency false in
theorem split_derivative (z : SourceCoordinateSlice) : HasFDerivAt splitL variationL z := by
  have hv : HasFDerivAt (fun w : SourceCoordinateSlice => variationL w) variationL z :=
    variationL.hasFDerivAt
  have h := HasFDerivAt.const_add (𝕜 := ℝ) (E := SourceCoordinateSlice)
    (F := Split →L[ℝ] Ambient) (splitL 0) hv
  convert h using 1 <;> first
  | rfl
  | (funext w; exact split_affine w)

theorem split_smooth : ContDiff ℝ ∞ splitL := by
  have hv : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => variationL w) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := SourceCoordinateSlice)
      (F := Split →L[ℝ] Ambient) variationL
  have h : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => splitL 0 + variationL w) :=
    contDiff_const.add hv
  simpa only [← split_affine] using h

def inverseL (z : SourceCoordinateSlice) : Ambient →L[ℝ] Split :=
  ContinuousLinearMap.inverse (splitL z)

theorem inverseL_equiv (z : physicalChart) :
    inverseL z.val = (splitEquiv z).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  change ContinuousLinearMap.inverse (splitEquiv z).toContinuousLinearEquiv.toContinuousLinearMap = _
  exact ContinuousLinearMap.inverse_equiv _

theorem inverse_smooth (z : physicalChart) : ContDiffAt ℝ ∞ inverseL z.val := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (splitL z.val) :=
    contDiffAt_map_inverse (splitEquiv z).toContinuousLinearEquiv
  exact hi.comp z.val split_smooth.contDiffAt

theorem inverse_left (z : physicalChart) (u : Split) : inverseL z.val (splitMap z.val u) = u := by
  rw [inverseL_equiv]
  exact split_left_inverse z u

theorem inverse_right (z : physicalChart) (v : Ambient) : splitMap z.val (inverseL z.val v) = v := by
  rw [inverseL_equiv]
  exact split_right_inverse z v

theorem inverse_derivative (z : physicalChart) (h : SourceCoordinateSlice) (v : Ambient) :
    fderiv ℝ inverseL z.val h v = -inverseL z.val (variationL h (inverseL z.val v)) := by
  have hi := ((inverse_smooth z).differentiableAt (by norm_num)).hasFDerivAt
  have hd := (split_derivative z.val).clm_comp hi
  have heq : (fun w => (splitL w).comp (inverseL w)) =ᶠ[𝓝 z.val]
      (fun _ => ContinuousLinearMap.id ℝ Ambient) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    apply ContinuousLinearMap.ext
    intro u
    exact inverse_right ⟨w, hw⟩ u
  have hz := (hd.congr_of_eventuallyEq heq.symm).unique
    (hasFDerivAt_const (ContinuousLinearMap.id ℝ Ambient) z.val)
  have hv := congrArg (fun D : SourceCoordinateSlice →L[ℝ] Ambient →L[ℝ] Ambient => D h v) hz
  change splitMap z.val (fderiv ℝ inverseL z.val h v) + variationL h (inverseL z.val v) = 0 at hv
  have hinv := congrArg (inverseL z.val) hv
  rw [map_add, inverse_left, map_zero] at hinv
  exact eq_neg_of_add_eq_zero_left hinv

/-- The original constraint value is the negative orbit charge. -/
def momentum (z : physicalChart) (charge : Module.Dual ℝ NativeLie)
    (p : Module.Dual ℝ Slice) : Module.Dual ℝ Ambient :=
  ((-charge).coprod p).comp (splitEquiv z).symm.toLinearMap

theorem momentum_orbit (z : physicalChart) (charge : Module.Dual ℝ NativeLie)
    (p : Module.Dual ℝ Slice) (a : NativeLie) :
    momentum z charge p (orbitMap z.val a) = -charge a := by
  have he : orbitMap z.val a = splitMap z.val (a, 0) := by
    simp [splitMap, sliceMap]
  change ((-charge).coprod p) ((splitEquiv z).symm (orbitMap z.val a)) = _
  rw [he, split_left_inverse]
  simp

theorem momentum_slice (z : physicalChart) (charge : Module.Dual ℝ NativeLie)
    (p : Module.Dual ℝ Slice) (v : Slice) :
    momentum z charge p (sliceMap v) = p v := by
  have he : sliceMap v = splitMap z.val (0, v) := by simp [splitMap]
  change ((-charge).coprod p) ((splitEquiv z).symm (sliceMap v)) = _
  rw [he, split_left_inverse]
  simp

theorem momentum_unique (z : physicalChart) (charge : Module.Dual ℝ NativeLie)
    (p : Module.Dual ℝ Slice) (q : Module.Dual ℝ Ambient)
    (hq : ∀ a, q (orbitMap z.val a) = -charge a)
    (hp : ∀ v, q (sliceMap v) = p v) : q = momentum z charge p := by
  apply LinearMap.ext
  intro v
  obtain ⟨u, rfl⟩ := (splitEquiv z).surjective v
  change q (orbitMap z.val u.1 + sliceMap u.2) =
    momentum z charge p (orbitMap z.val u.1 + sliceMap u.2)
  rw [map_add, hq, hp, map_add, momentum_orbit, momentum_slice]

#print axioms splitMap_injective
#print axioms splitEquiv
#print axioms split_right_inverse
#print axioms inverse_smooth
#print axioms inverse_derivative
#print axioms momentum_unique
#print axioms momentum_orbit
#print axioms momentum_slice
end LowEnergy.GaussLiveMomentum
