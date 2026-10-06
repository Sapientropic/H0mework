import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeGaugeCoframeMetricCurrent
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeMagneticForceCancellation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarSpatialCurrent
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCartanCubic SourceScalarVirialBulk SourceDilationRemainder SourceCoframeVolume SourceCoframeVolumeCurrent
open SourcePhysicalKineticSquare SourceScalarOscillatorAbsorption SourceInverseNoetherEnergy SourceScalarPositiveBulkWard
open SourceGaugeCoframeMetricCurrent SourceNativeCoframeCompatibility SourceNativeMatterCovarianceCancellation
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariationDensity StageNineP286LinkedActiveLieRepresentation
open scoped ContDiff InnerProductSpace Topology Matrix
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

private theorem native_line (v : Ambient) (z : SourceCoordinateSlice) :
    HasDerivAt (fun t : ℝ => z+t • direction v z) (direction v z) 0 := by
  simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z)).const_add z

private theorem connection_derivative (v : Ambient) (z : physicalChart) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => connectionField (z.val+t • direction v z.val) i)
      (gaugeCoordinate i v.2-nativeBracket (inverseL z.val v).1 (connectionField z.val i)) 0 := by
  let C : SourceCoordinateSlice →L[ℝ] NativeLie := (gaugeCoordinate i).toContinuousLinearMap.comp
    (coordinateSlice.subtypeL.comp ((ContinuousLinearMap.snd ℝ scalarSlice coordinateSlice).comp
      (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))))
  have hc := C.hasFDerivAt.comp_hasDerivAt 0 (native_line v z.val)
  have hi := congrArg (fun w : Ambient => gaugeCoordinate i w.2) (inverse_right z v)
  change nativeBracket (inverseL z.val v).1 (connectionField z.val i)+
    gaugeCoordinate i ((inverseL z.val v).2.2 : Gauge)=gaugeCoordinate i v.2 at hi
  have he : C (direction v z.val)=gaugeCoordinate i v.2-nativeBracket (inverseL z.val v).1 (connectionField z.val i) :=
    eq_sub_of_add_eq' hi
  rw [he] at hc
  exact hc

private theorem scalar_field_derivative (v : Ambient) (z : physicalChart) :
    HasDerivAt (fun t : ℝ => scalarField (z.val+t • direction v z.val))
      (v.1-scalarP286ActionBilinear (inverseL z.val v).1 (scalarField z.val)) 0 := by
  let C : SourceCoordinateSlice →L[ℝ] Scalar := scalarSlice.subtypeL.comp
    ((ContinuousLinearMap.fst ℝ scalarSlice coordinateSlice).comp (ContinuousLinearMap.snd ℝ Coframe Slice))
  have hc := (C.hasFDerivAt.comp_hasDerivAt 0 (native_line v z.val)).const_add vacuum
  have hi := congrArg Prod.fst (inverse_right z v)
  change scalarP286ActionBilinear (inverseL z.val v).1 (scalarField z.val)+((inverseL z.val v).2.1 : Scalar)=v.1 at hi
  have he : C (direction v z.val)=v.1-scalarP286ActionBilinear (inverseL z.val v).1 (scalarField z.val) :=
    eq_sub_of_add_eq' hi
  rw [he] at hc
  exact hc

private theorem bilinear_derivative {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G) {f : ℝ → E} {g : ℝ → F} {df : E} {dg : F}
    (hf : HasDerivAt f df 0) (hg : HasDerivAt g dg 0) :
    HasDerivAt (fun t => L (f t) (g t)) (L (f 0) dg+L df (g 0)) 0 := by
  simpa only [Function.comp_apply,add_comm] using (L.hasFDerivAt.comp_hasDerivAt 0 hf).clm_apply hg

/-- The two fixed source variations enter one scalar-gradient force before inverse-chart rotations cancel. -/
def gradientForce (v : Ambient) (i : Fin 3) (z : SourceCoordinateSlice) : Scalar :=
  scalarP286ActionBilinear (connectionField z i) v.1+
    scalarP286ActionBilinear (gaugeCoordinate i v.2) (scalarField z)

/-- Full native covariance of the original scalar gradient; both scalar and gauge input directions remain. -/
theorem original_scalar_gradient_covariance (v : Ambient) (i : Fin 3) (z : physicalChart) :
    HasDerivAt (fun t : ℝ => scalarGradient (z.val+t • direction v z.val) i)
      (gradientForce v i z.val-scalarP286ActionBilinear (inverseL z.val v).1 (scalarGradient z.val i)) 0 := by
  let rho : NativeLie →ₗ[ℝ] Scalar →ₗ[ℝ] Scalar := scalarP286ActionBilinear
  let R := rho.toContinuousBilinearMap
  have h := bilinear_derivative R (connection_derivative v z i) (scalar_field_derivative v z)
  simp only [zero_smul,add_zero] at h
  have he : R (connectionField z.val i) (v.1-rho (inverseL z.val v).1 (scalarField z.val))+
      R (gaugeCoordinate i v.2-nativeBracket (inverseL z.val v).1 (connectionField z.val i)) (scalarField z.val)=
      gradientForce v i z.val-rho (inverseL z.val v).1 (scalarGradient z.val i) := by
    change rho (connectionField z.val i) (v.1-rho (inverseL z.val v).1 (scalarField z.val))+
      rho (gaugeCoordinate i v.2-nativeBracket (inverseL z.val v).1 (connectionField z.val i)) (scalarField z.val)=_
    simp only [map_sub,LinearMap.sub_apply,gradientForce,scalarGradient]
    have hb := scalarP286ActionBilinear_coordinateBracket (inverseL z.val v).1 (connectionField z.val i) (scalarField z.val)
    change rho (nativeBracket (inverseL z.val v).1 (connectionField z.val i)) (scalarField z.val)=
      rho (inverseL z.val v).1 (rho (connectionField z.val i) (scalarField z.val))-
        rho (connectionField z.val i) (rho (inverseL z.val v).1 (scalarField z.val)) at hb
    rw [hb]
    module
  exact h.congr_deriv he

private theorem scalar_skew (a : NativeLie) (x y : Scalar) :
    inner ℝ (scalarP286ActionBilinear a x) y+inner ℝ x (scalarP286ActionBilinear a y)=0 := by
  have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) x y
  rw [original_scalar_pairing,original_scalar_pairing] at h
  exact h

private theorem metric_symm (z : SourceCoordinateSlice) (i j : Fin 3) : inverseSpatial z i j=inverseSpatial z j i := by
  simp only [inverseSpatial,Matrix.mul_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem symmetric_pair_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ i j,M i j=M j i) (F X : Fin 3 → E) :
    (∑ i : Fin 3,∑ j : Fin 3,M i j*(inner ℝ (F i) (X j)+inner ℝ (X i) (F j)))=
      2*(∑ i : Fin 3,∑ j : Fin 3,M i j*inner ℝ (F i) (X j)) := by
  simp only [mul_add,Finset.sum_add_distrib]
  have he : (∑ i : Fin 3,∑ j : Fin 3,M i j*inner ℝ (X i) (F j))=
      ∑ i : Fin 3,∑ j : Fin 3,M i j*inner ℝ (F i) (X j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM,real_inner_comm (F i) (X j)]
  rw [he]
  ring

/-- The literal signed scalar spatial potential from the original action. -/
def scalarSpatialValue (z : SourceCoordinateSlice) : ℝ :=
  -(sourceTime 0*volume z/2*(∑ i : Fin 3,∑ j : Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)))

private theorem scalar_spatial_smooth (z : physicalChart) : ContDiffAt ℝ ∞ scalarSpatialValue z.val := by
  exact ((contDiffAt_const.mul volume_smooth.contDiffAt).div_const 2 |>.mul
    (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      (inverseSpatial_smooth i j z).mul ((scalarGradient_smooth i).contDiffAt.inner ℝ (scalarGradient_smooth j).contDiffAt))))).neg

/-- Explicit scalar-plus-gauge force with the inverse-chart connection eliminated. -/
def scalarSpatialForce (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  -(sourceTime 0*volume z)*(∑ i : Fin 3,∑ j : Fin 3,
    inverseSpatial z i j*inner ℝ (gradientForce v i z) (scalarGradient z j))

/-- The complete mother skew relation cancels the moving inverse rotation in every native spatial derivative. -/
theorem original_scalar_spatial_derivative (v : Ambient) (z : physicalChart) :
    fderiv ℝ scalarSpatialValue z.val (direction v z.val)=scalarSpatialForce v z.val := by
  have hpair (i j : Fin 3) : HasDerivAt (fun t : ℝ =>
      inner ℝ (scalarGradient (z.val+t • direction v z.val) i) (scalarGradient (z.val+t • direction v z.val) j))
      (inner ℝ (gradientForce v i z.val) (scalarGradient z.val j)+
        inner ℝ (scalarGradient z.val i) (gradientForce v j z.val)) 0 := by
    have h := (original_scalar_gradient_covariance v i z).inner ℝ (original_scalar_gradient_covariance v j z)
    simp only [zero_smul,add_zero] at h
    apply h.congr_deriv
    simp only [inner_sub_left,inner_sub_right]
    linarith [scalar_skew (inverseL z.val v).1 (scalarGradient z.val i) (scalarGradient z.val j)]
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hpair i j).const_mul (inverseSpatial z.val i j)))
  have hc := hd.const_mul (-(sourceTime 0*volume z.val/2))
  have he : (fun t : ℝ => scalarSpatialValue (z.val+t • direction v z.val))=
      fun t => -(sourceTime 0*volume z.val/2)*(∑ i : Fin 3,∑ j : Fin 3,inverseSpatial z.val i j*
        inner ℝ (scalarGradient (z.val+t • direction v z.val) i) (scalarGradient (z.val+t • direction v z.val) j)) := by
    funext t
    simp only [scalarSpatialValue,volume,inverseSpatial,direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero,neg_mul]
  have hs := ((scalar_spatial_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 (native_line v z.val) (by simp)
  change HasDerivAt (fun t : ℝ => scalarSpatialValue (z.val+t • direction v z.val)) _ 0 at hs
  rw [he] at hs
  have h := hs.unique hc
  rw [symmetric_pair_sum (inverseSpatial z.val) (metric_symm z.val)] at h
  rw [h,scalarSpatialForce]
  ring

/-- The fixed gauge variation of each original magnetic component. -/
def magneticVariation (v : Ambient) (i : Fin 3) (z : SourceCoordinateSlice) : NativeLie :=
  ![nativeBracket (gaugeCoordinate 1 v.2) (connectionField z 2)+nativeBracket (connectionField z 1) (gaugeCoordinate 2 v.2),
    nativeBracket (gaugeCoordinate 2 v.2) (connectionField z 0)+nativeBracket (connectionField z 2) (gaugeCoordinate 0 v.2),
    nativeBracket (gaugeCoordinate 0 v.2) (connectionField z 1)+nativeBracket (connectionField z 0) (gaugeCoordinate 1 v.2)] i

private theorem magnetic_field_derivative (v : Ambient) (i : Fin 3) (z : physicalChart) :
    HasDerivAt (fun t : ℝ => magneticField (z.val+t • direction v z.val) i)
      (magneticVariation v i z.val-nativeBracket (inverseL z.val v).1 (magneticField z.val i)) 0 := by
  let a := (inverseL z.val v).1
  let L := nativeBracket.toContinuousBilinearMap
  have h (j k : Fin 3) : HasDerivAt (fun t : ℝ =>
      nativeBracket (connectionField (z.val+t • direction v z.val) j) (connectionField (z.val+t • direction v z.val) k))
      ((nativeBracket (gaugeCoordinate j v.2) (connectionField z.val k)+nativeBracket (connectionField z.val j) (gaugeCoordinate k v.2))-
        nativeBracket a (nativeBracket (connectionField z.val j) (connectionField z.val k))) 0 := by
    have hd := bilinear_derivative L (connection_derivative v z j) (connection_derivative v z k)
    simp only [zero_smul,add_zero] at hd
    apply hd.congr_deriv
    change nativeBracket (connectionField z.val j) (gaugeCoordinate k v.2-nativeBracket a (connectionField z.val k))+
      nativeBracket (gaugeCoordinate j v.2-nativeBracket a (connectionField z.val j)) (connectionField z.val k)=_
    have hb : nativeBracket a (nativeBracket (connectionField z.val j) (connectionField z.val k))=
      nativeBracket (nativeBracket a (connectionField z.val j)) (connectionField z.val k)+
        nativeBracket (connectionField z.val j) (nativeBracket a (connectionField z.val k)) :=
      SourceCartanCubic.bracket_derivation a _ _
    rw [hb]
    simp only [map_sub,LinearMap.sub_apply]
    module
  fin_cases i
  · exact h 1 2
  · exact h 2 0
  · exact h 0 1

private theorem magnetic_smooth (z : physicalChart) : ContDiffAt ℝ ∞ magneticPotential z.val :=
  (volume_smooth.contDiffAt.div_const _).mul
    (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      (inverseSpatial_smooth i j z).mul ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt))))

/-- The original magnetic force keeps only the fixed gauge variation and physical field. -/
def magneticNativeForce (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  volume z/(sourceSigma*sourceTime 0)*(∑ i : Fin 3,∑ j : Fin 3,
    inverseSpatial z i j*inner ℝ (magneticVariation v i z) (magneticField z j))

/-- The same actual adjoint invariance removes the inverse rotation from the full gauge magnetic derivative. -/
theorem original_magnetic_native_derivative (v : Ambient) (z : physicalChart) :
    fderiv ℝ magneticPotential z.val (direction v z.val)=magneticNativeForce v z.val := by
  have hpair (i j : Fin 3) : HasDerivAt (fun t : ℝ =>
      inner ℝ (magneticField (z.val+t • direction v z.val) i) (magneticField (z.val+t • direction v z.val) j))
      (inner ℝ (magneticVariation v i z.val) (magneticField z.val j)+
        inner ℝ (magneticField z.val i) (magneticVariation v j z.val)) 0 := by
    have h := (magnetic_field_derivative v i z).inner ℝ (magnetic_field_derivative v j z)
    simp only [zero_smul,add_zero] at h
    apply h.congr_deriv
    simp only [inner_sub_left,inner_sub_right]
    have hk : inner ℝ (nativeBracket (inverseL z.val v).1 (magneticField z.val i)) (magneticField z.val j)=
      -inner ℝ (magneticField z.val i) (nativeBracket (inverseL z.val v).1 (magneticField z.val j)) :=
      SourceCartanCubic.pair_skew _ _ _
    linarith [hk]
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hpair i j).const_mul (inverseSpatial z.val i j)))
  have hc := hd.const_mul (volume z.val/(2*sourceSigma*sourceTime 0))
  have he : (fun t : ℝ => magneticPotential (z.val+t • direction v z.val))=
      fun t => (volume z.val/(2*sourceSigma*sourceTime 0))*(∑ i : Fin 3,∑ j : Fin 3,inverseSpatial z.val i j*
        inner ℝ (magneticField (z.val+t • direction v z.val) i) (magneticField (z.val+t • direction v z.val) j)) := by
    funext t
    simp only [magneticPotential,volume,inverseSpatial,direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
  have hs := ((magnetic_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 (native_line v z.val) (by simp)
  change HasDerivAt (fun t : ℝ => magneticPotential (z.val+t • direction v z.val)) _ 0 at hs
  rw [he] at hs
  have h := hs.unique hc
  rw [symmetric_pair_sum (inverseSpatial z.val) (metric_symm z.val)] at h
  rw [h,magneticNativeForce]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem native_gradient_smooth (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => fderiv ℝ c x (direction v x)) z.val :=
  ((hc z).fderiv_right (by simp)).clm_apply (direction_smooth v z)

private theorem scalar_force_smooth (v : Ambient) (z : physicalChart) : ContDiffAt ℝ ∞ (scalarSpatialForce v) z.val := by
  have he : scalarSpatialForce v=ᶠ[nhds z.val] (fun x => fderiv ℝ scalarSpatialValue x (direction v x)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    exact (original_scalar_spatial_derivative v ⟨x,hx⟩).symm
  exact (native_gradient_smooth _ scalar_spatial_smooth v z).congr_of_eventuallyEq he

private theorem magnetic_force_smooth (v : Ambient) (z : physicalChart) : ContDiffAt ℝ ∞ (magneticNativeForce v) z.val := by
  have he : magneticNativeForce v=ᶠ[nhds z.val] (fun x => fderiv ℝ magneticPotential x (direction v x)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    exact (original_magnetic_native_derivative v ⟨x,hx⟩).symm
  exact (native_gradient_smooth _ magnetic_smooth v z).congr_of_eventuallyEq he

def scalarForceAction (v : Ambient) : End := multiply (scalarSpatialForce v) (scalar_force_smooth v)
def magneticForceAction (v : Ambient) : End := multiply (magneticNativeForce v) (magnetic_force_smooth v)

private theorem native_real_current (v : Ambient) (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hder : ∀ z : physicalChart,fderiv ℝ c z.val (direction v z.val)=d z.val) :
    covariantMomentum v*multiply c hc-multiply c hc*covariantMomentum v=(-Complex.I) • multiply d hd := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have he : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    change (-Complex.I) • (directional v (multiply c hc f) z+connection v z ((c z : ℂ) • f z))-
      (c z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))=(-Complex.I) • ((d z : ℂ) • f z)
    rw [directional_apply,directional_apply,he,fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt,map_smul]
    change (-Complex.I) • (c z • fderiv ℝ f z (direction v z)+fderiv ℝ c z (direction v z) • f z+
      (c z : ℂ) • connection v z (f z))-
      (c z : ℂ) • ((-Complex.I) • (fderiv ℝ f z (direction v z)+connection v z (f z)))=_
    rw [hder ⟨z,hz⟩]
    apply PiLp.ext
    intro word
    simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,Complex.real_smul]
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem transpose_real_current (v : Ambient) (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hder : ∀ z : physicalChart,fderiv ℝ c z.val (direction v z.val)=d z.val) :
    GaussMomentumAdjoint.adjoint v*multiply c hc-multiply c hc*GaussMomentumAdjoint.adjoint v=(-Complex.I) • multiply d hd := by
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  have h := congrArg (fun A : End => sourcePair (A f) g) (native_real_current v c d hc hd hder)
  change sourcePair (covariantMomentum v (multiply c hc f)-multiply c hc (covariantMomentum v f)) g=
    sourcePair ((-Complex.I) • multiply d hd f) g at h
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at h
  change sourcePair (covariantMomentum v (multiply c hc f)) g-sourcePair (multiply c hc (covariantMomentum v f)) g=
    Complex.I*sourcePair (multiply d hd f) g at h
  change sourcePair f (GaussMomentumAdjoint.adjoint v (multiply c hc g)-multiply c hc (GaussMomentumAdjoint.adjoint v g))=
    sourcePair f ((-Complex.I) • multiply d hd g)
  simp only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right]
  change sourcePair f (GaussMomentumAdjoint.adjoint v (multiply c hc g))-
    sourcePair f (multiply c hc (GaussMomentumAdjoint.adjoint v g))=(-Complex.I)*sourcePair f (multiply d hd g)
  rw [adjoint_pair,multiply_pair,multiply_pair,adjoint_pair,multiply_pair d hd]
  linear_combination -h

private theorem scalar_action : scalarSpatialAction=multiply scalarSpatialValue scalar_spatial_smooth := rfl
private theorem magnetic_action : magneticAction=multiply magneticPotential magnetic_smooth := rfl

private theorem scalar_momentum_current (v : Ambient) :
    covariantMomentum v*scalarSpatialAction-scalarSpatialAction*covariantMomentum v=(-Complex.I) • scalarForceAction v := by
  rw [scalar_action]
  exact native_real_current v _ _ _ _ (original_scalar_spatial_derivative v)
private theorem scalar_adjoint_current (v : Ambient) :
    GaussMomentumAdjoint.adjoint v*scalarSpatialAction-scalarSpatialAction*GaussMomentumAdjoint.adjoint v=(-Complex.I) • scalarForceAction v := by
  rw [scalar_action]
  exact transpose_real_current v _ _ _ _ (original_scalar_spatial_derivative v)
private theorem magnetic_momentum_current (v : Ambient) :
    covariantMomentum v*magneticAction-magneticAction*covariantMomentum v=(-Complex.I) • magneticForceAction v := by
  rw [magnetic_action]
  exact native_real_current v _ _ _ _ (original_magnetic_native_derivative v)
private theorem magnetic_adjoint_current (v : Ambient) :
    GaussMomentumAdjoint.adjoint v*magneticAction-magneticAction*GaussMomentumAdjoint.adjoint v=(-Complex.I) • magneticForceAction v := by
  rw [magnetic_action]
  exact transpose_real_current v _ _ _ _ (original_magnetic_native_derivative v)

private theorem multiply_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem product_current {R : Type*} [Ring R] [Algebra ℂ R] (P W Q M CP CQ : R) (c : ℂ)
    (hP : P*M-M*P=c • CP) (hQ : Q*M-M*Q=c • CQ) (hW : Commute W M) :
    (P*(W*Q))*M-M*(P*(W*Q))=c • (P*(W*CQ)+CP*(W*Q)) := by
  calc
    _=P*(W*(Q*M-M*Q))+(P*M-M*P)*(W*Q) := by
      linear_combination (norm := noncomm_ring) P*hW.eq*Q
    _=_ := by rw [hP,hQ,mul_smul_comm,mul_smul_comm,smul_mul_assoc,smul_add]

/-- Complete scalar spatial force current, with the original negative weight and independent transpose. -/
def scalarSpatialDivergence : End := (-Complex.I/2 : ℂ) • ∑ r : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection r)*(multiply scalarWeight scalarWeight_smooth*scalarForceAction (scalarDirection r))+
    scalarForceAction (scalarDirection r)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection r)))

/-- The signed scalar spatial/kinetic current is reduced to its explicit source force on both legs. -/
theorem original_scalar_spatial_current :
    scalarKinetic*scalarSpatialAction-scalarSpatialAction*scalarKinetic=scalarSpatialDivergence := by
  have h (r : ScalarIndex) : sandwich (scalarDirection r) (scalarDirection r) scalarWeight scalarWeight_smooth*scalarSpatialAction-
      scalarSpatialAction*sandwich (scalarDirection r) (scalarDirection r) scalarWeight scalarWeight_smooth=
      (-Complex.I) • (GaussMomentumAdjoint.adjoint (scalarDirection r)*
        (multiply scalarWeight scalarWeight_smooth*scalarForceAction (scalarDirection r))+
        scalarForceAction (scalarDirection r)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection r))) := by
    apply product_current _ _ _ _ _ _ _ (scalar_adjoint_current _) (scalar_momentum_current _)
    rw [scalar_action]
    exact multiply_commute _ _ _ _
  simp only [scalarKinetic,smul_mul_assoc,mul_smul_comm,←smul_sub,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,h,←Finset.smul_sum,smul_smul,scalarSpatialDivergence]
  congr 1
  ring

/-- The two actual spatial potentials share one explicit gauge-force row. -/
def spatialGaugeForce (v : Ambient) : End := scalarForceAction v+magneticForceAction v

private theorem spatial_momentum_current (v : Ambient) :
    covariantMomentum v*(scalarSpatialAction+magneticAction)-(scalarSpatialAction+magneticAction)*covariantMomentum v=
      (-Complex.I) • spatialGaugeForce v := by
  unfold spatialGaugeForce
  simp only [mul_add,add_mul,smul_add]
  linear_combination (norm := module) (scalar_momentum_current v)+(magnetic_momentum_current v)

private theorem spatial_adjoint_current (v : Ambient) :
    GaussMomentumAdjoint.adjoint v*(scalarSpatialAction+magneticAction)-(scalarSpatialAction+magneticAction)*GaussMomentumAdjoint.adjoint v=
      (-Complex.I) • spatialGaugeForce v := by
  unfold spatialGaugeForce
  simp only [mul_add,add_mul,smul_add]
  linear_combination (norm := module) (scalar_adjoint_current v)+(magnetic_adjoint_current v)

/-- Every original gauge metric entry contracts the explicit scalar-spatial plus magnetic force. -/
def gaugeSpatialDivergence : End := (-Complex.I/2 : ℂ) • ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
  (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*spatialGaugeForce (gaugeDirection j a))+
    spatialGaugeForce (gaugeDirection i a)*
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))

/-- The full gauge spatial/kinetic current has only the generated first-order force divergence. -/
theorem original_gauge_spatial_current :
    gaugeKinetic*(scalarSpatialAction+magneticAction)-(scalarSpatialAction+magneticAction)*gaugeKinetic=gaugeSpatialDivergence := by
  have h (a : LieIndex) (i j : Fin 3) :
      sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*(scalarSpatialAction+magneticAction)-
        (scalarSpatialAction+magneticAction)*sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)=
      (-Complex.I) • (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*spatialGaugeForce (gaugeDirection j a))+
        spatialGaugeForce (gaugeDirection i a)*
          (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) := by
    apply product_current _ _ _ _ _ _ _ (spatial_adjoint_current _) (spatial_momentum_current _)
    rw [scalar_action,magnetic_action]
    exact (multiply_commute _ _ _ _).add_right (multiply_commute _ _ _ _)
  simp only [gaugeKinetic,smul_mul_assoc,mul_smul_comm,←smul_sub,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,h,←Finset.smul_sum,smul_smul,gaugeSpatialDivergence]
  congr 1
  ring

/-- All unabsorbed spatial terms are explicit native force divergences; the source coframe metric, matter and volume words remain. -/
def spatialReducedBulkCurrent : End :=
  (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
    inverseVolumeAction*(-(8 : ℂ) • ((localAction*scalarKinetic-scalarKinetic*localAction-scalarSpatialDivergence)+
      (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*scalarKinetic))+
      (36 : ℂ) • (-gaugeSpatialDivergence+gaugeCoframeDivergence)-
      (36 : ℂ) • gaugeMatterDivergence+
      (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction))

/-- The complete original bulk directly consumes the scalar and gauge source-force cancellations. -/
theorem original_bulk_current_spatial_reduced : bulkCurrent=spatialReducedBulkCurrent := by
  have hs : (localAction+scalarSpatialAction)*scalarKinetic-scalarKinetic*(localAction+scalarSpatialAction)=
      localAction*scalarKinetic-scalarKinetic*localAction-scalarSpatialDivergence := by
    rw [←original_scalar_spatial_current]
    noncomm_ring
  have hg : (magneticAction+scalarSpatialAction)*gaugeKinetic-gaugeKinetic*(magneticAction+scalarSpatialAction)=
      -gaugeSpatialDivergence := by
    rw [←original_gauge_spatial_current]
    noncomm_ring
  rw [original_bulk_current_metric_reduced]
  unfold metricReducedBulkCurrent spatialReducedBulkCurrent
  rw [hs,hg]

/-- Same original F and raised defect; the signed force rows are exposed before the complete-shifted time budget is applied. -/
theorem original_remaining_raised_spatial_reduced (F : Index) (A : End) (q : QuantumTest) :
    remainingRaisedCurrent F A q=(sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
      (sourcePair (A q) ((spatialReducedBulkCurrent-scalarCurrent) (A q))).im/2 := by
  have h := original_current_split
  rw [original_bulk_current_spatial_reduced] at h
  have hr : remainingCurrent=spatialReducedBulkCurrent-scalarCurrent := by
    linear_combination (norm := module) -h
  rw [remainingRaisedCurrent,hr]

end LowEnergy.SourceScalarSpatialCurrent
