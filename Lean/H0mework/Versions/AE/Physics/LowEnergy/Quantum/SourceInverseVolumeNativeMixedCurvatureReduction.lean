import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarVirialCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNoetherEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceNativeMixedCurvatureReduction
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceQuantumResidualFlow SourceScalarFlatJoint
open SourceScalarNativeComparison SourceScalarVirialCurrent SourceHamiltonianVolume
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SaturationMonoid.PhysicsCore
open StageNineP286GaugeConnectionVariationDensity StageNineHolonomicField
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def residualInverse (z : SourceCoordinateSlice) : Gauge →L[ℝ] (stabilizer × coordinateSlice) :=
  ContinuousLinearMap.inverse ((combined (z.2.2 : Gauge)).toContinuousLinearMap)

private theorem combined_equiv (z : physicalChart) :
    (combined (z.val.2.2 : Gauge)).toContinuousLinearMap=(residualEquiv z).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact (residualEquiv_apply z x).symm

private theorem residual_inverse_equiv (z : physicalChart) :
    residualInverse z.val=(residualEquiv z).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  unfold residualInverse
  rw [combined_equiv]
  exact ContinuousLinearMap.inverse_equiv (residualEquiv z).toContinuousLinearEquiv

private theorem residual_inverse_right (z : physicalChart) (v : Gauge) :
    combined (z.val.2.2 : Gauge) (residualInverse z.val v)=v := by
  rw [residual_inverse_equiv]
  exact (residualEquiv_apply z ((residualEquiv z).symm v)).symm.trans ((residualEquiv z).apply_symm_apply v)

/-- A genuine gauge input fixes its orbit component in the actual stabilizer;
no zero-charge condition is added. -/
theorem original_gauge_inverse (z : physicalChart) (v : Gauge) :
    inverseL z.val (0,v)=(((residualInverse z.val v).1 : NativeLie),
      -scalarAction (residualInverse z.val v).1 z.val.2.1,(residualInverse z.val v).2) := by
  have he : splitMap z.val (((residualInverse z.val v).1 : NativeLie),
      -scalarAction (residualInverse z.val v).1 z.val.2.1,(residualInverse z.val v).2)=(0,v) := by
    apply Prod.ext
    · change action (vacuum+(z.val.2.1 : Scalar)) (residualInverse z.val v).1+
        ((-scalarAction (residualInverse z.val v).1 z.val.2.1 : scalarSlice) : Scalar)=0
      rw [scalar_stabilizer]
      simp
    · exact residual_inverse_right z v
  rw [←he,inverse_left]

/-- The scalar derivative of the gauge split is the source skew rotation only. -/
theorem original_gauge_inverse_scalar_derivative (z : physicalChart) (v : Gauge) (u : scalarSlice) :
    fderiv ℝ inverseL z.val (scalarAxis u) (0,v)=
      (0,-scalarAction (residualInverse z.val v).1 u,0) := by
  rw [inverse_derivative,original_gauge_inverse]
  have he : variationL (scalarAxis u)
      (((residualInverse z.val v).1 : NativeLie),-scalarAction (residualInverse z.val v).1 z.val.2.1,(residualInverse z.val v).2)=
      ((scalarAction (residualInverse z.val v).1 u : Scalar),0) := by
    apply Prod.ext
    · rfl
    · exact map_zero _
  rw [he,native_scalar_slice_inverse]
  simp only [Prod.neg_mk,neg_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem residual_inverse_smooth (z : physicalChart) : ContDiffAt ℝ ∞ residualInverse z.val := by
  let G : Gauge →L[ℝ] stabilizer →L[ℝ] Gauge := gaugeAction.flip.toContinuousBilinearMap
  have he : (fun A : Gauge => (combined A).toContinuousLinearMap)=
      (fun A : Gauge => (G A).comp (ContinuousLinearMap.fst ℝ stabilizer coordinateSlice)+
        coordinateSlice.subtypeL.comp (ContinuousLinearMap.snd ℝ stabilizer coordinateSlice)) := by
    funext A
    rfl
  have hc : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => (combined (w.2.2 : Gauge)).toContinuousLinearMap) := by
    have hl : ContDiff ℝ ∞ (fun A : Gauge => (combined A).toContinuousLinearMap) := by
      rw [he]
      have hG : ContDiff ℝ ∞ G := ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Gauge) (F := stabilizer →L[ℝ] Gauge) G
      have hP : ContDiff ℝ ∞ (fun A : Gauge => (G A).comp (ContinuousLinearMap.fst ℝ stabilizer coordinateSlice)) :=
        hG.clm_comp (contDiff_const (c := ContinuousLinearMap.fst ℝ stabilizer coordinateSlice))
      exact hP.add (contDiff_const (c := coordinateSlice.subtypeL.comp (ContinuousLinearMap.snd ℝ stabilizer coordinateSlice)))
    exact hl.comp (coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd))
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse ((combined (z.val.2.2 : Gauge)).toContinuousLinearMap) := by
    rw [combined_equiv]
    exact contDiffAt_map_inverse (residualEquiv z).toContinuousLinearEquiv
  exact hi.comp z.val hc.contDiffAt

private theorem residual_inverse_scalar_derivative (z : physicalChart) (v : Gauge) (u : scalarSlice) :
    fderiv ℝ (fun x => residualInverse x v) z.val (scalarAxis u)=0 := by
  have hf := (((residual_inverse_smooth z).clm_apply (contDiffAt_const (c := v))).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => z.val+t • scalarAxis u) (scalarAxis u) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (scalarAxis u)).const_add z.val
  have he := hf.comp_hasDerivAt_of_eq 0 hc (by simp)
  have hh : (fun t : ℝ => residualInverse (z.val+t • scalarAxis u) v)=(fun _ : ℝ => residualInverse z.val v) := by
    funext t
    simp only [residualInverse,scalarAxis,Prod.snd_add,Prod.smul_mk,smul_zero,add_zero]
  change HasDerivAt (fun t : ℝ => residualInverse (z.val+t • scalarAxis u) v)
    (fderiv ℝ (fun x => residualInverse x v) z.val (scalarAxis u)) 0 at he
  rw [hh] at he
  exact he.unique (hasDerivAt_const 0 _)

private def flatD (i : SliceIndex) : End := GaussCoframeCore.derivative (scalarAxis (scalarFrame i))

def rotationCoefficient (v : Gauge) (i j : SliceIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (scalarFrame i) (scalarAction (residualInverse z v).1 (scalarFrame j))

private theorem rotation_smooth (v : Gauge) (i j : SliceIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (rotationCoefficient v i j) z.val := by
  let L : stabilizer →L[ℝ] scalarSlice := (scalarAction.flip (scalarFrame j)).toContinuousLinearMap
  exact contDiffAt_const.inner ℝ (L.contDiff.contDiffAt.comp z.val
    (((residual_inverse_smooth z).clm_apply (contDiffAt_const (c := v))).fst))

def rotationAction (v : Gauge) (i j : SliceIndex) : End :=
  multiply (rotationCoefficient v i j) (rotation_smooth v i j)

private theorem rotation_skew (v : Gauge) (i j : SliceIndex) :
    rotationAction v i j= -rotationAction v j i := by
  have hs (z : SourceCoordinateSlice) : rotationCoefficient v i j z= -rotationCoefficient v j i z := by
    have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
      (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm ((residualInverse z v).1 : NativeLie)))
      (scalarFrame j : Scalar) (scalarFrame i : Scalar)
    rw [original_scalar_pairing,original_scalar_pairing] at h
    change inner ℝ (scalarAction (residualInverse z v).1 (scalarFrame j)) (scalarFrame i)+
      inner ℝ (scalarFrame j) (scalarAction (residualInverse z v).1 (scalarFrame i))=0 at h
    rw [real_inner_comm (scalarFrame i) (scalarAction (residualInverse z v).1 (scalarFrame j))] at h
    exact eq_neg_of_add_eq_zero_left h
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (rotationCoefficient v i j z : ℂ) • f z= -((rotationCoefficient v j i z : ℂ) • f z)
  rw [hs,Complex.ofReal_neg,neg_smul]

private theorem inverse_value_derivative (v : Ambient) (z : physicalChart) :
    HasFDerivAt (fun w => inverseL w v) ((fderiv ℝ inverseL z.val).flip v) z.val := by
  have hd := (((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt).clm_apply
    (hasFDerivAt_const v z.val)
  simpa only [ContinuousLinearMap.comp_zero,zero_add] using hd

private theorem direction_flat_derivative (v : Gauge) (u : scalarSlice) (z : physicalChart) :
    fderiv ℝ (direction (0,v)) z.val (scalarAxis u)=
      -scalarAxis (scalarAction (residualInverse z.val v).1 u) := by
  have hd := (hasFDerivAt_const (0 : Coframe) z.val).prodMk ((inverse_value_derivative (0,v) z).snd)
  have h := congrArg (fun D : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice => D (scalarAxis u)) hd.fderiv
  change fderiv ℝ (direction (0,v)) z.val (scalarAxis u)=
    (0,(fderiv ℝ inverseL z.val (scalarAxis u) (0,v)).2) at h
  rw [original_gauge_inverse_scalar_derivative] at h
  simpa only [scalarAxis,Prod.neg_mk,neg_zero] using h

private theorem connection_flat_derivative (v : Gauge) (u : scalarSlice) (z : physicalChart) :
    fderiv ℝ (connection (0,v)) z.val (scalarAxis u)=0 := by
  have hd := GaussNativeMatter.nativeFock.toContinuousLinearMap.hasFDerivAt.comp z.val
    ((inverse_value_derivative (0,v) z).fst)
  have h := congrArg (fun D : SourceCoordinateSlice →L[ℝ] (FockFiber →L[ℂ] FockFiber) => D (scalarAxis u)) hd.fderiv
  change fderiv ℝ (connection (0,v)) z.val (scalarAxis u)=
    GaussNativeMatter.nativeFock (fderiv ℝ inverseL z.val (scalarAxis u) (0,v)).1 at h
  simpa only [original_gauge_inverse_scalar_derivative,map_zero] using h

private theorem derivative_rotation (v : Gauge) (i : SliceIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fderiv ℝ f z (scalarAxis (scalarAction (residualInverse z v).1 (scalarFrame i)))=
      ∑ j : SliceIndex,(rotationCoefficient v j i z : ℂ) • (flatD j f z) := by
  have he : scalarAxis (scalarAction (residualInverse z v).1 (scalarFrame i))=
      ∑ j : SliceIndex,(rotationCoefficient v j i z) • scalarAxis (scalarFrame j) := by
    have hh := scalarFrame.sum_repr' (scalarAction (residualInverse z v).1 (scalarFrame i))
    apply Prod.ext
    · simp only [scalarAxis,Prod.fst_sum,Prod.smul_fst,smul_zero,Finset.sum_const_zero]
    · apply Prod.ext
      · simpa only [scalarAxis,Prod.snd_sum,Prod.smul_snd,Prod.fst_sum,Prod.smul_fst,rotationCoefficient] using hh.symm
      · simp only [scalarAxis,Prod.snd_sum,Prod.smul_snd,smul_zero,Finset.sum_const_zero]
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,flatD,GaussCoframeCore.derivative_apply]
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem directional_flat_current (v : Gauge) (i : SliceIndex) :
    flatD i*directional (0,v)-directional (0,v)*flatD i=
      -(∑ j : SliceIndex,rotationAction v j i*flatD j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hD : (directional (0,v) f : SourceCoordinateSlice → FockFiber)=
        fun x => fderiv ℝ f x (direction (0,v) x) := funext (directional_apply _ f)
    have hE : (flatD i f : SourceCoordinateSlice → FockFiber)=
        fun x => fderiv ℝ f x (scalarAxis (scalarFrame i)) := funext (GaussCoframeCore.derivative_apply _ f)
    change flatD i (directional (0,v) f) z-directional (0,v) (flatD i f) z=_
    change fderiv ℝ (directional (0,v) f) z (scalarAxis (scalarFrame i))-
      fderiv ℝ (flatD i f) z (direction (0,v) z)=_
    rw [hD,hE]
    have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
      (V := fun _ => scalarAxis (scalarFrame i)) (W := direction (0,v)) (x := z)
      f.contDiff.contDiffAt (by simp only [minSmoothness_of_isRCLikeNormedField];exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      ((direction_smooth (0,v) ⟨z,hz⟩).differentiableAt (by simp)) (differentiableAt_const _)
    have hb : VectorField.lieBracket ℝ (fun _ => scalarAxis (scalarFrame i)) (direction (0,v)) z=
        -scalarAxis (scalarAction (residualInverse z v).1 (scalarFrame i)) := by
      rw [VectorField.lieBracket,(hasFDerivAt_const (scalarAxis (scalarFrame i)) z).fderiv,zero_apply,sub_zero]
      exact direction_flat_derivative v (scalarFrame i) ⟨z,hz⟩
    rw [hb,map_neg,derivative_rotation] at h
    simpa only [LinearMap.neg_apply,LinearMap.sum_apply,Module.End.mul_apply,neg_apply,sum_apply,rotationAction,multiply_apply] using h.symm
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    change (flatD i (directional (0,v) f)-directional (0,v) (flatD i f)) z=
      (-(∑ j : SliceIndex,rotationAction v j i*flatD j) f) z
    rw [h0,h0]


private theorem real_fock_smul (r : ℝ) (x : FockFiber) : r • x=(r : ℂ) • x := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem multiplier_flat (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (i : SliceIndex)
    (hd : ∀ z : physicalChart,fderiv ℝ c z.val (scalarAxis (scalarFrame i))=0) :
    Commute (flatD i) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have he : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      exact (real_fock_smul _ _).symm
    change flatD i (multiply c hc f) z=multiply c hc (flatD i f) z
    rw [flatD,GaussCoframeCore.derivative_apply,he]
    rw [fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt]
    change c z • fderiv ℝ f z (scalarAxis (scalarFrame i))+
      fderiv ℝ c z (scalarAxis (scalarFrame i)) • f z=_
    rw [hd ⟨z,hz⟩,zero_smul,add_zero,real_fock_smul]
    rfl
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem rotation_flat_derivative (v : Gauge) (i j k : SliceIndex) (z : physicalChart) :
    fderiv ℝ (rotationCoefficient v i j) z.val (scalarAxis (scalarFrame k))=0 := by
  have hf := ((rotation_smooth v i j z).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => z.val+t • scalarAxis (scalarFrame k)) (scalarAxis (scalarFrame k)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (scalarAxis (scalarFrame k))).const_add z.val
  have he := hf.comp_hasDerivAt_of_eq 0 hc (by simp)
  have hh : (fun t : ℝ => rotationCoefficient v i j (z.val+t • scalarAxis (scalarFrame k)))=
      fun _ : ℝ => rotationCoefficient v i j z.val := by
    funext t
    simp only [rotationCoefficient,residualInverse,scalarAxis,Prod.snd_add,Prod.smul_mk,smul_zero,add_zero]
  change HasDerivAt (fun t : ℝ => rotationCoefficient v i j (z.val+t • scalarAxis (scalarFrame k)))
    (fderiv ℝ (rotationCoefficient v i j) z.val (scalarAxis (scalarFrame k))) 0 at he
  rw [hh] at he
  exact he.unique (hasDerivAt_const 0 _)

private theorem rotation_flat_commute (v : Gauge) (i j k : SliceIndex) :
    Commute (flatD k) (rotationAction v i j) :=
  multiplier_flat _ (rotation_smooth v i j) k (rotation_flat_derivative v i j k)

private theorem connection_flat_commute (v : Gauge) (i : SliceIndex) :
    Commute (flatD i) (localMultiplier (connection (0,v)) (connection_smooth (0,v))) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · let B := connection (0,v)
    have hB := ((connection_smooth (0,v) ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt
    have hr := (ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ).hasFDerivAt.comp z hB
    have h := (hr.clm_apply (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
    have he : (localMultiplier B (connection_smooth (0,v)) f : SourceCoordinateSlice → FockFiber)=
      fun x => B x (f x) := rfl
    change flatD i (localMultiplier B (connection_smooth (0,v)) f) z=B z (flatD i f z)
    rw [flatD,GaussCoframeCore.derivative_apply,he]
    change fderiv ℝ (fun x => B x (f x)) z=_ at h
    rw [h]
    change B z (fderiv ℝ f z (scalarAxis (scalarFrame i)))+
      (fderiv ℝ B z (scalarAxis (scalarFrame i))) (f z)=_
    rw [connection_flat_derivative v (scalarFrame i) ⟨z,hz⟩,zero_apply,add_zero]
    rfl
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem flat_native_current (v : Gauge) (i : SliceIndex) :
    flatD i*covariantMomentum (0,v)-covariantMomentum (0,v)*flatD i=
      Complex.I • ∑ j : SliceIndex,rotationAction v j i*flatD j := by
  unfold covariantMomentum
  simp only [mul_smul_comm,smul_mul_assoc,←smul_sub,mul_add,add_mul]
  have he := (connection_flat_commute v i).eq
  have hd := directional_flat_current v i
  linear_combination (norm := module) (-Complex.I) • (hd+he)

private theorem flat_derivative_commute (i j : SliceIndex) : Commute (flatD i) (flatD j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hi : (flatD i f : SourceCoordinateSlice → FockFiber)=fun x => fderiv ℝ f x (scalarAxis (scalarFrame i)) :=
    funext (GaussCoframeCore.derivative_apply _ f)
  have hj : (flatD j f : SourceCoordinateSlice → FockFiber)=fun x => fderiv ℝ f x (scalarAxis (scalarFrame j)) :=
    funext (GaussCoframeCore.derivative_apply _ f)
  change flatD i (flatD j f) z=flatD j (flatD i f) z
  change fderiv ℝ (flatD j f) z (scalarAxis (scalarFrame i))=fderiv ℝ (flatD i f) z (scalarAxis (scalarFrame j))
  rw [hi,hj]
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
    (V := fun _ => scalarAxis (scalarFrame i)) (W := fun _ => scalarAxis (scalarFrame j)) (x := z)
    f.contDiff.contDiffAt (by simp only [minSmoothness_of_isRCLikeNormedField];exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    (differentiableAt_const _) (differentiableAt_const _)
  rw [VectorField.lieBracket,(hasFDerivAt_const (scalarAxis (scalarFrame i)) z).fderiv,
    (hasFDerivAt_const (scalarAxis (scalarFrame j)) z).fderiv,zero_apply,zero_apply,sub_self,map_zero] at h
  exact sub_eq_zero.mp h.symm

private theorem laplace_native (v : Gauge) :
    Commute (∑ i : SliceIndex,flatD i*flatD i) (covariantMomentum (0,v)) := by
  have h (i : SliceIndex) : (flatD i*flatD i)*covariantMomentum (0,v)-covariantMomentum (0,v)*(flatD i*flatD i)=
      (2*Complex.I) • ∑ j : SliceIndex,rotationAction v j i*(flatD i*flatD j) := by
    have hi := flat_native_current v i
    have he : (flatD i*flatD i)*covariantMomentum (0,v)-covariantMomentum (0,v)*(flatD i*flatD i)=
        flatD i*(flatD i*covariantMomentum (0,v)-covariantMomentum (0,v)*flatD i)+
        (flatD i*covariantMomentum (0,v)-covariantMomentum (0,v)*flatD i)*flatD i := by noncomm_ring
    rw [he,hi]
    simp only [mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,←smul_add,←Finset.sum_add_distrib]
    have hsum : (∑ j : SliceIndex,(flatD i*(rotationAction v j i*flatD j)+(rotationAction v j i*flatD j)*flatD i))=
        (2 : ℂ) • ∑ j : SliceIndex,rotationAction v j i*(flatD i*flatD j) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hc := (rotation_flat_commute v j i i).eq
      have hd := (flat_derivative_commute j i).eq
      rw [←mul_assoc,hc,mul_assoc,mul_assoc,hd]
      module
    rw [hsum,smul_smul]
    congr 1
    ring
  have hs : (∑ i : SliceIndex,∑ j : SliceIndex,rotationAction v j i*(flatD i*flatD j))=0 := by
    let S := ∑ i : SliceIndex,∑ j : SliceIndex,rotationAction v j i*(flatD i*flatD j)
    have he : S= -S := by
      calc
        _ = ∑ j : SliceIndex,∑ i : SliceIndex,rotationAction v j i*(flatD i*flatD j) := Finset.sum_comm
        _ = _ := by
          simp only [S,←Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          calc
            _ = (-rotationAction v j i)*(flatD j*flatD i) := congrArg (fun A : End => A*(flatD j*flatD i)) (rotation_skew v i j)
            _ = _ := by rw [neg_mul,(flat_derivative_commute j i).eq]
    have hz : (2 : ℂ) • S=0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp he
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  apply sub_eq_zero.mp
  rw [Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  simp only [h,←Finset.smul_sum,hs,smul_zero]


private theorem flat_kinetic_derivatives : flatKinetic=(-1 : ℂ) • ∑ i : SliceIndex,flatD i*flatD i := by
  simp only [flatKinetic,flatMomentum,←Finset.smul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  have he : (-Complex.I)*(-Complex.I)=(-1 : ℂ) := by rw [neg_mul_neg,Complex.I_mul_I]
  rw [he]
  rfl

/-- The actual gauge momentum retains its skew scalar action; its entire flat61 Casimir commutes. -/
theorem original_flat_gauge_momentum (v : Gauge) : Commute flatKinetic (covariantMomentum (0,v)) := by
  rw [flat_kinetic_derivatives]
  exact (laplace_native v).smul_left (-1 : ℂ)

private theorem flat_kinetic_pair (f g : QuantumTest) : sourcePair f (flatKinetic g)=sourcePair (flatKinetic f) g := by
  simp only [flatKinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (flatMomentum (scalarFrame i) (flatMomentum (scalarFrame i) g))=
    sourcePair (flatMomentum (scalarFrame i) (flatMomentum (scalarFrame i) f)) g
  rw [flat_momentum_pair,flat_momentum_pair]

/-- The genuine transpose follows from the same original weighted source pairing. -/
theorem original_flat_gauge_adjoint (v : Gauge) : Commute flatKinetic (GaussMomentumAdjoint.adjoint (0,v)) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (flatKinetic (GaussMomentumAdjoint.adjoint (0,v) g))=
    sourcePair f (GaussMomentumAdjoint.adjoint (0,v) (flatKinetic g))
  rw [flat_kinetic_pair,adjoint_pair,adjoint_pair,flat_kinetic_pair]
  exact congrArg (fun q => sourcePair q g) (LinearMap.congr_fun (original_flat_gauge_momentum v).eq.symm f)

private theorem flat_multiplier_invariant (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi : ∀ (z : SourceCoordinateSlice) (t : ℝ) (u : scalarSlice),c (z+t • scalarAxis u)=c z) :
    Commute flatKinetic (multiply c hc) := by
  have hD (i : SliceIndex) : Commute (flatD i) (multiply c hc) := by
    apply multiplier_flat
    intro z
    have hf := ((hc z).differentiableAt (by simp)).hasFDerivAt
    have ht : HasDerivAt (fun t : ℝ => z.val+t • scalarAxis (scalarFrame i)) (scalarAxis (scalarFrame i)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (scalarAxis (scalarFrame i))).const_add z.val
    have he := hf.comp_hasDerivAt_of_eq 0 ht (by simp)
    have hh : (fun t : ℝ => c (z.val+t • scalarAxis (scalarFrame i)))=(fun _ : ℝ => c z.val) := funext (fun t => hi z.val t (scalarFrame i))
    change HasDerivAt (fun t : ℝ => c (z.val+t • scalarAxis (scalarFrame i)))
      (fderiv ℝ c z.val (scalarAxis (scalarFrame i))) 0 at he
    rw [hh] at he
    exact he.unique (hasDerivAt_const 0 _)
  rw [flat_kinetic_derivatives]
  apply Commute.smul_left
  apply Commute.sum_left
  intro i _
  exact (hD i).mul_left (hD i)

/-- The whole original electric form commutes with flat61, including its metric and independent adjoints. -/
theorem original_flat_gauge_kinetic : Commute flatKinetic gaugeKinetic := by
  unfold gaugeKinetic
  apply Commute.smul_right
  apply Commute.sum_right
  intro a _
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  have hw : Commute flatKinetic (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
    apply flat_multiplier_invariant
    intro z t u
    simp only [gaugeWeight,volume,inverseSpatial,scalarAxis,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
  exact (original_flat_gauge_adjoint (gaugeDirection i a).2).mul_right
    (hw.mul_right (original_flat_gauge_momentum (gaugeDirection j a).2))

private theorem gauge_inverse : Commute gaugeKinetic inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have h := congrArg inverseVolumeAction (LinearMap.congr_fun gauge_kinetic_volume.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using h.symm

private theorem scalar_orthogonal_split :
    scalarKinetic=inverseVolumeAction*orthogonalRemainder-
      ((sourceTime 0 : ℂ)/2) • (inverseVolumeAction*flatKinetic) := by
  have hVU : inverseVolumeAction*volumeAction=(1 : End) := by
    apply LinearMap.ext
    intro f
    have h : Commute inverseVolumeAction volumeAction := real_volume _ _
    exact (LinearMap.congr_fun h.eq f).trans (volume_inverse f)
  rw [orthogonalRemainder,mul_add,mul_smul_comm,←mul_assoc,hVU,one_mul]
  module

/-- Mixed44 now reads only the original nine orthogonal scalar rows; full native momenta were never assumed to commute. -/
theorem original_mixed_kinetic_reduction :
    scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic=
      inverseVolumeAction*(orthogonalRemainder*gaugeKinetic-gaugeKinetic*orthogonalRemainder) := by
  rw [scalar_orthogonal_split]
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,mul_assoc]
  have hg (A : End) : gaugeKinetic*(inverseVolumeAction*A)=inverseVolumeAction*(gaugeKinetic*A) := by
    rw [←mul_assoc,gauge_inverse.eq,mul_assoc]
  rw [hg,hg,(original_flat_gauge_kinetic).eq]
  module

open SourceInverseNoetherEnergy SourceScalarVirialBulk

/-- The same full H/bulk source current consumes the reduction before any signed-current estimate. -/
theorem original_bulk_mixed_reduction :
    bulkCurrent=(3*Complex.I*(sourceTime 0 : ℂ)/4) •
      (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
      inverseVolumeAction*((44 : ℂ) • (inverseVolumeAction*
          (orthogonalRemainder*gaugeKinetic-gaugeKinetic*orthogonalRemainder))-
        (8 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*scalarKinetic-
          scalarKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
        (36 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*gaugeKinetic-
          gaugeKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
        (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction)) := by
  rw [original_current_kinetic_source,original_mixed_kinetic_reduction]


end LowEnergy.SourceNativeMixedCurvatureReduction
