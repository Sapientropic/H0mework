import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMixedCurvatureReduction
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussInverseSecond
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeBrokenGaussCurvatureCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceNativeMomentumCurvature
open GaussLiveMomentum GaussInverseSecond GaussCoreDifferential GaussCoreHilbert GaussHistoryHilbert
open GaussNativeMatter GaussNativeForm GaussFockPair GaussNativeEnergy GaussDiagonalHistory
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceQuantumResidualFlow SourceNativeMixedCurvatureReduction
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariationDensity
open DiracExteriorMatterAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineCoframeGravityGaugeRegularity StageNineP286LinkedActiveLieRepresentation
open GaussQuantumMultiplier
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

/-- The native moving row retains both actual scalar and electric actions. -/
def nativeCurvature (u v : Ambient) (z : SourceCoordinateSlice) : Ambient :=
  ambientAction (inverseL z u).1 v-ambientAction (inverseL z v).1 u

/-- The actual inverse-chart derivative cancels the Lie connection curvature in the same source row. -/
theorem original_inverse_curvature (z : physicalChart) (u v : Ambient) :
    fderiv ℝ inverseL z.val (direction u z.val) v-
      fderiv ℝ inverseL z.val (direction v z.val) u=
      inverseL z.val (nativeCurvature u v z.val)-
        (nativeBracket (inverseL z.val u).1 (inverseL z.val v).1,0) := by
  have h := (inverse_curvature_transport z u v).symm.trans
    ((inverseCurvature_symmetric z u v).trans (inverse_curvature_transport z v u))
  have hb : nativeBracket (inverseL z.val v).1 (inverseL z.val u).1=
      -nativeBracket (inverseL z.val u).1 (inverseL z.val v).1 := coordinateBracket_skew _ _
  rw [hb,smul_neg] at h
  rw [nativeCurvature,map_sub]
  apply Prod.ext
  · have hf := congrArg Prod.fst h
    simp only [Prod.fst_add,Prod.fst_sub,direction] at hf ⊢
    linear_combination (norm := module) hf
  · have hf := congrArg Prod.snd h
    simp only [Prod.snd_add,Prod.snd_sub,add_zero,sub_zero,direction] at hf ⊢
    linear_combination (norm := module) hf

private theorem alg_bracket {R S : Type*} [Ring R] [Ring S] [Algebra ℂ R] [Algebra ℂ S]
    (e : R ≃ₐ[ℂ] S) (A B C : R) (h : A*B-B*A=C) : e A*e B-e B*e A=e C := by
  rw [←map_mul,←map_mul,←map_sub,h]

private theorem primal_bracket (a b : NativeLie) :
    nativePrimal a*nativePrimal b-
      nativePrimal b*nativePrimal a=nativePrimal (nativeBracket a b) := by
  have hp := (diracExteriorMotherLieAction_bracket
    (p286LieBlockEmbed (p286CoordinateEquiv.symm a))
    (p286LieBlockEmbed (p286CoordinateEquiv.symm b))).symm
  change LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a)))*
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm b)))-
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm b)))*
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a)))=
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed
        (p286CoordinateEquiv.symm (jointP286CoordinateLieBracket a b))))
  rw [jointP286CoordinateLieBracket,p286CoordinateEquiv.symm_apply_apply,p286LieBlockEmbed_bracket]
  simpa only using! alg_bracket (R := Module.End ℂ DiracExteriorMatterCarrier)
    (S := Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ) LowEnergy.Quantum.operatorMatrix _ _ _ hp

private theorem full_bracket (a b : NativeLie) :
    nativeFull a*nativeFull b-
      nativeFull b*nativeFull a=nativeFull (nativeBracket a b) := by
  change Matrix.fromBlocks (nativePrimal a) 0 0 ((nativePrimal a).map (starRingEnd ℂ))*
      Matrix.fromBlocks (nativePrimal b) 0 0 ((nativePrimal b).map (starRingEnd ℂ))-
      Matrix.fromBlocks (nativePrimal b) 0 0 ((nativePrimal b).map (starRingEnd ℂ))*
      Matrix.fromBlocks (nativePrimal a) 0 0 ((nativePrimal a).map (starRingEnd ℂ))=
      Matrix.fromBlocks (nativePrimal (nativeBracket a b)) 0 0 ((nativePrimal (nativeBracket a b)).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,neg_zero]
  congr 1
  · exact (sub_eq_add_neg _ _).symm.trans (primal_bracket a b)
  · have h := congrArg (fun A => A.map (starRingEnd ℂ)) (primal_bracket a b)
    rw [Matrix.map_sub (starRingEnd ℂ) (map_sub (starRingEnd ℂ)),Matrix.map_mul,Matrix.map_mul] at h
    exact (sub_eq_add_neg _ _).symm.trans h

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

/-- The original positive-conjugate Lie dual and actual CAR action close on the broken generator. -/
theorem original_fock_lie_bracket (a b : NativeLie) :
    nativeFock a*nativeFock b-nativeFock b*nativeFock a=
      nativeFock (nativeBracket a b) := by
  change quantized (nativeFull a)*quantized (nativeFull b)-
    quantized (nativeFull b)*quantized (nativeFull a)=quantized (nativeFull (nativeBracket a b))
  rw [quantized_bracket,full_bracket]



attribute [local irreducible] nativeFock

private theorem direction_derivative (z : physicalChart) (u : Ambient) (h : SourceCoordinateSlice) :
    fderiv ℝ (direction u) z.val h=(0,(fderiv ℝ inverseL z.val h u).2) := by
  have hi := ((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt
  have hv := hi.clm_apply (hasFDerivAt_const u z.val)
  have hp := (hasFDerivAt_const (0 : Coframe) z.val).prodMk hv.snd
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice => D h) hp.fderiv
  simp only [ContinuousLinearMap.coe_snd',ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,add_apply,zero_apply,map_zero,zero_add] at he
  change fderiv ℝ (fun x => ((0 : Coframe),(inverseL x u).2)) z.val h=_
  exact he

private theorem direction_curvature (z : physicalChart) (u v : Ambient) :
    VectorField.lieBracket ℝ (direction u) (direction v) z.val=
      direction (nativeCurvature u v z.val) z.val := by
  rw [VectorField.lieBracket,direction_derivative,direction_derivative]
  have h := congrArg Prod.snd (original_inverse_curvature z u v)
  simp only [Prod.snd_sub,sub_zero] at h
  apply Prod.ext
  · exact sub_self _
  · exact h

private theorem connection_derivative (z : physicalChart) (u : Ambient) (h : SourceCoordinateSlice) :
    fderiv ℝ (connection u) z.val h=nativeFock (fderiv ℝ inverseL z.val h u).1 := by
  have hi := ((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt
  have hv := hi.clm_apply (hasFDerivAt_const u z.val)
  let L : NativeLie →L[ℝ] (FockFiber →L[ℂ] FockFiber) := nativeFock.toContinuousLinearMap
  have hL : HasFDerivAt L L (inverseL z.val u).1 := L.hasFDerivAt
  have hp := hL.comp z.val hv.fst
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] (FockFiber →L[ℂ] FockFiber) => D h) hp.fderiv
  simp only [L,Function.comp_def,LinearMap.coe_toContinuousLinearMap',
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.flip_apply,add_apply,zero_apply,map_zero,zero_add] at he
  change fderiv ℝ (fun x => nativeFock (inverseL x u).1) z.val h=_
  exact he

private theorem connection_curvature (z : physicalChart) (u v : Ambient) :
    fderiv ℝ (connection v) z.val (direction u z.val)-
      fderiv ℝ (connection u) z.val (direction v z.val)+
      (connection u z.val*connection v z.val-connection v z.val*connection u z.val)=
        connection (nativeCurvature u v z.val) z.val := by
  rw [connection_derivative,connection_derivative]
  have h := congrArg Prod.fst (original_inverse_curvature z u v)
  simp only [Prod.fst_sub] at h
  have he := congrArg nativeFock h
  simp only [map_sub] at he
  change nativeFock (fderiv ℝ inverseL z.val (direction u z.val) v).1-
      nativeFock (fderiv ℝ inverseL z.val (direction v z.val) u).1+
      (nativeFock (inverseL z.val u).1*nativeFock (inverseL z.val v).1-
        nativeFock (inverseL z.val v).1*nativeFock (inverseL z.val u).1)=_
  rw [original_fock_lie_bracket]
  change _=nativeFock (inverseL z.val (nativeCurvature u v z.val)).1
  linear_combination (norm := module) he

private theorem directional_curvature (z : physicalChart) (u v : Ambient) (f : QuantumTest) :
    directional u (directional v f) z.val-directional v (directional u f) z.val=
      directional (nativeCurvature u v z.val) f z.val := by
  have hu : (directional u f : SourceCoordinateSlice → FockFiber)=
    fun x => fderiv ℝ f x (direction u x) := funext (directional_apply u f)
  have hv : (directional v f : SourceCoordinateSlice → FockFiber)=
    fun x => fderiv ℝ f x (direction v x) := funext (directional_apply v f)
  rw [directional_apply,directional_apply,hu,hv]
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
    (V := direction u) (W := direction v) (x := z.val)
    f.contDiff.contDiffAt (by simp only [minSmoothness_of_isRCLikeNormedField];exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    ((direction_smooth v z).differentiableAt (by simp)) ((direction_smooth u z).differentiableAt (by simp))
  rw [direction_curvature] at h
  exact h.symm

private theorem directional_connection (z : physicalChart) (u v : Ambient) (f : QuantumTest) :
    directional u (localMultiplier (connection v) (connection_smooth v) f) z.val=
      connection v z.val (directional u f z.val)+
        (fderiv ℝ (connection v) z.val (direction u z.val)) (f z.val) := by
  have hB := ((connection_smooth v z).differentiableAt (by simp)).hasFDerivAt
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ).hasFDerivAt.comp z.val hB
  have h := (hr.clm_apply (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  have he : (localMultiplier (connection v) (connection_smooth v) f : SourceCoordinateSlice → FockFiber)=
    fun x => connection v x (f x) := rfl
  rw [directional_apply,he]
  change fderiv ℝ (fun x => connection v x (f x)) z.val=_ at h
  rw [h]
  rfl

/-- Original covariant momenta have a first-order moving curvature row, including all native Lie components. -/
theorem original_native_momentum_curvature (z : physicalChart) (u v : Ambient) (f : QuantumTest) :
    covariantMomentum u (covariantMomentum v f) z.val-
      covariantMomentum v (covariantMomentum u f) z.val=
      (-Complex.I) • covariantMomentum (nativeCurvature u v z.val) f z.val := by
  have hd := directional_curvature z u v f
  have hc := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z.val)) (connection_curvature z u v)
  simp only [add_apply,sub_apply,mul_apply_eq_comp] at hc
  simp only [covariantMomentum,LinearMap.smul_apply,LinearMap.add_apply,map_smul,map_add,
    smul_apply,add_apply,smul_smul]
  change (-Complex.I) • ((-Complex.I) •
      (directional u (directional v f) z.val+connection u z.val (directional v f z.val))+
        (-Complex.I) • (directional u (localMultiplier (connection v) (connection_smooth v) f) z.val+
          connection u z.val (connection v z.val (f z.val))))-
    (-Complex.I) • ((-Complex.I) •
      (directional v (directional u f) z.val+connection v z.val (directional u f z.val))+
        (-Complex.I) • (directional v (localMultiplier (connection u) (connection_smooth u) f) z.val+
          connection v z.val (connection u z.val (f z.val))))=
    (-Complex.I*(-Complex.I)) •
      (directional (nativeCurvature u v z.val) f z.val+connection (nativeCurvature u v z.val) z.val (f z.val))
  rw [directional_connection,directional_connection]
  linear_combination (norm := module) (-Complex.I*(-Complex.I)) • (hd+hc)

/-- Mixed scalar/electric curvature preserves the actual residual and broken Lie actions. -/
theorem original_scalar_gauge_curvature (z : physicalChart) (e : Scalar) (w : Gauge) (f : QuantumTest) :
    covariantMomentum (e,0) (covariantMomentum (0,w) f) z.val-
      covariantMomentum (0,w) (covariantMomentum (e,0) f) z.val=
      (-Complex.I) • (-covariantMomentum
        (scalarP286ActionBilinear ((SourceNativeMixedCurvatureReduction.residualInverse z.val w).1 : NativeLie) e,0) f z.val+
        covariantMomentum (0,nativeGauge (inverseL z.val (e,0)).1 w) f z.val) := by
  rw [original_native_momentum_curvature]
  have he : nativeCurvature (e,0) (0,w) z.val=
      -(scalarP286ActionBilinear ((SourceNativeMixedCurvatureReduction.residualInverse z.val w).1 : NativeLie) e,0)+
        (0,nativeGauge (inverseL z.val (e,0)).1 w) := by
    unfold nativeCurvature ambientAction
    rw [original_gauge_inverse]
    simp only [LinearMap.prodMap_apply,map_zero,Prod.mk_sub_mk,Prod.neg_mk,Prod.mk_add_mk,
      zero_sub,sub_zero,neg_zero,add_zero,zero_add]
  have hp := congrArg (SourceElectricColumns.pointMomentum f z.val) he
  simp only [map_add,map_neg] at hp
  exact congrArg (fun x : FockFiber => (-Complex.I) • x) hp

open GaussScalarTransport GaussDensityCore

/-- The exact source Number-weighted divergence coefficient, retaining the physical density. -/
def divergenceCoefficient (N : ℕ) (v : Ambient) (z : SourceCoordinateSlice) : ℂ :=
  ∑ i : FrameIndex, (complexDensity N z)⁻¹*
    fderiv ℝ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z (frame i)

private theorem coefficient_density_smooth (N : ℕ) (v : Ambient) (i : FrameIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val :=
  (complexDensity_smooth N z).mul (coefficient_smooth v i z)

private theorem divergence_coefficient_smooth (N : ℕ) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (divergenceCoefficient N v) z.val := by
  apply ContDiffAt.sum
  intro i _
  exact (inverseDensity_smooth N z).mul
    (((coefficient_density_smooth N v i z).fderiv_right (by simp)).clm_apply contDiffAt_const)

private theorem field_transpose_value (N : ℕ) (v : Ambient) (f : ScalarTest) (z : physicalChart) :
    fieldTranspose N v f z.val=
      -fieldDerivative v f z.val-divergenceCoefficient N v z.val*f z.val := by
  have hr : complexDensity N z.val≠0 := by
    change (density N z.val : ℂ)≠0
    exact_mod_cast (density_pos N z).ne'
  have hterm (i : FrameIndex) :
      weightedTranspose N (frame i) (multiplyCoefficient v i f) z.val=
        -(coefficient v i z.val : ℂ)*derivative (frame i) f z.val-
          ((complexDensity N z.val)⁻¹*fderiv ℝ
            (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val (frame i))*f z.val := by
    rw [weightedTranspose_apply]
    have he : (fun x => complexDensity N x*(multiplyCoefficient v i f) x)=
        fun x => (complexDensity N x*(coefficient v i x : ℂ))*f x := by
      funext x
      change complexDensity N x*((coefficient v i x : ℂ)*f x)=(complexDensity N x*(coefficient v i x : ℂ))*f x
      ring
    rw [he,fderiv_fun_mul ((coefficient_density_smooth N v i z).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt,derivative_apply]
    change -(complexDensity N z.val)⁻¹*
      ((complexDensity N z.val*(coefficient v i z.val : ℂ))*fderiv ℝ f z.val (frame i)+
        f z.val*fderiv ℝ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val (frame i))=_
    field_simp [hr]
    ring
  simp only [fieldTranspose,fieldDerivative,LinearMap.sum_apply,LinearMap.comp_apply,sum_apply,
    hterm,divergenceCoefficient,Finset.sum_sub_distrib,Finset.sum_mul,neg_mul,Finset.sum_neg_distrib]
  rfl

private theorem derivative_transpose_component (v : Ambient) (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    GaussMomentumAdjoint.derivativeTranspose v f z.val word=
      fieldTranspose word.card v (component word f) z.val := by
  have h := congrArg (fun x : H => x word) (GaussMomentumAdjoint.transpose_embed v f)
  change embed (GaussMomentumAdjoint.derivativeTranspose v f) word=
    scalarLp word.card (fieldTranspose word.card v (component word f)) at h
  have he : (fun x : physicalChart => GaussMomentumAdjoint.derivativeTranspose v f x.val word)=ᵐ[GaussHistoryHilbert.numberMeasure word.card]
      (fun x : physicalChart => fieldTranspose word.card v (component word f) x.val) :=
    (embed_ae (GaussMomentumAdjoint.derivativeTranspose v f) word).symm.trans
      (h.symm ▸ scalarLp_ae word.card (fieldTranspose word.card v (component word f)))
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq he
    ((component word (GaussMomentumAdjoint.derivativeTranspose v f)).continuous.comp continuous_subtype_val)
    ((fieldTranspose word.card v (component word f)).continuous.comp continuous_subtype_val)) z

/-- This existing-core operator is zero order by its exact Number-weighted source value. -/
def divergenceAction (v : Ambient) : End := -(GaussMomentumAdjoint.derivativeTranspose v+directional v)

private theorem divergence_value (v : Ambient) (f : QuantumTest) (z : physicalChart) :
    divergenceAction v f z.val=
      GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (f z.val) := by
  apply PiLp.ext
  intro word
  change -(GaussMomentumAdjoint.derivativeTranspose v f z.val word+directional v f z.val word)=_
  rw [derivative_transpose_component,field_transpose_value]
  have hd := congrArg (fun q : ScalarTest => q z.val) (GaussMomentumAdjoint.component_directional v f word)
  change directional v f z.val word=fieldDerivative v (component word f) z.val at hd
  rw [hd,GaussFockWeights.weight_apply]
  change -(-fieldDerivative v (component word f) z.val-
    divergenceCoefficient word.card v z.val*f z.val word+fieldDerivative v (component word f) z.val)=_
  ring

/-- The actual transpose differs by the generated zero-order density divergence, not by an assumed P=P†. -/
theorem original_adjoint_divergence (v : Ambient) :
    GaussMomentumAdjoint.adjoint v=covariantMomentum v-Complex.I • divergenceAction v := by
  unfold GaussMomentumAdjoint.adjoint covariantMomentum divergenceAction
  change Complex.I • (GaussMomentumAdjoint.derivativeTranspose v-connectionAction v)=
    (-Complex.I) • (directional v+connectionAction v)-Complex.I • (-(GaussMomentumAdjoint.derivativeTranspose v+directional v))
  module

private theorem divergence_directional (z : physicalChart) (u v : Ambient) (f : QuantumTest) :
    directional u (divergenceAction v f) z.val=
      GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (directional u f z.val)+
      GaussFockWeights.weight (fun N => fderiv ℝ (divergenceCoefficient N v) z.val (direction u z.val)) (f z.val) := by
  apply PiLp.ext
  intro word
  have he : (fun x => component word (divergenceAction v f) x)=ᶠ[nhds z.val]
      (fun x => divergenceCoefficient word.card v x*component word f x) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    have h := congrArg (fun y : FockFiber => y word) (divergence_value v f ⟨x,hx⟩)
    exact h
  have hd := congrArg (fun q : ScalarTest => q z.val)
    (GaussMomentumAdjoint.component_directional u (divergenceAction v f) word)
  have hf := congrArg (fun q : ScalarTest => q z.val) (GaussMomentumAdjoint.component_directional u f word)
  change directional u (divergenceAction v f) z.val word=fieldDerivative u (component word (divergenceAction v f)) z.val at hd
  change directional u f z.val word=fieldDerivative u (component word f) z.val at hf
  change directional u (divergenceAction v f) z.val word=
    (GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (directional u f z.val)) word+
      (GaussFockWeights.weight (fun N => fderiv ℝ (divergenceCoefficient N v) z.val (direction u z.val)) (f z.val)) word
  rw [hd,GaussFockWeights.weight_apply,GaussFockWeights.weight_apply,hf,
    fieldDerivative_apply,fieldDerivative_apply,he.fderiv_eq,
    fderiv_fun_mul ((divergence_coefficient_smooth word.card v z).differentiableAt (by simp))
      ((component word f).contDiff.differentiable (by simp)).differentiableAt]
  change divergenceCoefficient word.card v z.val*fderiv ℝ (component word f) z.val (direction u z.val)+
      f z.val word*fderiv ℝ (divergenceCoefficient word.card v) z.val (direction u z.val)=_
  ring

private theorem native_divergence_current (z : physicalChart) (u v : Ambient) (f : QuantumTest) :
    covariantMomentum u (divergenceAction v f) z.val-divergenceAction v (covariantMomentum u f) z.val=
      (-Complex.I) • GaussFockWeights.weight
        (fun N => fderiv ℝ (divergenceCoefficient N v) z.val (direction u z.val)) (f z.val) := by
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z.val))
    (GaussFockWeights.native_weight_commute (fun N => divergenceCoefficient N v z.val) (inverseL z.val u).1).eq
  change GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (connection u z.val (f z.val))=
    connection u z.val (GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (f z.val)) at h
  change (-Complex.I) • (directional u (divergenceAction v f) z.val+
    connection u z.val (divergenceAction v f z.val))-divergenceAction v (covariantMomentum u f) z.val=_
  rw [divergence_value,divergence_value,divergence_directional,←h]
  change (-Complex.I) • (GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (directional u f z.val)+
      GaussFockWeights.weight (fun N => fderiv ℝ (divergenceCoefficient N v) z.val (direction u z.val)) (f z.val)+
      GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (connection u z.val (f z.val)))-
    GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val)
      ((-Complex.I) • (directional u f z.val+connection u z.val (f z.val)))=_
  rw [map_smul,map_add]
  module

/-- The genuine mixed transpose curvature is first order plus its exact Number-density contact. -/
theorem original_native_adjoint_curvature (z : physicalChart) (u v : Ambient) (f : QuantumTest) :
    covariantMomentum u (GaussMomentumAdjoint.adjoint v f) z.val-
      GaussMomentumAdjoint.adjoint v (covariantMomentum u f) z.val=
      (-Complex.I) • covariantMomentum (nativeCurvature u v z.val) f z.val-
        GaussFockWeights.weight (fun N => fderiv ℝ (divergenceCoefficient N v) z.val (direction u z.val)) (f z.val) := by
  rw [original_adjoint_divergence]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul,sub_apply,smul_apply]
  have hc := original_native_momentum_curvature z u v f
  have hd := native_divergence_current z u v f
  have he : covariantMomentum u (covariantMomentum v f) z.val-
      Complex.I • covariantMomentum u (divergenceAction v f) z.val-
      (covariantMomentum v (covariantMomentum u f) z.val-Complex.I • divergenceAction v (covariantMomentum u f) z.val)=
      (covariantMomentum u (covariantMomentum v f) z.val-covariantMomentum v (covariantMomentum u f) z.val)-
        Complex.I • (covariantMomentum u (divergenceAction v f) z.val-divergenceAction v (covariantMomentum u f) z.val) := by module
  rw [he,hc,hd,smul_smul]
  simp only [mul_neg,Complex.I_mul_I,neg_neg,one_smul]

private theorem real_fock_smul (r : ℝ) (f : FockFiber) : r • f=(r : ℂ) • f := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem metric_derivative (z : physicalChart) (u : Ambient) (i j : Fin 3) :
    fderiv ℝ (fun x => gaugeWeight x i j) z.val (direction u z.val)=0 := by
  have hf := ((gaugeWeight_smooth i j z).differentiableAt (by simp)).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => z.val+t • direction u z.val) (direction u z.val) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (direction u z.val)).const_add z.val
  have hd := hf.comp_hasDerivAt_of_eq 0 ht (by simp)
  have he : (fun t : ℝ => gaugeWeight (z.val+t • direction u z.val) i j)=fun _ : ℝ => gaugeWeight z.val i j := by
    funext t
    simp only [gaugeWeight,volume,inverseSpatial,direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
  change HasDerivAt (fun t : ℝ => gaugeWeight (z.val+t • direction u z.val) i j)
    (fderiv ℝ (fun x => gaugeWeight x i j) z.val (direction u z.val)) 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 _)

private theorem momentum_metric (u : Ambient) (i j : Fin 3) :
    Commute (covariantMomentum u) (GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · let M := GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
    have he : (M f : SourceCoordinateSlice → FockFiber)=fun x => gaugeWeight x i j • f x := by
      funext x
      exact (real_fock_smul _ _).symm
    have hd : directional u (M f) z=(gaugeWeight z i j : ℂ) • directional u f z := by
      rw [directional_apply,he,fderiv_fun_smul ((gaugeWeight_smooth i j ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change gaugeWeight z i j • fderiv ℝ f z (direction u z)+
        fderiv ℝ (fun x => gaugeWeight x i j) z (direction u z) • f z=_
      rw [metric_derivative ⟨z,hz⟩,zero_smul,add_zero,real_fock_smul]
      rfl
    change (-Complex.I) • (directional u (M f) z+connection u z ((gaugeWeight z i j : ℂ) • f z))=
      (gaugeWeight z i j : ℂ) • ((-Complex.I) • (directional u f z+connection u z (f z)))
    rw [hd,map_smul,←smul_add,smul_comm]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- Its source value is the first-order row in `original_native_momentum_curvature`. -/
def curvatureRow (u v : Ambient) : End := covariantMomentum u*covariantMomentum v-covariantMomentum v*covariantMomentum u

/-- Its source value contains the independent Number-density contact of `original_native_adjoint_curvature`. -/
def transposeCurvatureRow (u v : Ambient) : End := covariantMomentum u*GaussMomentumAdjoint.adjoint v-
  GaussMomentumAdjoint.adjoint v*covariantMomentum u

/-- The complete electric row has at most two native derivatives; the original metric and transpose stay literal. -/
def electricCurvature (u : Ambient) : End := (1/2 : ℂ) • ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
  (transposeCurvatureRow u (gaugeDirection i a)*
      GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)+
    GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
      GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*curvatureRow u (gaugeDirection j a))

/-- Third-order electric commutators are consumed by their generated first-order curvature and zero-order contact. -/
theorem original_electric_curvature (u : Ambient) :
    covariantMomentum u*gaugeKinetic-gaugeKinetic*covariantMomentum u=electricCurvature u := by
  simp only [gaugeKinetic,electricCurvature,mul_smul_comm,smul_mul_assoc,←smul_sub,
    Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hm := (momentum_metric u i j).eq
  change covariantMomentum u*(GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
      (GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))-
    (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
      (GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))*covariantMomentum u=_
  unfold transposeCurvatureRow curvatureRow
  linear_combination (norm := noncomm_ring)
    GaussMomentumAdjoint.adjoint (gaugeDirection i a)*hm*covariantMomentum (gaugeDirection j a)

open SourceBrokenGaussCurvatureCurrent SourceScalarNativeComparison SourceHamiltonianVolume SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare

/-- The original mixed44 signed half-current directly consumes the reduced electric rows. -/
theorem original_mixed_electric_current (f : QuantumTest) :
    (sourcePair f (((44 : ℂ) • (inverseVolumeAction*(scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic))) f)).im/2=
      -22*sourceTime 0*(∑ i : OrthogonalIndex,
        sourcePair (inverseVolumeAction (orthogonalColumn i f))
          (inverseVolumeAction (electricCurvature ((orthogonalFrame i : Scalar),0) f))).im := by
  have hrows (i : OrthogonalIndex) : curvatureColumn i=electricCurvature ((orthogonalFrame i : Scalar),0) :=
    original_electric_curvature ((orthogonalFrame i : Scalar),0)
  rw [original_mixed_half_current]
  unfold signedCurvaturePair
  simp only [hrows]

end LowEnergy.SourceNativeMomentumCurvature
