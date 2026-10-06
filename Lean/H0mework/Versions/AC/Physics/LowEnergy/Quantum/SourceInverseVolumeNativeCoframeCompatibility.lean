import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMatterCovarianceCancellation
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeDensityTrace
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceEulerCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceNativeCoframeCompatibility
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open GaussScalarTransport GaussDensityCore SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceNativeMomentumCurvature SourceNativeDensityTrace
open SourceDoubleGramCurvatureForm SourceNativeMatterCovarianceCancellation SourceUnmixedPotentialCancellation
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceDilationRemainder SourceScalarOscillatorAbsorption SourceInverseNoetherEnergy
open SourceScalarPositiveBulkWard SourceEulerCore
open scoped ContDiff Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

private theorem inverse_shift (c : Coframe) (z : SourceCoordinateSlice) : inverseL (z+(c,0))=inverseL z := by
  change inverseL (z.1+c,z.2+0)=inverseL z
  rw [add_zero]
  rfl

private theorem direction_shift (v : Ambient) (c : Coframe) (z : SourceCoordinateSlice) :
    direction v (z+(c,0))=direction v z := by rw [direction,inverse_shift];rfl

private theorem gamma_shift (c : Coframe) (z : SourceCoordinateSlice) : gammaLog (z+(c,0))=gammaLog z := by
  unfold gammaLog gammaField
  simp only [Prod.snd_add,add_zero]

private theorem gamma_density_shift (v : Ambient) (c : Coframe) (z : SourceCoordinateSlice) :
    gammaDensity v (z+(c,0))=gammaDensity v z := by
  have he : (fun x => gammaLog (x+(c,0)))=gammaLog := funext (gamma_shift c)
  have hd : fderiv ℝ gammaLog (z+(c,0))=fderiv ℝ gammaLog z := by
    rw [←fderiv_comp_add_right,he]
  rw [gammaDensity,gammaDensity,hd,direction_shift]

def nativeDensityCorrection (v : Ambient) (z : SourceCoordinateSlice) : ℝ := intrinsicDensity v z-gammaDensity v z

private theorem density_correction_shift (v : Ambient) (c : Coframe) (z : SourceCoordinateSlice) :
    nativeDensityCorrection v (z+(c,0))=nativeDensityCorrection v z := by
  unfold nativeDensityCorrection intrinsicDensity sourceLieResponse inverseLie
  rw [inverse_shift,gamma_density_shift]

private theorem density_coefficient_smooth (N : ℕ) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (divergenceCoefficient N v) z.val := by
  apply ContDiffAt.sum
  intro i _
  exact (inverseDensity_smooth N z).mul
    ((((complexDensity_smooth N z).mul (coefficient_smooth v i z)).fderiv_right (by simp)).clm_apply contDiffAt_const)

private theorem density_correction_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (nativeDensityCorrection v) z.val := by
  have he : nativeDensityCorrection v=ᶠ[nhds z.val] (fun x => (divergenceCoefficient 0 v x).re) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    have h := congrArg Complex.re (original_density_gamma_return 0 v ⟨x,hx⟩)
    simpa only [Complex.ofReal_re,nativeDensityCorrection,intrinsicDensity] using h.symm
  have hr : ContDiffAt ℝ ∞ (fun x => (divergenceCoefficient 0 v x).re) z.val :=
    Complex.reCLM.contDiff.contDiffAt.comp z.val (density_coefficient_smooth 0 v z)
  exact hr.congr_of_eventuallyEq he

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
    rw [he,fderiv_fun_mul (((complexDensity_smooth N z).mul (coefficient_smooth v i z)).differentiableAt (by simp))
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

/-- The original independent adjoint correction is a real scalar multiplier independent of Number and coframe translation. -/
theorem original_native_density_multiplier (v : Ambient) :
    divergenceAction v=multiply (nativeDensityCorrection v) (density_correction_smooth v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · rw [divergence_value v f ⟨z,hz⟩]
    apply PiLp.ext
    intro word
    rw [GaussFockWeights.weight_apply,original_density_gamma_return word.card v ⟨z,hz⟩]
    rfl
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem invariant_multiplier_derivative (A : End) (T : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ f z,A f z=T z (f z)) (hi : ∀ c z,T (z+(c,0))=T z) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) A := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let v := GaussCoframeCore.coframeDirection i
  let γ : ℝ → SourceCoordinateSlice := fun t => z+t • v
  have hγ : HasDerivAt γ v 0 := by
    simpa only [γ,one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hγ0 : γ 0=z := by simp [γ]
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have hg := ((A f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have hT := (T z).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0 hf
  have he : (fun t => A f (γ t))=(fun t => T z (f (γ t))) := by
    funext t
    rw [hA]
    have ht : γ t=z+(t • EuclideanSpace.single i 1,0) := by
      simp only [γ,v,GaussCoframeCore.coframeDirection,Prod.smul_mk,smul_zero]
    rw [ht,hi]
  change HasDerivAt (fun t => A f (γ t)) _ 0 at hg
  change HasDerivAt (fun t => T z (f (γ t))) _ 0 at hT
  rw [he] at hg
  have heq := hg.unique hT
  change GaussCoframeCore.derivative v (A f) z=A (GaussCoframeCore.derivative v f) z
  rw [GaussCoframeCore.derivative_apply,hA,GaussCoframeCore.derivative_apply]
  exact heq

private theorem direction_coframe_derivative (v : Ambient) (i : Fin 6) (z : physicalChart) :
    fderiv ℝ (direction v) z.val (GaussCoframeCore.coframeDirection i)=0 := by
  let e := GaussCoframeCore.coframeDirection i
  have hg : HasDerivAt (fun t : ℝ => z.val+t • e) e 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z.val
  have hd := ((direction_smooth v z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hg (by simp)
  have he (t : ℝ) : direction v (z.val+t • e)=direction v z.val := by
    have hh : t • e=(t • EuclideanSpace.single i 1,0) := by simp only [e,GaussCoframeCore.coframeDirection,Prod.smul_mk,smul_zero]
    rw [hh,direction_shift]
  have hz : HasDerivAt (fun t : ℝ => direction v (z.val+t • e)) 0 0 := by
    simpa only [he] using hasDerivAt_const (0 : ℝ) (direction v z.val)
  exact hd.unique hz

private theorem coframe_directional (v : Ambient) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (directional v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · let e := GaussCoframeCore.coframeDirection i
    have hd : (directional v f : SourceCoordinateSlice → FockFiber)=fun x => fderiv ℝ f x (direction v x) :=
      funext (directional_apply v f)
    have hc : (GaussCoframeCore.derivative e f : SourceCoordinateSlice → FockFiber)=fun x => fderiv ℝ f x e :=
      funext (GaussCoframeCore.derivative_apply e f)
    have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
      (V := fun _ => e) (W := direction v) (x := z) f.contDiff.contDiffAt (by
        simp only [minSmoothness_of_isRCLikeNormedField];exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      ((direction_smooth v ⟨z,hz⟩).differentiableAt (by simp)) (differentiableAt_const _)
    have hb : VectorField.lieBracket ℝ (fun _ => e) (direction v) z=0 := by
      rw [VectorField.lieBracket,direction_coframe_derivative v i ⟨z,hz⟩,(hasFDerivAt_const e z).fderiv,zero_apply,sub_self]
    rw [hb,map_zero] at h
    change GaussCoframeCore.derivative e (directional v f) z=directional v (GaussCoframeCore.derivative e f) z
    rw [GaussCoframeCore.derivative_apply,directional_apply,hd,hc]
    exact sub_eq_zero.mp h.symm
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem coframe_connection (v : Ambient) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i))
      (localMultiplier (connection v) (connection_smooth v)) := by
  apply invariant_multiplier_derivative _ (connection v) (fun _ _ => rfl)
  intro c z
  unfold connection
  rw [inverse_shift]

/-- Coframe differentiation commutes with every original native momentum. -/
theorem original_native_coframe_derivative (v : Ambient) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (covariantMomentum v) := by
  unfold covariantMomentum
  exact ((coframe_directional v i).add_right (coframe_connection v i)).smul_right _

private theorem coframe_divergence (v : Ambient) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (divergenceAction v) := by
  rw [original_native_density_multiplier]
  apply invariant_multiplier_derivative _
    (fun z => (nativeDensityCorrection v z : ℂ) • ContinuousLinearMap.id ℂ FockFiber) (fun _ _ => rfl)
  intro c z
  rw [density_correction_shift]

/-- The true native transpose retains the same coframe compatibility after its source density correction. -/
theorem original_native_adjoint_coframe_derivative (v : Ambient) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (GaussMomentumAdjoint.adjoint v) := by
  rw [original_adjoint_divergence]
  exact (original_native_coframe_derivative v i).sub_right ((coframe_divergence v i).smul_right _)

private theorem paired_commute (A B C : End)
    (hA : ∀ f g,sourcePair f (A g)=sourcePair (A f) g)
    (hC : ∀ f g,sourcePair f (C g)=sourcePair (B f) g) (h : Commute A B) : Commute A C := by
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  change sourcePair f (A (C g))=sourcePair f (C (A g))
  calc
    _=sourcePair (A f) (C g) := hA _ _
    _=sourcePair (B (A f)) g := hC _ _
    _=sourcePair (A (B f)) g := congrArg (fun x => sourcePair x g) (LinearMap.congr_fun h.eq f).symm
    _=sourcePair (B f) (A g) := (hA _ _).symm
    _=_ := (hC _ _).symm

private theorem gram_pair (f g : QuantumTest) : sourcePair f (scalarGram g)=sourcePair (scalarGram f) g := by
  simp only [scalarGram,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact (GaussNativeForm.adjoint_pair _ _ _).trans (GaussMomentumAdjoint.momentum_pair _ _ _)

private theorem gram_coframe_momentum (i : Fin 6) : Commute scalarGram (GaussCoframeCore.momentum i) := by
  unfold GaussCoframeCore.momentum
  apply Commute.smul_right
  unfold scalarGram
  apply Commute.sum_left
  intro r _
  exact (original_native_adjoint_coframe_derivative (scalarDirection r) i).symm.mul_left
    (original_native_coframe_derivative (scalarDirection r) i).symm

private theorem gram_coframe_adjoint (i : Fin 6) : Commute scalarGram (GaussCoframeCore.adjoint i) :=
  paired_commute _ _ _ gram_pair (GaussCoframeKinetic.adjoint_pair i) (gram_coframe_momentum i)

private theorem native_coframe_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : ∀ z s,c (z.1,s)=c z)
    (v : Ambient) : Commute (multiply c hc) (covariantMomentum v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hd : fderiv ℝ c z (direction v z)=0 := by
      have hg : HasDerivAt (fun t : ℝ => z+t • direction v z) (direction v z) 0 := by
        simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z)).const_add z
      have he (t : ℝ) : c (z+t • direction v z)=c z := by
        change c (z.1+t • (0 : Coframe),z.2+t • (inverseL z v).2)=c z
        rw [smul_zero,add_zero,hi]
      have dh := ((hc ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt
        |>.comp_hasDerivAt_of_eq 0 hg (by simp)
      apply dh.unique
      change HasDerivAt (fun t : ℝ => c (z+t • direction v z)) 0 0
      rw [show (fun t : ℝ => c (z+t • direction v z))=(fun _ : ℝ => c z) from funext he]
      exact hasDerivAt_const (0 : ℝ) (c z)
    have hf : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    have hD : directional v (multiply c hc f) z=(c z : ℂ) • directional v f z := by
      rw [directional_apply,hf,fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change c z • fderiv ℝ f z (direction v z)+fderiv ℝ c z (direction v z) • f z=_
      rw [hd,zero_smul,add_zero]
      apply PiLp.ext
      intro word
      exact Complex.real_smul
    change (c z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))=
      (-Complex.I) • (directional v (multiply c hc f) z+connection v z ((c z : ℂ) • f z))
    rw [hD,map_smul,←smul_add,smul_comm]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem gram_coframe_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : ∀ z s,c (z.1,s)=c z) :
    Commute scalarGram (multiply c hc) := by
  unfold scalarGram
  apply Commute.sum_left
  intro r _
  have hp := native_coframe_coefficient c hc hi (scalarDirection r)
  exact (paired_commute _ _ _ (multiply_pair c hc) (adjoint_pair _) hp).symm.mul_left hp.symm

open GaussNativeMatter GaussQuantumMultiplier
open SaturationMonoid.PhysicsCore
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

private theorem full_spin_native (a : Fin 7) (b : NativeLie) : Commute (GaussCoframeSpin.full a) (nativeFull b) := by
  have hp := GaussMatterCore.spin_native_commute (GaussCoframeSpin.sourceSpin a) b
  change GaussCoframeSpin.primal a*nativePrimal b=nativePrimal b*GaussCoframeSpin.primal a at hp
  have hd := congrArg (fun M : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ => M.map (starRingEnd ℂ)) hp
  rw [Matrix.map_mul,Matrix.map_mul] at hd
  change Matrix.fromBlocks (GaussCoframeSpin.primal a) 0 0
    (if a.val<3 then (GaussCoframeSpin.primal a).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal a).map (starRingEnd ℂ))*
    Matrix.fromBlocks (nativePrimal b) 0 0 ((nativePrimal b).map (starRingEnd ℂ))=_
  change _=Matrix.fromBlocks (nativePrimal b) 0 0 ((nativePrimal b).map (starRingEnd ℂ))*
    Matrix.fromBlocks (GaussCoframeSpin.primal a) 0 0
      (if a.val<3 then (GaussCoframeSpin.primal a).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal a).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero]
  apply congrArg₂ (fun A B : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ => Matrix.fromBlocks A 0 0 B) hp
  split_ifs <;> simp only [Matrix.neg_mul,Matrix.mul_neg,hd]

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem spin_fiber_native (a : Fin 7) (b : NativeLie) :
    Commute (quantized (GaussCoframeSpin.full a)) (nativeFock b) := by
  apply sub_eq_zero.mp
  change quantized (GaussCoframeSpin.full a)*quantized (nativeFull b)-
    quantized (nativeFull b)*quantized (GaussCoframeSpin.full a)=0
  rw [quantized_bracket,(full_spin_native a b).eq,sub_self]
  exact map_zero quantizer

private theorem spin_directional (a : Fin 7) (v : Ambient) : Commute (GaussCoframeSpin.current a) (directional v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let T := (quantized (GaussCoframeSpin.full a)).restrictScalars ℝ
  have hf : (GaussCoframeSpin.current a f : SourceCoordinateSlice → FockFiber)=T ∘ f := rfl
  have hd := T.hasFDerivAt.comp z (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change quantized (GaussCoframeSpin.full a) (directional v f z)=directional v (GaussCoframeSpin.current a f) z
  rw [directional_apply,directional_apply,hf,hd.fderiv]
  rfl

private theorem spin_momentum (a : Fin 7) (v : Ambient) : Commute (GaussCoframeSpin.current a) (covariantMomentum v) := by
  have hc : Commute (GaussCoframeSpin.current a) (localMultiplier (connection v) (connection_smooth v)) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z)) (spin_fiber_native a (inverseL z v).1).eq
  unfold covariantMomentum
  exact ((spin_directional a v).add_right hc).smul_right _

private theorem gram_spin (a : Fin 7) : Commute scalarGram (GaussCoframeSpin.current a) := by
  unfold scalarGram
  apply Commute.sum_left
  intro r _
  have hp := spin_momentum a (scalarDirection r)
  exact (paired_commute _ _ _ (GaussCoframeSpin.current_pair a) (adjoint_pair _) hp).symm.mul_left hp.symm

private theorem gram_number : Commute scalarGram GaussCoframeForm.number := by
  unfold scalarGram
  apply Commute.sum_left
  intro r _
  have hp : Commute GaussCoframeForm.number (covariantMomentum (scalarDirection r)) := by
    unfold covariantMomentum
    exact ((number_directional _).add_right (number_connection _)).smul_right _
  exact (paired_commute _ _ _ GaussCoframeForm.number_pair (adjoint_pair _) hp).symm.mul_left hp.symm

private theorem gram_coframe_kinetic : Commute scalarGram GaussCoframeKinetic.kinetic := by
  unfold GaussCoframeKinetic.kinetic
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  change Commute scalarGram (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j))
  exact (gram_coframe_adjoint i).mul_right
    ((gram_coframe_coefficient _ _ (fun _ _ => rfl)).mul_right (gram_coframe_momentum j))

private theorem gram_coframe_mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : ∀ z s,c (z.1,s)=c z) :
    Commute scalarGram (GaussCoframeForm.mixed i a c hc) := by
  change Commute scalarGram ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply c hc*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply c hc*GaussCoframeSpin.current a)))
  exact ((gram_spin a).mul_right ((gram_coframe_coefficient c hc hi).mul_right (gram_coframe_momentum i)) |>.add_right
    ((gram_coframe_adjoint i).mul_right ((gram_coframe_coefficient c hc hi).mul_right (gram_spin a)))).smul_right _

/-- The full original coframe action, including all mixed, spin and Number terms, commutes with the actual native scalar Gram. -/
theorem original_scalar_gram_coframe_commute : Commute scalarGram GaussCoframeForm.coframeAction := by
  have hm : Commute scalarGram GaussCoframeForm.currentAction := by
    unfold GaussCoframeForm.currentAction
    exact (((gram_coframe_mixed _ _ _ _ (fun _ _ => rfl)).add_right
      (gram_coframe_mixed _ _ _ _ (fun _ _ => rfl))).add_right
      (gram_coframe_mixed _ _ _ _ (fun _ _ => rfl))).add_right
      (gram_coframe_mixed _ _ _ _ (fun _ _ => rfl))
  have hs (a : Fin 7) : Commute scalarGram (GaussCoframeForm.spinSquare a) := by
    change Commute scalarGram ((GaussCoframeForm.spinWeight a : ℂ) •
      (GaussCoframeSpin.current a*(multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
        GaussCoframeSpin.current a)))
    exact ((gram_spin a).mul_right ((gram_coframe_coefficient _ _ (fun _ _ => rfl)).mul_right (gram_spin a))).smul_right _
  have hn : Commute scalarGram GaussCoframeForm.numberShift := by
    change Commute scalarGram ((1/2 : ℂ) •
      (GaussCoframeForm.number*multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
        multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number))
    have hc := gram_coframe_coefficient GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth (fun _ _ => rfl)
    exact ((gram_number.mul_right hc).add_right (hc.mul_right gram_number)).smul_right _
  unfold GaussCoframeForm.coframeAction
  exact (((gram_coframe_kinetic.add_right hm).add_right (Commute.sum_right _ _ _ (fun a _ => hs a))).add_right hn).add_right
    (gram_coframe_coefficient _ _ (fun _ _ => rfl))

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem matter_inverse : Commute GaussMatterCore.matterAction inverseVolumeAction := by
  unfold GaussMatterCore.matterAction
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussMatterCore.localMatrix i b z)) (reciprocalVolume z : ℂ) (f z)

/-- The full original coframe action carries precisely the already generated inverse-volume flux. -/
theorem original_coframe_inverse_current :
    GaussCoframeForm.coframeAction*inverseVolumeAction-inverseVolumeAction*GaussCoframeForm.coframeAction=
      (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction) := by
  have hr : Commute (nativeAction+GaussMatterCore.matterAction) inverseVolumeAction := by
    unfold nativeAction
    exact (((inverse_commute _ scalar_kinetic_volume).add_left (inverse_commute _ gauge_kinetic_volume)).add_left
      (inverse_commute _ (real_volume _ _))).add_left matter_inverse
  have he : diagonalAction=GaussCoframeForm.coframeAction+(nativeAction+GaussMatterCore.matterAction) := by
    unfold diagonalAction
    abel
  have h := SourceScalarInverseRetardedBudget.original_inverse_current
  rw [he,add_mul,mul_add,hr.eq] at h
  simpa only [add_sub_add_right_eq_sub] using h

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0 : ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (scalarWeight z : ℂ) • f z=(-(sourceTime 0 : ℂ)) • ((reciprocalVolume z : ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem scalar_kinetic_gram : scalarKinetic=(-(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*scalarGram) := by
  have hr (i : ScalarIndex) : sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth=
      (-(sourceTime 0 : ℂ)) • (inverseVolumeAction*(GaussMomentumAdjoint.adjoint (scalarDirection i)*covariantMomentum (scalarDirection i))) := by
    change GaussMomentumAdjoint.adjoint (scalarDirection i)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i))=_
    rw [weight_inverse,smul_mul_assoc,mul_smul_comm,←mul_assoc,
      (inverse_commute _ (native_adjoint_volume (scalarDirection i))).eq,mul_assoc]
  simp only [scalarKinetic,hr,←Finset.smul_sum,←Finset.mul_sum,smul_smul,scalarGram]
  congr 1
  ring

/-- The native/coframe current is an exact source volume/dilation word; its sign is retained. -/
theorem original_coframe_scalar_current :
    GaussCoframeForm.coframeAction*scalarKinetic-scalarKinetic*GaussCoframeForm.coframeAction=
      (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*scalarKinetic) := by
  have hc : GaussCoframeForm.coframeAction*(inverseVolumeAction*scalarGram)-
      (inverseVolumeAction*scalarGram)*GaussCoframeForm.coframeAction=
      (GaussCoframeForm.coframeAction*inverseVolumeAction-inverseVolumeAction*GaussCoframeForm.coframeAction)*scalarGram := by
    linear_combination (norm := noncomm_ring) -inverseVolumeAction*original_scalar_gram_coframe_commute.eq
  rw [scalar_kinetic_gram]
  simp only [mul_smul_comm,smul_mul_assoc,←smul_sub]
  rw [hc,original_coframe_inverse_current,smul_mul_assoc]
  simp only [mul_assoc,smul_smul]
  congr 1
  ring

private theorem scalar_coframe_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : ∀ z s,c (z.1,s)=c z) :
    Commute scalarKinetic (multiply c hc) := by
  rw [scalar_kinetic_gram]
  exact (((inverse_commute _ (real_volume c hc)).symm).mul_left (gram_coframe_coefficient c hc hi)).smul_left _

private theorem geometric_split : geometricAction=
    GaussCoframeForm.coframeAction-multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth+scalarSpatialAction := by
  unfold geometricAction GaussCoframeForm.coframeAction
  abel

/-- The two volume fluxes remain with their actual signs; the scalar/coframe reader has been replaced by its exact dilation word. -/
def nativeCoframeBulkCurrent : End :=
  (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
    inverseVolumeAction*(-(8 : ℂ) • (((localAction+scalarSpatialAction)*scalarKinetic-
      scalarKinetic*(localAction+scalarSpatialAction))+
      (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*scalarKinetic))+
      (36 : ℂ) • ((magneticAction+geometricAction)*gaugeKinetic-
        gaugeKinetic*(magneticAction+geometricAction))-
      (36 : ℂ) • gaugeMatterDivergence+
      (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction))

/-- The complete original bulk current consumes the source coframe compatibility before any estimate. -/
theorem original_bulk_current_native_coframe : bulkCurrent=nativeCoframeBulkCurrent := by
  have hs : (localAction+geometricAction)*scalarKinetic-scalarKinetic*(localAction+geometricAction)=
      ((localAction+scalarSpatialAction)*scalarKinetic-scalarKinetic*(localAction+scalarSpatialAction))+
        (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*scalarKinetic) := by
    rw [←original_coframe_scalar_current,geometric_split]
    have hv := (scalar_coframe_coefficient GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
      (fun _ _ => rfl)).eq
    simp only [add_mul,mul_add,sub_mul,mul_sub]
    rw [hv]
    module
  rw [original_bulk_current_matter_reduced]
  unfold matterReducedBulkCurrent nativeCoframeBulkCurrent
  rw [hs]

/-- Same actual F and raised defect, with every remaining coframe, spatial, gauge and matter term retained. -/
theorem original_remaining_raised_native_coframe (F : Index) (A : End) (q : QuantumTest) :
    remainingRaisedCurrent F A q=(sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
      (sourcePair (A q) ((nativeCoframeBulkCurrent-scalarCurrent) (A q))).im/2 := by
  have h := original_current_split
  rw [original_bulk_current_native_coframe] at h
  have hr : remainingCurrent=nativeCoframeBulkCurrent-scalarCurrent := by
    linear_combination (norm := module) -h
  rw [remainingRaisedCurrent,hr]

end LowEnergy.SourceNativeCoframeCompatibility
