import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockReflectedForm
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceEulerCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceCoframeBlockHardy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussCoframeForm SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumScalarChart
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def blockIndices (b : Fin 3) : Finset (Fin 6) := ![{0},{1,2},{3,4,5}] b
def blockVector (b : Fin 3) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  ∑ i ∈ blockIndices b,z.1 i • GaussCoframeCore.coframeDirection i
private def blockScale (b : Fin 3) (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  z+(r-1) • blockVector b z

private theorem block_card (b : Fin 3) : (blockIndices b).card=b.val+1 := by
  fin_cases b <;> simp [blockIndices]

private theorem block_scale_one (b : Fin 3) (z : SourceCoordinateSlice) : blockScale b 1 z=z := by
  simp [blockScale]
private theorem block_scale_gauge (b : Fin 3) (r : ℝ) (z : SourceCoordinateSlice) :
    (blockScale b r z).2=z.2 := by
  fin_cases b <;> simp [blockScale,blockVector,blockIndices,GaussCoframeCore.coframeDirection]

private theorem block_scale_volume (b : Fin 3) (r : ℝ) (z : SourceCoordinateSlice) :
    volume (blockScale b r z)=r*volume z := by
  fin_cases b <;> simp [blockScale,blockVector,blockIndices,GaussCoframeCore.coframeDirection,
    volume,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] <;> ring

private theorem block_density_scale (b : Fin 3) (N : ℕ) (r : ℝ) (z : SourceCoordinateSlice) :
    GaussDensityCore.density N (blockScale b r z)=r^(N+2)*GaussDensityCore.density N z := by
  change jacobian ((blockScale b r z).2.2 : Gauge)*volume (blockScale b r z)^(N+2)=
    r^(N+2)*(jacobian (z.2.2 : Gauge)*volume z^(N+2))
  rw [block_scale_gauge,block_scale_volume,mul_pow]
  ring

private theorem density_block (b : Fin 3) (N : ℕ) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.density N) z.val (blockVector b z.val)=
      (N+2)*GaussDensityCore.density N z.val := by
  have hs : HasDerivAt (fun r : ℝ => blockScale b r z.val) (blockVector b z.val) 1 := by
    simpa only [blockScale,sub_self,zero_smul,add_zero,one_smul,zero_add] using!
      ((hasDerivAt_const (1:ℝ) z.val).add
        (((hasDerivAt_id (1:ℝ)).sub_const (1:ℝ)).smul_const (blockVector b z.val)))
  have chain := ((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 hs (block_scale_one b z.val).symm
  have hp := (((hasDerivAt_id (1 : ℝ)).pow (N+2)).mul_const (GaussDensityCore.density N z.val))
  have hvalue : HasDerivAt (fun r : ℝ => r^(N+2)*GaussDensityCore.density N z.val)
      ((N+2)*GaussDensityCore.density N z.val) 1 := by
    simpa [id_eq] using hp
  have he : (fun r : ℝ => GaussDensityCore.density N (blockScale b r z.val))=
      (fun r : ℝ => r^(N+2)*GaussDensityCore.density N z.val) :=
    funext (fun r => block_density_scale b N r z.val)
  change HasDerivAt (fun r : ℝ => GaussDensityCore.density N (blockScale b r z.val)) _ 1 at chain
  rw [he] at chain
  exact chain.unique hvalue

private theorem complex_density_block (b : Fin 3) (N : ℕ) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.complexDensity N) z.val (blockVector b z.val)=
      (N+2)*GaussDensityCore.complexDensity N z.val := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := GaussDensityCore.density N z.val)).comp z.val
    (((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt)
  change HasFDerivAt (GaussDensityCore.complexDensity N) _ z.val at h
  rw [h.fderiv]
  change (fderiv ℝ (GaussDensityCore.density N) z.val (blockVector b z.val) : ℂ)=_
  rw [density_block]
  push_cast
  rfl

def blockMomentum (b : Fin 3) : End := ∑ i ∈ blockIndices b,
  coordinateAction i*GaussCoframeCore.momentum i
private def blockAdjoint (b : Fin 3) : End := ∑ i ∈ blockIndices b,
  GaussCoframeCore.adjoint i*coordinateAction i
def blockDensity (b : Fin 3) : End := number+((b.val+3:ℕ):ℂ) • (1:End)
def centeredBlock (b : Fin 3) : End := blockMomentum b-(Complex.I/2) • blockDensity b

private theorem transpose_component (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word=
      GaussDensityCore.weightedTranspose word.card v (component word f) z.val := by
  let h := GaussDensityCore.weightedTranspose word.card v (component word f)
  have row : embed (GaussCoframeCore.transpose v f) word=scalarLp word.card h := by
    rw [GaussCoframeCore.transpose_embed]
    rfl
  have ae : (fun w : physicalChart => GaussCoframeCore.transpose v f w.val word)=ᵐ[
      GaussHistoryHilbert.numberMeasure word.card] (fun w : physicalChart => h w.val) :=
    (embed_ae (GaussCoframeCore.transpose v f) word).symm.trans (row ▸ scalarLp_ae word.card h)
  have eq := MeasureTheory.Measure.eq_of_ae_eq ae
    ((component word (GaussCoframeCore.transpose v f)).continuous.comp continuous_subtype_val)
    (h.continuous.comp continuous_subtype_val)
  exact congrFun eq z

private theorem transpose_formula (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word=
      -fderiv ℝ (component word f) z.val v-
        (GaussDensityCore.complexDensity word.card z.val)⁻¹*
          fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v*f z.val word := by
  rw [transpose_component,GaussDensityCore.weightedTranspose_apply,fderiv_fun_mul
    ((GaussDensityCore.complexDensity_smooth word.card z).differentiableAt (by simp))
    ((component word f).contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  have hn : GaussDensityCore.complexDensity word.card z.val≠0 := by
    change (GaussDensityCore.density word.card z.val:ℂ)≠0
    exact_mod_cast (GaussDensityCore.density_pos word.card z).ne'
  change -(GaussDensityCore.complexDensity word.card z.val)⁻¹*
      (GaussDensityCore.complexDensity word.card z.val*fderiv ℝ (component word f) z.val v+
      f z.val word*fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v)=_
  field_simp [hn]
  ring

private theorem coordinate_component (i : Fin 6) (f : QuantumTest) (word : Occupation) :
    (component word (coordinateAction i f) : SourceCoordinateSlice → ℂ)=
      fun z => (z.1 i:ℂ)*component word f z := rfl
private theorem coordinate_component_derivative (i : Fin 6) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    fderiv ℝ (component word (coordinateAction i f)) z (GaussCoframeCore.coframeDirection i)=
      (z.1 i:ℂ)*fderiv ℝ (component word f) z (GaussCoframeCore.coframeDirection i)+f z word := by
  rw [coordinate_component]
  have hc := (Complex.ofRealCLM.comp (SourceCoframeVolume.coordinate i)).hasFDerivAt (x := z)
  change HasFDerivAt (fun w : SourceCoordinateSlice => (w.1 i:ℂ)) _ z at hc
  rw [fderiv_fun_mul hc.differentiableAt
    ((component word f).contDiff.differentiable (by simp)).differentiableAt,hc.fderiv]
  simp [SourceCoframeVolume.coordinate,GaussCoframeCore.coframeDirection,component]
private theorem momentum_component (i : Fin 6) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    GaussCoframeCore.momentum i f z word=
      -Complex.I*fderiv ℝ (component word f) z (GaussCoframeCore.coframeDirection i) := by
  have h := congrArg (fun g : GaussDensityCore.ScalarTest => g z)
    (GaussCoframeCore.component_derivative (GaussCoframeCore.coframeDirection i) f word)
  change GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z word=
    GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) (component word f) z at h
  rw [GaussDensityCore.derivative_apply] at h
  change -Complex.I*GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z word=_
  rw [h]

private theorem block_sum (b : Fin 3) (z : SourceCoordinateSlice)
    (L : SourceCoordinateSlice →L[ℝ] ℂ) :
    (∑ i ∈ blockIndices b,(z.1 i:ℂ)*L (GaussCoframeCore.coframeDirection i))=L (blockVector b z) := by
  rw [blockVector,map_sum]
  simp only [map_smul,Complex.real_smul]

private def evaluate (z : SourceCoordinateSlice) (word : Occupation) : QuantumTest →ₗ[ℂ] ℂ where
  toFun f := f z word
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem original_block_adjoint (b : Fin 3) :
    blockAdjoint b=blockMomentum b-Complex.I • blockDensity b := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · let x : physicalChart := ⟨z,hz⟩
    apply PiLp.ext
    intro word
    have hn : GaussDensityCore.complexDensity word.card z≠0 := by
      change (GaussDensityCore.density word.card x.val:ℂ)≠0
      exact_mod_cast (GaussDensityCore.density_pos word.card x).ne'
    have he (i : Fin 6) : GaussCoframeCore.adjoint i (coordinateAction i f) z word=
        (z.1 i:ℂ)*GaussCoframeCore.momentum i f z word-Complex.I*f z word-
        Complex.I*(GaussDensityCore.complexDensity word.card z)⁻¹*
          ((z.1 i:ℂ)*fderiv ℝ (GaussDensityCore.complexDensity word.card) z
            (GaussCoframeCore.coframeDirection i))*f z word := by
      change Complex.I*GaussCoframeCore.transpose (GaussCoframeCore.coframeDirection i)
        (coordinateAction i f) z word=_
      rw [transpose_formula _ _ _ x,coordinate_component_derivative,momentum_component]
      have hc : coordinateAction i f z word=(z.1 i:ℂ)*f z word := rfl
      rw [hc]
      dsimp only [x]
      ring
    change evaluate z word (blockAdjoint b f)=
      evaluate z word ((blockMomentum b-Complex.I • blockDensity b) f)
    simp only [blockAdjoint,blockMomentum,blockDensity,LinearMap.sum_apply,
      LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.add_apply,
      Module.End.mul_apply,map_sum,map_sub,map_smul,map_add]
    change (∑ i ∈ blockIndices b,GaussCoframeCore.adjoint i (coordinateAction i f) z word)=
      (∑ i ∈ blockIndices b,(z.1 i:ℂ)*GaussCoframeCore.momentum i f z word)-
        Complex.I*(number f z word+((b.val+3:ℕ):ℂ)*f z word)
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,block_card,nsmul_eq_mul]
    have hs : (∑ i ∈ blockIndices b,Complex.I*(GaussDensityCore.complexDensity word.card z)⁻¹*
        ((z.1 i:ℂ)*fderiv ℝ (GaussDensityCore.complexDensity word.card) z
          (GaussCoframeCore.coframeDirection i))*f z word)=
        Complex.I*(GaussDensityCore.complexDensity word.card z)⁻¹*
          (∑ i ∈ blockIndices b,(z.1 i:ℂ)*fderiv ℝ (GaussDensityCore.complexDensity word.card) z
            (GaussCoframeCore.coframeDirection i))*f z word := by
      simp only [Finset.mul_sum,Finset.sum_mul]
    rw [hs,block_sum,complex_density_block b word.card x,number_apply]
    change _= _
    push_cast
    field_simp [hn]
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem block_momentum_pair (b : Fin 3) (f g : QuantumTest) :
    sourcePair f (blockMomentum b g)=sourcePair (blockAdjoint b f) g := by
  simp only [blockMomentum,blockAdjoint,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (coordinateAction i (GaussCoframeCore.momentum i g))=
    sourcePair (GaussCoframeCore.adjoint i (coordinateAction i f)) g
  exact (multiply_pair _ _ f (GaussCoframeCore.momentum i g)).trans
    (GaussCoframeCore.momentum_pair i (coordinateAction i f) g)

private theorem block_density_pair (b : Fin 3) (f g : QuantumTest) :
    sourcePair f (blockDensity b g)=sourcePair (blockDensity b f) g := by
  have h := number_pair f g
  unfold blockDensity
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,map_natCast]
  exact congrArg (fun a : ℂ => a+((b.val+3:ℕ):ℂ)*sourcePair f g) h

private theorem number_coordinate (i : Fin 6) : Commute number (coordinateAction i) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change number (coordinateAction i f) z word=coordinateAction i (number f) z word
  rw [number_apply]
  change (word.card:ℂ)*((z.1 i:ℂ)*f z word)=(z.1 i:ℂ)*(number f z word)
  rw [number_apply]
  ring

private theorem number_momentum (i : Fin 6) (f : QuantumTest) :
    number (GaussCoframeCore.momentum i f)=GaussCoframeCore.momentum i (number f) := by
  change number ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f)=
    (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (number f)
  rw [map_smul]
  exact congrArg ((-Complex.I) • ·) (LinearMap.congr_fun
    (SourceEulerCore.number_coframe_derivative (GaussCoframeCore.coframeDirection i)).eq f)

private theorem number_block (b : Fin 3) : Commute number (blockMomentum b) := by
  apply LinearMap.ext
  intro f
  change number (blockMomentum b f)=blockMomentum b (number f)
  simp only [blockMomentum,LinearMap.sum_apply,map_sum,Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (LinearMap.congr_fun (number_coordinate i).eq (GaussCoframeCore.momentum i f)).trans
    (congrArg (coordinateAction i) (number_momentum i f))

private theorem block_density_commute (b : Fin 3) : Commute (blockMomentum b) (blockDensity b) := by
  change blockMomentum b*blockDensity b=blockDensity b*blockMomentum b
  unfold blockDensity
  rw [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul,(number_block b).eq]

private theorem centered_density_commute (b : Fin 3) : Commute (centeredBlock b) (blockDensity b) := by
  apply LinearMap.ext
  intro f
  change centeredBlock b (blockDensity b f)=blockDensity b (centeredBlock b f)
  simp only [centeredBlock,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul]
  exact congrArg (fun t : QuantumTest => t-(Complex.I/2) • blockDensity b (blockDensity b f))
    (LinearMap.congr_fun (block_density_commute b).eq f)

private theorem centered_pair (b : Fin 3) (f g : QuantumTest) :
    sourcePair f (centeredBlock b g)=sourcePair (centeredBlock b f) g := by
  have h := block_momentum_pair b f g
  rw [original_block_adjoint] at h
  have hd := block_density_pair b f g
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_left,inner_smul_left,Complex.conj_I] at h
  unfold centeredBlock
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    map_div₀,Complex.conj_I,map_ofNat]
  change sourcePair f (blockMomentum b g)-(Complex.I/2)*sourcePair f (blockDensity b g)=
    sourcePair (blockMomentum b f) g-(-Complex.I/2)*sourcePair (blockDensity b f) g
  rw [hd]
  change sourcePair f (blockMomentum b g)=sourcePair (blockMomentum b f) g-
    (-Complex.I)*sourcePair (blockDensity b f) g at h
  linear_combination h

private theorem centered_density_real (b : Fin 3) (f : QuantumTest) :
    (sourcePair (centeredBlock b f) (blockDensity b f)).im=0 := by
  have hc := LinearMap.congr_fun (centered_density_commute b).eq f
  have he : sourcePair (centeredBlock b f) (blockDensity b f)=
      sourcePair (blockDensity b f) (centeredBlock b f) := by
    calc
      _=sourcePair f (centeredBlock b (blockDensity b f)) := (centered_pair b f _).symm
      _=sourcePair f (blockDensity b (centeredBlock b f)) := congrArg (sourcePair f) hc
      _=_ := block_density_pair b f _
  have h := congrArg Complex.im (pair_conjugate (centeredBlock b f) (blockDensity b f))
  rw [←he] at h
  simp only [Complex.conj_im] at h
  linarith

/-- The true block transpose generates its Number shift and the exact centered Hardy square. -/
theorem original_block_centered_square (b : Fin 3) (f : QuantumTest) :
    ‖embed (blockMomentum b f)‖^2=‖embed (centeredBlock b f)‖^2+
      (1/4:ℝ)*‖embed (blockDensity b f)‖^2 := by
  have hx : embed (blockMomentum b f)=embed (centeredBlock b f)+
      (Complex.I/2) • embed (blockDensity b f) := by
    unfold centeredBlock
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul]
    module
  rw [hx,norm_add_sq (𝕜 := ℂ),norm_smul,inner_smul_right]
  have hn : ‖(Complex.I/2:ℂ)‖=(1/2:ℝ) := by rw [norm_div];norm_num
  rw [hn]
  have hi := centered_density_real b f
  change _+2*((Complex.I/2)*sourcePair (centeredBlock b f) (blockDensity b f)).re+_= _
  simp only [Complex.mul_re,Complex.div_re,Complex.div_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul]
  norm_num
  rw [hi]
  ring

private theorem chart_diagonal_ne (z : physicalChart) :
    z.val.1 0≠0 ∧ z.val.1 2≠0 ∧ z.val.1 5≠0 := by
  have h := (volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at h
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2,(mul_ne_zero_iff.mp h).2⟩

private theorem block_connection_coefficient (b : Fin 3) (z : physicalChart) (a : Fin 3) :
    (∑ i ∈ blockIndices b,z.val.1 i*SourceCoframeSpinConnection.spinConnection z.val.1 i a)=0 := by
  obtain ⟨h0,h2,h5⟩ := chart_diagonal_ne z
  fin_cases b <;> fin_cases a <;> simp [blockIndices,SourceCoframeSpinConnection.spinConnection]
  all_goals field_simp
  all_goals ring

private theorem block_connection_fiber (b : Fin 3) (z : physicalChart) :
    (∑ i ∈ blockIndices b,z.val.1 i • SourceCoframeSpinConnection.connectionFiber i z.val)=0 := by
  simp only [SourceCoframeSpinConnection.connectionFiber,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_smul,block_connection_coefficient,zero_smul,Finset.sum_const_zero]

private def evaluateFiber (z : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] FockFiber where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem block_connection_zero (b : Fin 3) :
    (∑ i ∈ blockIndices b,coordinateAction i*SourceCoframeCovariantAction.connectionAction i)=(0:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have h := congrArg (fun A : SourceCoframeSpinConnection.FiberEnd => A (f z))
      (block_connection_fiber b ⟨z,hz⟩)
    simp only [sum_apply,smul_apply,zero_apply] at h
    change evaluateFiber z ((∑ i ∈ blockIndices b,coordinateAction i*
      SourceCoframeCovariantAction.connectionAction i) f)=0
    simp only [LinearMap.sum_apply,Module.End.mul_apply,map_sum]
    change (∑ i ∈ blockIndices b,(z.1 i:ℂ) •
      (SourceCoframeSpinConnection.connectionFiber i z (f z)))=0
    have he (i : Fin 6) : (z.1 i:ℂ) • (SourceCoframeSpinConnection.connectionFiber i z (f z))=
        z.1 i • (SourceCoframeSpinConnection.connectionFiber i z (f z)) := by
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    simpa only [he] using h
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- The actual spin connection cancels in each of the three source blocks, not only in their total trace. -/
theorem original_block_covariant_return (b : Fin 3) :
    (∑ i ∈ blockIndices b,coordinateAction i*SourceCoframeCovariantAction.covariantMomentum i)=
      blockMomentum b := by
  simp only [SourceCoframeCovariantAction.covariantMomentum,mul_add,Finset.sum_add_distrib,
    block_connection_zero,add_zero]
  rfl

private def densityRoot (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  GaussFockWeights.weight (fun N => (Real.sqrt (GaussDensityCore.density N z):ℂ))

private theorem density_root_pair (z : physicalChart) (f g : QuantumTest) :
    inner ℂ (densityRoot z.val (f z.val)) (densityRoot z.val (g z.val))=densityPair f g z.val := by
  rw [PiLp.inner_apply,densityPair_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [RCLike.inner_apply]
  change ((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*g z.val word)*
      star ((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*f z.val word)=_
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  have hs : ((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*
      (Real.sqrt (GaussDensityCore.density word.card z.val):ℂ))=
      (GaussDensityCore.density word.card z.val:ℂ) := by
    rw [←Complex.ofReal_mul,Real.mul_self_sqrt (GaussDensityCore.density_pos word.card z).le]
  change _=(GaussDensityCore.density word.card z.val:ℂ)*(starRingEnd ℂ (f z.val word))*g z.val word
  calc
    _=(((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*
      (Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)))*
        (starRingEnd ℂ (f z.val word))*g z.val word := by ring
    _=_ := by rw [hs]

private theorem density_root_square (f : QuantumTest) (z : SourceCoordinateSlice) :
    ‖densityRoot z (f z)‖^2=(densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · have h := congrArg Complex.re (density_root_pair ⟨z,hz⟩ f f)
    change (inner ℂ (densityRoot z (f z)) (densityRoot z (f z))).re=(densityPair f f z).re at h
    rw [←h]
    symm
    simpa only [RCLike.re_to_complex] using! inner_self_eq_norm_sq (𝕜 := ℂ) (densityRoot z (f z))
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp [hf,densityPair]

private theorem core_square_integral (f : QuantumTest) :
    MeasureTheory.Integrable (fun z => ‖densityRoot z (f z)‖^2) GaussHistoryHilbert.configurationMeasure ∧
      (∫ z,‖densityRoot z (f z)‖^2 ∂GaussHistoryHilbert.configurationMeasure)=‖embed f‖^2 := by
  simp_rw [density_root_square]
  refine ⟨(densityPair_integrable f f).re,?_⟩
  have h : (sourcePair f f).re=(∫ z,(densityPair f f z).re ∂GaussHistoryHilbert.configurationMeasure) := by
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f f)).symm
  rw [←h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (embed f)

private theorem fock_real_smul (c : ℝ) (v : FockFiber) : c • v=(c:ℂ) • v := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem root_real_smul (z : SourceCoordinateSlice) (c : ℝ) (v : FockFiber) :
    densityRoot z (c • v)=c • densityRoot z v := by
  rw [fock_real_smul,map_smul,←fock_real_smul]

private theorem block_point (b : Fin 3) (f : QuantumTest) (z : SourceCoordinateSlice) :
    blockMomentum b f z=∑ i ∈ blockIndices b,z.1 i •
      ((SourceCoframeCovariantAction.covariantMomentum i f) z) := by
  rw [←original_block_covariant_return]
  change evaluateFiber z ((∑ i ∈ blockIndices b,coordinateAction i*
    SourceCoframeCovariantAction.covariantMomentum i) f)=_
  simp only [LinearMap.sum_apply,Module.End.mul_apply,map_sum]
  change (∑ i ∈ blockIndices b,(z.1 i:ℂ) •
    ((SourceCoframeCovariantAction.covariantMomentum i f) z))=_
  simp only [fock_real_smul]

private def extraColumn (a : Fin 3) : End :=
  ![coordinateAction 0*SourceCoframeCovariantAction.covariantMomentum 1,
    coordinateAction 0*SourceCoframeCovariantAction.covariantMomentum 3,
    coordinateAction 1*SourceCoframeCovariantAction.covariantMomentum 3+
      coordinateAction 2*SourceCoframeCovariantAction.covariantMomentum 4] a

private theorem extra_point (a : Fin 3) (f : QuantumTest) (z : SourceCoordinateSlice) :
    extraColumn a f z=
      ![z.1 0 • ((SourceCoframeCovariantAction.covariantMomentum 1 f) z),
        z.1 0 • ((SourceCoframeCovariantAction.covariantMomentum 3 f) z),
        z.1 1 • ((SourceCoframeCovariantAction.covariantMomentum 3 f) z)+
          z.1 2 • ((SourceCoframeCovariantAction.covariantMomentum 4 f) z)] a := by
  fin_cases a <;> simp only [fock_real_smul] <;> rfl

private theorem point_gram (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceCoframeClockGram.clockGram z.1
      (fun i => densityRoot z ((SourceCoframeCovariantAction.covariantMomentum i f) z))=
        2*(∑ b : Fin 3,‖densityRoot z (blockMomentum b f z)‖^2)+
        4*(∑ a : Fin 3,‖densityRoot z (extraColumn a f z)‖^2) := by
  simp only [block_point,extra_point,map_sum,root_real_smul]
  simp [SourceCoframeClockGram.clockGram,blockIndices,Fin.sum_univ_succ]
  simp only [add_assoc]
  ring

private theorem original_block_gram_decomposition (f : QuantumTest) :
    SourceClockReflectedForm.coframeGram f=
      2*(∑ b : Fin 3,‖embed (blockMomentum b f)‖^2)+
      4*(∑ a : Fin 3,‖embed (extraColumn a f)‖^2) := by
  have hb (b : Fin 3) := (core_square_integral (blockMomentum b f)).1
  have ha (a : Fin 3) := (core_square_integral (extraColumn a f)).1
  have hbe (b : Fin 3) := (core_square_integral (blockMomentum b f)).2
  have hae (a : Fin 3) := (core_square_integral (extraColumn a f)).2
  change (∫ z,SourceCoframeClockGram.clockGram z.1
    (fun i => densityRoot z ((SourceCoframeCovariantAction.covariantMomentum i f) z))
    ∂GaussHistoryHilbert.configurationMeasure)=_
  simp_rw [point_gram]
  rw [MeasureTheory.integral_add ((MeasureTheory.integrable_finsetSum _ (fun b _ => hb b)).const_mul 2)
    ((MeasureTheory.integrable_finsetSum _ (fun a _ => ha a)).const_mul 4),
    MeasureTheory.integral_const_mul,MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ (fun b _ => hb b),
    MeasureTheory.integral_finsetSum _ (fun a _ => ha a)]
  simp only [hbe,hae]

/-- Whole-H coframe Gram pays the three exact centered block squares and all remaining positive rows. -/
theorem original_coframe_centered_block_square (f : QuantumTest) :
    SourceClockReflectedForm.coframeGram f=
      2*(∑ b : Fin 3,‖embed (centeredBlock b f)‖^2)+
      (1/2:ℝ)*(∑ b : Fin 3,‖embed (blockDensity b f)‖^2)+
      4*(∑ a : Fin 3,‖embed (extraColumn a f)‖^2) := by
  rw [original_block_gram_decomposition]
  simp_rw [original_block_centered_square]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  ring

private theorem density_norm (b : Fin 3) (f : QuantumTest) :
    ‖embed (blockDensity b f)‖^2=‖embed (number f)‖^2+
      2*(b.val+3:ℝ)*(sourcePair f (number f)).re+(b.val+3:ℝ)^2*‖embed f‖^2 := by
  unfold blockDensity
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
  rw [norm_add_sq (𝕜 := ℂ),norm_smul,inner_smul_right]
  have hn : ‖((b.val+3:ℕ):ℂ)‖=(b.val+3:ℝ) := by
    rw [Complex.norm_natCast]
    push_cast
    rfl
  rw [hn]
  have hi : (inner ℂ (embed (number f)) (embed f)).re=(sourcePair f (number f)).re := by
    exact inner_re_symm (𝕜 := ℂ) _ _
  change _+2*(((b.val+3:ℕ):ℂ)*inner ℂ (embed (number f)) (embed f)).re+_= _
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  rw [hi]
  push_cast
  simp only [Module.End.one_eq_id,LinearMap.id_apply]
  ring

private theorem three_density_norms (f : QuantumTest) :
    (1/2:ℝ)*(∑ b : Fin 3,‖embed (blockDensity b f)‖^2)=
      (3/2:ℝ)*‖embed (number f)‖^2+12*(sourcePair f (number f)).re+25*‖embed f‖^2 := by
  simp_rw [density_norm]
  simp [Fin.sum_univ_succ]
  ring

/-- The original Number-weighted Hilbert space receives the full three-block Hardy lower bound. -/
theorem original_coframe_three_block_hardy (f : QuantumTest) :
    2*(∑ b : Fin 3,‖embed (centeredBlock b f)‖^2)+
      (3/2:ℝ)*‖embed (number f)‖^2+12*(sourcePair f (number f)).re+25*‖embed f‖^2 ≤
        SourceClockReflectedForm.coframeGram f := by
  rw [original_coframe_centered_block_square,three_density_norms]
  have ha : 0≤∑ a : Fin 3,‖embed (extraColumn a f)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith only [ha]

end LowEnergy.SourceCoframeBlockHardy
