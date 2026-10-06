import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockSourceTail
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaCoframeRotationRows
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussQuantumMultiplier SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceCoframeSpinConnection SourceCoframeClockGram SourceClockReflectedForm SourceCoframeBlockHardy
open scoped ContDiff InnerProductSpace Matrix BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev J (b : Fin 3) : End := GaussCoframeSpin.current ⟨3+b.val,by omega⟩
private def rowForm (P : Fin 6 → End) (b : Fin 3) : End :=
  ![coordinateAction 1*P 3+coordinateAction 2*P 4,-(coordinateAction 0*P 3),coordinateAction 0*P 1] b

def bareRow (b : Fin 3) : End := rowForm GaussCoframeCore.momentum b
def covariantRow (b : Fin 3) : End := rowForm SourceCoframeCovariantAction.covariantMomentum b

private theorem diagonal_ne (z : physicalChart) : z.val.1 0≠0 ∧ z.val.1 2≠0 ∧ z.val.1 5≠0 := by
  have h := (volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at h
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2,(mul_ne_zero_iff.mp h).2⟩

private theorem row_connection (z : physicalChart) (b a : Fin 3) :
    (∑ i : Fin 6,currentRows z.val.1 i b*spinConnection z.val.1 i a)=if a=b then -1/2 else 0 := by
  obtain ⟨h0,h2,h5⟩ := diagonal_ne z
  fin_cases a <;> fin_cases b <;> simp [spinConnection,currentRows,Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

private theorem row_smooth (i : Fin 6) (b : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => currentRows w.1 i b) z.val := by
  fin_cases i <;> fin_cases b <;> simp [currentRows] <;> fun_prop
private def rowCoefficient (i : Fin 6) (b : Fin 3) : End :=
  multiply (fun z => currentRows z.1 i b) (row_smooth i b)

private theorem row_sum (P : Fin 6 → End) (b : Fin 3) : rowForm P b=∑ i : Fin 6,rowCoefficient i b*P i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  fin_cases b <;> simp [rowForm,rowCoefficient,currentRows,coordinateAction,Fin.sum_univ_succ,
    Module.End.mul_apply,LinearMap.add_apply,LinearMap.neg_apply,multiply_apply]

private theorem real_smul_fiber (c : ℝ) (v : FockFiber) : c • v=(c:ℂ) • v := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem row_connection_core (b : Fin 3) :
    rowForm SourceCoframeCovariantAction.connectionAction b=(-1/2:ℂ) • J b := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · rw [row_sum]
    simp only [LinearMap.sum_apply,Module.End.mul_apply,rowCoefficient]
    change (∑ i : Fin 6,(currentRows z.1 i b:ℂ) • connectionFiber i z (f z))=(-1/2:ℂ) • rotation b (f z)
    simp only [←real_smul_fiber,connectionFiber,sum_apply,smul_apply,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    simp only [←Finset.sum_smul]
    simp_rw [row_connection ⟨z,hz⟩ b]
    norm_num [real_smul_fiber]
  · have h0 (p : QuantumTest) : p z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (p.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- The complete original connection contraction is the fixed half rotation, including every beta coefficient. -/
theorem original_bare_covariant_row (b : Fin 3) : bareRow b=covariantRow b+(1/2:ℂ) • J b := by
  have h : covariantRow b=bareRow b+rowForm SourceCoframeCovariantAction.connectionAction b := by
    fin_cases b
    · change coordinateAction 1*(GaussCoframeCore.momentum 3+SourceCoframeCovariantAction.connectionAction 3)+
        coordinateAction 2*(GaussCoframeCore.momentum 4+SourceCoframeCovariantAction.connectionAction 4)=_
      change _=coordinateAction 1*GaussCoframeCore.momentum 3+coordinateAction 2*GaussCoframeCore.momentum 4+
        (coordinateAction 1*SourceCoframeCovariantAction.connectionAction 3+coordinateAction 2*SourceCoframeCovariantAction.connectionAction 4)
      noncomm_ring
    · change -(coordinateAction 0*(GaussCoframeCore.momentum 3+SourceCoframeCovariantAction.connectionAction 3))=
        -(coordinateAction 0*GaussCoframeCore.momentum 3)+ -(coordinateAction 0*SourceCoframeCovariantAction.connectionAction 3)
      noncomm_ring
    · change coordinateAction 0*(GaussCoframeCore.momentum 1+SourceCoframeCovariantAction.connectionAction 1)=
        coordinateAction 0*GaussCoframeCore.momentum 1+coordinateAction 0*SourceCoframeCovariantAction.connectionAction 1
      noncomm_ring
  rw [h,row_connection_core]
  module

private def extraRow (a : Fin 3) : End :=
  ![coordinateAction 0*SourceCoframeCovariantAction.covariantMomentum 1,
    coordinateAction 0*SourceCoframeCovariantAction.covariantMomentum 3,
    coordinateAction 1*SourceCoframeCovariantAction.covariantMomentum 3+
      coordinateAction 2*SourceCoframeCovariantAction.covariantMomentum 4] a

private theorem covariant_norm_sum (f : QuantumTest) :
    (∑ b : Fin 3,‖embed (covariantRow b f)‖^2)=(∑ a : Fin 3,‖embed (extraRow a f)‖^2) := by
  simp [Fin.sum_univ_succ,covariantRow,rowForm,extraRow,map_neg,LinearMap.neg_apply,norm_neg]
  ring

private theorem covariant_price (f : QuantumTest) : 4*(∑ b : Fin 3,‖embed (covariantRow b f)‖^2)≤coframeGram f := by
  have h := original_coframe_centered_block_square f
  change coframeGram f=2*(∑ b : Fin 3,‖embed (centeredBlock b f)‖^2)+
    (1/2:ℝ)*(∑ b : Fin 3,‖embed (blockDensity b f)‖^2)+4*(∑ a : Fin 3,‖embed (extraRow a f)‖^2) at h
  rw [←covariant_norm_sum] at h
  have h1 : 0≤∑ b : Fin 3,‖embed (centeredBlock b f)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0≤∑ b : Fin 3,‖embed (blockDensity b f)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith only [h,h1,h2]

private theorem current_norm (b : Fin 3) (f : QuantumTest) :
    ‖embed (J b f)‖≤‖quantized (GaussCoframeSpin.full ⟨3+b.val,by omega⟩)‖*‖embed f‖ :=
  GaussBoundedMultiplier.action_bound (fun _ => quantized (GaussCoframeSpin.full ⟨3+b.val,by omega⟩))
    (fun _ => contDiffAt_const) (fun _ w => weight_commute w _)
      ‖quantized (GaussCoframeSpin.full ⟨3+b.val,by omega⟩)‖ (norm_nonneg _)
      (fun _ v => ContinuousLinearMap.le_opNorm _ v) f

def rotationPrice : ℝ := 1/2+(∑ b : Fin 3,‖quantized (GaussCoframeSpin.full ⟨3+b.val,by omega⟩)‖^2)/50

/-- The actual six-row clock Gram and its source25 floor pay the bare rotational rows. -/
theorem original_bare_row_coframe_price (f : QuantumTest) :
    (∑ b : Fin 3,‖embed (bareRow b f)‖^2)≤rotationPrice*coframeGram f := by
  have hrow (b : Fin 3) : ‖embed (bareRow b f)‖^2≤2*‖embed (covariantRow b f)‖^2+(1/2:ℝ)*‖embed (J b f)‖^2 := by
    rw [original_bare_covariant_row]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
    have hn := norm_add_le (embed (covariantRow b f)) ((1/2:ℂ) • embed (J b f))
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
    simp only [norm_smul] at hp
    norm_num at hp
    nlinarith only [hp,sq_nonneg (‖embed (covariantRow b f)‖-‖embed (J b f)‖/2)]
  have hs := Finset.sum_le_sum (fun b (_ : b∈(Finset.univ:Finset (Fin 3))) => hrow b)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have hj : (∑ b : Fin 3,‖embed (J b f)‖^2)≤
      (∑ b : Fin 3,‖quantized (GaussCoframeSpin.full ⟨3+b.val,by omega⟩)‖^2)*‖embed f‖^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    have hn := pow_le_pow_left₀ (norm_nonneg _) (current_norm b f) 2
    simpa only [mul_pow] using hn
  have hf := SourceClockSourceTail.original_inverse_coframe_floor f
  have hc := covariant_price f
  have hK : 0≤∑ b : Fin 3,‖quantized (GaussCoframeSpin.full ⟨3+b.val,by omega⟩)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpay := mul_le_mul_of_nonneg_left hf hK
  unfold rotationPrice
  nlinarith only [hs,hj,hc,hpay]

private theorem density_off (N : ℕ) (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.complexDensity N) z.val (GaussCoframeCore.coframeDirection i)=0 := by
  have hd := ((GaussDensityCore.complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => z.val+r • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const (GaussCoframeCore.coframeDirection i) |>.const_add z.val
  have hh := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  have he : (fun r : ℝ => GaussDensityCore.complexDensity N (z.val+r • GaussCoframeCore.coframeDirection i))=
      (fun _ : ℝ => GaussDensityCore.complexDensity N z.val) := by
    funext r
    rcases hi with rfl | rfl | rfl <;>
      simp [GaussDensityCore.complexDensity,GaussDensityCore.density,GaussCoframeCore.coframeDirection,
        PiLp.add_apply,PiLp.smul_apply]
  change HasDerivAt (fun r : ℝ => GaussDensityCore.complexDensity N (z.val+r • GaussCoframeCore.coframeDirection i))
    (fderiv ℝ (GaussDensityCore.complexDensity N) z.val (GaussCoframeCore.coframeDirection i)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

private theorem scalar_transpose (N : ℕ) (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) (f : GaussDensityCore.ScalarTest) :
    GaussDensityCore.weightedTranspose N (GaussCoframeCore.coframeDirection i) f=
      -GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · rw [GaussDensityCore.weightedTranspose_apply N _ _ ⟨z,hz⟩,
      fderiv_fun_mul ((GaussDensityCore.complexDensity_smooth N ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [density_off N i hi ⟨z,hz⟩]
    have hn : GaussDensityCore.complexDensity N z≠0 := by
      change (GaussDensityCore.density N z:ℂ)≠0
      exact_mod_cast (GaussDensityCore.density_pos N ⟨z,hz⟩).ne'
    change -(GaussDensityCore.complexDensity N z)⁻¹*
      (GaussDensityCore.complexDensity N z*fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+f z*0)=
      -GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) f z
    rw [GaussDensityCore.derivative_apply]
    simp only [mul_zero,add_zero]
    field_simp [hn]
  · have hl : GaussDensityCore.weightedTranspose N (GaussCoframeCore.coframeDirection i) f z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((GaussDensityCore.weightedTranspose N (GaussCoframeCore.coframeDirection i) f).tsupport_subset h))
    have hr : (-GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((-GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) f).tsupport_subset h))
    exact hl.trans hr.symm

private theorem transpose_off (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) (f : QuantumTest) :
    GaussCoframeCore.transpose (GaussCoframeCore.coframeDirection i) f=
      -GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f := by
  apply embed_injective
  rw [GaussCoframeCore.transpose_embed,map_neg]
  apply PiLp.ext
  intro word
  change GaussScalarTransport.scalarEmbed word.card
    (GaussDensityCore.weightedTranspose word.card (GaussCoframeCore.coframeDirection i) (component word f))=
    -(embed (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f) word)
  rw [scalar_transpose _ i hi,map_neg]
  change -(GaussScalarTransport.scalarEmbed word.card (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) (component word f)))=
    -(GaussScalarTransport.scalarEmbed word.card (component word (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f)))
  rw [GaussCoframeCore.component_derivative]

private theorem adjoint_off (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) :
    GaussCoframeCore.adjoint i=GaussCoframeCore.momentum i := by
  apply LinearMap.ext
  intro f
  change Complex.I • GaussCoframeCore.transpose (GaussCoframeCore.coframeDirection i) f=
    (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f
  rw [transpose_off i hi,smul_neg,neg_smul]

private theorem coordinate_momentum (i j : Fin 6) (hij : i≠j) :
    Commute (GaussCoframeCore.momentum i) (coordinateAction j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let C := Complex.ofRealCLM.comp (SourceCoframeVolume.coordinate j)
  have hc : HasFDerivAt (fun w : SourceCoordinateSlice => (w.1 j:ℂ)) C z := C.hasFDerivAt
  have hf : (coordinateAction j f : SourceCoordinateSlice → FockFiber)=fun w => (w.1 j:ℂ) • f w := rfl
  change (-Complex.I) • fderiv ℝ (coordinateAction j f) z (GaussCoframeCore.coframeDirection i)=
    (z.1 j:ℂ) • ((-Complex.I) • fderiv ℝ f z (GaussCoframeCore.coframeDirection i))
  rw [hf,fderiv_fun_smul hc.differentiableAt (f.contDiff.differentiable (by simp)).differentiableAt]
  have hz : C (GaussCoframeCore.coframeDirection i)=0 := by
    simp [C,SourceCoframeVolume.coordinate,GaussCoframeCore.coframeDirection,Ne.symm hij]
  rw [hc.fderiv]
  change (-Complex.I) • ((z.1 j:ℂ) • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    C (GaussCoframeCore.coframeDirection i) • f z)=_
  rw [hz,zero_smul,add_zero]
  exact smul_comm (-Complex.I) (z.1 j:ℂ) _

private theorem coordinate_pair (i j : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) (hij : i≠j) (p q : QuantumTest) :
    sourcePair p ((coordinateAction j*GaussCoframeCore.momentum i) q)=
      sourcePair ((coordinateAction j*GaussCoframeCore.momentum i) p) q := by
  change sourcePair p (coordinateAction j (GaussCoframeCore.momentum i q))=
    sourcePair (coordinateAction j (GaussCoframeCore.momentum i p)) q
  have hQ (x y : QuantumTest) : sourcePair x (coordinateAction j y)=sourcePair (coordinateAction j x) y := by
    unfold coordinateAction
    exact GaussNativeForm.multiply_pair _ _ x y
  rw [hQ,GaussCoframeCore.momentum_pair,adjoint_off i hi]
  have hc := LinearMap.congr_fun (coordinate_momentum i j hij).eq p
  exact congrArg (fun f => sourcePair f q) hc

/-- The off-diagonal source density itself makes these three bare rows formally self-adjoint. -/
theorem original_bare_row_pair (b : Fin 3) (p q : QuantumTest) : sourcePair p (bareRow b q)=sourcePair (bareRow b p) q := by
  fin_cases b
  · change sourcePair p ((coordinateAction 1*GaussCoframeCore.momentum 3+coordinateAction 2*GaussCoframeCore.momentum 4) q)=
      sourcePair ((coordinateAction 1*GaussCoframeCore.momentum 3+coordinateAction 2*GaussCoframeCore.momentum 4) p) q
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,inner_add_left]
    exact congrArg₂ (·+·) (coordinate_pair 3 1 (Or.inr (Or.inl rfl)) (by decide) p q)
      (coordinate_pair 4 2 (Or.inr (Or.inr rfl)) (by decide) p q)
  · change sourcePair p ((-(coordinateAction 0*GaussCoframeCore.momentum 3)) q)=
      sourcePair ((-(coordinateAction 0*GaussCoframeCore.momentum 3)) p) q
    simp only [LinearMap.neg_apply,sourcePair,map_neg,inner_neg_right,inner_neg_left]
    exact congrArg Neg.neg (coordinate_pair 3 0 (Or.inr (Or.inl rfl)) (by decide) p q)
  · exact coordinate_pair 1 0 (Or.inl rfl) (by decide) p q

private theorem coordinate_inverse (j : Fin 6) : Commute (coordinateAction j) inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (z.1 j:ℂ) (reciprocalVolume z:ℂ) (f z)
private theorem zero_gradient (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) : gradientAction i=0 := by
  rcases hi with rfl | rfl | rfl <;>
    apply LinearMap.ext <;> intro f <;> apply DFunLike.ext <;> intro z <;>
    change (volumeGradient z _:ℂ) • f z=0 <;> simp [volumeGradient]
private theorem momentum_inverse (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) :
    Commute (GaussCoframeCore.momentum i) inverseVolumeAction := by
  have hp : Commute (GaussCoframeCore.momentum i) volumeAction := by
    apply LinearMap.ext
    intro f
    simpa only [zero_gradient i hi,LinearMap.zero_apply,smul_zero,add_zero] using!
      SourceCoframeVolume.momentum_volume i f
  have hv : (volumeAction:End)*inverseVolumeAction=1 := by apply LinearMap.ext;intro f;exact volume_inverse f
  have hu : inverseVolumeAction*(volumeAction:End)=1 := by
    have hc : Commute inverseVolumeAction (volumeAction:End) := by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (reciprocalVolume z:ℂ) (volume z:ℂ) (f z)
    rw [hc.eq]
    exact hv
  calc
    _=inverseVolumeAction*(volumeAction*GaussCoframeCore.momentum i)*inverseVolumeAction := by
      rw [←mul_assoc inverseVolumeAction volumeAction,hu,one_mul]
    _=inverseVolumeAction*(GaussCoframeCore.momentum i*volumeAction)*inverseVolumeAction := by rw [hp.eq.symm]
    _=_ := by rw [mul_assoc,mul_assoc,hv,mul_one]

/-- The three off-diagonal rows commute with the actual inverse-volume coefficient. -/
theorem original_bare_row_inverse (b : Fin 3) : Commute (bareRow b) inverseVolumeAction := by
  fin_cases b
  · exact ((coordinate_inverse 1).mul_left (momentum_inverse 3 (Or.inr (Or.inl rfl)))).add_left
      ((coordinate_inverse 2).mul_left (momentum_inverse 4 (Or.inr (Or.inr rfl))))
  · exact ((coordinate_inverse 0).mul_left (momentum_inverse 3 (Or.inr (Or.inl rfl)))).neg_left
  · exact (coordinate_inverse 0).mul_left (momentum_inverse 1 (Or.inl rfl))

private theorem spin_real (j : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (GaussCoframeSpin.current j) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussCoframeSpin.full j)) (c z:ℂ) (f z)
private theorem spin_momentum (j : Fin 7) (i : Fin 6) : Commute (GaussCoframeSpin.current j) (GaussCoframeCore.momentum i) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let T := (quantized (GaussCoframeSpin.full j)).restrictScalars ℝ
  have hf : (GaussCoframeSpin.current j f : SourceCoordinateSlice → FockFiber)=T ∘ f := rfl
  have hd := T.hasFDerivAt.comp z (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change quantized (GaussCoframeSpin.full j) ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)=
    (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (GaussCoframeSpin.current j f) z
  rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,hf,hd.fderiv,map_smul]
  rfl

private theorem current_factor (j : Fin 6) : multiply (GaussCoframeForm.currentCoefficient j)
    (GaussCoframeForm.currentCoefficient_smooth j)=(sourceTime 0:ℂ) • (inverseVolumeAction*coordinateAction j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (GaussCoframeForm.currentCoefficient j z:ℂ) • f z=
    (sourceTime 0:ℂ) • ((reciprocalVolume z:ℂ) • ((z.1 j:ℂ) • f z))
  simp only [smul_smul]
  congr 1
  unfold GaussCoframeForm.currentCoefficient GaussCoframeForm.inverseVolume reciprocalVolume
  push_cast
  ring
private theorem negative_factor : multiply (fun z => -GaussCoframeForm.currentCoefficient 0 z)
    (fun z => (GaussCoframeForm.currentCoefficient_smooth 0 z).neg)=
      -(multiply (GaussCoframeForm.currentCoefficient 0) (GaussCoframeForm.currentCoefficient_smooth 0)) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((-GaussCoframeForm.currentCoefficient 0 z:ℝ):ℂ) • f z=
    -((GaussCoframeForm.currentCoefficient 0 z:ℂ) • f z)
  rw [Complex.ofReal_neg,neg_smul]

private theorem mixed_return (i : Fin 6) (j : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : i=1 ∨ i=3 ∨ i=4)
    (hP : Commute (GaussCoframeCore.momentum i) (multiply c hc)) :
    GaussCoframeForm.mixed i j c hc=GaussCoframeSpin.current j*multiply c hc*GaussCoframeCore.momentum i := by
  unfold GaussCoframeForm.mixed
  change (1/2:ℂ) • (GaussCoframeSpin.current j*(multiply c hc*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply c hc*GaussCoframeSpin.current j))=_
  rw [adjoint_off i hi]
  have h : GaussCoframeCore.momentum i*(multiply c hc*GaussCoframeSpin.current j)=
      GaussCoframeSpin.current j*(multiply c hc*GaussCoframeCore.momentum i) := by
    calc
      _=(GaussCoframeCore.momentum i*multiply c hc)*GaussCoframeSpin.current j := by rw [mul_assoc]
      _=(multiply c hc*GaussCoframeCore.momentum i)*GaussCoframeSpin.current j := by rw [hP.eq]
      _=multiply c hc*(GaussCoframeSpin.current j*GaussCoframeCore.momentum i) := by rw [mul_assoc,(spin_momentum j i).eq.symm]
      _=_ := by rw [←mul_assoc,(spin_real j c hc).eq.symm,mul_assoc]
  rw [h]
  module

private theorem momentum_current (i j : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) (hij : i≠j) :
    Commute (GaussCoframeCore.momentum i) (multiply (GaussCoframeForm.currentCoefficient j)
      (GaussCoframeForm.currentCoefficient_smooth j)) := by
  rw [current_factor]
  exact ((momentum_inverse i hi).mul_right (coordinate_momentum i j hij)).smul_right _

/-- The four literal mixed currents are the original three rotational rows, with their exact volume and lapse. -/
theorem original_mixed_current_source : GaussCoframeForm.currentAction=
    (sourceTime 0:ℂ) • (inverseVolumeAction*∑ b : Fin 3,J b*bareRow b) := by
  unfold GaussCoframeForm.currentAction
  rw [mixed_return 1 5 _ _ (Or.inl rfl) (momentum_current 1 0 (Or.inl rfl) (by decide)),
    mixed_return 3 3 _ _ (Or.inr (Or.inl rfl)) (momentum_current 3 1 (Or.inr (Or.inl rfl)) (by decide)),
    mixed_return 3 4 _ _ (Or.inr (Or.inl rfl)),
    mixed_return 4 3 _ _ (Or.inr (Or.inr rfl)) (momentum_current 4 2 (Or.inr (Or.inr rfl)) (by decide))]
  · rw [negative_factor]
    simp only [current_factor,mul_smul_comm,smul_mul_assoc,mul_neg,neg_mul]
    simp [Fin.sum_univ_three,bareRow,rowForm,J]
    simp only [←smul_neg,←smul_add]
    congr 1
    have hu (b : Fin 3) : Commute (J b) inverseVolumeAction := spin_real _ _ _
    have hu3 : GaussCoframeSpin.current 3*inverseVolumeAction=inverseVolumeAction*GaussCoframeSpin.current 3 := (hu 0).eq
    have hu4 : GaussCoframeSpin.current 4*inverseVolumeAction=inverseVolumeAction*GaussCoframeSpin.current 4 := (hu 1).eq
    have hu5 : GaussCoframeSpin.current 5*inverseVolumeAction=inverseVolumeAction*GaussCoframeSpin.current 5 := (hu 2).eq
    linear_combination (norm := noncomm_ring)
      hu3*coordinateAction 1*GaussCoframeCore.momentum 3+
      hu3*coordinateAction 2*GaussCoframeCore.momentum 4-
      hu4*coordinateAction 0*GaussCoframeCore.momentum 3+
      hu5*coordinateAction 0*GaussCoframeCore.momentum 1
  · rw [negative_factor]
    exact (momentum_current 3 0 (Or.inr (Or.inl rfl)) (by decide)).neg_right

end LowEnergy.SourceClockYukawaCoframeRotationRows
