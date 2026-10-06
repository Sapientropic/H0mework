import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralSpinCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaSpinRelativeForm
open SourceNativeMomentumCurvature SourceScalarDoubleCurrent GaussYukawaCoefficient
open GaussNativePotential
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent
open GaussFockWeights GaussQuantumMultiplier SourcePhysicalKineticSquare SourceClockReflectedForm SourceCoframeBlockHardy
open scoped ContDiff InnerProductSpace BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
attribute [local irreducible] fullAction

private def inverseNumber : FiberEnd := weight (fun n => (n:ℂ)⁻¹)
private def relativeSpin (j : Fin 4) : FiberEnd := quantized (GaussCoframeSpin.full (activeIndex j))*inverseNumber

def spinNumberPrice (j : Fin 4) : ℝ := ‖relativeSpin j‖

private theorem vacuum_zero (A : Matrix Mode Mode ℂ) :
    quantized A (EuclideanSpace.single ∅ 1)=0 := by
  apply fiberCoordinates.injective
  have hv : fiberCoordinates (EuclideanSpace.single (∅:Occupation) (1:ℂ))=
      SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion.vacuum := by
    funext word
    simp [fiberCoordinates,EuclideanSpace.single,
      SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion.vacuum,
      SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion.occupationBasis]
  change SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize A
    (fiberCoordinates (EuclideanSpace.single (∅:Occupation) (1:ℂ)))=fiberCoordinates 0
  rw [hv,map_zero]
  simp only [SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,
    SaturationMonoid.PhysicsCore.LowEnergy.Fermion.annihilation_apply,
    SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion.annihilate_vacuum,
    map_zero,smul_zero,Finset.sum_const_zero]

private theorem inverse_number_return (A : Matrix Mode Mode ℂ) (psi : FockFiber) :
    quantized A (inverseNumber (fiberNumber psi))=quantized A psi := by
  have expansion : psi=∑ word : Occupation,psi word • EuclideanSpace.single word 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum,Finset.sum_apply,EuclideanSpace.single,Pi.single_apply]
  have hb (word : Occupation) : fiberNumber (EuclideanSpace.single word 1)=
      (word.card:ℂ) • EuclideanSpace.single word 1 := by
    apply PiLp.ext
    intro out
    rw [fiberNumber_apply]
    by_cases h : out=word
    · subst out;simp
    · simp [EuclideanSpace.single,h]
  change quantized A ((weight (fun n => (n:ℂ)⁻¹)) (fiberNumber psi))=_
  rw [expansion]
  simp only [map_sum,map_smul,hb,smul_smul]
  apply Finset.sum_congr rfl
  intro word _
  by_cases h : word.card=0
  · have he : word=∅ := Finset.card_eq_zero.mp h
    subst word
    rw [vacuum_zero]
    simp
  · have hn : (word.card:ℂ)≠0 := by exact_mod_cast h
    have hw : (GaussFockWeights.weight (fun n => (n:ℂ)⁻¹)) (EuclideanSpace.single word (1:ℂ))=
        (word.card:ℂ)⁻¹ • (EuclideanSpace.single word (1:ℂ)) := by
      apply PiLp.ext
      intro out
      rw [GaussFockWeights.weight_apply]
      by_cases he : out=word
      · subst out;simp
      · simp [EuclideanSpace.single,he]
    rw [hw,map_smul,smul_smul]
    have hc : (psi word*(word.card:ℂ))*(word.card:ℂ)⁻¹=psi word := by field_simp
    rw [hc]

private theorem relative_commute (j : Fin 4) (w : ℕ → ℂ) : Commute (weight w) (relativeSpin j) := by
  have hw : Commute (weight w) inverseNumber := by
    apply ContinuousLinearMap.ext
    intro f
    apply PiLp.ext
    intro word
    change w word.card*((word.card:ℂ)⁻¹*f word)=(word.card:ℂ)⁻¹*(w word.card*f word)
    ring
  exact (weight_commute w _).mul_right hw

/-- Every occupation sector pays the actual active spin by one original Number action. -/
theorem original_active_spin_number_form (j : Fin 4) (f : QuantumTest) :
    ‖embed (activeSpin j f)‖ ≤ spinNumberPrice j*‖embed (GaussCoframeForm.number f)‖ := by
  have h := GaussBoundedMultiplier.action_bound (fun _ => relativeSpin j) (fun _ => contDiffAt_const)
    (fun _ w => relative_commute j w) (spinNumberPrice j) (norm_nonneg _)
    (fun _ psi => (relativeSpin j).le_opNorm psi) (GaussCoframeForm.number f)
  have he : activeSpin j f=localMultiplier (fun _ => relativeSpin j) (fun _ => contDiffAt_const) (GaussCoframeForm.number f) := by
    apply DFunLike.ext
    intro z
    change quantized (GaussCoframeSpin.full (activeIndex j)) (f z)=
      relativeSpin j (GaussCoframeForm.number f z)
    have hn : GaussCoframeForm.number f z=fiberNumber (f z) := by
      apply PiLp.ext
      intro word
      exact (GaussCoframeForm.number_apply f z word).trans (fiberNumber_apply (f z) word).symm
    rw [hn]
    exact (inverse_number_return _ _).symm
  rw [←he] at h
  exact h

/-- The actual chirality partner is retained together with all three boost partners. -/
def spinCoefficient (sharp : Bool) (mu : Fin 8) : End :=
  if h0 : mu.val=0 then fullAction sharp else
  if h1 : mu.val<5 then spinVariation sharp ⟨mu.val-1,by omega⟩ else
    bracket (activeSpin ⟨mu.val-5,by omega⟩) (spinVariation sharp 3)

def spinVariationGram (sharp : Bool) (q : QuantumTest) : ℝ :=
  ∑ mu : Fin 8,‖embed (spinCoefficient sharp mu q)‖^2

private theorem reordered_current (sharp : Bool) : reducedSpinCurrent sharp=(3/2:ℂ) •
    (spinVolume*(activeSpin 3*spinVariation sharp 3-activeSpin 0*spinVariation sharp 0-
      activeSpin 1*spinVariation sharp 1-activeSpin 2*spinVariation sharp 2+fullAction sharp)) := by
  have h (j : Fin 4) : bracket (activeSpin j) (spinVariation sharp j)=fullAction sharp := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    have hf (q : QuantumTest) : fullAction sharp q z=branchMap sharp (scalarField z) (q z) := by
      unfold SourceMixedNativeReturn.fullAction
      cases sharp <;> rfl
    have hs (q : QuantumTest) : activeSpin j q z=quantized (GaussCoframeSpin.full (activeIndex j)) (q z) := rfl
    have h := congrArg (fun A : FiberEnd => A (f z)) (original_active_spin_ladder j sharp (scalarField z))
    simpa only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,
      hs,hf,map_sub,mul_apply_eq_comp] using h
  unfold reducedSpinCurrent
  congr 2
  simp only [bracket] at h
  linear_combination (norm := noncomm_ring) h 0+h 1+h 2-h 3


private def spinSign (j : Fin 4) : ℂ := if j.val<3 then -1 else 1
private theorem sign_norm (j : Fin 4) : ‖spinSign j‖=1 := by fin_cases j <;> norm_num [spinSign]

private theorem spin_inverse_pair (p q : QuantumTest) :
    sourcePair p (spinVolume q)=(sourceTime 0:ℂ)*sourcePair (inverseVolumeAction p) q := by
  have h : spinVolume q=(sourceTime 0:ℂ) • inverseVolumeAction q := by
    apply DFunLike.ext
    intro z
    change (GaussCoframeForm.inverseVolume z:ℂ) • q z=(sourceTime 0:ℂ) • ((reciprocalVolume z:ℂ) • q z)
    simp only [GaussCoframeForm.inverseVolume,reciprocalVolume,div_eq_mul_inv,
      Complex.ofReal_mul,Complex.ofReal_inv,mul_smul]
  rw [h]
  change inner ℂ (embed p) (embed ((sourceTime 0:ℂ) • inverseVolumeAction q))=_
  rw [map_smul,inner_smul_right]
  congr 1
  exact multiply_pair _ _ p q
private theorem pair_smul (p q : QuantumTest) (c : ℂ) : sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_add (p q r : QuantumTest) : sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sum (p : QuantumTest) (f : Fin 4 → QuantumTest) :
    sourcePair p (∑ j,f j)=∑ j,sourcePair p (f j) := by simp only [sourcePair,map_sum,inner_sum]
private theorem active_pair (j : Fin 4) (p q : QuantumTest) : sourcePair p (activeSpin j q)=sourcePair (activeSpin j p) q :=
  GaussCoframeSpin.current_pair (activeIndex j) p q

private theorem current_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (spinCurrent sharp q)=(3/2:ℂ)*(sourceTime 0:ℂ)*
      ((∑ j : Fin 4,spinSign j*sourcePair (activeSpin j (inverseVolumeAction p)) (spinVariation sharp j q))+
        sourcePair (inverseVolumeAction p) (fullAction sharp q)) := by
  have hs : activeSpin 3*spinVariation sharp 3-activeSpin 0*spinVariation sharp 0-
      activeSpin 1*spinVariation sharp 1-activeSpin 2*spinVariation sharp 2+fullAction sharp=
      (∑ j : Fin 4,spinSign j • (activeSpin j*spinVariation sharp j))+fullAction sharp := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,spinSign,Fin.val_zero,Fin.val_succ]
    norm_num
    have he : (Fin.succ (2:Fin 3):Fin 4)=3 := by decide
    rw [he]
    abel
  rw [original_spin_ladder_return,reordered_current,hs]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,pair_smul,spin_inverse_pair,
    LinearMap.add_apply,LinearMap.sum_apply,pair_add,pair_sum,active_pair]
  ring

private theorem current_norm (sharp : Bool) (p q : QuantumTest) :
    ‖sourcePair p (spinCurrent sharp q)‖ ≤ (3/2:ℝ)*sourceTime 0*
      ((∑ j : Fin 4,spinNumberPrice j*‖embed (GaussCoframeForm.number (inverseVolumeAction p))‖*
        ‖embed (spinVariation sharp j q)‖)+‖embed (inverseVolumeAction p)‖*‖embed (fullAction sharp q)‖) := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  rw [current_pair,norm_mul,norm_mul]
  have hc : ‖(3/2:ℂ)‖=(3/2:ℝ) := by norm_num
  rw [hc,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb (j : Fin 4) : ‖spinSign j*sourcePair (activeSpin j (inverseVolumeAction p)) (spinVariation sharp j q)‖ ≤
      spinNumberPrice j*‖embed (GaussCoframeForm.number (inverseVolumeAction p))‖*‖embed (spinVariation sharp j q)‖ := by
    rw [norm_mul,sign_norm,one_mul]
    exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_mul_of_nonneg_right (original_active_spin_number_form j _) (norm_nonneg _))
  exact (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hb j)))
    (norm_inner_le_norm (𝕜 := ℂ) _ _))

private theorem number_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (GaussCoframeForm.number f)).re := by
  rw [sourcePair_integral]
  change 0 ≤ RCLike.re (∫ z,densityPair f (GaussCoframeForm.number f) z ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable f (GaussCoframeForm.number f))]
  apply MeasureTheory.integral_nonneg
  intro z
  change 0 ≤ (densityPair f (GaussCoframeForm.number f) z).re
  by_cases hz : z∈physicalChart
  · rw [densityPair_sum]
    simp only [Complex.re_sum,GaussCoframeForm.number_apply]
    apply Finset.sum_nonneg
    intro word _
    have hd := (GaussDensityCore.density_pos word.card ⟨z,hz⟩).le
    have he : (GaussDensityCore.complexDensity word.card z*star (f z word)*((word.card:ℂ)*f z word)).re=
        GaussDensityCore.density word.card z*(word.card:ℝ)*‖f z word‖^2 := by
      rw [GaussDensityCore.complexDensity]
      have hh : (star (f z word))*(f z word)=((‖f z word‖^2:ℝ):ℂ) := by
        simpa only [RCLike.inner_apply,mul_comm,starRingEnd_apply,Complex.ofReal_pow] using!
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f z word)
      calc
        _=(((GaussDensityCore.density word.card z:ℂ)*(word.card:ℂ))*(star (f z word)*f z word)).re := by congr 1;ring
        _=_ := by
          rw [hh]
          norm_cast
          rw [←Complex.ofReal_mul,Complex.ofReal_re]
    rw [he]
    positivity
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem number_floor (f : QuantumTest) :
    (3/2:ℝ)*‖embed (GaussCoframeForm.number f)‖^2+25*‖embed f‖^2 ≤ coframeGram f := by
  have h := original_coframe_three_block_hardy f
  have hc : 0 ≤ ∑ b : Fin 3,‖embed (centeredBlock b f)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn := number_nonnegative f
  nlinarith only [h,hc,hn]

/-- Original Y and the complete boost/chirality responses retain their full CAR positive squares. -/
def spinRelativePrice (sharp : Bool) (q : QuantumTest) : ℝ :=
  (9/400:ℝ)*‖embed (fullAction sharp q)‖^2+
    (3/2:ℝ)*(∑ j : Fin 4,(spinNumberPrice j)^2*‖embed (spinVariation sharp j q)‖^2)+
    ∑ j : Fin 3,‖embed (bracket (activeSpin ⟨j.val,by omega⟩) (spinVariation sharp 3) q)‖^2

private theorem young (a b t : ℝ) (ht : 0<t) : a*b ≤ t*a^2+b^2/(4*t) := by
  have he : (4*t)*(b^2/(4*t))=b^2 := by field_simp
  nlinarith [sq_nonneg (2*t*a-b)]

/-- The same source coframe Number slot pays the entire signed spin current.
The positive right word remains an actual eight-coefficient CAR obligation. -/
theorem original_spin_relative_coframe_price (sharp : Bool) (p q : QuantumTest) (δ : ℝ) (hδ : 0<δ) :
    ‖sourcePair p (spinCurrent sharp q)‖ ≤ δ*(sourceTime 0)^2*coframeGram (inverseVolumeAction p)+
      spinRelativePrice sharp q/δ := by
  let n := sourceTime 0
  let x := ‖embed (GaussCoframeForm.number (inverseVolumeAction p))‖
  let y := ‖embed (inverseVolumeAction p)‖
  let b (j : Fin 4) := ‖embed (spinVariation sharp j q)‖
  let c := ‖embed (fullAction sharp q)‖
  have hrow (j : Fin 4) : (3/2:ℝ)*n*spinNumberPrice j*x*b j ≤
      δ*n^2*(3/8:ℝ)*x^2+((3/2:ℝ)*(spinNumberPrice j)^2*b j^2)/δ := by
    have h := young (n*x) ((3/2:ℝ)*spinNumberPrice j*b j) (3*δ/8) (by positivity)
    have he : ((3/2:ℝ)*spinNumberPrice j*b j)^2/(4*(3*δ/8))=
        ((3/2:ℝ)*(spinNumberPrice j)^2*b j^2)/δ := by field_simp;ring
    rw [he] at h
    nlinarith only [h]
  have hy : (3/2:ℝ)*n*y*c ≤ δ*n^2*25*y^2+((9/400:ℝ)*c^2)/δ := by
    have h := young (n*y) ((3/2:ℝ)*c) (25*δ) (by positivity)
    have he : ((3/2:ℝ)*c)^2/(4*(25*δ))=((9/400:ℝ)*c^2)/δ := by field_simp;ring
    rw [he] at h
    nlinarith only [h]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hrow j)
  have hc : ∑ j : Fin 4,δ*n^2*(3/8:ℝ)*x^2=δ*n^2*(3/2:ℝ)*x^2 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hf := mul_le_mul_of_nonneg_left (number_floor (inverseVolumeAction p))
    (show 0 ≤ δ*n^2 by positivity)
  change δ*n^2*((3/2:ℝ)*x^2+25*y^2) ≤ _ at hf
  have he : 0 ≤ ∑ j : Fin 3,‖embed (bracket (activeSpin ⟨j.val,by omega⟩) (spinVariation sharp 3) q)‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [Finset.sum_add_distrib,hc,←Finset.sum_div] at hsum
  have hb := current_norm sharp p q
  change ‖sourcePair p (spinCurrent sharp q)‖ ≤ (3/2:ℝ)*n*((∑ j : Fin 4,spinNumberPrice j*x*b j)+y*c) at hb
  have hd : (3/2:ℝ)*n*(∑ j : Fin 4,spinNumberPrice j*x*b j)=
      ∑ j : Fin 4,(3/2:ℝ)*n*spinNumberPrice j*x*b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp : (3/2:ℝ)*(∑ j : Fin 4,(spinNumberPrice j)^2*b j^2)=
      ∑ j : Fin 4,(3/2:ℝ)*(spinNumberPrice j)^2*b j^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change ‖sourcePair p (spinCurrent sharp q)‖ ≤ δ*n^2*coframeGram (inverseVolumeAction p)+_
  unfold spinRelativePrice
  change ‖sourcePair p (spinCurrent sharp q)‖ ≤ δ*n^2*coframeGram (inverseVolumeAction p)+
    ((9/400:ℝ)*c^2+(3/2:ℝ)*(∑ j : Fin 4,(spinNumberPrice j)^2*b j^2)+_)/δ
  rw [←hp] at hsum
  have hδpay : 0 ≤ (∑ j : Fin 3,‖embed (bracket (activeSpin ⟨j.val,by omega⟩) (spinVariation sharp 3) q)‖^2)/δ :=
    div_nonneg he hδ.le
  rw [mul_add,hd] at hb
  rw [add_div,add_div]
  nlinarith only [hb,hsum,hy,hf,hδpay]

end LowEnergy.SourceClockYukawaSpinRelativeForm
