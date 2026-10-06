import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceContactCoframeJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceContactMixedFlux
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceMatterContactNative SourceMatterContactCoframe SourceContactCoframeJet GaussMatterCore
open GaussCoframeCore GaussCoframeForm
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def spinContact (a : Fin 7) : End := GaussCoframeSpin.current a*gramAction-gramAction*GaussCoframeSpin.current a

/-- The spin contact is the original finite CAR commutator, with no derivatives of the state. -/
theorem original_spin_contact_value (a : Fin 7) (f : QuantumTest) (z : SourceCoordinateSlice) :
    spinContact a f z=(GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)*gramFiber z-
      gramFiber z*GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)) (f z) := by
  change (GaussCoframeSpin.current a (gramAction f)) z-(gramAction (GaussCoframeSpin.current a f)) z=_
  rw [original_contact_gram_value]
  change GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (gramAction f z)-
    gramFiber z (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (f z))=_
  rw [original_contact_gram_value]
  rfl

private theorem spin_gram (a : Fin 7) (f : QuantumTest) :
    GaussCoframeSpin.current a (gramAction f)=gramAction (GaussCoframeSpin.current a f)+spinContact a f := by
  simp only [spinContact,LinearMap.sub_apply,Module.End.mul_apply]
  abel

private theorem real_gram (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) :
    gramAction (multiply c hc f)=multiply c hc (gramAction f) := by
  apply DFunLike.ext
  intro z
  rw [original_contact_gram_value]
  change gramFiber z ((c z : ℂ) • f z)=(c z : ℂ) • gramAction f z
  rw [map_smul,original_contact_gram_value]

private theorem real_gram_pair (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourcePair f (multiply c hc (gramAction g))=sourcePair (multiply c hc (gramAction f)) g := by
  rw [multiply_pair,original_contact_gram_pair,real_gram]

private theorem half_current (A : End) (hA : Paired A A) (f : QuantumTest) :
    (sourcePair f ((A*gramAction-gramAction*A) f)).im/2=(sourcePair f (A (gramAction f))).im := by
  have he : sourcePair f ((A*gramAction-gramAction*A) f)=
      sourcePair f (A (gramAction f))-starRingEnd ℂ (sourcePair f (A (gramAction f))) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
    change sourcePair f (A (gramAction f))-sourcePair f (gramAction (A f))=_
    rw [original_contact_gram_pair,←GaussNativeForm.pair_conjugate (A f) (gramAction f),←hA]
    rfl
  rw [he]
  simp only [Complex.sub_im,Complex.conj_im]
  ring

/-- Both original mixed halves are retained; their principal conjugate pair cancels in the imaginary part. -/
def mixedFlux (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) : ℝ :=
  (-(sourcePair (GaussCoframeSpin.current a f) (multiply c hc (gramJet i f))).re+
    (sourcePair (momentum i f) (multiply c hc (spinContact a f))).im)/2

theorem original_mixed_contact_flux (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) :
    (sourcePair f ((mixed i a c hc*gramAction-gramAction*mixed i a c hc) f)).im/2=mixedFlux i a c hc f := by
  rw [half_current _ (mixed_pair i a c hc)]
  have hm : sourcePair f (mixed i a c hc (gramAction f))=(1/2 : ℂ)*
      (sourcePair (GaussCoframeSpin.current a f) (multiply c hc (momentum i (gramAction f)))+
        sourcePair (momentum i f) (multiply c hc (GaussCoframeSpin.current a (gramAction f)))) := by
    simp only [mixed,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,sourcePair,
      map_smul,map_add,inner_smul_right,inner_add_right]
    change (1/2 : ℂ)*(sourcePair f (GaussCoframeSpin.current a (multiply c hc (momentum i (gramAction f))))+
      sourcePair f (adjoint i (multiply c hc (GaussCoframeSpin.current a (gramAction f)))))=
      (1/2 : ℂ)*(sourcePair (GaussCoframeSpin.current a f) (multiply c hc (momentum i (gramAction f)))+
      sourcePair (momentum i f) (multiply c hc (GaussCoframeSpin.current a (gramAction f))))
    rw [GaussCoframeSpin.current_pair,GaussCoframeKinetic.adjoint_pair]
  have hp : sourcePair (momentum i f) (multiply c hc (gramAction (GaussCoframeSpin.current a f)))=
      starRingEnd ℂ (sourcePair (GaussCoframeSpin.current a f) (multiply c hc (gramAction (momentum i f)))) := by
    rw [GaussNativeForm.pair_conjugate]
    exact real_gram_pair c hc _ _
  rw [hm,original_contact_coframe_momentum,spin_gram]
  simp only [map_add,map_smul,sourcePair,inner_add_right,inner_smul_right]
  change (((1/2 : ℂ)*(sourcePair (GaussCoframeSpin.current a f) (multiply c hc (gramAction (momentum i f)))+
    (-Complex.I)*sourcePair (GaussCoframeSpin.current a f) (multiply c hc (gramJet i f))+
    (sourcePair (momentum i f) (multiply c hc (gramAction (GaussCoframeSpin.current a f)))+
    sourcePair (momentum i f) (multiply c hc (spinContact a f)))))).im=_
  rw [hp]
  simp only [mixedFlux,Complex.mul_im,Complex.add_im,Complex.div_re,Complex.div_im,
    Complex.one_re,Complex.one_im,Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat,
    Complex.neg_re,Complex.I_re,Complex.neg_im,Complex.I_im,Complex.conj_im]
  ring

def spinFlux (a : Fin 7) (f : QuantumTest) : ℝ :=
  spinWeight a*(sourcePair (GaussCoframeSpin.current a f)
    (multiply inverseVolume inverseVolume_smooth (spinContact a f))).im

theorem original_spin_square_contact_flux (a : Fin 7) (f : QuantumTest) :
    (sourcePair f ((spinSquare a*gramAction-gramAction*spinSquare a) f)).im/2=spinFlux a f := by
  have hA : Paired (spinSquare a) (spinSquare a) := by
    intro p q
    simp only [spinSquare,LinearMap.smul_apply,LinearMap.comp_apply,sourcePair,map_smul,
      inner_smul_right,inner_smul_left,Complex.conj_ofReal]
    change (spinWeight a : ℂ)*sourcePair p (GaussCoframeSpin.current a
      (multiply inverseVolume inverseVolume_smooth (GaussCoframeSpin.current a q)))=_
    rw [GaussCoframeSpin.current_pair,multiply_pair,GaussCoframeSpin.current_pair]
    rfl
  rw [half_current _ hA]
  have hr : (sourcePair (GaussCoframeSpin.current a f)
      (multiply inverseVolume inverseVolume_smooth (gramAction (GaussCoframeSpin.current a f)))).im=0 := by
    have he := real_gram_pair inverseVolume inverseVolume_smooth (GaussCoframeSpin.current a f) (GaussCoframeSpin.current a f)
    have hconj := (GaussNativeForm.pair_conjugate (GaussCoframeSpin.current a f)
      (multiply inverseVolume inverseVolume_smooth (gramAction (GaussCoframeSpin.current a f)))).trans he.symm
    have h := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h
    linarith
  simp only [spinSquare,LinearMap.smul_apply,LinearMap.comp_apply,sourcePair,map_smul,inner_smul_right]
  change ((spinWeight a : ℂ)*sourcePair f (GaussCoframeSpin.current a
    (multiply inverseVolume inverseVolume_smooth (GaussCoframeSpin.current a (gramAction f))))).im=_
  rw [GaussCoframeSpin.current_pair,spin_gram]
  simp only [sourcePair,map_add,inner_add_right]
  change ((spinWeight a : ℂ)*(sourcePair (GaussCoframeSpin.current a f)
    (multiply inverseVolume inverseVolume_smooth (gramAction (GaussCoframeSpin.current a f)))+
    sourcePair (GaussCoframeSpin.current a f) (multiply inverseVolume inverseVolume_smooth (spinContact a f)))).im=_
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,Complex.add_im,hr,zero_add,spinFlux]

end LowEnergy.SourceContactMixedFlux
