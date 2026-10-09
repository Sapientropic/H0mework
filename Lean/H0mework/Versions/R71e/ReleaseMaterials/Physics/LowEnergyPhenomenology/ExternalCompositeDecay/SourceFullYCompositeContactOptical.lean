import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCompositeBornMeasure
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.CompositeChannelOptical
open MeasureTheory Filter Set
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussFockPair
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussUnitaryHistory
open FullYDynamicSource FullYDynamicResponse CompositeFullYBorn SourceScalarPairedTransport
open scoped Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] embed sourcePair literalCoreResolvent literalSharpResolvent
  sourceOrbit sourceSpace literalResponse letter channelVector diagonalAction

def detector(channel spin:Fin 2):End:=GaussComposite.contactSource channel spin channel spin
def contactCurrent(channel spin:Fin 2):End:=
  diagonalAction*detector channel spin-detector channel spin*diagonalAction

theorem original_detector_pair(channel spin:Fin 2)(f g:QuantumTest):
    sourcePair f (detector channel spin g)=sourcePair (detector channel spin f) g:=by
  have h:=congrArg (starRingEnd ℂ) (GaussComposite.source_contact_hermitian channel spin channel spin f g)
  simpa only [detector,sourcePair,inner_conj_symm] using h

private theorem detector_im_zero(channel spin:Fin 2)(u:QuantumTest):
    (sourcePair u (detector channel spin u)).im=0:=by
  rw [detector,←GaussComposite.source_contact]
  have hh(x:H):(inner ℂ x x).im=0:=by
    exact inner_self_im (𝕜:=ℂ) x
  simp only [Complex.add_im,hh,add_zero]

private theorem contact_current_pair(channel spin:Fin 2)(u:QuantumTest):
    sourcePair u (contactCurrent channel spin u)=
      sourcePair (diagonalAction u) (detector channel spin u)-
        star (sourcePair (diagonalAction u) (detector channel spin u)):=by
  have hs:sourcePair u (contactCurrent channel spin u)=
      sourcePair u (diagonalAction (detector channel spin u))-
      sourcePair u (detector channel spin (diagonalAction u)):=by
    simp only [contactCurrent,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
  have hh:=diagonalAction_pair u (detector channel spin u)
  have hc:=original_detector_pair channel spin u (diagonalAction u)
  have hp:=GaussNativeForm.pair_conjugate (diagonalAction u) (detector channel spin u)
  exact hs.trans ((congrArg₂ (fun a b:ℂ=>a-b) hh hc).trans
    (congrArg (fun b:ℂ=>sourcePair (diagonalAction u) (detector channel spin u)-b) hp.symm))

private theorem original_residual(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(w:ℝ):
    diagonalAction (literalResponse F sharp f advanced μ hμ w)+
      sourceY sharp (literalResponse F sharp f advanced μ hμ w)=
      f+SourceResolventBandLimit.line (FullYPairedParseval.direction advanced*μ) w •
        literalResponse F sharp f advanced μ hμ w+
          defectAction F (literalResponse F sharp f advanced μ hμ w):=by
  cases sharp
  · have h:=literal_full_source_residual F _ (causal_line_nonreal advanced μ w hμ) f
    simp only [literalResponse,Bool.false_eq_true,ite_false,sourceY,GaussFullHamiltonian.fullAction,
      LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply] at h ⊢
    linear_combination (norm := module) h
  · have h:=literal_sharp_full_source_residual F _ (causal_line_nonreal advanced μ w hμ) f
    simp only [literalResponse,ite_true,sourceY,GaussFullHamiltonian.sharpAction,
      LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply] at h ⊢
    linear_combination (norm := module) h

private theorem optical_core(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(w:ℝ)(channel spin:Fin 2):
    let u:=literalResponse F sharp f advanced μ hμ w
    (FullYPairedParseval.direction advanced*μ)*(sourcePair u (detector channel spin u)).re=
      (sourcePair f (detector channel spin u)).im-
      (sourcePair u (contactCurrent channel spin u)).im/2-
      (sourcePair (sourceY sharp u) (detector channel spin u)).im+
      (sourcePair (defectAction F u) (detector channel spin u)).im:=by
  dsimp only
  let u:=literalResponse F sharp f advanced μ hμ w
  have h:=congrArg (fun q:QuantumTest=>(sourcePair q (detector channel spin u)).im)
    (original_residual F sharp f advanced μ hμ w)
  have hc:=congrArg Complex.im (contact_current_pair channel spin u)
  have hz: (sourcePair u (detector channel spin u)).im=0:=detector_im_zero channel spin u
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,
    Complex.add_im,Complex.mul_im,Complex.conj_re,Complex.conj_im] at h
  dsimp only [u] at hc hz ⊢
  simp only [sourcePair] at hc hz ⊢
  rw [hz,SourceResolventBandLimit.line_im] at h
  simp only [Complex.sub_im,Complex.star_def,Complex.conj_im] at hc
  nlinarith only [h,hc]

/-- Original positive outgoing CAR intensity, with the full H0 current, Y leg and own compression defect. -/
theorem actual_channel_optical_balance(F:Index)(sharp additionIn:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    let q:=letter additionIn channelIn spinIn f
    let u:=literalResponse F sharp q advanced μ hμ w
    (FullYPairedParseval.direction advanced*μ)*
      (‖channelVector F sharp additionIn true channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2+
       ‖channelVector F sharp additionIn false channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2)=
      (sourcePair q (detector channelOut spinOut u)).im-
      (sourcePair u (contactCurrent channelOut spinOut u)).im/2-
      (sourcePair (sourceY sharp u) (detector channelOut spinOut u)).im+
      (sourcePair (defectAction F u) (detector channelOut spinOut u)).im:=by
  dsimp only
  rw [actual_propagated_contact]
  exact optical_core F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w channelOut spinOut

private theorem word_continuous(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(A:End):
    Continuous (fun w:ℝ=>embed (A (literalResponse F sharp f advanced μ hμ w))):=by
  apply ((sourceReader F sharp f A).continuous.comp
    (actual_response_continuous F sharp f advanced μ hμ)).congr
  intro w
  exact source_reader_return F sharp f _ A (actual_response_orbit F sharp f advanced μ hμ w)

/-- Quadratic original words have an internally paid full-frequency L1 price on the same full-Y response. -/
theorem actual_word_pair_integrable(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(A B:End):
    Integrable (fun w:ℝ=>sourcePair (A (literalResponse F sharp f advanced μ hμ w))
      (B (literalResponse F sharp f advanced μ hμ w))):=by
  have hA:=actual_core_word_square_integrable F sharp f advanced μ hμ A
  have hB:=actual_core_word_square_integrable F sharp f advanced μ hμ B
  apply ((hA.add hB).div_const 2).mono'
    (by simpa only [sourcePair] using
      ((word_continuous F sharp f advanced μ hμ A).inner (𝕜:=ℂ)
        (word_continuous F sharp f advanced μ hμ B)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro w
  have h:=norm_inner_le_norm (𝕜:=ℂ)
    (embed (A (literalResponse F sharp f advanced μ hμ w)))
    (embed (B (literalResponse F sharp f advanced μ hμ w)))
  simp only [sourcePair,Pi.add_apply]
  nlinarith only [h,sq_nonneg (‖embed (A (literalResponse F sharp f advanced μ hμ w))‖-
    ‖embed (B (literalResponse F sharp f advanced μ hμ w))‖)]

end LowEnergy.CompositeChannelOptical
