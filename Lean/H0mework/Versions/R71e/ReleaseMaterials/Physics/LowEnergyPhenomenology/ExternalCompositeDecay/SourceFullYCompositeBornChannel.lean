import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYBornFrequency
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCore
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeContactRead
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.CompositeFullYBorn
open MeasureTheory Filter Set
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussFockPair GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussFockLift GaussComposite GaussHalfDensity
open FullYDynamicSource FullYDynamicSourceNext FullYDynamicResponse
open scoped Topology InnerProductSpace Interval
attribute [local irreducible] embed sourcePair literalCoreResolvent literalSharpResolvent
  sourceOrbit sourceSpace literalResponse creationTest annihilationTest

/-- These are exactly the original scalar-dressed matter letters, with their source half-density. -/
def letter(addition:Bool)(channel spin:Fin 2):QuantumTest→ₗ[ℂ]QuantumTest:=
  if addition then creationTest channel spin else annihilationTest channel spin

private theorem weighted_pair(f g:QuantumTest):
    sourcePair f g=∫z,inner ℂ (weightedValue f z) (weightedValue g z) ∂GaussHistoryHilbert.chartMeasure:=by
  simp only [sourcePair]
  let U:=fockHalfDensityEquiv
  rw [←U.inner_map_map (embed f) (embed g),flat_inner_integral]
  apply integral_congr_ae
  filter_upwards [flat_embed_value f,flat_embed_value g] with z hf hg
  rw [hf,hg]

theorem actual_letter_pair(addition:Bool)(channel spin:Fin 2)(f g:QuantumTest):
    sourcePair (letter addition channel spin f) g=
      sourcePair f (letter (!addition) channel spin g):=by
  rw [weighted_pair,weighted_pair]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  cases addition
  · simp only [letter,Bool.false_eq_true,ite_false,Bool.not_false,ite_true,
      annihilation_test_value,creation_test_value]
    exact fiber_annihilation_pair channel spin _ _ _
  · simp only [letter,ite_true,Bool.not_true,Bool.false_eq_true,ite_false,
      annihilation_test_value,creation_test_value]
    exact fiber_creation_pair channel spin _ _ _

theorem actual_letter_embed(addition:Bool)(channel spin:Fin 2)(f:QuantumTest):
    embed (letter addition channel spin f)=
      if addition then creationSource channel spin f else annihilationSource channel spin f:=by
  cases addition
  · exact embed_annihilation_test channel spin f
  · exact embed_creation_test channel spin f

def channelVector(F:Index)(sharp additionIn additionOut:Bool)(channelIn spinIn channelOut spinOut:Fin 2)
    (f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):H:=
  embed (letter additionOut channelOut spinOut
    (literalResponse F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w))

/-- The inclusive output is the original H-valued composite source, retaining every full-Y output grade. -/
theorem actual_channel_source(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    channelVector F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ w=
      if additionOut then creationSource channelOut spinOut
        (literalResponse F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w)
      else annihilationSource channelOut spinOut
        (literalResponse F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w):=
  actual_letter_embed additionOut channelOut spinOut _

theorem actual_channel_frequency_integrable(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun w:ℝ=>‖channelVector F sharp additionIn additionOut
      channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2):=
  actual_core_word_square_integrable F sharp (letter additionIn channelIn spinIn f) advanced μ hμ
    (letter additionOut channelOut spinOut)

theorem actual_channel_continuous(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Continuous (channelVector F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ):=by
  let q:=letter additionIn channelIn spinIn f
  let A:=letter additionOut channelOut spinOut
  apply ((sourceReader F sharp q A).continuous.comp
    (actual_response_continuous F sharp q advanced μ hμ)).congr
  intro w
  exact source_reader_return F sharp q _ A (actual_response_orbit F sharp q advanced μ hμ w)

/-- Reversing the actual composite words returns the independent original dual resolvent. -/
theorem actual_composite_independent_dual(F:Index)(additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f g:QuantumTest)(z:ℂ)(hz:z.im≠0):
    sourcePair g (letter additionOut channelOut spinOut
      (literalSharpResolvent F z hz (letter additionIn channelIn spinIn f)))=
    sourcePair (letter (!additionIn) channelIn spinIn
      (literalCoreResolvent F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz)
        (letter (!additionOut) channelOut spinOut g))) f:=by
  have ho:=actual_letter_pair (!additionOut) channelOut spinOut g
    (literalSharpResolvent F z hz (letter additionIn channelIn spinIn f))
  simp only [Bool.not_not] at ho
  rw [←ho,literal_two_leg_pair]
  have hi:=actual_letter_pair (!additionIn) channelIn spinIn
    (literalCoreResolvent F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz)
      (letter (!additionOut) channelOut spinOut g)) f
  simpa only [Bool.not_not] using hi.symm

/-- The two actual outgoing channels exhaust their original field-valued CAR contact. -/
theorem actual_propagated_contact(F:Index)(sharp additionIn:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    ‖channelVector F sharp additionIn true channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2+
      ‖channelVector F sharp additionIn false channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2=
      (sourcePair (literalResponse F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w)
        (contactSource channelOut spinOut channelOut spinOut
          (literalResponse F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w))).re:=by
  rw [actual_channel_source,actual_channel_source]
  exact source_contact_norm channelOut spinOut _

def channelCausal(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(z:ℂ)(T:ℝ):H:=
  (if advanced then -Complex.I else Complex.I) • ∫t in (0:ℝ)..T,
    Complex.exp ((if advanced then -t else t) • (Complex.I*z)) •
      embed (letter additionOut channelOut spinOut
        (literalCoreTime F sharp (letter additionIn channelIn spinIn f) (if advanced then -t else t)))

private theorem channel_causal_reader(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(z:ℂ)(T:ℝ):
    channelCausal F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced z T=
      sourceReader F sharp (letter additionIn channelIn spinIn f) (letter additionOut channelOut spinOut)
        (uncutCausalVector F sharp (letter additionIn channelIn spinIn f) advanced z T):=by
  let q:=letter additionIn channelIn spinIn f
  let A:=letter additionOut channelOut spinOut
  let L:=sourceReader F sharp q A
  have ht(t:ℝ):L (embed (literalCoreTime F sharp q t))=embed (A (literalCoreTime F sharp q t)):=by
    apply source_reader_return
    unfold literalCoreTime
    exact Subtype.property _
  have hc:Continuous (fun t:ℝ=>embed (literalCoreTime F sharp q t)):=
    continuous_iff_continuousAt.mpr (fun t=>(literal_core_time_derivative F sharp q t).continuousAt)
  have ho:Continuous (fun t:ℝ=>if advanced then -t else t):=by
    cases advanced <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact continuous_id
    · exact continuous_neg
  have hi:IntervalIntegrable (fun t:ℝ=>Complex.exp ((if advanced then -t else t) • (Complex.I*z)) •
      embed (literalCoreTime F sharp q (if advanced then -t else t))) volume 0 T:=
    ((Complex.continuous_exp.comp (ho.smul continuous_const)).smul (hc.comp ho)).intervalIntegrable _ _
  change (if advanced then -Complex.I else Complex.I) •
    (∫t in (0:ℝ)..T,Complex.exp ((if advanced then -t else t) • (Complex.I*z)) •
      embed (A (literalCoreTime F sharp q (if advanced then -t else t))))=
    L ((if advanced then -Complex.I else Complex.I) •
      (∫t in (0:ℝ)..T,Complex.exp ((if advanced then -t else t) • (Complex.I*z)) •
        embed (literalCoreTime F sharp q (if advanced then -t else t))))
  rw [map_smul,←L.intervalIntegral_comp_comm hi]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [map_smul,ht]

/-- Both physical half-lines generate the actual inclusive composite channel amplitude. -/
theorem actual_channel_causal_return(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(z:ℂ)
    (hz:if advanced then z.im<0 else 0<z.im):
    Tendsto (channelCausal F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced z)
      atTop (𝓝 (embed (letter additionOut channelOut spinOut
        (if sharp then literalSharpResolvent F z
          (by cases advanced;exact hz.ne';exact hz.ne) (letter additionIn channelIn spinIn f)
        else literalCoreResolvent F z
          (by cases advanced;exact hz.ne';exact hz.ne) (letter additionIn channelIn spinIn f))))):=by
  let q:=letter additionIn channelIn spinIn f
  let A:=letter additionOut channelOut spinOut
  have h:=(sourceReader F sharp q A).continuous.tendsto _ |>.comp
    (actual_original_uncut_retarded_kernel F sharp q advanced z hz)
  have hm:(if sharp then literalSharpResolvent F z
      (by cases advanced;exact hz.ne';exact hz.ne) q else literalCoreResolvent F z
      (by cases advanced;exact hz.ne';exact hz.ne) q)∈sourceOrbit F sharp q:=by
    rw [←source_resolvent_literal_return]
    exact Subtype.property _
  rw [source_reader_return F sharp q _ A hm] at h
  exact h.congr' (Eventually.of_forall (fun T=>(channel_causal_reader F sharp additionIn additionOut
    channelIn spinIn channelOut spinOut f advanced z T).symm))

end LowEnergy.CompositeFullYBorn
