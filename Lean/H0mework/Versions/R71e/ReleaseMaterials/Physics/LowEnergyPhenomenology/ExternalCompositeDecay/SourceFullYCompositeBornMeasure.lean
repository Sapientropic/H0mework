import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCompositeBornChannel
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYFullSourceCausalReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.CompositeFullYBorn
open MeasureTheory Filter Set
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussFockPair
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussUnitaryHistory
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse
open SourceResolventBandLimit SourceResolventLorentzian
open scoped Topology InnerProductSpace ENNReal
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] embed sourcePair literalCoreResolvent literalSharpResolvent
  sourceOrbit sourceSpace literalResponse letter channelVector

def channelMeasure(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):Measure ℝ:=
  volume.withDensity (fun w=>ENNReal.ofReal
    (‖channelVector F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2))

private theorem positive_density_return(p:ℝ→ℝ)(hi:Integrable p)(hn:∀w,0≤p w)(B:Set ℝ)(hB:MeasurableSet B):
    volume.withDensity (fun w=>ENNReal.ofReal (p w)) B=ENNReal.ofReal (∫w in B,p w):=by
  rw [withDensity_apply _ hB]
  exact (ofReal_integral_eq_lintegral_ofReal hi.restrict (Eventually.of_forall hn)).symm

/-- Actual composite channel probabilities form a finite positive measure on the whole frequency line. -/
theorem actual_channel_measure(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    (∀B:Set ℝ,MeasurableSet B →
      channelMeasure F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ B=
        ENNReal.ofReal (∫w in B,‖channelVector F sharp additionIn additionOut
          channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2)) ∧
      channelMeasure F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ univ<∞:=by
  have hi:=actual_channel_frequency_integrable F sharp additionIn additionOut
    channelIn spinIn channelOut spinOut f advanced μ hμ
  have hb(B:Set ℝ)(hB:MeasurableSet B):channelMeasure F sharp additionIn additionOut
      channelIn spinIn channelOut spinOut f advanced μ hμ B=
      ENNReal.ofReal (∫w in B,‖channelVector F sharp additionIn additionOut
        channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2):=
    positive_density_return _ hi (fun _=>sq_nonneg _) B hB
  exact ⟨hb,by rw [hb univ MeasurableSet.univ];exact ENNReal.ofReal_lt_top⟩

/-- The original field-valued contact has a finite inclusive full-Y frequency price. -/
theorem actual_contact_frequency(F:Index)(sharp additionIn:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun w:ℝ=>(sourcePair
      (literalResponse F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w)
      (GaussComposite.contactSource channelOut spinOut channelOut spinOut
        (literalResponse F sharp (letter additionIn channelIn spinIn f) advanced μ hμ w))).re):=by
  have hc:=actual_channel_frequency_integrable F sharp additionIn true
    channelIn spinIn channelOut spinOut f advanced μ hμ
  have ha:=actual_channel_frequency_integrable F sharp additionIn false
    channelIn spinIn channelOut spinOut f advanced μ hμ
  apply (hc.add ha).congr
  exact Eventually.of_forall (actual_propagated_contact F sharp additionIn
    channelIn spinIn channelOut spinOut f advanced μ hμ)

/-- The source forcing contains the literal full H0 and the independently selected original Y leg. -/
def fullSourcePulse(sharp:Bool)(q:QuantumTest)(advanced:Bool)(μ w:ℝ):QuantumTest:=
  (line (FullYPairedParseval.direction advanced*μ) w)⁻¹ •
    (((if sharp then GaussFullHamiltonian.sharpAction else GaussFullHamiltonian.fullAction)-
      line (FullYPairedParseval.direction advanced*μ) w • (1:End)) q)

def pulseVector(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):H:=
  embed (letter additionOut channelOut spinOut (literalResponse F sharp
    (fullSourcePulse sharp (letter additionIn channelIn spinIn f) advanced μ w) advanced μ hμ w))

def pulseMeasure(F:Index)(sharp additionIn additionOut:Bool)
    (channelIn spinIn channelOut spinOut:Fin 2)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):Measure ℝ:=
  volume.withDensity (fun w=>ENNReal.ofReal
    (‖pulseVector F sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2))

private theorem pulse_return(K:Index)(q:QuantumTest)(sharp advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ)
    (hp:literalCoreResolvent K (line (FullYPairedParseval.direction advanced*μ) w)
      (causal_line_nonreal advanced μ w hμ)
      ((GaussFullHamiltonian.fullAction-line (FullYPairedParseval.direction advanced*μ) w • (1:End)) q)=q)
    (hs:literalSharpResolvent K (line (FullYPairedParseval.direction advanced*μ) w)
      (causal_line_nonreal advanced μ w hμ)
      ((GaussFullHamiltonian.sharpAction-line (FullYPairedParseval.direction advanced*μ) w • (1:End)) q)=q):
    literalResponse K sharp (fullSourcePulse sharp q advanced μ w) advanced μ hμ w=
      (line (FullYPairedParseval.direction advanced*μ) w)⁻¹ • q:=by
  cases sharp
  · simp only [literalResponse,fullSourcePulse,Bool.false_eq_true,ite_false,map_smul,hp]
  · simp only [literalResponse,fullSourcePulse,ite_true,map_smul,hs]

private theorem line_inverse_norm(advanced:Bool)(μ w:ℝ):
    ‖(line (FullYPairedParseval.direction advanced*μ) w)⁻¹‖^2=kernel μ 0 w:=by
  have h:=inverse_norm_square (FullYPairedParseval.direction advanced*μ) 0 w
  cases advanced <;> simpa only [FullYPairedParseval.direction,ite_true,Bool.false_eq_true,ite_false,
    one_mul,neg_one_mul,Complex.ofReal_zero,zero_sub,inv_neg,norm_neg,line,
    mul_comm Complex.I,kernel,neg_sq] using h

/-- One source-generated common upper works for every frequency, damping and causal/dual leg. -/
theorem actual_cofinal_pulse_response(F:Index)(additionIn:Bool)(channelIn spinIn:Fin 2)(f:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀sharp advanced additionOut:Bool,
      ∀channelOut spinOut:Fin 2,∀μ:ℝ,∀hμ:0<μ,∀w:ℝ,
      pulseVector K sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ w=
        (line (FullYPairedParseval.direction advanced*μ) w)⁻¹ •
          embed (letter additionOut channelOut spinOut (letter additionIn channelIn spinIn f)):=by
  let q:=letter additionIn channelIn spinIn f
  obtain ⟨K₀,hF,hK₀⟩:=actual_full_source_forcing_return F q q
  refine ⟨K₀,hF,?_⟩
  intro K hK sharp advanced additionOut channelOut spinOut μ hμ w
  have h:=hK₀ K hK (line (FullYPairedParseval.direction advanced*μ) w)
    (causal_line_nonreal advanced μ w hμ)
  unfold pulseVector
  rw [pulse_return K q sharp advanced μ hμ w h.1 h.2,map_smul,map_smul]

/-- The complete positive measure stabilizes on this literal full-source forcing family, not only its mass. -/
theorem actual_cofinal_pulse_measure(F:Index)(additionIn:Bool)(channelIn spinIn:Fin 2)(f:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀sharp advanced additionOut:Bool,
      ∀channelOut spinOut:Fin 2,∀μ:ℝ,∀hμ:0<μ,
      pulseMeasure K sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ=
        volume.withDensity (fun w=>ENNReal.ofReal (kernel μ 0 w*
          ‖embed (letter additionOut channelOut spinOut (letter additionIn channelIn spinIn f))‖^2)) ∧
      pulseMeasure K sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ univ=
        ENNReal.ofReal ((Real.pi/μ)*
          ‖embed (letter additionOut channelOut spinOut (letter additionIn channelIn spinIn f))‖^2):=by
  obtain ⟨K₀,hF,hK₀⟩:=actual_cofinal_pulse_response F additionIn channelIn spinIn f
  refine ⟨K₀,hF,?_⟩
  intro K hK sharp advanced additionOut channelOut spinOut μ hμ
  have he(w:ℝ):‖pulseVector K sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ w‖^2=
      kernel μ 0 w*‖embed (letter additionOut channelOut spinOut (letter additionIn channelIn spinIn f))‖^2:=by
    rw [hK₀ K hK sharp advanced additionOut channelOut spinOut μ hμ w,norm_smul,mul_pow,line_inverse_norm]
  have hm:pulseMeasure K sharp additionIn additionOut channelIn spinIn channelOut spinOut f advanced μ hμ=
      volume.withDensity (fun w=>ENNReal.ofReal (kernel μ 0 w*
        ‖embed (letter additionOut channelOut spinOut (letter additionIn channelIn spinIn f))‖^2)):=by
    unfold pulseMeasure
    simp_rw [he]
  refine ⟨hm,?_⟩
  rw [hm,positive_density_return _ ((kernel_integrable μ 0 hμ).mul_const _) _ univ MeasurableSet.univ]
  · simp only [Measure.restrict_univ,integral_mul_const,kernel_integral μ 0 hμ]
  · intro w
    unfold kernel
    positivity

end LowEnergy.CompositeFullYBorn
