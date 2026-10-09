import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSharpTail
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open MeasureTheory Filter Set GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open GaussFockPair FullYDynamicSource FullYDynamicResponse SourceResolventBandLimit GaussDensityCore
open scoped InnerProductSpace Topology
attribute [local irreducible] embed sourcePair literalSharpResolvent literalCoreResolvent

/-- The amplitude tests the complete original primal-Y response against its actual epsilon source. -/
def epsilonPrimalAmplitude(F:Index)(dual:Bool)(e:Epsilon20)(f:ScalarTest)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):ℂ:=
  sourcePair (epsilonSection dual e f) (literalResponse F false g advanced μ hμ w)

private theorem causal_conjugate(advanced:Bool)(μ w:ℝ):
    star (line (FullYPairedParseval.direction advanced*μ) w)=
      line (FullYPairedParseval.direction (!advanced)*μ) w:=by
  cases advanced <;> apply Complex.ext <;> simp [line,FullYPairedParseval.direction]

private theorem causal_pair(F:Index)(dual:Bool)(e:Epsilon20)(f:ScalarTest)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    epsilonPrimalAmplitude F dual e f g advanced μ hμ w=
      inner ℂ (embed (literalResponse F true (epsilonSection dual e f) (!advanced) μ hμ w)) (embed g):=by
  let z:=line (FullYPairedParseval.direction (!advanced)*μ) w
  have h:=congrArg (starRingEnd ℂ) (literal_two_leg_pair F z
    (causal_line_nonreal (!advanced) μ w hμ) g (epsilonSection dual e f))
  simp only [sourcePair,inner_conj_symm] at h
  have hz:star z=line (FullYPairedParseval.direction advanced*μ) w:=by
    simpa only [Bool.not_not] using causal_conjugate (!advanced) μ w
  simp only [hz] at h
  simp only [epsilonPrimalAmplitude,sourcePair,literalResponse,if_true,Bool.false_eq_true,if_false]
  exact h.symm

/-- The opposite sharp leg pays the complete primal channel for arbitrary forcing; both legs retain the same frequency. -/
theorem actual_epsilon_primal_channel_bound(F:Index)(dual:Bool)(e:Epsilon20)(f:ScalarTest)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    ‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2≤
      ‖embed g‖^2*‖embed (literalResponse F true (epsilonSection dual e f) (!advanced) μ hμ w)‖^2:=by
  rw [causal_pair]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜:=ℂ) _ _) 2).trans_eq
    (by rw [mul_pow,mul_comm])

theorem actual_epsilon_primal_channel_integrable(F:Index)(dual:Bool)(e:Epsilon20)(f:ScalarTest)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun w:ℝ=>‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2):=by
  apply ((actual_epsilon_sharp_frequency_integrable F (!advanced) μ hμ dual e f).const_mul (‖embed g‖^2)).mono'
  · have hc:Continuous (fun w:ℝ=>inner ℂ
        (embed (literalResponse F true (epsilonSection dual e f) (!advanced) μ hμ w)) (embed g)):=
      (CompositeFullYBorn.actual_response_continuous F true (epsilonSection dual e f)
        (!advanced) μ hμ).inner continuous_const
    simp_rw [causal_pair]
    exact (hc.norm.pow 2).aestronglyMeasurable
  · apply Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact actual_epsilon_primal_channel_bound F dual e f g advanced μ hμ w

/-- An all-cutoff positive frequency price for the literal full-Y channel, with no norm budget supplied by the caller. -/
theorem actual_epsilon_primal_common_frequency_price(F:Index)(dual:Bool)(e:Epsilon20)(f:ScalarTest)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ):
    (∫w:ℝ,‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2)≤
      ‖embed g‖^2*(Real.pi/μ*(‖e‖^2*‖scalarLp 3 f‖^2)):=by
  calc
    _≤∫w:ℝ,‖embed g‖^2*‖embed (literalResponse F true (epsilonSection dual e f) (!advanced) μ hμ w)‖^2:=
      integral_mono_ae (actual_epsilon_primal_channel_integrable F dual e f g advanced μ hμ)
        ((actual_epsilon_sharp_frequency_integrable F (!advanced) μ hμ dual e f).const_mul _)
        (ae_of_all _ (actual_epsilon_primal_channel_bound F dual e f g advanced μ hμ))
    _=_:=by rw [integral_const_mul,actual_epsilon_sharp_common_frequency_price]

/-- The external source chooses K0 before the arbitrary forcing, frequency scale and causal branch. -/
theorem actual_epsilon_primal_ordinary_common_tail(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    ∃K0:Index,∀(g:QuantumTest)(μ:ℝ)(hμ:0<μ)(ε:ℝ),0<ε →∃R:ℝ,0≤R ∧
      ∀F:Index,K0⊆F →∀advanced:Bool,
        (∫w in Ioi R,‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2)+
        (∫w in Iio (-R),‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2)<ε:=by
  obtain ⟨K0,hK⟩:=actual_epsilon_sharp_cofinal_envelope dual e f
  refine ⟨K0,fun g μ hμ ε hε=>?_⟩
  let B:=fun w:ℝ=>‖embed g‖^2*epsilonFrequencyEnvelope dual e f μ w
  have hB:Integrable B:=(actual_epsilon_envelope_integrable dual e f μ hμ).const_mul _
  have ht:Tendsto (fun R:ℝ=>(∫w in Ioi R,B w)+(∫w in Iio (-R),B w)) atTop (𝓝 0):=by
    have h1:=tendsto_integral_Ioi_zero (f:=B) (μ:=volume) tendsto_id
    have h2:=tendsto_integral_Iio_zero (f:=B) (μ:=volume) tendsto_neg_atTop_atBot
    simpa only [id_eq,add_zero] using h1.add h2
  obtain ⟨R0,hR0⟩:=eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  let R:=max R0 0
  refine ⟨R,le_max_right _ _,fun F hF advanced=>?_⟩
  have hi:=actual_epsilon_primal_channel_integrable F dual e f g advanced μ hμ
  have hb(w:ℝ):‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2≤B w:=
    (actual_epsilon_primal_channel_bound F dual e f g advanced μ hμ w).trans
      (mul_le_mul_of_nonneg_left (hK F hF μ hμ (!advanced) w) (sq_nonneg _))
  have hr:(∫w in Ioi R,‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2)≤∫w in Ioi R,B w:=
    integral_mono_ae hi.integrableOn hB.integrableOn (ae_of_all _ hb)
  have hl:(∫w in Iio (-R),‖epsilonPrimalAmplitude F dual e f g advanced μ hμ w‖^2)≤∫w in Iio (-R),B w:=
    integral_mono_ae hi.integrableOn hB.integrableOn (ae_of_all _ hb)
  exact lt_of_le_of_lt (add_le_add hr hl) (hR0 R (le_max_left _ _))

end LowEnergy.NamedColorQtNext
