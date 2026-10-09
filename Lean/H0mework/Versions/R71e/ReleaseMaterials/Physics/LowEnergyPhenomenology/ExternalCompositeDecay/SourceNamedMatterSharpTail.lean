import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSharpFrequency
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open MeasureTheory Filter Set GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open GaussDiagonalHistory FullYDynamicSource FullYDynamicResponse FullYSourceResolventGraphSplice
open SourceResolventBandLimit SourceResolventLorentzian GaussDensityCore
open scoped BigOperators InnerProductSpace Topology
local instance labelFintype : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _
attribute [local irreducible] embed literalSharpResolvent diagonalAction

private theorem resolvent_graph_decay {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
    (C:E→L[ℂ]E)(hC:IsSelfAdjoint C)(z:ℂ)(hz:z.im≠0)(x:E):
    ‖z‖*‖FullYSourceResolventGraphSplice.resolvent C z x‖≤‖x‖+(1/|z.im|)*‖C x‖:=by
  let R:=FullYSourceResolventGraphSplice.resolvent C z
  have h:=congrArg (fun T:E→L[ℂ]E=>T x) (resolvent_compression C hC z hz)
  change R (C x)=x+z • R x at h
  have he:z • R x=R (C x)-x:=by rw [h]; abel
  change ‖z‖*‖R x‖≤_
  rw [←norm_smul,he]
  calc
    _≤‖R (C x)‖+‖x‖:=norm_sub_le _ _
    _≤‖R‖*‖C x‖+‖x‖:=add_le_add (R.le_opNorm _) le_rfl
    _≤(1/|z.im|)*‖C x‖+‖x‖:=
      add_le_add (mul_le_mul_of_nonneg_right (resolvent_norm C hC z hz) (norm_nonneg _)) le_rfl
    _=_:=add_comm _ _

private theorem core_action(f:QuantumTest):diagonal (coreEquiv f)=embed (diagonalAction f):=by
  change embed (diagonalAction (coreEquiv.symm (coreEquiv f)))=_
  rw [coreEquiv.symm_apply_apply]

def epsilonGraphPrice(dual:Bool)(e:Epsilon20)(f:ScalarTest)(μ:ℝ):ℝ:=
  ‖embed (epsilonSection dual e f)‖+μ⁻¹*‖embed (diagonalAction (epsilonSection dual e f))‖
def epsilonFrequencyEnvelope(dual:Bool)(e:Epsilon20)(f:ScalarTest)(μ w:ℝ):ℝ:=
  kernel μ 0 w*(epsilonGraphPrice dual e f μ)^2

private theorem causal_im_abs(advanced:Bool)(μ w:ℝ)(hμ:0<μ):
    |(line (FullYPairedParseval.direction advanced*μ) w).im|=μ:=by
  rw [line_im]
  cases advanced <;> simp [FullYPairedParseval.direction,abs_of_pos hμ]
private theorem causal_norm_sq(advanced:Bool)(μ w:ℝ):
    ‖line (FullYPairedParseval.direction advanced*μ) w‖^2=w^2+μ^2:=by
  rw [Complex.sq_norm]
  cases advanced <;> simp [line,FullYPairedParseval.direction,Complex.normSq_apply] <;> ring

/-- An ordinary common upper support, selected before all damping/frequency/cause parameters, generates the actual full sharp-Y frequency domination from its original H0 source jet. -/
theorem actual_epsilon_sharp_cofinal_envelope(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    ∃K0:Index,∀F:Index,K0⊆F →∀(μ:ℝ)(hμ:0<μ)(advanced:Bool)(w:ℝ),
      ‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2≤
        epsilonFrequencyEnvelope dual e f μ w:=by
  classical
  let q:=epsilonSection dual e f
  let x:diagonal.domain:=coreEquiv q
  refine ⟨GaussGradedCompression.support x,fun F hF μ hμ advanced w=>?_⟩
  have hi(g:NativeHistoryGrade.Label):GaussGradedCompression.piece g x∈F:=by
    apply hF
    change GaussGradedCompression.piece g x∈Finset.univ.image (fun g:NativeHistoryGrade.Label=>GaussGradedCompression.piece g x)
    exact Finset.mem_image.mpr ⟨g,Finset.mem_univ g,rfl⟩
  have hc:‖GaussGradedCompression.compression F (embed q)‖≤‖embed (diagonalAction q)‖:=by
    have hx:(x:H)=embed q:=rfl
    have h:=GaussGradedCompression.compression_core_bound F x hi
    rw [hx] at h
    exact h.trans_eq (congrArg norm (core_action q))
  let z:=line (FullYPairedParseval.direction advanced*μ) w
  have hz:z.im≠0:=causal_line_nonreal advanced μ w hμ
  have h:=resolvent_graph_decay (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz (embed q)
  have him:|z.im|=μ:=causal_im_abs advanced μ w hμ
  have hnz:‖z‖^2=w^2+μ^2:=causal_norm_sq advanced μ w
  have hb:‖z‖*‖finiteResolvent F z (embed q)‖≤epsilonGraphPrice dual e f μ:=by
    apply h.trans
    rw [him,one_div]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hμ.le))
  have hs:=pow_le_pow_left₀ (mul_nonneg (norm_nonneg z) (norm_nonneg _)) hb 2
  rw [mul_pow,hnz] at hs
  have hd:0<w^2+μ^2:=by nlinarith [sq_nonneg w,sq_pos_of_pos hμ]
  change ‖embed (literalSharpResolvent F z hz (epsilonSection dual e f))‖^2≤_
  rw [actual_epsilon_sharp_resolvent]
  simp only [epsilonFrequencyEnvelope,kernel,zero_sub,neg_sq]
  change ‖finiteResolvent F z (embed q)‖^2≤(w^2+μ^2)⁻¹*(epsilonGraphPrice dual e f μ)^2
  rw [←div_eq_inv_mul]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hs)

theorem actual_epsilon_envelope_integrable(dual:Bool)(e:Epsilon20)(f:ScalarTest)(μ:ℝ)(hμ:0<μ):
    Integrable (epsilonFrequencyEnvelope dual e f μ):=
  (kernel_integrable μ 0 hμ).mul_const _

/-- The generated envelope pays both ordinary frequency tails, independently of the cutoff. -/
theorem actual_epsilon_sharp_ordinary_common_tail(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    ∃K0:Index,∀(μ:ℝ)(hμ:0<μ)(ε:ℝ),0<ε →∃R:ℝ,0≤R ∧
      ∀F:Index,K0⊆F →∀advanced:Bool,
        (∫w in Ioi R,‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2)+
        (∫w in Iio (-R),‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2)<ε:=by
  obtain ⟨K0,hK⟩:=actual_epsilon_sharp_cofinal_envelope dual e f
  refine ⟨K0,fun μ hμ ε hε=>?_⟩
  let B:=epsilonFrequencyEnvelope dual e f μ
  have hB:Integrable B:=actual_epsilon_envelope_integrable dual e f μ hμ
  have ht:Tendsto (fun R:ℝ=>(∫w in Ioi R,B w)+(∫w in Iio (-R),B w)) atTop (𝓝 0):=by
    have h1:=tendsto_integral_Ioi_zero (f:=B) (μ:=volume) tendsto_id
    have h2:=tendsto_integral_Iio_zero (f:=B) (μ:=volume) tendsto_neg_atTop_atBot
    simpa only [id_eq,add_zero] using h1.add h2
  obtain ⟨R0,hR0⟩:=eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  let R:=max R0 0
  refine ⟨R,le_max_right _ _,fun F hF advanced=>?_⟩
  have hi:=actual_epsilon_sharp_frequency_integrable F advanced μ hμ dual e f
  have hright:(∫w in Ioi R,‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2)≤
      ∫w in Ioi R,B w:=integral_mono_ae hi.integrableOn hB.integrableOn
        (ae_of_all _ (fun w=>hK F hF μ hμ advanced w))
  have hleft:(∫w in Iio (-R),‖embed (literalResponse F true (epsilonSection dual e f) advanced μ hμ w)‖^2)≤
      ∫w in Iio (-R),B w:=integral_mono_ae hi.integrableOn hB.integrableOn
        (ae_of_all _ (fun w=>hK F hF μ hμ advanced w))
  exact lt_of_le_of_lt (add_le_add hright hleft) (hR0 R (le_max_left _ _))

end LowEnergy.NamedColorQtNext
