import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualExactSylvesterRawStorage
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterGram
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterMixedFrequency
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualExactSylvesterRawFrequencyBalance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceJointResidualEnergy SourceInverseNoetherChannelGap SourceResolventBandLimit
open ActualSylvesterChannels ActualSylvesterCore ActualSylvesterKernels ActualVectorJointCost
open ActualTwoResolventSylvester ActualExactSylvesterRawStorage ActualTwoResolventCascade
open SourceFourPoleEnergyClosed FullYSourceResolventGraphSplice MeasureTheory SourceRetardedGraph
open ActualSylvesterMixedFrequency SourceCutoffDilationWard ActualVectorJointCost Filter
open Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore

elab "paid_raw_frequency_kernel%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterKernels 0) "LowEnergy") "ActualSylvesterKernels"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing paid causal kernel"
  mkConstWithFreshMVarLevels name

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

private theorem core_resolvent_channels (advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)(w:ℝ)(g:QuantumTest):
    resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g=
      ∑i:Channel F,pole (if advanced then -μ else μ) (channelValue F i) w • channelCore F i g := by
  unfold resolventCore
  change state F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) (coreEquiv g)=_
  rw [actual_state_channels]
  apply Finset.sum_congr rfl
  intro i _
  cases advanced <;> rfl

private theorem pair_channels (advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)(w:ℝ)(Q:End)(g:QuantumTest):
    sourcePair
      (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g)
      (Q (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))=
      ∑i:Channel F,∑j:Channel F,
      (star (pole (if advanced then -μ else μ) (channelValue F i) w)*
        pole (if advanced then -μ else μ) (channelValue F j) w)*
        sourcePair (channelCore F i g) (Q (channelCore F j g)) := by
  rw [core_resolvent_channels advanced F μ hμ]
  simp only [map_sum,map_smul,sourcePair,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem core_pair_integrable (advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)(Q:End)(g:QuantumTest):
    Integrable (fun w:ℝ=>sourcePair
      (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g)
      (Q (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))) := by
  simp_rw [pair_channels advanced F μ hμ]
  exact integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ
    (fun j _=>((paid_raw_frequency_kernel% two_integrable) advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem core_pair_integral (advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)(Q:End)(g:QuantumTest):
    (∫w:ℝ,sourcePair
      (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g)
      (Q (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g)))=
      ∑i:Channel F,∑j:Channel F,twoKernel advanced μ (channelValue F i) (channelValue F j)*
        sourcePair (channelCore F i g) (Q (channelCore F j g)) := by
  have hi (i j:Channel F):Integrable (fun w:ℝ=>
      (star (pole (if advanced then -μ else μ) (channelValue F i) w)*
        pole (if advanced then -μ else μ) (channelValue F j) w)*
        sourcePair (channelCore F i g) (Q (channelCore F j g))) :=
    ((paid_raw_frequency_kernel% two_integrable) advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _
  simp_rw [pair_channels advanced F μ hμ]
  rw [integral_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _=>hi _ j),integral_mul_const,
    (paid_raw_frequency_kernel% two_integral) advanced μ _ _ hμ]

private theorem core_resolution (F:Index)(g:QuantumTest):∑i:Channel F,channelCore F i g=g := by
  apply embed_injective
  simp only [map_sum,actual_channel_core,channel_resolution]

private theorem compression_pair (F:Index)(f g:QuantumTest):
    sourcePair f (compressionCore F g)=sourcePair (compressionCore F f) g := by
  have h:=(GaussGradedCompression.compression_selfAdjoint F).isSymmetric (embed f) (embed g)
  have hc (q:QuantumTest):embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simpa only [sourcePair,hc] using! h.symm

private def frequencyLyapunov (advanced:Bool)(F:Index)(μ:ℝ)(Q:End):End :=
  (2*(μ:ℂ)) • Q-(Complex.I*(causalSign advanced:ℂ)) • (compressionCore F*Q-Q*compressionCore F)

private theorem lyapunov_channel (advanced:Bool)(F:Index)(μ:ℝ)(Q:End)(g:QuantumTest)(i j:Channel F):
    sourcePair (channelCore F i g) (frequencyLyapunov advanced F μ Q (channelCore F j g))=
      (2*(μ:ℂ)-Complex.I*(causalSign advanced:ℂ)*((channelValue F i:ℂ)-(channelValue F j:ℂ)))*
        sourcePair (channelCore F i g) (Q (channelCore F j g)) := by
  have hi:compressionCore F (channelCore F i g)=(channelValue F i:ℂ) • channelCore F i g :=
    actual_channel_eigen F (coreEquiv g) i
  have hj:compressionCore F (channelCore F j g)=(channelValue F j:ℂ) • channelCore F j g :=
    actual_channel_eigen F (coreEquiv g) j
  simp only [frequencyLyapunov,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right]
  have hc:=compression_pair F (channelCore F i g) (Q (channelCore F j g))
  change sourcePair _ _=sourcePair _ _ at hc
  rw [hi] at hc
  simp only [sourcePair,map_smul,inner_smul_left,Complex.conj_ofReal] at hc
  rw [hc,hj]
  simp only [map_smul,inner_smul_right]
  ring

private theorem lyapunov_kernel (advanced:Bool)(μ a b:ℝ)(hμ:0 < μ):
    twoKernel advanced μ a b*(2*(μ:ℂ)-Complex.I*(causalSign advanced:ℂ)*((a:ℂ)-(b:ℂ)))=
      2*(Real.pi:ℂ) := by
  cases advanced
  · simp only [twoKernel,ActualTwoResolventPoleIdentity.twoCoefficient,causalSign,Bool.false_eq_true,ite_false,Complex.ofReal_one,mul_one]
    change (2*(Real.pi:ℂ)/gap μ a b)*(2*(μ:ℂ)-Complex.I*((a:ℂ)-(b:ℂ)))=2*(Real.pi:ℂ)
    have he:2*(μ:ℂ)-Complex.I*((a:ℂ)-(b:ℂ))=gap μ a b := by unfold gap;ring
    rw [he,div_mul_cancel₀ _ (gap_ne μ a b hμ)]
  · simp only [twoKernel,ActualTwoResolventPoleIdentity.twoCoefficient,causalSign,ite_true,Complex.ofReal_neg,Complex.ofReal_one]
    change star (2*(Real.pi:ℂ)/gap μ a b)*(2*(μ:ℂ)-Complex.I*(-1)*((a:ℂ)-(b:ℂ)))=2*(Real.pi:ℂ)
    have he:2*(μ:ℂ)-Complex.I*(-1)*((a:ℂ)-(b:ℂ))=star (gap μ a b) := by
      simp only [gap,star_add,star_mul,star_sub,Complex.star_def,Complex.conj_ofReal,Complex.conj_ofNat,Complex.conj_I]
      ring
    rw [he,star_div₀]
    simp only [Complex.star_def,Complex.conj_ofReal,Complex.conj_ofNat,map_mul]
    exact div_mul_cancel₀ _ (by simpa using (gap_ne μ a b hμ))

/-- Even an unbounded source form is consumed on the actual finite core channel
orbit, including escape; no global bounded realization of Q is required. -/
theorem actual_core_lyapunov_frequency_balance (advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)
    (Q:End)(g:QuantumTest):
    let f:=fun w:ℝ=>sourcePair
      (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g)
      (frequencyLyapunov advanced F μ Q
        (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))
    Integrable f ∧ (∫w:ℝ,f w)=2*(Real.pi:ℂ)*sourcePair g (Q g) := by
  dsimp only
  refine ⟨core_pair_integrable advanced F μ hμ _ g,?_⟩
  rw [core_pair_integral advanced F μ hμ]
  simp_rw [lyapunov_channel,←mul_assoc,lyapunov_kernel advanced μ _ _ hμ,←Finset.mul_sum]
  have hs:(∑i:Channel F,∑j:Channel F,sourcePair (channelCore F i g) (Q (channelCore F j g)))=
      sourcePair (∑i:Channel F,channelCore F i g) (Q (∑j:Channel F,channelCore F j g)) := by
    simp only [sourcePair,map_sum,sum_inner,inner_sum]
    exact Finset.sum_comm
  rw [hs,core_resolution]


private theorem source_mu_positive:0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large

attribute [local irreducible] sourceMu sourceQAction sourceQ lyapunov rawResidual

private theorem lyapunov_source (advanced:Bool)(F:Index)(Q:End):
    frequencyLyapunov advanced F sourceMu Q=lyapunov advanced F Q := by
  unfold frequencyLyapunov lyapunov
  rfl

/-- The complete actual lower block is kept inside one frequency integrand. -/
def rawFrequencyResidual (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  let q:=resolventCore F (causalFrequency advanced sourceMu w)
    (causal_nonreal advanced sourceMu source_mu_positive w) g
  (sourcePair q (rawResidual advanced sharp F m ell q)).re

theorem actual_raw_frequency_residual_integrable (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (rawFrequencyResidual advanced sharp m ell F g) := by
  have hi:=core_pair_integrable advanced F sourceMu source_mu_positive (rawResidual advanced sharp F m ell) g
  exact hi.re.congr (Filter.Eventually.of_forall (fun _=>rfl))

private theorem damping_integrand_integrable (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>sourcePair
      (resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g)
      (lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell)
        (resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g))) :=
  core_pair_integrable advanced F sourceMu source_mu_positive _ g

private theorem actual_source_Q_frequency_balance (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    (∫w:ℝ,(sourcePair
      (resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g)
      (lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell)
        (resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g))).re)=
      4*Real.pi*sourceQ sharp m ell g := by
  have h:=(actual_core_lyapunov_frequency_balance advanced F sourceMu source_mu_positive
    ((2:ℂ) • sourceQAction sharp m ell) g).2
  have he:=lyapunov_source advanced F ((2:ℂ) • sourceQAction sharp m ell)
  rw [he] at h
  have hr:=congrArg Complex.re h
  have hi:=damping_integrand_integrable advanced sharp m ell F g
  have hir:=integral_re hi
  simp only [RCLike.re_to_complex] at hir
  rw [hir,hr]
  have hq:sourcePair g (((2:ℂ) • sourceQAction sharp m ell) g)=
      (2:ℂ)*sourcePair g (sourceQAction sharp m ell g) := by
    simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
  rw [hq]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,zero_mul,mul_zero,sub_zero,(paid_raw_source_Q_energy%)]
  ring


elab "paid_raw_increment_pair%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventCascade 0) "LowEnergy") "ActualTwoResolventCascade") "increment_pair")

private theorem resolvent_embed (F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    embed (resolventCore F z hz g)=finiteResolvent F z (embed g) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private def dampingFrequency (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  let q:=resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g
  (sourcePair q (lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell) q)).re

private def mixedFrequency (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  (frequencyPair advanced F sourceMu (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g) w).re

private theorem actual_residual_frequency_return (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    rawFrequencyResidual advanced sharp m ell F g w=
      dampingFrequency advanced sharp m ell F g w-mixedFrequency advanced sharp m ell F g w := by
  let q:=resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g
  have hd:sourcePair q (literalIncrementAction (!sharp) m ell (exactL advanced sharp F m ell q))=
      sourcePair (literalIncrementAction sharp m ell q) (exactL advanced sharp F m ell q) := by
    simpa only [Bool.not_not] using (paid_raw_increment_pair%) (!sharp) m ell q (exactL advanced sharp F m ell q)
  have hl:sourcePair q (exactL advanced (!sharp) F m ell (literalIncrementAction sharp m ell q))=
      sourcePair (exactL advanced sharp F m ell q) (literalIncrementAction sharp m ell q) := by
    simpa only [exactL,Bool.not_not] using actual_source_core_pair advanced (!sharp) F sourceMu m ell q
      (literalIncrementAction sharp m ell q)
  have hL:embed (exactL advanced sharp F m ell q)=
      ActualTwoResolventSylvester.sourceL advanced F sourceMu (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed q) :=
    actual_source_L_core advanced sharp F sourceMu m ell q
  have hr:embed q=finiteResolvent F (causalFrequency advanced sourceMu w) (embed g) :=
    resolvent_embed F _ _ g
  unfold rawFrequencyResidual dampingFrequency
  change (sourcePair q (rawResidual advanced sharp F m ell q)).re=_
  unfold rawResidual
  simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right,Complex.sub_re]
  change (sourcePair q (lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell) q)).re-
    (sourcePair q (literalIncrementAction (!sharp) m ell (exactL advanced sharp F m ell q))).re-
    (sourcePair q (exactL advanced (!sharp) F m ell (literalIncrementAction sharp m ell q))).re=_
  rw [hd,hl]
  have hm:mixedFrequency advanced sharp m ell F g w=
      (sourcePair (literalIncrementAction sharp m ell q) (exactL advanced sharp F m ell q)+
        sourcePair (exactL advanced sharp F m ell q) (literalIncrementAction sharp m ell q)).re := by
    simp only [mixedFrequency,frequencyPair,sourcePair,←literal_increment_core,hL,hr]
  rw [hm,Complex.add_re]
  change (sourcePair q (lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell) q)).re-
      (sourcePair (literalIncrementAction sharp m ell q) (exactL advanced sharp F m ell q)).re-
      (sourcePair (exactL advanced sharp F m ell q) (literalIncrementAction sharp m ell q)).re=
    (sourcePair q (lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell) q)).re-
      ((sourcePair (literalIncrementAction sharp m ell q) (exactL advanced sharp F m ell q)).re+
        (sourcePair (exactL advanced sharp F m ell q) (literalIncrementAction sharp m ell q)).re)
  ring

/-- The raw lower block returns the actual positive two-R price through a paid
source seed and one whole signed dynamic residual, without a PSD premise. -/
theorem actual_raw_frequency_balance (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    (∫w:ℝ,rawFrequencyResidual advanced sharp m ell F g w)=
      4*Real.pi*sourceQ sharp m ell g-2*sourceMu*
        (∫w:ℝ,‖finiteResolvent F (causalFrequency advanced sourceMu w)
          (SourceEscapeSeedTail.actualIncrement sharp m ell
            (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g)))‖^2) := by
  have hd:Integrable (dampingFrequency advanced sharp m ell F g) :=
    (damping_integrand_integrable advanced sharp m ell F g).re.congr
      (Filter.Eventually.of_forall (fun _=>rfl))
  have hm:Integrable (mixedFrequency advanced sharp m ell F g) :=
    (actual_mixed_frequency_integrable advanced F sourceMu source_mu_positive
      (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)).re.congr
      (Filter.Eventually.of_forall (fun _=>rfl))
  simp_rw [actual_residual_frequency_return]
  rw [integral_sub hd hm]
  have hdv:(∫w:ℝ,dampingFrequency advanced sharp m ell F g w)=4*Real.pi*sourceQ sharp m ell g :=
    actual_source_Q_frequency_balance advanced sharp m ell F g
  rw [hdv]
  have hx:=congrArg Complex.re (actual_mixed_frequency_integral advanced F sourceMu source_mu_positive
    (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g))
  have hi:=actual_mixed_frequency_integrable advanced F sourceMu source_mu_positive
    (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)
  have hir:=integral_re hi
  simp only [RCLike.re_to_complex] at hir
  rw [←hir] at hx
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,mul_zero,sub_zero] at hx
  change (∫w:ℝ,mixedFrequency advanced sharp m ell F g w)=_ at hx
  rw [hx,actual_vector_causal_energy F advanced sourceMu source_mu_positive]

theorem actual_two_resolvent_raw_price (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    (∫w:ℝ,‖finiteResolvent F (causalFrequency advanced sourceMu w)
      (SourceEscapeSeedTail.actualIncrement sharp m ell
        (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g)))‖^2)=
      (2*Real.pi/sourceMu)*sourceQ sharp m ell g-
        (∫w:ℝ,rawFrequencyResidual advanced sharp m ell F g w)/(2*sourceMu) := by
  have h:=actual_raw_frequency_balance advanced sharp m ell F g
  have hm:=source_mu_positive
  field_simp
  nlinarith only [h]

/-- The fixed Q seed is paid internally, before F and causal orientation. -/
theorem actual_two_resolvent_raw_paid_price (sharp:Bool)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →∀F:Index,∀advanced:Bool,
      (∫w:ℝ,‖finiteResolvent F (causalFrequency advanced sourceMu w)
        (SourceEscapeSeedTail.actualIncrement sharp m ell
          (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g)))‖^2)≤
        ε-(∫w:ℝ,rawFrequencyResidual advanced sharp m ell F g w)/(2*sourceMu) := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_raw_initial_tail sharp g (ε*sourceMu/Real.pi)
    (div_pos (mul_pos hε source_mu_positive) Real.pi_pos)
  refine ⟨N,fun m hm ell hml F advanced=>?_⟩
  have h:=hN m hm ell hml F advanced
  rw [actual_raw_initial_value] at h
  rw [actual_two_resolvent_raw_price]
  have hpi:=Real.pi_pos
  have hmu:=source_mu_positive
  have hp: (2*Real.pi/sourceMu)*sourceQ sharp m ell g≤ε := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmu).mpr
    have hs:2*sourceQ sharp m ell g*Real.pi≤ε*sourceMu := by
      exact (le_div_iff₀ hpi).mp h
    nlinarith only [hs]
  linarith only [hp]


private theorem joint_increment_price (advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:H):
    vectorJointCost advanced sharp m ell F sourceMu g≤
      2*(∫w:ℝ,‖finiteResolvent F (causalFrequency advanced sourceMu w)
        (SourceEscapeSeedTail.actualIncrement sharp m ell
          (finiteResolvent F (causalFrequency advanced sourceMu w) g))‖^2)+
      2*hardyPrice advanced sharp m ell F sourceMu g := by
  let u:=fun w:ℝ=>finiteResolvent F (causalFrequency advanced sourceMu w)
    (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F (causalFrequency advanced sourceMu w) g))
  have hi:Integrable (fun w:ℝ=>‖u w‖^2) :=
    actual_vector_causal_integrable F advanced sourceMu source_mu_positive _ g
  have hj:Integrable (fun w:ℝ=>‖jointVector advanced sharp m ell F sourceMu g w‖^2) :=
    actual_vector_causal_integrable F advanced sourceMu source_mu_positive _ g
  have hh:=actual_hardy_vector_integrable advanced sharp m ell F sourceMu source_mu_positive g
  have hb (w:ℝ):‖jointVector advanced sharp m ell F sourceMu g w‖^2≤
      2*(‖u w‖^2+‖hardyVector advanced sharp m ell F sourceMu g w‖^2) := by
    have he:=actual_increment_vector_split advanced sharp m ell F sourceMu source_mu_positive g w
    change u w=jointVector advanced sharp m ell F sourceMu g w+hardyVector advanced sharp m ell F sourceMu g w at he
    have hl:jointVector advanced sharp m ell F sourceMu g w=
        u w+(-hardyVector advanced sharp m ell F sourceMu g w) := by rw [he];abel
    rw [hl]
    have hn:=norm_add_le (u w) (-hardyVector advanced sharp m ell F sourceMu g w)
    rw [norm_neg] at hn
    have hs:=pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith only [hs,sq_nonneg (‖u w‖-‖hardyVector advanced sharp m ell F sourceMu g w‖)]
  have he:=integral_mono hj ((hi.add hh).const_mul 2) hb
  rw [integral_const_mul] at he
  change (∫w:ℝ,‖jointVector advanced sharp m ell F sourceMu g w‖^2)≤
    2*(∫w:ℝ,‖u w‖^2+‖hardyVector advanced sharp m ell F sourceMu g w‖^2) at he
  rw [integral_add hi hh,actual_hardy_vector_energy advanced sharp m ell F sourceMu source_mu_positive g] at he
  have hjv:(∫w:ℝ,‖jointVector advanced sharp m ell F sourceMu g w‖^2)=
      vectorJointCost advanced sharp m ell F sourceMu g :=
    actual_vector_joint_energy advanced sharp m ell F sourceMu source_mu_positive g
  rw [hjv] at he
  exact he.trans_eq (by ring)

/-- The original full-vector joint price now reads the entire source-generated
raw residual. Hardy and the fixed Q seed are paid on one event, before both causes. -/
theorem actual_vector_joint_raw_paid_price (sharp:Bool)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        vectorJointCost advanced sharp m ell F sourceMu (embed g)≤
          ε-(∫w:ℝ,rawFrequencyResidual advanced sharp m ell F g w)/sourceMu := by
  intro ε hε
  obtain ⟨N0,h0⟩:=actual_two_resolvent_raw_paid_price sharp g (ε/4) (by positivity)
  obtain ⟨N1,h1⟩:=actual_hardy_price_causal_tail sharp sourceMu source_mu_positive (coreEquiv g) (ε/4) (by positivity)
  refine ⟨max N0 N1,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml] with F hF
  intro advanced
  have hi:=h0 m (by omega) ell hml F advanced
  have hh:hardyPrice advanced sharp m ell F sourceMu (embed g)≤ε/4 := hF advanced
  have hj:=joint_increment_price advanced sharp m ell F (embed g)
  have hm:=source_mu_positive
  have hd:(∫w:ℝ,rawFrequencyResidual advanced sharp m ell F g w)/sourceMu=
      2*((∫w:ℝ,rawFrequencyResidual advanced sharp m ell F g w)/(2*sourceMu)) := by ring
  rw [hd]
  linarith only [hi,hh,hj]

end LowEnergy.ActualExactSylvesterRawFrequencyBalance
