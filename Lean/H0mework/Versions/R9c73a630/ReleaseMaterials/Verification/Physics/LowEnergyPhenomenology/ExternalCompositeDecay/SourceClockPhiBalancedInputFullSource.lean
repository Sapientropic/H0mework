import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedInputCommonPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeForceNoetherDebit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarInputJointNoether
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare SourceScalarDoubleCurrent
open SourceClockPhiNativeJointPayment SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceJointResidualEnergy SourceBulkTwoTime
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseScalarGaugeWard ReverseForceNoetherPayer
open SourceClockYukawaCubicCurrent SourceInverseNoetherChannelGap SourceFourPoleEnergyClosed
open FinitePhysicalSource
open MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator
attribute [local irreducible] sourcePair embed diagonalAction resolventCore coreEquiv inputSeed balancedInputSeed phaseRow
  balancedInputVector reverseNativeClock SourceGaugeScaleTransport.generator reverseInputVector gaugeInputVector
private def pole(advanced:Bool)(μ a q:ℝ):ℂ:=((a:ℂ)-actualFrequency advanced μ q)⁻¹
private theorem pole_pair(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (fun q:ℝ=>star (pole advanced μ a q)*pole advanced μ b q):=by
  cases advanced
  · simpa only [pole,actualFrequency,Bool.false_eq_true,ite_false,SourceJointResidualEnergy.pole] using! two_pole_integrable μ a b hμ
  · have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (two_pole_integrable μ a b hμ)
    have he(q:ℝ):star (pole true μ a q)*pole true μ b q=star (star (SourceJointResidualEnergy.pole μ a q)*SourceJointResidualEnergy.pole μ b q):=by
      simp only [pole,actualFrequency,ite_true,SourceJointResidualEnergy.pole,star_mul,star_inv₀,star_sub,Complex.star_def,Complex.conj_ofReal]
      ring
    simpa only [he] using! h
private theorem finite_pair {ι:Type*}[Fintype ι](c d:ι→QuantumTest)(a:ι→ℂ):
    sourcePair (∑i,a i • c i) (∑j,a j • d j)=∑i,∑j,(star (a i)*a j)*sourcePair (c i) (d j):=by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  ring
private theorem finite_integrable {ι:Type*}[Fintype ι](a:ι→ℝ)(c d:ι→QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun q:ℝ=>sourcePair (∑i,pole advanced μ (a i) q • c i) (∑i,pole advanced μ (a i) q • d i)):=by
  have hi:Integrable (fun q:ℝ=>∑i,∑j,(star (pole advanced μ (a i) q)*pole advanced μ (a j) q)*sourcePair (c i) (d j)):=
    integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>(pole_pair advanced μ hμ (a i) (a j)).mul_const _))
  exact hi.congr (Eventually.of_forall (fun q=>(finite_pair c d _).symm))
private theorem core_channels(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    resolventCore F z hz (coreEquiv.symm g)=∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • channelTest F g j:=by
  have h:resolventCore F z hz (coreEquiv.symm g)=state F z hz g:=by
    simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
  rw [h,actual_state_channels]
private theorem input_rows(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedInputVector m ell F z hz g=∑i:Fin 2,
      (bracket Zbar (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
        phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (balancedInputSeed g i)))):=by
  have he:=congrArg (fun v:QuantumTest=>v-(9:ℂ) • gaugeInputVector m ell F z hz g)
    (actual_reverse_input_vector m ell F z hz g).symm
  unfold balancedInputVector
  refine he.trans ?_
  simp only [gaugeInputVector,balancedInputSeed,coreEquiv.symm_apply_apply,Finset.smul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro i _
  simp only [Zbar,bracket,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul]
  module

/-- Four actual input columns: the original outer commutators and the two source-generated compensated seeds. -/
def inputSourceColumn(m ell:ℕ)(F:Index)(g:diagonal.domain)(j:Channel F):QuantumTest:=
  ∑i:Fin 2,(bracket Zbar (phaseRow m ell i) (channelTest F (inputSeed g i) j)+
    phaseRow m ell i (channelTest F (balancedInputSeed g i) j))

attribute [local irreducible] inputSourceColumn
theorem actual_balanced_input_channels(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedInputVector m ell F z hz g=
      ∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • inputSourceColumn m ell F g j:=by
  rw [input_rows]
  simp_rw [core_channels,map_sum,map_smul]
  simp only [inputSourceColumn,Finset.smul_sum,smul_add,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_comm

/-- Every actual fixed word on these source inputs has its whole-frequency L1 pair, including escape and all four-column interference. -/
theorem actual_balanced_input_pair_integrable(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(L R:End):
    Integrable (fun q:ℝ=>sourcePair
      (L (balancedInputVector m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g))
      (R (balancedInputVector m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g))):=by
  have h:=finite_integrable (channelValue F) (fun j=>L (inputSourceColumn m ell F g j))
    (fun j=>R (inputSourceColumn m ell F g j)) advanced μ hμ
  exact h.congr (Eventually.of_forall (fun q=>by
    simp only [actual_balanced_input_channels,map_sum,map_smul,pole]))

theorem actual_balanced_input_word_integrable(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (balancedInputVector m ell F
      (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g))‖^2):=by
  have h:=(actual_balanced_input_pair_integrable μ hμ advanced m ell F g L L).re
  apply h.congr
  apply Eventually.of_forall;intro q
  dsimp only
  simp only [sourcePair,inner_self_eq_norm_sq]

private theorem word_source(F:Index)(z:ℂ)(hz:z.im≠0)(L:End)(f:QuantumTest):
    H0 (L (resolventCore F z hz f))=
      L f+wordPhysicalEscape F L (resolventCore F z hz f)+z • L (resolventCore F z hz f):=by
  have h:=(actual_force_response_full_noether F z hz f).1
  simp only [wordPhysicalEscape,bracket,LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,h,map_add,map_smul]
  module

/-- Each actual outer word keeps its own [H0,L]+L deltaF escape. In particular this definition does not substitute a desired forcing or a projection-free CF equation. -/
def balancedInputForcing(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(T:End):QuantumTest:=
  ∑i:Fin 2,((T*bracket Zbar (phaseRow m ell i)) (coreEquiv.symm (inputSeed g i))+
    wordPhysicalEscape F (T*bracket Zbar (phaseRow m ell i))
      (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
    (T*phaseRow m ell i) (coreEquiv.symm (balancedInputSeed g i))+
    wordPhysicalEscape F (T*phaseRow m ell i)
      (resolventCore F z hz (coreEquiv.symm (balancedInputSeed g i))))

attribute [local irreducible] balancedInputForcing
theorem actual_balanced_input_full_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(T:End):
    H0 (T (balancedInputVector m ell F z hz g))=
      balancedInputForcing m ell F z hz g T+z • T (balancedInputVector m ell F z hz g):=by
  rw [input_rows]
  simp only [map_sum,map_add]
  have h(i:Fin 2):
      H0 (T (bracket Zbar (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))))+
      H0 (T (phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (balancedInputSeed g i)))))=
      (T*bracket Zbar (phaseRow m ell i)) (coreEquiv.symm (inputSeed g i))+
      wordPhysicalEscape F (T*bracket Zbar (phaseRow m ell i)) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
      (T*phaseRow m ell i) (coreEquiv.symm (balancedInputSeed g i))+
      wordPhysicalEscape F (T*phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (balancedInputSeed g i)))+
      z • (T (bracket Zbar (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i))))+
        T (phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (balancedInputSeed g i))))):=by
    have h1:=word_source F z hz (T*bracket Zbar (phaseRow m ell i)) (coreEquiv.symm (inputSeed g i))
    have h2:=word_source F z hz (T*phaseRow m ell i) (coreEquiv.symm (balancedInputSeed g i))
    simp only [Module.End.mul_apply] at h1 h2
    linear_combination (norm:=module) h1+h2
  simp_rw [h]
  simp only [balancedInputForcing,Finset.sum_add_distrib,Finset.smul_sum,smul_add]

private theorem channel_resolution(F:Index)(g:diagonal.domain):
    (∑j:Channel F,channelTest F g j)=coreEquiv.symm g:=by
  apply embed_injective
  have h:=actual_core_time F g 0
  simp only [coreTime,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul,
    SourceFiniteUnitary.time_zero,one_apply_eq_self] at h
  with_unfolding_all exact h.trans (congrArg Subtype.val (coreEquiv.apply_symm_apply g)).symm
private theorem two_seed_zero(m ell:ℕ)(F:Index)(g:diagonal.domain):
    (∑i:Fin 2,phaseRow m ell i (coreEquiv.symm (inputSeed g i)))=0:=by
  have h:=actual_source_column_zero (1:End) m ell F g
  unfold sourceColumn at h
  simp only [Module.End.one_apply] at h
  rw [Finset.sum_comm] at h
  simp_rw [←map_sum,channel_resolution] at h
  exact h

private theorem derivative_sum(A:End)(L:Fin 2→End)(u:Fin 2→QuantumTest):
    (∑i:Fin 2,(bracket A (L i) (u i)+L i (A (u i))))=A (∑i:Fin 2,L i (u i)):=by
  rw [map_sum]
  apply Finset.sum_congr rfl;intro i _
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  module

/-- The original compensated input has no constant pole tail: its four columns add to the derivative of the same zero two-seed source. -/
theorem actual_balanced_input_column_zero(m ell:ℕ)(F:Index)(g:diagonal.domain):
    (∑j:Channel F,inputSourceColumn m ell F g j)=0:=by
  simp only [inputSourceColumn,Finset.sum_add_distrib]
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun j i=>phaseRow m ell i (channelTest F (balancedInputSeed g i) j))]
  simp_rw [←map_sum,channel_resolution]
  have hi:(∑i:Fin 2,(bracket Zbar (phaseRow m ell i) (coreEquiv.symm (inputSeed g i))+
      phaseRow m ell i (coreEquiv.symm (balancedInputSeed g i))))=
      Zbar (∑i:Fin 2,phaseRow m ell i (coreEquiv.symm (inputSeed g i))):=by
    simpa only [balancedInputSeed,coreEquiv.symm_apply_apply] using
      derivative_sum Zbar (phaseRow m ell) (fun i=>coreEquiv.symm (inputSeed g i))
  rw [←Finset.sum_add_distrib,hi,two_seed_zero m ell F g,map_zero]

def inputSourceDrift(m ell:ℕ)(F:Index)(g:diagonal.domain)(T:End)(j:Channel F):QuantumTest:=
  H0 (T (inputSourceColumn m ell F g j))-(channelValue F j:ℂ) • T (inputSourceColumn m ell F g j)
attribute [local irreducible] inputSourceDrift
private theorem inverse_source(z:ℂ)(hz:z.im≠0)(a:ℝ)(T:End)(v:QuantumTest):
    H0 (T ((((a:ℂ)-z)⁻¹) • v))-z • T ((((a:ℂ)-z)⁻¹) • v)=
      ((a:ℂ)-z)⁻¹ • (H0 (T v)-(a:ℂ) • T v)+T v:=by
  have hne:(a:ℂ)-z≠0:=by
    intro h
    have hh:=congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hh
    exact hz hh
  have hc:((a:ℂ)-z)⁻¹*(a:ℂ)-z*((a:ℂ)-z)⁻¹=1:=by
    calc _=((a:ℂ)-z)⁻¹*((a:ℂ)-z):=by ring
         _=1:=inv_mul_cancel₀ hne
  simp only [map_smul,smul_sub,smul_smul]
  linear_combination (norm:=module) hc • T v

/-- The complete input forcing has the same actual single poles; its leading constant vanishes by the original two-seed identity. -/
theorem actual_balanced_input_forcing_channels(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(T:End):
    balancedInputForcing m ell F z hz g T=
      ∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • inputSourceDrift m ell F g T j:=by
  have h:=actual_balanced_input_full_source m ell F z hz g T
  have he:balancedInputForcing m ell F z hz g T=
      H0 (T (balancedInputVector m ell F z hz g))-z • T (balancedInputVector m ell F z hz g):=by
    linear_combination (norm:=module) -h
  rw [he,actual_balanced_input_channels]
  simp only [map_sum,Finset.smul_sum,←Finset.sum_sub_distrib]
  simp_rw [inverse_source z hz]
  have hzero:=congrArg T (actual_balanced_input_column_zero m ell F g)
  simp only [map_sum,map_zero] at hzero
  rw [Finset.sum_add_distrib,hzero,add_zero]
  unfold inputSourceDrift
  rfl

theorem actual_balanced_input_forcing_pair_integrable(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(T L R:End):
    Integrable (fun q:ℝ=>sourcePair
      (L (balancedInputForcing m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g T))
      (R (balancedInputVector m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g))):=by
  have h:=finite_integrable (channelValue F) (fun j=>L (inputSourceDrift m ell F g T j))
    (fun j=>R (inputSourceColumn m ell F g j)) advanced μ hμ
  exact h.congr (Eventually.of_forall (fun q=>by
    simp only [actual_balanced_input_forcing_channels,actual_balanced_input_channels,map_sum,map_smul,pole]))
end LowEnergy.ScalarInputJointNoether
