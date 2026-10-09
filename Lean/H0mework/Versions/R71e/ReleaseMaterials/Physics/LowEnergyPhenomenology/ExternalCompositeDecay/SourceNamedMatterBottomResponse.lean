import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterPrimalChannelPrice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussFockPair
open FullYDynamicSource FullYSourceResolventGraphSplice SourceClockYukawaCubicCurrent SourceScalarPairedTransport
open GaussCoreLabel GaussYukawaGrade GaussYukawaInteraction NativeHistoryGrade
open FullYDynamicResponse SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace
local instance bottomLabelFintype:Fintype Label:=Fintype.ofFinite _
attribute [local irreducible] embed sourcePair GaussYukawaGrade.grade
  GaussCoreLabel.project GaussDiagonalHistory.diagonalAction

private theorem project_bottom(n:Fin 505)(f:QuantumTest):gradeCore (project (n,0) f)=0:=by
  apply embed_injective
  rw [←grade_core,embed_project,map_zero]
  have h:=congrArg (fun A:H→L[ℂ]H=>A (embed f)) (source_grade_right (n,0))
  simpa only [mul_apply_eq_comp,_root_.smul_apply,Fin.val_zero,Nat.cast_zero,zero_smul] using h

private theorem core_embed(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_embed(F:Index)(f:QuantumTest):
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem project_compression(F:Index)(l:Label)(f:QuantumTest):
    project l (compressionCore F f)=compressionCore F (project l f):=by
  apply embed_injective
  simp only [embed_project,compression_embed]
  exact congrArg (fun A:H→L[ℂ]H=>A (embed f)) (GaussGradedCompression.compression_commutes F l).eq

private theorem project_original_zero(n:Fin 505)(f:QuantumTest):
    project (n,0) (GaussYukawaOperator.originalAction f)=0:=by
  apply pair_separates
  intro h
  rw [project_pair]
  have hp:=GaussFullHamiltonian.yukawa_pair f (project (n,0) h)
  rw [actual_bottom_sharp_action _ (project_bottom n h)] at hp
  have he:=congrArg (starRingEnd ℂ) hp
  simp only [sourcePair,map_zero,inner_zero_right,inner_conj_symm,map_zero] at he
  simp only [sourcePair,map_zero,inner_zero_right]
  exact he.symm

/-- The original label projector reads the full primal inverse as its exact base response; Y is cancelled by the actual bottom-grade source law. -/
theorem actual_bottom_primal_projected_resolvent(F:Index)(n:Fin 505)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    project (n,0) (literalCoreResolvent F z hz g)=resolventCore F z hz (project (n,0) g):=by
  let u:=literalCoreResolvent F z hz g
  have h:=LinearMap.congr_fun (literal_core_right_inverse F z hz) g
  change compressionCore F u+GaussYukawaOperator.originalAction u-z • u=g at h
  have hp:=congrArg (project (n,0)) h
  simp only [map_sub,map_add,map_smul,project_compression,project_original_zero,add_zero] at hp
  have hv:=congrArg embed hp
  simp only [map_sub,map_smul,compression_embed,embed_project] at hv
  apply embed_injective
  rw [embed_project,core_embed,embed_project]
  let R:=finiteResolvent F z
  have hl:=congrArg (fun A:H→L[ℂ]H=>A (projection (n,0) (embed u)))
    (resolvent_left (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change R (GaussGradedCompression.compression F (projection (n,0) (embed u))-
    z • projection (n,0) (embed u))=projection (n,0) (embed u) at hl
  rw [hv] at hl
  exact hl.symm

/-- This equality concerns the actual fullY output before every spin/colour reader, on the whole physical number-n bottom-grade field. -/
theorem actual_bottom_primal_hilbert_response(F:Index)(n:Fin 505)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    projection (n,0) (embed (literalResponse F false g advanced μ hμ w))=
      finiteResolvent F (line (FullYPairedParseval.direction advanced*μ) w) (embed (project (n,0) g)):=by
  rw [←embed_project]
  change embed (project (n,0) (literalCoreResolvent F _ _ g))=_
  rw [actual_bottom_primal_projected_resolvent,core_embed]

private theorem bottom_response_norm(F:Index)(n:Fin 505)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    ‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2=
      ‖finiteResolvent F (line μ w) (embed (project (n,0) g))‖^2:=by
  rw [actual_bottom_primal_hilbert_response]
  cases advanced with
  | false=>simp only [FullYPairedParseval.direction,Bool.false_eq_true,ite_false,one_mul]
  | true=>
    simp only [FullYPairedParseval.direction,ite_true,neg_one_mul]
    have he:line (-μ) w=star (line μ w):=by
      apply Complex.ext <;> simp [line,Complex.mul_re,Complex.mul_im]
    rw [he,SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
      (by simpa only [line_im] using hμ.ne')]

/-- All cutoff dependence drops out of this positive full-frequency price, with arbitrary complete forcing and either causal branch. -/
theorem actual_bottom_primal_positive_price(F:Index)(n:Fin 505)(g:QuantumTest)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun w:ℝ=>‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2) ∧
    (∫w:ℝ,‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2)=
      Real.pi/μ*‖projection (n,0) (embed g)‖^2:=by
  simp_rw [bottom_response_norm]
  rw [←embed_project]
  constructor
  · simpa only [line,mul_comm (μ:ℂ) Complex.I] using
      SourceActualResolventEnergy.actual_square_integrable F μ hμ (embed (project (n,0) g))
  · simpa only [line,mul_comm (μ:ℂ) Complex.I] using
      SourceActualResolventEnergy.actual_square_integral F μ hμ (embed (project (n,0) g))

attribute [local irreducible] finiteResolvent projection literalResponse
  GaussGradedCompression.compression SourceHamiltonianSpectralFrequency.profile

/-- The original fullY projected response generates one finite positive source measure before damping and the two causal choices. -/
theorem actual_bottom_primal_source_measure(n:Fin 505)(g:QuantumTest):
    ∃ν:Measure ℝ,IsFiniteMeasure ν ∧ ν Set.univ=ENNReal.ofReal (‖projection (n,0) (embed g)‖^2) ∧
    ∀(μ:ℝ)(hμ:0<μ),Integrable (SourceHamiltonianSpectralFrequency.profile ν μ) ∧
      (∫w:ℝ,SourceHamiltonianSpectralFrequency.profile ν μ w)=
        Real.pi/μ*‖projection (n,0) (embed g)‖^2 ∧
      ∀advanced:Bool,Filter.Tendsto
        (fun F:Index=>∫w:ℝ,|‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2-
          SourceHamiltonianSpectralFrequency.profile ν μ w|) (sourceFilter:Filter Index) (nhds 0):=by
  let x:GaussDiagonalHistory.diagonal.domain:=coreEquiv (project (n,0) g)
  obtain ⟨ν,hν,hm,hlim⟩:=SourceHamiltonianSpectralFrequency.actual_source_frequency_measure x
  have hx:(x:H)=projection (n,0) (embed g):=embed_project (n,0) g
  refine ⟨ν,hν,?_,fun μ hμ=>?_⟩
  · simpa only [hx] using hm
  · obtain ⟨hi,hp,ht⟩:=hlim μ hμ
    refine ⟨hi,?_,fun advanced=>?_⟩
    · simpa only [hx] using hp
    · have hq:(x:H)=embed (project (n,0) g):=rfl
      have he(F:Index)(w:ℝ):
          |‖finiteResolvent F (line μ w) (x:H)‖^2-SourceHamiltonianSpectralFrequency.profile ν μ w|=
          |‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2-
            SourceHamiltonianSpectralFrequency.profile ν μ w|:=
        congrArg (fun r:ℝ=>|r-SourceHamiltonianSpectralFrequency.profile ν μ w|)
          ((congrArg (fun v:H=>‖finiteResolvent F (line μ w) v‖^2) hq).trans
            (bottom_response_norm F n g advanced μ hμ w).symm)
      apply ht.congr'
      exact Filter.Eventually.of_forall (fun F=>integral_congr_ae (ae_of_all _ (he F)))

private theorem graph_decay {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
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

private theorem core_action(f:QuantumTest):
    GaussDiagonalHistory.diagonal (coreEquiv f)=embed (GaussDiagonalHistory.diagonalAction f):=by
  change embed (GaussDiagonalHistory.diagonalAction (coreEquiv.symm (coreEquiv f)))=_
  rw [coreEquiv.symm_apply_apply]

def bottomGraphPrice(n:Fin 505)(g:QuantumTest)(μ:ℝ):ℝ:=
  ‖embed (project (n,0) g)‖+μ⁻¹*‖embed (GaussDiagonalHistory.diagonalAction (project (n,0) g))‖

/-- The original fullY output has a common frequency envelope generated from its projected H0 source jet. -/
theorem actual_bottom_primal_cofinal_envelope(n:Fin 505)(g:QuantumTest):
    ∃K0:Index,∀F:Index,K0⊆F →∀(μ:ℝ)(hμ:0<μ)(advanced:Bool)(w:ℝ),
      ‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2≤
        SourceResolventLorentzian.kernel μ 0 w*(bottomGraphPrice n g μ)^2:=by
  classical
  let q:=project (n,0) g
  let x:GaussDiagonalHistory.diagonal.domain:=coreEquiv q
  refine ⟨GaussGradedCompression.support x,fun F hF μ hμ advanced w=>?_⟩
  have hi(l:Label):GaussGradedCompression.piece l x∈F:=by
    apply hF
    change GaussGradedCompression.piece l x∈Finset.univ.image (fun l:Label=>GaussGradedCompression.piece l x)
    exact Finset.mem_image.mpr ⟨l,Finset.mem_univ l,rfl⟩
  have hc:‖GaussGradedCompression.compression F (embed q)‖≤‖embed (GaussDiagonalHistory.diagonalAction q)‖:=by
    have hx:(x:H)=embed q:=rfl
    have h:=GaussGradedCompression.compression_core_bound F x hi
    rw [hx] at h
    exact h.trans_eq (congrArg norm (core_action q))
  let z:=line μ w
  have hz:z.im≠0:=by simpa only [z,line_im] using hμ.ne'
  have hb:‖z‖*‖finiteResolvent F z (embed q)‖≤bottomGraphPrice n g μ:=by
    simp only [finiteResolvent]
    apply (graph_decay (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz (embed q)).trans
    rw [show z.im=μ from line_im μ w,abs_of_pos hμ,one_div]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hμ.le))
  have hnz:‖z‖^2=w^2+μ^2:=by rw [Complex.sq_norm]; simp [z,line,Complex.normSq_apply]; ring
  have hs:=pow_le_pow_left₀ (mul_nonneg (norm_nonneg z) (norm_nonneg _)) hb 2
  rw [mul_pow,hnz] at hs
  have hd:0<w^2+μ^2:=by nlinarith [sq_nonneg w,sq_pos_of_pos hμ]
  rw [bottom_response_norm]
  simp only [SourceResolventLorentzian.kernel,zero_sub,neg_sq]
  rw [←div_eq_inv_mul]
  exact (le_div_iff₀ hd).mpr ((le_of_eq (mul_comm _ _)).trans hs)

/-- Ordinary cofinal cutoffs share both frequency tails for the complete projected primal field. -/
theorem actual_bottom_primal_ordinary_common_tail(n:Fin 505)(g:QuantumTest):
    ∃K0:Index,∀(μ:ℝ)(hμ:0<μ)(ε:ℝ),0<ε →∃R:ℝ,0≤R ∧∀F:Index,K0⊆F →∀advanced:Bool,
      (∫w in Set.Ioi R,‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2)+
      (∫w in Set.Iio (-R),‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2)<ε:=by
  obtain ⟨K0,hK⟩:=actual_bottom_primal_cofinal_envelope n g
  refine ⟨K0,fun μ hμ ε hε=>?_⟩
  let B:=fun w:ℝ=>SourceResolventLorentzian.kernel μ 0 w*(bottomGraphPrice n g μ)^2
  have hB:Integrable B:=(SourceResolventLorentzian.kernel_integrable μ 0 hμ).mul_const _
  have ht:Filter.Tendsto (fun R:ℝ=>(∫w in Set.Ioi R,B w)+(∫w in Set.Iio (-R),B w)) Filter.atTop (nhds 0):=by
    have h1:=tendsto_integral_Ioi_zero (f:=B) (μ:=volume) Filter.tendsto_id
    have h2:=tendsto_integral_Iio_zero (f:=B) (μ:=volume) Filter.tendsto_neg_atTop_atBot
    simpa only [id_eq,add_zero] using h1.add h2
  obtain ⟨R0,hR0⟩:=Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  let R:=max R0 0
  refine ⟨R,le_max_right _ _,fun F hF advanced=>?_⟩
  have hi:=(actual_bottom_primal_positive_price F n g advanced μ hμ).1
  have hr:(∫w in Set.Ioi R,‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2)≤∫w in Set.Ioi R,B w:=
    integral_mono_ae hi.integrableOn hB.integrableOn (ae_of_all _ (hK F hF μ hμ advanced))
  have hl:(∫w in Set.Iio (-R),‖projection (n,0) (embed (literalResponse F false g advanced μ hμ w))‖^2)≤∫w in Set.Iio (-R),B w:=
    integral_mono_ae hi.integrableOn hB.integrableOn (ae_of_all _ (hK F hF μ hμ advanced))
  exact lt_of_le_of_lt (add_le_add hr hl) (hR0 R (le_max_left _ _))

end LowEnergy.NamedColorQtNext
