import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaNormalizedCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarCoefficientTail
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceRadiusHalfSourceBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaNormalizedResponse
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaNormalizedCurrent SourceClockYukawaTail SourceScalarPairedTransport
open SourceScalarPositiveBulkWard SourceMixedNativeReturn SourceRelativePowerTail
open SourceFamilyHilbert SourceFamilyOperator SourceRetardedBandCurrent SourceActualResolventEnergy
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRadiusHalfSourceBudget
open FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph FullYSourceCutoffTimeGraph
open MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
private abbrev L2H := Lp H 2 (MeasureTheory.volume : Measure ℝ)
private abbrev TH := TimeSpace (MeasureTheory.volume : Measure ℝ)
attribute [local irreducible] state normalizedAction normalizedCorrectedCurrent compressionCore

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have h := actual_raised_source F z hz g (1:End)
  simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,
    zero_add,defectAction,LinearMap.sub_apply] at h
  linear_combination (norm := module) h

def response (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : H :=
  finiteResolvent F z (embed (normalizedCorrectedCurrent sharp F (state F z hz g)))

/-- The complete native70, signed spin, matter and compression current returns
to two actual bounded B source profiles at the same F. -/
theorem actual_normalized_response (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    response sharp F z hz g=sourceB sharp (finiteResolvent F z (g:H))-
      finiteResolvent F z (sourceB sharp (g:H)) := by
  let q := state F z hz g
  have hc : compressionCore F (normalizedAction sharp q)-z • normalizedAction sharp q=
      normalizedAction sharp (coreEquiv.symm g)+normalizedCorrectedCurrent sharp F q := by
    rw [←actual_normalized_compression_current]
    simp only [SourceScalarDoubleCurrent.bracket,LinearMap.sub_apply,Module.End.mul_apply,
      show compressionCore F q=coreEquiv.symm g+z • q from compression_equation F z hz g,
      map_add,map_smul]
    module
  have he := congrArg embed hc
  simp only [map_sub,map_smul,map_add,compression_embed] at he
  have hr := congrArg (fun T : Op => T (embed (normalizedAction sharp q)))
    (resolvent_left (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (embed (normalizedAction sharp q))-
    z • embed (normalizedAction sharp q))=embed (normalizedAction sharp q) at hr
  rw [he,map_add] at hr
  rw [←original_normalized_core,←original_normalized_core] at hr
  have hg : embed (coreEquiv.symm g)=(g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  dsimp only [q] at hr
  rw [hg,state_embed] at hr
  unfold response
  linear_combination (norm := module) hr

private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (causalPoint advanced μ w)) := by
  cases advanced
  · exact finite_frequency_continuous μ hμ F
  · have he (w : ℝ) : finiteResolvent F (star (line μ w))=(finiteResolvent F (line μ w)).adjoint := by
      change Ring.inverse (GaussGradedCompression.compression F-star (line μ w) • 1)=
        (Ring.inverse (GaussGradedCompression.compression F-line μ w • 1)).adjoint
      rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
      congr 1
      simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
    have heq : (fun w : ℝ => finiteResolvent F (causalPoint true μ w))=
        (fun w : ℝ => (finiteResolvent F (line μ w)).adjoint) := by
      funext w
      exact he w
    exact heq ▸ (ContinuousLinearMap.adjoint.continuous.comp (finite_frequency_continuous μ hμ F))

private theorem frequency_norm (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) (w : ℝ) :
    ‖finiteResolvent F (causalPoint advanced μ w) g‖=‖finiteResolvent F (line μ w) g‖ := by
  cases advanced
  · rfl
  · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
      (by simpa only [line_im] using hμ.ne') g

private theorem input_memLp (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    MemLp (fun w : ℝ => finiteResolvent F (causalPoint advanced μ w) g) 2 MeasureTheory.volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (((frequency_continuous advanced μ hμ F).clm_apply continuous_const).aestronglyMeasurable)).mpr
  have hi : Integrable (fun w : ℝ => ‖finiteResolvent F (line μ w) g‖^2) := by
    simpa only [line,mul_comm (μ:ℂ) Complex.I] using actual_square_integrable F μ hμ g
  simpa only [frequency_norm advanced μ hμ F g] using hi

private theorem input_ae (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (fun w => value (SourceLocalizedInverseFormPayment.wholeInputFamily advanced μ hμ g) F w)=ᵐ[MeasureTheory.volume]
      (fun w => finiteResolvent F (causalPoint advanced μ w) g) :=
  (input_memLp advanced μ hμ F g).coeFn_toLp

private def responseFamily (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) : Family L2H sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant ((sourceB sharp).compLpL 2 MeasureTheory.volume))
    (SourceLocalizedInverseFormPayment.wholeInputFamily advanced μ hμ g)-
      SourceLocalizedInverseFormPayment.wholeInputFamily advanced μ hμ (sourceB sharp g)

private theorem response_ae (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index)
    (g : diagonal.domain) :
    (fun w => value (responseFamily sharp advanced μ hμ (g:H)) F w)=ᵐ[MeasureTheory.volume]
      (fun w => response sharp F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g) := by
  let f := value (SourceLocalizedInverseFormPayment.wholeInputFamily advanced μ hμ (g:H)) F
  let b := value (SourceLocalizedInverseFormPayment.wholeInputFamily advanced μ hμ (sourceB sharp (g:H))) F
  have hg := input_ae advanced μ hμ F (g:H)
  have hb := input_ae advanced μ hμ F (sourceB sharp (g:H))
  have hm := (sourceB sharp).coeFn_compLpL f
  have hs := Lp.coeFn_sub ((sourceB sharp).compLpL 2 MeasureTheory.volume f) b
  filter_upwards [hs,hm,hg,hb] with w hsw hmw hgw hbw
  change (((sourceB sharp).compLpL 2 MeasureTheory.volume f-b) w)=_
  rw [hsw]
  simp only [Pi.sub_apply]
  rw [hmw]
  change sourceB sharp (value (SourceLocalizedInverseFormPayment.wholeInputFamily advanced μ hμ (g:H)) F w)-
    value (SourceLocalizedInverseFormPayment.wholeInputFamily advanced μ hμ (sourceB sharp (g:H))) F w=_
  rw [hgw,hbw,actual_normalized_response]

private def tailFamily (m ell : ℕ) (f : Family L2H sourceFilter) : Family L2H sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant ((relativeTail m ell).compLpL 2 MeasureTheory.volume)) f

private theorem tail_family_norm (m ell : ℕ) (f : Family L2H sourceFilter) :
    ‖tailFamily m ell f‖=‖familyReader MeasureTheory.volume (relativeTail m ell) (f:TH)‖ := by
  unfold familyReader
  rw [lift_coe,UniformSpace.Completion.norm_coe]
  rfl

attribute [local irreducible] tailFamily

set_option backward.isDefEq.respectTransparency false in
private theorem family_tail (f : Family L2H sourceFilter) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),‖value (tailFamily m ell f) F‖^2 ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := time_space_relative_tail MeasureTheory.volume
    (f:TH) (Real.sqrt (ε/2)) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨N,fun m hm ell hell => ?_⟩
  have he := hN m hm ell hell
  rw [←tail_family_norm] at he
  have hs : ‖tailFamily m ell f‖^2<ε := by
    have hr := Real.sq_sqrt (show 0≤ε/2 by positivity)
    nlinarith only [he,hr,norm_nonneg (tailFamily m ell f),Real.sqrt_nonneg (ε/2)]
  exact ((square_tendsto sourceFilter (tailFamily m ell f)).eventually (gt_mem_nhds hs)).mono
    (fun _ h => h.le)

private theorem response_tail_integral (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index)
    (m ell : ℕ) (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖relativeTail m ell
      (response sharp F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)‖^2))=
      ENNReal.ofReal (‖value (tailFamily m ell (responseFamily sharp advanced μ hμ (g:H))) F‖^2) := by
  let f := responseFamily sharp advanced μ hμ (g:H)
  have he : (fun w : ℝ => ‖relativeTail m ell
      (response sharp F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)‖^2)=ᵐ[MeasureTheory.volume]
      (fun w => ‖value (tailFamily m ell f) F w‖^2) := by
    filter_upwards [(relativeTail m ell).coeFn_compLpL (value f F),response_ae sharp advanced μ hμ F g] with w hT hR
    unfold tailFamily
    change _=‖((relativeTail m ell).compLpL 2 MeasureTheory.volume (value f F)) w‖^2
    rw [hT]
    exact congrArg (fun x : H => ‖relativeTail m ell x‖^2) hR.symm
  have hi := (square_integrable MeasureTheory.volume (value (tailFamily m ell f) F)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),
    integral_congr_ae he,←square_integral]

/-- The original complete normalized current has an internally generated theta
tail on either causal leg; no uniform current bound is asked of the caller. -/
private theorem response_common_tail (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖relativeTail m ell
          (response sharp F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := family_tail (responseFamily sharp advanced μ hμ (g:H)) ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  rw [response_tail_integral sharp advanced μ hμ F m ell g]
  exact ENNReal.ofReal_le_ofReal hF

/-- One source-generated cutoff pays both complete sharp currents on both causal
legs. Every field in normalizedCorrectedCurrent is consumed before taking the tail. -/
theorem actual_normalized_response_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖relativeTail m ell
          (response sharp F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N00,h00⟩ := response_common_tail false false μ hμ g ε hε
  obtain ⟨N01,h01⟩ := response_common_tail false true μ hμ g ε hε
  obtain ⟨N10,h10⟩ := response_common_tail true false μ hμ g ε hε
  obtain ⟨N11,h11⟩ := response_common_tail true true μ hμ g ε hε
  refine ⟨max (max N00 N01) (max N10 N11),fun m hm ell hell => ?_⟩
  filter_upwards [h00 m (by omega) ell hell,h01 m (by omega) ell hell,
    h10 m (by omega) ell hell,h11 m (by omega) ell hell] with F hF00 hF01 hF10 hF11 sharp advanced
  cases sharp <;> cases advanced
  · exact hF00
  · exact hF01
  · exact hF10
  · exact hF11

end LowEnergy.SourceClockYukawaNormalizedResponse
