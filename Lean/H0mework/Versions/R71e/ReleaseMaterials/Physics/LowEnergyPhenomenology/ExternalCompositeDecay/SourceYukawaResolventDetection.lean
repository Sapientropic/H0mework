import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleBalance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.YukawaResolventDetection
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussYukawaCoefficient GaussYukawaOperator
open FullYSourceResolventGraphSplice SourceResolventBandLimit GeneralThreeParticleResponse
open SourceClockYukawaCubicCurrent FullYDynamicSource
open Filter MeasureTheory
open scoped Topology InnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem original_resolvent_eq (A : E →L[ℂ] E) (z : ℂ) :
    FullYSourceResolventGraphSplice.resolvent A z = _root_.resolvent (-A) (-z) := by
  unfold FullYSourceResolventGraphSplice.resolvent _root_.resolvent
  congr 1
  rw [Algebra.algebraMap_eq_smul_one]
  module

theorem line_resolvent_tendsto_zero (A : E →L[ℂ] E) (c : ℝ) :
    Tendsto (fun ω : ℝ => FullYSourceResolventGraphSplice.resolvent A (line c ω))
      atTop (𝓝 0) := by
  have hl : Tendsto (fun ω : ℝ => -line c ω) atTop (Bornology.cobounded ℂ) := by
    have h := (tendsto_const_sub_cobounded (-(c : ℂ) * Complex.I)).comp
      (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
    convert h using 1
    funext ω
    change -((ω : ℂ) + (c : ℂ) * Complex.I) = -(c : ℂ) * Complex.I - (ω : ℂ)
    ring
  simpa only [original_resolvent_eq, Function.comp_def] using
    (spectrum.resolvent_tendsto_cobounded (-A)).comp hl

theorem scaled_line_resolvent_tendsto (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun ω : ℝ => line c ω • FullYSourceResolventGraphSplice.resolvent A (line c ω))
      atTop (𝓝 (-1)) := by
  have h := ((line_resolvent_tendsto_zero A c).mul_const A).sub_const 1
  have he (ω : ℝ) :
      FullYSourceResolventGraphSplice.resolvent A (line c ω) * A - 1 =
        line c ω • FullYSourceResolventGraphSplice.resolvent A (line c ω) := by
    rw [resolvent_compression A hA _ (by simpa only [line_im] using hc)]
    abel
  simpa only [zero_mul, zero_sub, he] using h

/-- A generated nonzero bounded source reader cannot annihilate the entire
frequency line of any one actual self-adjoint compression. -/
theorem exists_reader_resolvent_nonzero (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (B : E →L[ℂ] E) (q : E) (hq : B q ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    ∃ω : ℝ, B (FullYSourceResolventGraphSplice.resolvent A (line c ω) q) ≠ 0 := by
  by_contra! hz
  have hv := ((ContinuousLinearMap.apply ℂ E q).continuous.tendsto (-1)).comp
    (scaled_line_resolvent_tendsto A hA c hc)
  have hb := (B.continuous.tendsto _).comp hv
  have hz' : (fun ω : ℝ => B ((line c ω •
      FullYSourceResolventGraphSplice.resolvent A (line c ω)) q)) = fun _ => 0 := by
    funext ω
    simp only [smul_apply, map_smul, hz ω, smul_zero]
  change Tendsto (fun ω : ℝ => B ((line c ω •
      FullYSourceResolventGraphSplice.resolvent A (line c ω)) q))
    atTop (𝓝 (B ((-1 : E →L[ℂ] E) q))) at hb
  rw [hz'] at hb
  have he : (0 : E) = B ((-1 : E →L[ℂ] E) q) :=
    tendsto_nhds_unique tendsto_const_nhds hb
  have he' : -(B q) = 0 := by
    simpa only [neg_apply, one_apply_eq_self, map_neg] using he.symm
  exact hq (neg_eq_zero.mp he')

end Hilbert

theorem normalized_zero_of_original_zero (q : QuantumTest) (hq : originalAction q = 0) :
    GaussYukawaOperator.bounded (embed q) = 0 := by
  rw [bounded_core]
  have hz : GaussYukawaCoefficient.action q = 0 := by
    apply DFunLike.ext
    intro z
    have hs := congrArg (fun f : QuantumTest => f z) hq
    change sourceMap (GaussNativePotential.scalarField z) (q z) = 0 at hs
    have hr := congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (q z)) (radius_return z)
    have hv : (radius z : ℝ) • normalized z (q z) = 0 := hr.trans hs
    exact (smul_eq_zero.mp hv).resolve_left (radius_pos z).ne'
  rw [hz, map_zero]

private theorem core_resolvent_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) :
    embed (resolventCore F z hz q) = finiteResolvent F z (embed q) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The original unbounded Y is detected through its already-generated
bounded factor Y/r, so no finite-Y extension or extra source budget is needed. -/
theorem actual_first_Y_leg_nonzero (F : Index) (q : QuantumTest)
    (hq : GaussYukawaOperator.bounded (embed q) ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    ∃ω : ℝ, leg F (line c ω) (by simpa only [line_im] using hc) q 1 ≠ 0 := by
  obtain ⟨ω,hω⟩ := exists_reader_resolvent_nonzero (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) GaussYukawaOperator.bounded
    (embed q) hq c hc
  refine ⟨ω,?_⟩
  intro hz
  let z := line c ω
  have hn : z.im ≠ 0 := by simpa only [z,line_im] using hc
  let r := resolventCore F z hn q
  have hy : resolventCore F z hn (originalAction r) = 0 := by
    change -resolventCore F z hn (originalAction r) = 0 at hz
    exact neg_eq_zero.mp hz
  have he : finiteResolvent F z (embed (originalAction r)) = 0 := by
    rw [←core_resolvent_embed F z hn (originalAction r),hy,map_zero]
  have hi := congrArg (fun v : H => (GaussGradedCompression.compression F - z • 1) v) he
  have inv := congrArg (fun A : H →L[ℂ] H => A (embed (originalAction r)))
    (resolvent_right (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hn)
  have he' : embed (originalAction r) = 0 := by
    simpa only [mul_apply_eq_comp,one_apply_eq_self,map_zero] using inv.symm.trans hi
  have hy' : originalAction r = 0 := embed_injective (he'.trans (map_zero embed).symm)
  have hb := normalized_zero_of_original_zero r hy'
  rw [core_resolvent_embed] at hb
  exact hω hb

end LowEnergy.YukawaResolventDetection
