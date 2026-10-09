import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterFourChannelResponse
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterWedgeResponse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open FullYDynamicSource FullYDynamicResponse FullYSourceResolventGraphSplice SourceResolventBandLimit
open GaussCoreLabel NativeHistoryGrade NamedMatterWedgeQt GaussDensityCore MeasureTheory
open scoped BigOperators InnerProductSpace
attribute [local irreducible] embed literalCoreResolvent GaussCoreLabel.project NativeHistoryGrade.projection

private def channelLabel(j:Fin 4):Label:=(3,⟨j.val,by omega⟩)
private theorem projected_word(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest)(i j:Fin 4):
    projection (channelLabel i) (embed (originalWedgeLeg F z hz dual a f j.val))=
      if i=j then embed (originalWedgeLeg F z hz dual a f j.val) else 0:=by
  have hj:projection (channelLabel j) (embed (originalWedgeLeg F z hz dual a f j.val))=
      embed (originalWedgeLeg F z hz dual a f j.val):=
    (embed_project (channelLabel j) _).symm.trans (congrArg embed (actual_four_channel_sector F z hz dual a f j))
  by_cases hij:i=j
  · subst j
    simpa only [if_true] using hj
  · have hneq:channelLabel i≠channelLabel j:=by intro h; exact hij (Fin.ext (congrArg (fun l:Label=>l.2.val) h))
    have h:=congrArg (fun T:H→L[ℂ]H=>T (embed (originalWedgeLeg F z hz dual a f j.val)))
      (projection_product (channelLabel i) (channelLabel j))
    simp only [if_neg hneq,mul_apply_eq_comp,zero_apply,hj] at h
    simpa only [if_neg hij] using h

/-- These are physical output readers of the original fullY response, not independently supplied channel states. -/
def gradeChannelResponse(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)
    (j:Fin 4)(w:ℝ):H:=projection (channelLabel j) (wedgeResponse F dual false advanced a f μ hμ w)

/-- The actual output reader is exactly the corresponding interleaved original resolvent/Y word. -/
theorem actual_grade_channel_word(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)
    (j:Fin 4)(w:ℝ):gradeChannelResponse F dual advanced a f μ hμ j w=
      embed (originalWedgeLeg F (line (FullYPairedParseval.direction advanced*μ) w)
        (causal_line_nonreal advanced μ w hμ) dual a f j.val):=by
  simp only [gradeChannelResponse,wedgeResponse,literalResponse,Bool.false_eq_true,if_false]
  rw [actual_fullY_four_channel_response,map_sum,map_sum]
  simp only [projected_word]
  simp

theorem actual_grade_channel_integrable(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)
    (j:Fin 4):Integrable (fun w:ℝ=>‖gradeChannelResponse F dual advanced a f μ hμ j w‖^2):=by
  have hc:Continuous (fun w:ℝ=>gradeChannelResponse F dual advanced a f μ hμ j w):=
    (projection (channelLabel j)).continuous.comp
      (CompositeFullYBorn.actual_response_continuous F false (wedgeTest dual a f) advanced μ hμ)
  apply (actual_wedge_response_frequency F dual false advanced a f μ hμ).mono' (hc.norm.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  change ‖projection (channelLabel j) (wedgeResponse F dual false advanced a f μ hμ w)‖≤_
  simpa only [NativeHistoryGrade.projection] using!
    piece_bound (channelLabel j) (wedgeResponse F dual false advanced a f μ hμ w)

theorem actual_complete_grade_intensity(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    ‖wedgeResponse F dual false advanced a f μ hμ w‖^2=
      ∑j:Fin 4,‖gradeChannelResponse F dual advanced a f μ hμ j w‖^2:=by
  simp_rw [actual_grade_channel_word]
  exact actual_fullY_four_channel_norm F _ _ dual a f

/-- Every one of the four actual original-Y channels produces a positive finite Borel measure. -/
def gradeChannelMeasure(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)(j:Fin 4):Measure ℝ:=
  volume.withDensity (fun w=>ENNReal.ofReal (‖gradeChannelResponse F dual advanced a f μ hμ j w‖^2))

theorem actual_grade_channel_measure(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)(j:Fin 4):
    (∀B:Set ℝ,MeasurableSet B → gradeChannelMeasure F dual advanced a f μ hμ j B=
      ENNReal.ofReal (∫w in B,‖gradeChannelResponse F dual advanced a f μ hμ j w‖^2)) ∧
      IsFiniteMeasure (gradeChannelMeasure F dual advanced a f μ hμ j):=by
  have hi:=actual_grade_channel_integrable F dual advanced a f μ hμ j
  have he(B:Set ℝ)(hB:MeasurableSet B):gradeChannelMeasure F dual advanced a f μ hμ j B=
      ENNReal.ofReal (∫w in B,‖gradeChannelResponse F dual advanced a f μ hμ j w‖^2):=by
    rw [gradeChannelMeasure,withDensity_apply _ hB]
    exact (ofReal_integral_eq_lintegral_ofReal hi.restrict (Filter.Eventually.of_forall (fun _=>sq_nonneg _))).symm
  exact ⟨he,⟨by rw [he Set.univ MeasurableSet.univ];exact ENNReal.ofReal_lt_top⟩⟩

/-- The four source-generated grades exhaust the original inclusive Born measure on every Borel set. -/
theorem actual_fullY_grade_Born_measure(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)
    (B:Set ℝ)(hB:MeasurableSet B):
    wedgeResponseMeasure F dual false advanced a f μ hμ B=
      ∑j:Fin 4,gradeChannelMeasure F dual advanced a f μ hμ j B:=by
  rw [(actual_wedge_response_measure F dual false advanced a f μ hμ).1 B hB]
  simp_rw [(actual_grade_channel_measure F dual advanced a f μ hμ _).1 B hB]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun j _=>integral_nonneg (fun _=>sq_nonneg _))]
  congr 1
  calc
    _=∫w in B,∑j:Fin 4,‖gradeChannelResponse F dual advanced a f μ hμ j w‖^2:=
      integral_congr_ae (Filter.Eventually.of_forall (actual_complete_grade_intensity F dual advanced a f μ hμ))
    _=_:=integral_finsetSum Finset.univ (fun j _=>(actual_grade_channel_integrable F dual advanced a f μ hμ j).restrict)

def actualLeakageDensity(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ)(w:ℝ):ℝ:=
  ∑j:Fin 3,‖gradeChannelResponse F dual advanced a f μ hμ j.succ w‖^2

theorem actual_leakage_integrable(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ):
    Integrable (actualLeakageDensity F dual advanced a f μ hμ):=
  integrable_finsetSum Finset.univ (fun j _=>actual_grade_channel_integrable F dual advanced a f μ hμ j.succ)

/-- The entire positive response budget equals the cutoff-independent bottom price plus the three explicit original-Y leakage intensities. -/
theorem actual_fullY_positive_leakage_balance(F:Index)(dual advanced:Bool)(a:WedgeFiber)(f:ScalarTest)(μ:ℝ)(hμ:0<μ):
    (∫w:ℝ,‖wedgeResponse F dual false advanced a f μ hμ w‖^2)=
      Real.pi/μ*(‖a‖^2*‖scalarLp 3 f‖^2)+∫w:ℝ,actualLeakageDensity F dual advanced a f μ hμ w:=by
  have he(w:ℝ):‖wedgeResponse F dual false advanced a f μ hμ w‖^2=
      ‖gradeChannelResponse F dual advanced a f μ hμ 0 w‖^2+actualLeakageDensity F dual advanced a f μ hμ w:=by
    rw [actual_complete_grade_intensity,Fin.sum_univ_succ]
    rfl
  have hp: (∫w:ℝ,‖gradeChannelResponse F dual advanced a f μ hμ 0 w‖^2)=
      Real.pi/μ*(‖a‖^2*‖scalarLp 3 f‖^2):=by
    have h:=(actual_bottom_primal_positive_price F 3 (wedgeTest dual a f) advanced μ hμ).2
    have hi:projection (3,0) (embed (wedgeTest dual a f))=embed (wedgeTest dual a f):=
      (embed_project (3,0) _).symm.trans (congrArg embed (actual_wedge_bottom_sector dual a f))
    rw [hi,actual_wedge_source_norm,mul_pow] at h
    exact h
  simp_rw [he]
  rw [integral_add (actual_grade_channel_integrable F dual advanced a f μ hμ 0)
    (actual_leakage_integrable F dual advanced a f μ hμ),hp]

end LowEnergy.NamedColorQtNext
