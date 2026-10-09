import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.GeneralThreeParticleResponse
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussFockPair
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse FullYSourceResolventGraphSplice
open SourceClockYukawaCubicCurrent GaussCoreLabel NativeHistoryGrade NamedColorQtNext CompositeFullYBorn
open SourceResolventBandLimit SourceResolventLorentzian SourceQuantumConfigurationHilbert
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace ENNReal
attribute [local irreducible] embed sourcePair GaussCoreLabel.project NativeHistoryGrade.projection
  literalCoreResolvent literalSharpResolvent

def originalYCorrection (F : Index) (q : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (w : ℝ) : H :=
  embed (literalResponse F false q advanced μ hμ w) -
    projection (3,0) (embed (literalResponse F false q advanced μ hμ w))

def responseMeasure (F : Index) (q : QuantumTest) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) : Measure ℝ :=
  volume.withDensity (fun w => ENNReal.ofReal (‖embed (literalResponse F sharp q advanced μ hμ w)‖^2))

def correctionMeasure (F : Index) (q : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) : Measure ℝ :=
  volume.withDensity (fun w => ENNReal.ofReal (‖originalYCorrection F q advanced μ hμ w‖^2))

private theorem projection_pythagoras (u : H) :
    ‖u‖^2 = ‖projection (3,0) u‖^2 + ‖u-projection (3,0) u‖^2 := by
  have hp : projection (3,0) (projection (3,0) u) = projection (3,0) u := by
    have h := congrArg (fun A : H →L[ℂ] H => A u) (projection_product (3,0) (3,0))
    simpa only [if_true,mul_apply_eq_comp] using! h
  have hz : inner ℂ (projection (3,0) u) (u-projection (3,0) u) = 0 := by
    calc
      _ = inner ℂ u (projection (3,0) (u-projection (3,0) u)) := projection_symmetric (3,0) _ _
      _ = 0 := by rw [map_sub,hp,sub_self,inner_zero_right]
  simpa only [add_sub_cancel,pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (projection (3,0) u) (u-projection (3,0) u) hz

private theorem sharp_bottom_response (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    embed (literalResponse F true q advanced μ hμ w) =
      projection (3,0) (embed (literalResponse F false q advanced μ hμ w)) := by
  rw [←embed_project]
  change embed (literalSharpResolvent F _ _ q) = embed (project (3,0) (literalCoreResolvent F _ _ q))
  rw [sharp_response F _ _ q hq,actual_bottom_primal_projected_resolvent,hq]

/-- The positive unforced spectrum splits on every frequency set into the
independent sharp baseline and the original-Y excess measure. -/
theorem actual_unforced_measure_decomposition (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    responseMeasure F q false advanced μ hμ =
      responseMeasure F q true advanced μ hμ + correctionMeasure F q advanced μ hμ := by
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (literalResponse F true q advanced μ hμ w)‖^2)) :=
    ENNReal.measurable_ofReal.comp ((actual_response_continuous F true q advanced μ hμ).norm.pow 2).measurable
  simp only [responseMeasure,correctionMeasure]
  rw [←withDensity_add_left hm]
  congr 1
  funext w
  simp only [Pi.add_apply]
  rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1
  rw [sharp_bottom_response F q hq advanced μ hμ w]
  exact projection_pythagoras _

/-- The unforced excess is the three literal original-Y words, rather than a
new independent output budget or a pulse forcing cancellation. -/
theorem actual_correction_three_words (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    originalYCorrection F q advanced μ hμ w =
      ∑j : Fin 3, embed (leg F (line (FullYPairedParseval.direction advanced * μ) w)
        (causal_line_nonreal advanced μ w hμ) q (j.val+1)) := by
  unfold originalYCorrection
  rw [←embed_project]
  change embed (literalCoreResolvent F _ _ q) - embed (project (3,0) (literalCoreResolvent F _ _ q)) = _
  rw [actual_bottom_primal_projected_resolvent,hq,full_response F _ _ q hq,map_sum,Fin.sum_univ_succ]
  change embed (resolventCore F _ _ q) + _ - embed (resolventCore F _ _ q) = _
  simp only [add_sub_cancel_left,Fin.val_succ]

/-- Paid fullY and source-bottom prices produce the actual nonnegative
unforced Yukawa excess; its integral is generated from the response itself. -/
theorem actual_unforced_frequency_balance (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ => ‖originalYCorrection F q advanced μ hμ w‖^2) ∧
    (∫w : ℝ, ‖embed (literalResponse F false q advanced μ hμ w)‖^2) =
      (Real.pi / μ) * ‖embed q‖^2 + (∫w : ℝ, ‖originalYCorrection F q advanced μ hμ w‖^2) ∧
    (Real.pi / μ) * ‖embed q‖^2 ≤
      (∫w : ℝ, ‖embed (literalResponse F false q advanced μ hμ w)‖^2) := by
  have whole := actual_response_square_integrable F false q advanced μ hμ
  obtain ⟨bottom,bottomMass⟩ := actual_bottom_primal_positive_price F 3 q advanced μ hμ
  have input : projection (3,0) (embed q) = embed q :=
    (embed_project (3,0) q).symm.trans (congrArg embed hq)
  rw [input] at bottomMass
  have point (w : ℝ) := projection_pythagoras (embed (literalResponse F false q advanced μ hμ w))
  have excess : Integrable (fun w : ℝ => ‖originalYCorrection F q advanced μ hμ w‖^2) := by
    apply (whole.sub bottom).congr
    apply Eventually.of_forall
    intro w
    dsimp only [Pi.sub_apply]
    unfold originalYCorrection
    linarith [point w]
  have total : (∫w : ℝ, ‖embed (literalResponse F false q advanced μ hμ w)‖^2) =
      (Real.pi / μ) * ‖embed q‖^2 + ∫w : ℝ, ‖originalYCorrection F q advanced μ hμ w‖^2 := by
    rw [←bottomMass,←integral_add bottom excess]
    apply integral_congr_ae
    exact Eventually.of_forall point
  refine ⟨excess,total,?_⟩
  rw [total]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

private theorem positive_measure_univ (p : ℝ → ℝ) (hi : Integrable p) (hp : ∀w,0 ≤ p w) :
    volume.withDensity (fun w => ENNReal.ofReal (p w)) Set.univ = ENNReal.ofReal (∫w : ℝ,p w) := by
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp)).symm

/-- The actual fullY and independent-sharp measures have a generated positive
balance: the common source price plus the three original-Y output grades. -/
theorem actual_unforced_measure_balance (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    responseMeasure F q false advanced μ hμ Set.univ =
      ENNReal.ofReal ((Real.pi / μ) * ‖embed q‖^2) +
        correctionMeasure F q advanced μ hμ Set.univ ∧
    responseMeasure F q true advanced μ hμ Set.univ =
      ENNReal.ofReal ((Real.pi / μ) * ‖embed q‖^2) ∧
    responseMeasure F q true advanced μ hμ Set.univ ≤ responseMeasure F q false advanced μ hμ Set.univ := by
  obtain ⟨excess,total,_⟩ := actual_unforced_frequency_balance F q hq advanced μ hμ
  have baseNonneg : 0 ≤ (Real.pi / μ) * ‖embed q‖^2 := mul_nonneg (div_pos Real.pi_pos hμ).le (sq_nonneg _)
  have extraNonneg : 0 ≤ ∫w : ℝ, ‖originalYCorrection F q advanced μ hμ w‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have primal : responseMeasure F q false advanced μ hμ Set.univ =
      ENNReal.ofReal ((Real.pi / μ) * ‖embed q‖^2) + correctionMeasure F q advanced μ hμ Set.univ := by
    rw [responseMeasure,positive_measure_univ _ (actual_response_square_integrable F false q advanced μ hμ)
      (fun _ => sq_nonneg _),total,ENNReal.ofReal_add baseNonneg extraNonneg,
      correctionMeasure,positive_measure_univ _ excess (fun _ => sq_nonneg _)]
  have sharpPoint (w : ℝ) : embed (literalResponse F true q advanced μ hμ w) =
      projection (3,0) (embed (literalResponse F false q advanced μ hμ w)) := by
    rw [←embed_project]
    change embed (literalSharpResolvent F _ _ q) = embed (project (3,0) (literalCoreResolvent F _ _ q))
    rw [sharp_response F _ _ q hq,actual_bottom_primal_projected_resolvent,hq]
  have sharp : responseMeasure F q true advanced μ hμ Set.univ = ENNReal.ofReal ((Real.pi / μ) * ‖embed q‖^2) := by
    obtain ⟨_,bottomMass⟩ := actual_bottom_primal_positive_price F 3 q advanced μ hμ
    have input : projection (3,0) (embed q) = embed q :=
      (embed_project (3,0) q).symm.trans (congrArg embed hq)
    rw [input] at bottomMass
    rw [responseMeasure,positive_measure_univ _ (actual_response_square_integrable F true q advanced μ hμ) (fun _ => sq_nonneg _)]
    simp_rw [sharpPoint]
    exact congrArg ENNReal.ofReal bottomMass
  refine ⟨primal,sharp,?_⟩
  rw [sharp,primal]
  exact le_add_right le_rfl

end LowEnergy.GeneralThreeParticleResponse
