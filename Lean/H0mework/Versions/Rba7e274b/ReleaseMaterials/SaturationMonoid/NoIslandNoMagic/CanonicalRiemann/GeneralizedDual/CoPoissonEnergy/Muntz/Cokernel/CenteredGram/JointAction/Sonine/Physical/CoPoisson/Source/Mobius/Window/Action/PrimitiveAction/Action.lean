import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveAction.Tail
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

def primitiveReturnRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x|≤4 then -(2:ℂ)*((|x|:ℝ):ℂ)^(star coordinate.value-1)*tailWord coordinate |x| else 0

theorem original_primitive_M_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))=
      Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate) := by
  rw [FiniteMobiusResolventFlux.lower_full_source]
  simp only [map_sub,map_smul]
  have full : reflectL2 (FiniteMobiusResolventFlux.fullS (OriginalRieszFiniteSource.edgePrimitive coordinate))=
      FiniteMobiusResolventFlux.fullS (OriginalRieszFiniteSource.edgePrimitive coordinate) := by
    unfold FiniteMobiusResolventFlux.fullS
    simp only [sum_apply,smul_apply,map_sum,map_smul,
      FiniteMobiusResolventFlux.fullPullback,LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry,reflectL2_burnolMultiplicativeDilation,Paid.original_primitive_even]
  rw [FiniteMobiusResolventFlux.cutoff_even _ full,OriginalPrimitiveRankBalance.box_source_even]

 theorem original_primitive_M_support (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.cutoff 4 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))=
      Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate) := by
  apply Lp.ext
  filter_upwards [Paid.cutoff_read 4 (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)),Paid.primitive_lower_word coordinate] with x cut word
  rw [cut,word]
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside]
    exact word
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

 theorem original_primitive_Rplus_positive (coordinate : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,∀ _positive : 0<x,∀ _bounded : x≤4,
      Paid.Rplus (star coordinate.value/2) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)) x=
      -(2:ℂ)*(x:ℂ)^(star coordinate.value-1)*tailWord coordinate x := by
  have source := OriginalPaPhysicalGreen.sourceVolterraResolvent_positive_profile (Paid.conjugateCoordinate coordinate)
    (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  have same : OriginalPaPhysicalGreen.sourceVolterraResolvent (Paid.conjugateCoordinate coordinate)
      (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))=
      Paid.Rplus (star coordinate.value/2) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)) := by
    exact (FiniteMobiusResolventFlux.Rplus_tate _ right _).symm
  rw [same] at source
  filter_upwards [source] with x actual positive bounded
  rw [actual positive]
  change -(2:ℂ)*(x:ℂ)^(star coordinate.value-1)*burnolRadiusMellinTailEvaluator x positive (star coordinate.value)
    (by simpa [Complex.star_def] using coordinate.rightHalf) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))=_
  rw [primitive_tail_source coordinate x positive bounded]

-- Complete two-leg actual vector read: every finite n radius, actual mean and cutoff remains.
theorem original_primitive_Rplus_read (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.Rplus (star coordinate.value/2) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate)):ℝ→ℂ)=ᵐ[volume]
      primitiveReturnRaw coordinate := by
  let field := Paid.Rplus (star coordinate.value/2) (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))
  have even : reflectL2 field=field := FiniteMobiusResolventFlux.Rplus_even (Paid.conjugateCoordinate coordinate) _ (original_primitive_M_even coordinate)
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  have supported : Paid.cutoff 4 field=field := by
    have source := OriginalPrimitiveRankBalance.cutoff_Rplus_source 4 (by norm_num) (star coordinate.value/2) right (Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate))
    rw [original_primitive_M_support] at source
    exact source
  have support := Paid.cutoff_read 4 field
  rw [supported] at support
  have reflection := Lp.coeFn_compMeasurePreserving field negMeasurePreserving
  change (reflectL2 field:ℝ→ℂ)=ᵐ[volume] (field:ℝ→ℂ) ∘ (fun x=>-x) at reflection
  rw [even] at reflection
  have negative := negMeasurePreserving.quasiMeasurePreserving.ae (original_primitive_Rplus_positive coordinate)
  filter_upwards [original_primitive_Rplus_positive coordinate,negative,reflection,support,volume.ae_ne (0:ℝ)] with x positive negative reflected support nonzero
  change field x=primitiveReturnRaw coordinate x
  unfold primitiveReturnRaw
  by_cases inside : |x|≤4
  · rw [if_pos inside]
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · rw [show field x=field (-x) from reflected,abs_of_neg neg]
      exact negative (by linarith) (by simpa only [abs_of_neg neg] using inside)
    · rw [abs_of_pos pos]
      exact positive pos (by simpa only [abs_of_pos pos] using inside)
  · rw [if_neg inside,support,indicator_of_notMem (show x∉symmetricInterval 4 from fun h=>inside (abs_le.mpr h))]
end OriginalPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
