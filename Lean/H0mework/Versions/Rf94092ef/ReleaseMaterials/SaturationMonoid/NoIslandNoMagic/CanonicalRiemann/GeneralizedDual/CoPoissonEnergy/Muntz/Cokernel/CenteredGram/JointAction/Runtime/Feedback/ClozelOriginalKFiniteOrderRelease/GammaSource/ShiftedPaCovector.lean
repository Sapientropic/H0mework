import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCovector
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.Residue

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceJointContact.ShiftedPaCovector

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.KappaConductor
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.ConductorDual
open OriginalGamma.Source.GammaKernelWholeWeakCount OriginalGamma.Source.GammaFirstCountingConductor
open OriginalGamma.Source.CountedPositionTateGamma
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.TateWindow
open OriginalKCrossParameterRAdjointSource PaCoefficientSourceGram
open scoped InnerProductSpace Topology

open private actual_nu_forward from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCrossAction
open private counted_kernel_position_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaUnitFourierClockKPriceSource
open private gamma_pair_dilation log_pair_dilation dilation_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private inverse_log_from_complete_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
open private annulus_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy

local notation "D" => burnolMultiplicativeDilation
local notation "DN" => DualSource.source
local notation "K" => burnolCompletedMellinRieszVector
local notation "T" => burnolTateReciprocalL2
local notation "A" => sourceAnnulusCut
local notation "V" => sourceVolterraResolvent
local notation "Pa" => PaNativePortSource.Pa

/-- The two counting limits share the same shifted window conductor. -/
private theorem shifted_cross_source
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (shift : ℝ)
    (value : BurnolL2) (even : reflectL2 value = value) :
    inner ℂ (D shift (actualGammaKernel c)) (sourceVolterraPhysical c value : BurnolL2) =
      inner ℂ (A (D (-shift) (originalDualLogValue c))) (V c (A value)) := by
  let w := tateWindow c value
  let shiftedWindow := D (-shift) w
  let shiftedGamma := D (-shift) (tateWindowGamma c value)
  have sourceWindow : GammaPair shiftedWindow shiftedGamma :=
    gamma_pair_dilation (-shift) _ _ (actual_tate_window_Gamma c value even)
  have positionWindow := log_pair_dilation (-shift) _ _ (actual_tate_window_two_sources c value even).1
  have frequencyWindow := inverse_log_from_complete_source _ _ _ sourceWindow positionWindow
  have finite (N : ℕ) : inner ℂ (DN N (D shift (actualGammaKernel c))) w =
      inner ℂ (DN N (K c : BurnolL2)) shiftedGamma := by
    have source := actual_original_gamma_kernel_complete_count c N
    have position := counted_kernel_position_source c N
    have frequency := inverse_log_from_complete_source _ _ _ source position
    rw [OriginalGamma.Source.CountingQuadraticLimit.dual_dilation]
    calc
      _ = inner ℂ (DN N (actualGammaKernel c)) shiftedWindow := by
        simpa only [shiftedWindow, neg_neg] using
          (dilation_pair (-shift) (DN N (actualGammaKernel c)) w).symm
      _ = _ := whole_conductor_dual _ _ _ _ _ _ _ _ source sourceWindow
        position frequency positionWindow frequencyWindow
  have cofinal := (KCounting.original_tendsto c zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := shiftedGamma))
  change Tendsto _ atTop (𝓝 (inner ℂ (originalFirstField c zero) shiftedGamma)) at cofinal
  have complete := whole_conductor_dual _ _ _ _ _ _ _ _
    (actual_original_first_field_complete_Gamma_source c zero) sourceWindow
    (actual_original_first_field_complete_log_sources c zero).1
    (actual_original_first_field_complete_log_sources c zero).2 positionWindow frequencyWindow
  rw [← complete] at cofinal
  have right : Tendsto (fun N : ℕ => inner ℂ (DN N (D shift (actualGammaKernel c))) w) atTop
      (𝓝 (inner ℂ (originalFirstFieldGamma c) shiftedWindow)) :=
    cofinal.congr' (Eventually.of_forall (fun N => (finite N).symm))
  have forward := (tendsto_const_nhds (x := D shift (actualGammaKernel c))).inner (𝕜 := ℂ)
    (actual_nu_forward c value even)
  have left : Tendsto (fun N : ℕ => inner ℂ (DN N (D shift (actualGammaKernel c))) w) atTop
      (𝓝 (inner ℂ (D shift (actualGammaKernel c)) (sourceVolterraPhysical c value : BurnolL2))) := by
    apply forward.congr'
    apply Eventually.of_forall
    intro N
    exact (ContinuousLinearMap.adjoint_inner_left (CountingDual.sourceCLM N)
      w (D shift (actualGammaKernel c))).symm.trans (by rw [← CountingDual.dual_eq_adjoint])
  have contact := tendsto_nhds_unique left right
  have moved : inner ℂ (originalFirstFieldGamma c) shiftedWindow =
      inner ℂ (D shift (originalFirstFieldGamma c)) w := by
    simpa only [shiftedWindow, neg_neg] using dilation_pair (-shift) (originalFirstFieldGamma c) w
  rw [moved] at contact
  change inner ℂ (D shift (actualGammaKernel c)) (sourceVolterraPhysical c value : BurnolL2) =
    inner ℂ (D shift (originalFirstFieldGamma c)) (T (A (V c (A value)))) at contact
  have tate : T (D shift (originalFirstFieldGamma c)) = D (-shift) (originalDualLogValue c) := by
    have commute := burnolTateReciprocalL2_dilation_inverse (-shift) (originalFirstFieldGamma c)
    rw [neg_neg, actual_original_counted_first_dual_same_Gamma_occurrence c zero] at commute
    exact commute.symm
  rw [← OriginalRieszFiniteSynthesis.tate_pairing, tate, ← annulus_pair] at contact
  exact contact

private theorem shifted_generator_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (shift : ℝ) (i : Index) :
    inner ℂ (D shift (actualGammaKernel c)) (burnolCompactCoPoissonGenerator i : BurnolL2) =
      inner ℂ (A (D (-shift) (originalDualLogValue c))) (sigmaGenerator i) := by
  let input := (RecipeInverse.inverseSource c (recipe i)).1.toLp 2 volume
  have paid := shifted_cross_source c zero shift input (RecipeInverse.compact_source_even _)
  dsimp only [input] at paid
  rw [RecipeInverse.sourceVolterraPhysical_inverse] at paid
  have cut := annulus_pair (A (D (-shift) (originalDualLogValue c))) (V c (A input))
  dsimp only [input] at cut
  rw [sourceAnnulusCut_idempotent] at cut
  rw [cut, RecipeInverse.compact_source_supported] at paid
  change inner ℂ (D shift (actualGammaKernel c)) (burnolCompactAdditivePhysicalState (recipe i) : BurnolL2) =
    inner ℂ (A (D (-shift) (originalDualLogValue c))) (sourceVolterraWindow c input) at paid
  dsimp only [input] at paid
  rw [RecipeInverse.sourceVolterraWindow_inverse] at paid
  simpa only [generator_recipe, sigmaGenerator] using paid

/-- The original shifted kernel reads every Pa vector through its actual source map. -/
theorem actual_shifted_Gamma_Pa_source_covector
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (shift : ℝ) (p : ↥Pa) :
    inner ℂ (D shift (actualGammaKernel c)) ((p : BurnolPaAmbientCarrier) : BurnolL2) =
      inner ℂ (A (D (-shift) (originalDualLogValue c))) (PaNativePortSource.sourceMap p) := by
  let left : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
    (innerSL ℂ (D shift (actualGammaKernel c))).comp
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL
  let right : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
    (innerSL ℂ (A (D (-shift) (originalDualLogValue c)))).comp (burnolTateReciprocalL2.comp burnolMobiusSourceL2)
  have onRange : Set.EqOn left right (Set.range burnolCompactCoPoissonLanding) := by
    rintro _ ⟨input,rfl⟩
    induction input using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add u v hu hv => simp only [map_add,hu,hv]
    | single i z =>
      have atom : left (burnolCompactCoPoissonGenerator i) = right (burnolCompactCoPoissonGenerator i) := by
        change inner ℂ (D shift (actualGammaKernel c)) (burnolCompactCoPoissonGenerator i : BurnolL2) =
          inner ℂ (A (D (-shift) (originalDualLogValue c))) (T (burnolMobiusSourceL2 (burnolCompactCoPoissonGenerator i)))
        rw [sigma_generator_read]
        exact shifted_generator_price c zero shift i
      simp only [burnolCompactCoPoissonLanding_single,map_smul,atom]
  have admitted : (p : BurnolPaAmbientCarrier) ∈ closure (Set.range burnolCompactCoPoissonLanding) := by
    have actual : (p : BurnolPaAmbientCarrier) ∈
        (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure := p.property
    change (p : BurnolPaAmbientCarrier) ∈ closure ((LinearMap.range burnolCompactCoPoissonLanding) : Set BurnolPaAmbientCarrier) at actual
    simpa only [LinearMap.coe_range] using actual
  exact onRange.closure left.continuous right.continuous admitted

/-- Both terms of the actual prime-three action act on the original dual-log value. -/
theorem actual_primeThree_Gamma_Pa_source_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (p : ↥Pa) :
    inner ℂ (actualGammaKernel c) (primeThreePhysicalResidue ((p : BurnolPaAmbientCarrier) : BurnolL2)) =
      inner ℂ (A (primeThreePhysicalResidue (originalDualLogValue c))) (PaNativePortSource.sourceMap p) := by
  let a := Real.sqrt 3
  let h := Real.log a
  let b : ℂ := Real.sqrt a
  let physical := ((p : BurnolPaAmbientCarrier) : BurnolL2)
  have raw : inner ℂ (actualGammaKernel c) (primeThreePhysicalResidue physical) =
      b * inner ℂ (D (-h) (actualGammaKernel c)) physical -
        b⁻¹ * inner ℂ (D h (actualGammaKernel c)) physical := by
    change inner ℂ (actualGammaKernel c) (b • D h physical - b⁻¹ • D (-h) physical) = _
    simp only [inner_sub_right, inner_smul_right, dilation_pair, neg_neg]
  rw [raw, actual_shifted_Gamma_Pa_source_covector c zero (-h) p,
    actual_shifted_Gamma_Pa_source_covector c zero h p, neg_neg]
  change _ = inner ℂ (A (b • D h (originalDualLogValue c) - b⁻¹ • D (-h) (originalDualLogValue c)))
    (PaNativePortSource.sourceMap p)
  have starWeight : star b = b := by
    dsimp only [b]
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  simp only [map_sub, map_smul, inner_sub_left, inner_smul_left, starRingEnd_apply, star_inv₀, starWeight]

end OriginalRSourceJointContact.ShiftedPaCovector
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
