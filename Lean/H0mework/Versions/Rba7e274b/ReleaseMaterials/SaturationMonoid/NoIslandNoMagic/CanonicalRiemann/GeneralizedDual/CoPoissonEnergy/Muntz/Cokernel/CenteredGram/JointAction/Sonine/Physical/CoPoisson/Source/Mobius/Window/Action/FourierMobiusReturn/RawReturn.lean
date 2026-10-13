import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Word
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology

def actualReturnTimeRaw (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (x : ℝ) : ℂ :=
  -(∫ tau : ℝ in Ioi 0,Complex.exp ((-star coordinate.value/2)*(tau:ℂ))*value (Real.exp (-tau/2)*x))

-- The original R, including its normalized dilation Jacobian, is read through the paid Bochner consumer.
theorem original_R_raw (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (burnolDirectRightResolvent (star coordinate.value/2) value:ℝ→ℂ)=ᵐ[volume] actualReturnTimeRaw coordinate value := by
  let z := star coordinate.value/2
  have right : 1/4<z.re := by dsimp only [z];rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  let family : ℝ→BurnolL2 := burnolDirectRightResolventIntegrand z value
  let raw : ℝ×ℝ→ℂ := fun p=>Complex.exp ((-star coordinate.value/2)*(p.1:ℂ))*value (Real.exp (-p.1/2)*p.2)
  have measured : Measurable raw := by
    unfold raw
    exact (by fun_prop : Measurable (fun p : ℝ×ℝ=>Complex.exp ((-star coordinate.value/2)*(p.1:ℂ)))).mul
      ((Lp.stronglyMeasurable value).measurable.comp (by fun_prop))
  have reads : ∀ᵐ tau ∂volume.restrict (Ioi 0),(family tau:ℝ→ℂ)=ᵐ[volume] fun x=>raw (tau,x) := by
    filter_upwards with tau
    filter_upwards [Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight z tau)
      (burnolMultiplicativeDilation (-tau/2) value),burnolMultiplicativeDilation_coeFn (-tau/2) value]
      with x scalar moved
    unfold family burnolDirectRightResolventIntegrand
    rw [scalar]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [moved]
    unfold raw positiveMellinQuarterRightResolventWeight burnolL2RawNormalizedDilation
    dsimp only
    rw [Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
    congr 2
    dsimp only [z]
    push_cast
    ring
  unfold burnolDirectRightResolvent
  filter_upwards [Lp.coeFn_neg (∫ tau : ℝ in Ioi 0,family tau),
    OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict (Ioi 0)) family
      (burnolDirectRightResolventIntegrand_integrableOn z right value) raw measured reads]
      with x negRead rawRead
  rw [negRead,Pi.neg_apply,rawRead]
  rfl

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
