import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Arithmetic.BurnolCarrier.AdditiveFullEvenL2
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection
import H0mework.Arithmetic.BurnolMellin.CompletedMellinEvaluatorKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousChannels
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCounting
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaKernelWholeWeakCount
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology BigOperators ENNReal
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.JointLogConductor OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.KGamma
noncomputable section

macro "gammaCountDilationPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.RelativeConductorGapReadback
  return Lean.mkIdent (owner.append (scope.append field.getId))

private theorem channel_pair (v gamma : BurnolL2) (source : GammaPair v gamma) (a : ℝ) :
    GammaPair (ContinuousChannels.channel 1 a v) (ContinuousChannels.channel 1 a gamma) := by
  intro test
  unfold ContinuousChannels.channel
  simp only [one_mul]
  rw [inner_smul_right,inner_smul_right]
  exact congrArg (fun price : ℂ=>(Real.sqrt a:ℂ)⁻¹*price)
    ((gammaCountDilationPaid% gamma_pair_dilation) (Real.log a) v gamma source test)

private theorem actual_complete_count_gamma_pair (N : ℕ) (v gamma : BurnolL2)
    (source : GammaPair v gamma) : GammaPair (DualSource.source N v) (DualSource.source N gamma) := by
  intro test
  change inner ℂ (wholeConductorTest test)
      ((∑ n∈Finset.Ico 1 N,ContinuousChannels.channel 1 (n:ℝ) v)-
        ∫ a : ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a v)=
    inner ℂ (test.toLp 2 volume)
      ((∑ n∈Finset.Ico 1 N,ContinuousChannels.channel 1 (n:ℝ) gamma)-
        ∫ a : ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a gamma)
  rw [inner_sub_right,inner_sub_right,inner_sum,inner_sum]
  have discrete : (∑ n∈Finset.Ico 1 N,inner ℂ (wholeConductorTest test) (ContinuousChannels.channel 1 (n:ℝ) v))=
      ∑ n∈Finset.Ico 1 N,inner ℂ (test.toLp 2 volume) (ContinuousChannels.channel 1 (n:ℝ) gamma) := by
    apply Finset.sum_congr rfl
    intro n _
    exact channel_pair v gamma source (n:ℝ) test
  have position := (innerSL ℂ (wholeConductorTest test)).integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N v)
  have frequency := (innerSL ℂ (test.toLp 2 volume)).integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N gamma)
  simp only [innerSL_apply_apply] at position frequency
  rw [discrete,←position,←frequency]
  congr 1
  apply integral_congr_ae
  filter_upwards with a
  exact channel_pair v gamma source a test

/-- The full actual Gamma kernel count is generated by both original count channels; all positive continuous scales are retained. -/
theorem actual_original_gamma_kernel_complete_count (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    GammaPair (DualSource.source N (burnolCompletedMellinRieszVector c:BurnolL2))
      (DualSource.source N (actualGammaKernel c)) :=
  actual_complete_count_gamma_pair N _ _ (actual_gamma_original_kernel c)

end
end OriginalGamma.Source.GammaKernelWholeWeakCount
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
