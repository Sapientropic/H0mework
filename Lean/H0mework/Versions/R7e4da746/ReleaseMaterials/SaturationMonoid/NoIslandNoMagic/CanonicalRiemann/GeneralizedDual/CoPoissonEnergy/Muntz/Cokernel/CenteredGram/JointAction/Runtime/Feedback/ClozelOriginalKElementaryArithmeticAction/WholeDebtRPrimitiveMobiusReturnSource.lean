import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusFiniteSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestReturnSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRPrimitiveMobiusSource
open Complex MeasureTheory Set FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalWholeDebtRPowerWaveDilationSource OriginalKSourceResolventReconstruction
open scoped InnerProductSpace BigOperators FourierTransform
namespace A
export OriginalWholeDebtRReciprocalCotestActionSource
  (positionColumn fourierColumn reciprocalCotest weight weightedField effectCotest
   weighted_field_action actual_defect_fee)
end A
namespace Return
export OriginalWholeDebtRReciprocalCotestReturnSource (returnPrice actual_weighted_wave)
end Return
open private meanPrice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestReturnSource
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "FL" => fourierL2
local notation "Tate" => burnolTateReciprocalL2
local notation "q" => (1/4 : ℝ)
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "p" => Flux.primitiveSource observation nontrivial half
local notation "K" => OriginalKCombCofinalTwoDirection.originalK observation nontrivial half
local notation "aa" => Flux.sourceA observation

private theorem tate_pair (left right : BurnolL2) :
    inner ℂ (Tate left) right = inner ℂ left (Tate right) :=
  OriginalRieszFiniteSynthesis.tate_pairing left right

private theorem full_return_source :
    Return.returnPrice observation nontrivial half =
      inner ℂ (Flux.M (FL K))
        (A.weight c • (burnolAnnulusSamplingL2 (A.positionColumn c) 0+A.reciprocalCotest c)) +
      A.weight c * meanPrice c +
      inner ℂ (Flux.M (FL p)) (A.effectCotest c) -
      inner ℂ (Flux.M p) (Tate (A.effectCotest c)) -
      star aa * inner ℂ (Flux.defectFlux (observation.coordinate/2) K) (A.effectCotest c) := by
  have kernel : generatedK c = K := by
    rw [generatedK_eq_original]
    rfl
  unfold Return.returnPrice Flux.defectForcing Flux.D
  rw [kernel]
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    inner_sub_left, inner_smul_left, starRingEnd_apply]
  rw [tate_pair]
  ring

/-- The complete old return now consumes all three actual finite-window source actions. -/
theorem actual_native_return :
    star (returnPhase observation nontrivial half)*Return.returnPrice observation nontrivial half =
      star (primitivePhase observation nontrivial half spread*
        fourierPrimitivePhase observation nontrivial half spread)*
        inner ℂ (kernelWindowSource observation nontrivial half)
          (A.weight c • (burnolAnnulusSamplingL2 (A.positionColumn c) 0+A.reciprocalCotest c))+
      star (returnPhase observation nontrivial half)*A.weight c*meanPrice c+
      star (primitivePhase observation nontrivial half spread*fourierKernelPhase observation spread)*
        inner ℂ (fourierPrimitiveWindowSource observation nontrivial half) (A.effectCotest c)-
      star (fourierKernelPhase observation spread*fourierPrimitivePhase observation nontrivial half spread)*
        inner ℂ (-Flux.M (primitiveIncrement observation nontrivial half spread)) (Tate (A.effectCotest c))-
      star (returnPhase observation nontrivial half)*star aa*
        inner ℂ (Flux.defectFlux (observation.coordinate/2) K) (A.effectCotest c) := by
  have first:=congrArg (fun field : BurnolL2 => inner ℂ field
    (A.weight c • (burnolAnnulusSamplingL2 (A.positionColumn c) 0+A.reciprocalCotest c)))
    (fourier_kernel_window_source observation nontrivial half)
  have second:=congrArg (fun field : BurnolL2 => inner ℂ field (A.effectCotest c))
    (fourier_primitive_window_source observation nontrivial half)
  have third:=congrArg (fun field : BurnolL2 => inner ℂ field (Tate (A.effectCotest c)))
    (primitive_window_source observation nontrivial half)
  simp only [inner_smul_left,starRingEnd_apply] at first second third
  rw [full_return_source]
  simp only [returnPhase,star_mul]
  linear_combination
    (star (primitivePhase observation nontrivial half spread)*
      star (fourierPrimitivePhase observation nontrivial half spread))*first+
    (star (primitivePhase observation nontrivial half spread)*
      star (fourierKernelPhase observation spread))*second-
    (star (fourierKernelPhase observation spread)*
      star (fourierPrimitivePhase observation nontrivial half spread))*third

end OriginalWholeDebtRPrimitiveMobiusSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
