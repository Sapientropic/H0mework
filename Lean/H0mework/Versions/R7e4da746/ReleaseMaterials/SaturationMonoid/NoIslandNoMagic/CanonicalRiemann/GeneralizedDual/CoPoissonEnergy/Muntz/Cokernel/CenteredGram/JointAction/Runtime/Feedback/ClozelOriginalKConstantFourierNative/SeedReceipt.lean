import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveRootSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierSeedReceipt
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace C
export OriginalKCombReceiptFeedback (Value Var receipt wholeDebtRWaveSourceCode wholeDebtRWaveSourceTrace)
end C
namespace Seed
export OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual (seed)
end Seed

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "actual" => C.wholeDebtRWaveSourceTrace observation nontrivial depth half

def sourceCode : Expr C.Value C.Var () := .const Seed.seed

/-- Every cut consumes the original parent trace; the constant child incurs no Step. -/
noncomputable def originalChild : Trace.SourceReceipt actual sourceCode := by
  let outer := Trace.splitLinear actual
  let pair := Trace.splitAdd outer.trace
  let transform := Trace.splitLinear pair.leftTrace
  let weighted := Trace.splitAdd transform.trace
  let weight := Trace.splitLinear weighted.leftTrace
  let profile := Trace.splitAdd weight.trace
  let negative := Trace.splitLinear profile.rightTrace
  let edge := Trace.splitAdd negative.trace
  let dilation := Trace.splitLinear edge.leftTrace
  let primitive := Trace.splitAdd dilation.trace
  let coefficient := Trace.splitLinear primitive.leftTrace
  let resolvent := Trace.splitLinear coefficient.trace
  refine ⟨resolvent.input, resolvent.trace, ?_⟩
  exact .linear outer (.left pair (.linear transform (.left weighted (.linear weight
    (.right profile (.linear negative (.left edge (.linear dilation (.left primitive
      (.linear coefficient (.linear resolvent (.refl _))))))))))))

theorem original_child_address :
    (originalChild observation nontrivial half depth).retained.address =
      [2,0,2,0,2,1,2,0,2,0,2,2] := rfl

theorem original_value : (originalChild observation nontrivial half depth).value = Seed.seed :=
  (originalChild observation nontrivial half depth).trace.sound.symm

theorem original_child_paid : (originalChild observation nontrivial half depth).trace.length = 0 :=
  (originalChild observation nontrivial half depth).trace.length_to_const

theorem original_seed_source : (originalChild observation nontrivial half depth).value =
    burnolQuarterZeroExtension (intervalConstant (1/4 : ℝ)) := original_value observation nontrivial half depth

end OriginalConstantFourierSeedReceipt
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
