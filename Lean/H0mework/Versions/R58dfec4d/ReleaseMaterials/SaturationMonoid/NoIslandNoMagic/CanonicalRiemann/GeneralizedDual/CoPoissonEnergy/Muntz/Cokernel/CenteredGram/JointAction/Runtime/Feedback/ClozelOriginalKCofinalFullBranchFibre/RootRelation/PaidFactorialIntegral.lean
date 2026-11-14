import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.Residual
import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFactorialHomology

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift
open CofinalAllPrimeTopology

attribute [local instance] relationGroups

open private modelCharge actual_model_square from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

-- The proof retains the original dependent occurrence and action in the result.
set_option cleanup.letToHave false in
/-- An eventually bounded original H¹ class writes its unique integral source through the native action. -/
def actual_paid_factorial_integral_next :=
  fun charge =>
  let read := actualPaidFactorialHomologyIso observation nontrivial half depth ordinal
  let value := read.hom.hom.toFun charge
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  fun bounded =>
  let paid := (factorial_integral_source_iff coordinate value).2 bounded
  let source := Classical.choose paid
  let witness := Classical.choose_spec paid
  let move := modelCharge observation nontrivial half depth ordinal
  let written := (congrArg (factorialCompletionAction move).toFun witness.1.symm).trans
    (factorial_action_canonical move source)
  let native := actual_model_square observation nontrivial half depth ordinal source
  let whole := actual_root_relation_consumer observation nontrivial half depth ordinal
  PProd.mk source (And.intro witness (And.intro written (And.intro native whole)))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
