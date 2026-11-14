import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Cokernel
import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.Consumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift
open SourceGeneratedPrimePowerCompletion CofinalAllPrimeTopology

attribute [local instance] relationGroups

open private paidEvaluation from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage
open private ambient_power_bijective from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelTopology
open private modelCharge actual_model_square complex_power_bijective from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
variable (primes : Finset Nat.Primes) (level : primes → Nat)

local notation "evaluator" => paidEvaluation observation nontrivial half depth ordinal
local notation "coordinate" => actualPaidCompletion observation nontrivial half depth ordinal
local notation "faithful" => actual_paid_evaluation_injective observation nontrivial half depth ordinal
private theorem sourceDivides (prime : Nat.Primes) (stage : Nat) :
    Function.Bijective (powerMultiplication
      (L := PairValue (L.Value (PairValue C.Value) (D.packet observation nontrivial half depth ordinal).1) ()) prime stage) :=
  ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 prime stage

local notation "divides" => sourceDivides observation nontrivial half depth ordinal

/-- The original paid R relation class realizes the full finite input from its evaluator cokernel. -/
def actualPaidFiniteCharge :=
  finiteCokernelCharge evaluator faithful divides primes level coordinate

-- The conclusion retains the original dependent source and ledger indices.
set_option cleanup.letToHave false in
/-- One finite charge advances through the actual R action, with the original next and whole consumer. -/
def actual_paid_finite_charge_next :=
  fun family =>
  let charge := actualPaidFiniteCharge observation nontrivial half depth ordinal primes level family
  let move := modelCharge observation nontrivial half depth ordinal
  let nextFactor := factor observation nontrivial half depth (ordinal+1)
  let nextFaithful := actual_paid_factor_injective observation nontrivial half depth (ordinal+1)
  let connected := (allPrimeCokernelEquiv evaluator faithful divides).symm family
  let stageAt := fun p : primes => finite_cokernel_charge_stage evaluator faithful divides primes level coordinate family p
  let nextAt := fun p : primes =>
    let prime := p.val
    let stage := level p
    let restricted := (torsionCompletionRestriction (_ ⧸ LinearMap.range nextFactor) prime stage).hom.toFun
    let fromInput := all_prime_cokernel_roundtrip evaluator faithful divides family prime
    let action := (actualPaidCokernelCompletionNext observation nontrivial half depth ordinal prime).toFun
    let movedBySource := actual_paid_cokernel_coherent_next observation nontrivial half depth ordinal prime (connected prime)
    let movedStage := finite_cokernel_charge_successor evaluator faithful divides primes level coordinate family
      nextFactor nextFaithful (fun prime => complex_power_bijective prime) move p
    (congrArg (fun value => restricted (action value)) fromInput.symm).trans
      ((congrArg restricted movedBySource).trans movedStage)
  let native := actual_model_square observation nontrivial half depth ordinal charge
  let whole := actual_root_relation_consumer observation nontrivial half depth ordinal
  PProd.mk charge (And.intro stageAt (And.intro nextAt (And.intro native whole)))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
