import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality
import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

-- These dependent runtime equalities are consumed by name.
run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_cokernel_completion_restriction"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_cokernel_coherent_next"

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open CategoryTheory BurnolPhysicalState SourceOperationScalarInventoryLift SourceGeneratedPrimePowerCompletion

attribute [local instance] relationGroups

open private paidEvaluation from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage
open private ambient_power_bijective from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelTopology
open private evaluationToModel modelCharge modelAction actual_model_square complex_power_bijective from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

/-- The actual evaluator recovers the entire coherent source in its original coverage cokernel. -/
def actualPaidCokernelCompletion (ordinal : Nat) (p : Nat.Primes) :=
  cokernelCompletionEquiv (paidEvaluation observation nontrivial half depth ordinal)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal) p
    (ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 p)

def actualPaidModelCokernelCompletion (ordinal : Nat) (p : Nat.Primes) :=
  cokernelCompletionEquiv (factor observation nontrivial half depth ordinal)
    (actual_paid_factor_injective observation nontrivial half depth ordinal) p (complex_power_bijective p)

/-- The actual factor and native action on the literal next model generate the coherent advance. -/
def actualPaidCokernelCompletionNext (ordinal : Nat) (p : Nat.Primes) :=
  (primePowerTorsionLimitMap (actualPaidModelCokernelNext observation nontrivial half depth ordinal) p).comp
    (primePowerTorsionLimitMap (actualPaidCokernelToModel observation nontrivial half depth ordinal) p)

theorem actual_paid_cokernel_completion_restriction (ordinal : Nat) (p : Nat.Primes) (j : Nat)
    (value : Completion (L := SourceCompletion observation nontrivial half depth ordinal) p) :
    (torsionCompletionRestriction
      (_ ⧸ LinearMap.range (paidEvaluation observation nontrivial half depth ordinal)) p j).hom
        (actualPaidCokernelCompletion observation nontrivial half depth ordinal p value) =
      actualPaidCokernelStage observation nontrivial half depth ordinal p j ((restriction p j).hom value) :=
  cokernel_completion_restriction (paidEvaluation observation nontrivial half depth ordinal)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal) p
    (ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 p) j value

private theorem actual_coherent_factor (ordinal : Nat) (p : Nat.Primes)
    (value : Completion (L := SourceCompletion observation nontrivial half depth ordinal) p) :
    primePowerTorsionLimitMap (actualPaidCokernelToModel observation nontrivial half depth ordinal) p
        (actualPaidCokernelCompletion observation nontrivial half depth ordinal p value) =
      actualPaidModelCokernelCompletion observation nontrivial half depth ordinal p value := by
  let grade := (D.packet observation nontrivial half depth ordinal).1
  have moved := cokernel_completion_equiv_naturality
    (paidEvaluation observation nontrivial half depth ordinal) (factor observation nontrivial half depth ordinal)
    LinearMap.id (evaluationToModel observation nontrivial half grade) (fun _ => rfl)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal)
    (actual_paid_factor_injective observation nontrivial half depth ordinal) p
    (ambient_power_bijective grade p) (complex_power_bijective p) value
  have same : inducedCompletionLinearMap p LinearMap.id value = value :=
    ConcreteCategory.congr_hom (inducedCompletionMap_id (L := SourceCompletion observation nontrivial half depth ordinal) p) value
  exact moved.trans (congrArg (actualPaidModelCokernelCompletion observation nontrivial half depth ordinal p) same)

/-- Every coherent source class advances by the original actual action, with all its prime-power coordinates. -/
theorem actual_paid_cokernel_coherent_next (ordinal : Nat) (p : Nat.Primes)
    (value : Completion (L := SourceCompletion observation nontrivial half depth ordinal) p) :
    actualPaidCokernelCompletionNext observation nontrivial half depth ordinal p
        (actualPaidCokernelCompletion observation nontrivial half depth ordinal p value) =
      actualPaidModelCokernelCompletion observation nontrivial half depth (ordinal+1) p
        (inducedCompletionLinearMap p (modelCharge observation nontrivial half depth ordinal) value) := by
  let advance := primePowerTorsionLimitMap (actualPaidModelCokernelNext observation nontrivial half depth ordinal) p
  have viaFactor := congrArg (fun middle => advance middle)
    (actual_coherent_factor observation nontrivial half depth ordinal p value)
  have viaNext := cokernel_completion_equiv_naturality (factor observation nontrivial half depth ordinal)
    (factor observation nontrivial half depth (ordinal+1)) (modelCharge observation nontrivial half depth ordinal)
    (modelAction observation nontrivial half) (actual_model_square observation nontrivial half depth ordinal)
    (actual_paid_factor_injective observation nontrivial half depth ordinal)
    (actual_paid_factor_injective observation nontrivial half depth (ordinal+1)) p
    (complex_power_bijective p) (complex_power_bijective p) value
  exact viaFactor.trans viaNext

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
