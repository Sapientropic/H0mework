import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Quotient
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCompletion

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift SourceOperationPaidRelations

attribute [local instance] relationGroups

open private paidTrace from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCompletion

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private abbrev traceRoot (ordinal : Nat) :=
  RootedAccountedUnfolding.zero (sourceRuntime observation nontrivial half depth ordinal).emittedOccurrence

/-- The original paid relation completion is carried by its actual interpreted syntax. -/
def actualPaidSyntaxCompletion (ordinal : Nat) (p : Nat.Primes) :=
  SourceOperationCompletion.completionEquiv (traceRoot observation nontrivial half depth ordinal) p
    (paidTrace observation nontrivial half depth ordinal)

private def interpretedCoordinate (ordinal : Nat) (p : Nat.Primes) :=
  paidCompletionEquiv (traceRoot observation nontrivial half depth ordinal)
    (SourceOperationCompletion.trace p (paidTrace observation nontrivial half depth ordinal))

theorem actual_paid_syntax_source_unit (ordinal : Nat) (p : Nat.Primes) :
    actualPaidSyntaxCompletion observation nontrivial half depth ordinal p
        (sourceClass observation nontrivial half depth ordinal) =
      (interpretedCoordinate observation nontrivial half depth ordinal p).symm 1 := by
  let read := interpretedCoordinate observation nontrivial half depth ordinal p
  apply read.injective
  have interpreted := SourceOperationCompletion.completion_equiv_coordinate
    (traceRoot observation nontrivial half depth ordinal) p (paidTrace observation nontrivial half depth ordinal)
    (sourceClass observation nontrivial half depth ordinal)
  exact interpreted.trans ((actual_paid_completion_source_unit observation nontrivial half depth ordinal).trans
    (read.apply_symm_apply 1).symm)

private theorem inverse_preserves_charge (ordinal : Nat) (p : Nat.Primes) (coefficient : ℤ) :
    (actualPaidSyntaxCompletion observation nontrivial half depth ordinal p).symm
        ((interpretedCoordinate observation nontrivial half depth ordinal p).symm coefficient) =
      (actualPaidCompletion observation nontrivial half depth ordinal).symm coefficient := by
  let actual := actualPaidSyntaxCompletion observation nontrivial half depth ordinal p
  let old := actualPaidCompletion observation nontrivial half depth ordinal
  let read := interpretedCoordinate observation nontrivial half depth ordinal p
  let target := read.symm coefficient
  apply old.injective
  have interpreted := SourceOperationCompletion.completion_equiv_coordinate
    (traceRoot observation nontrivial half depth ordinal) p (paidTrace observation nontrivial half depth ordinal)
    (actual.symm target)
  exact interpreted.symm.trans ((congrArg read (actual.apply_symm_apply target)).trans
    ((read.apply_symm_apply coefficient).trans (old.apply_symm_apply coefficient).symm))

/-- The original native model action consumes the interpreted paid fibre through its generated inverse. -/
theorem actual_paid_syntax_model_next (ordinal : Nat) (p : Nat.Primes) (coefficient : ℤ) :
    H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
        (factor observation nontrivial half depth ordinal
          ((actualPaidSyntaxCompletion observation nontrivial half depth ordinal p).symm
            ((interpretedCoordinate observation nontrivial half depth ordinal p).symm coefficient))) =
      factor observation nontrivial half depth (ordinal+1)
        ((actualPaidSyntaxCompletion observation nontrivial half depth (ordinal+1) p).symm
          ((interpretedCoordinate observation nontrivial half depth (ordinal+1) p).symm coefficient)) := by
  have before := congrArg (fun word =>
    H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
      (factor observation nontrivial half depth ordinal word))
    (inverse_preserves_charge observation nontrivial half depth ordinal p coefficient)
  have after := congrArg (factor observation nontrivial half depth (ordinal+1))
    (inverse_preserves_charge observation nontrivial half depth (ordinal+1) p coefficient)
  exact before.trans ((actual_paid_model_next observation nontrivial half depth ordinal coefficient).trans after.symm)

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
