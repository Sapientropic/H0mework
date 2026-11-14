import H0mework.Versions.R62742ad3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.EffectJump
import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFactorialIntegral
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.PositionGapEuler

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift
open CofinalAllPrimeTopology

attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The installed factor and actual model action give both original successor slots. -/
def factorialPairAction : SourceCompletion observation nontrivial half depth ordinal →ₗ[ℤ] SourcePair :=
  ((modelReadback observation nontrivial half).restrictScalars ℤ).comp
    (((H.modelAction (sourceStep observation nontrivial half)
      (sourceBranches observation nontrivial half)).restrictScalars ℤ).comp
      (factor observation nontrivial half depth ordinal))

def factorialWholeAction : SourceCompletion observation nontrivial half depth ordinal →ₗ[ℤ] BurnolL2 :=
  (Inv.pairTotal.restrictScalars ℤ).comp (factorialPairAction observation nontrivial half depth ordinal)

theorem actual_factorial_pair_source (charge : SourceCompletion observation nontrivial half depth ordinal) :
    factorialPairAction observation nontrivial half depth ordinal charge =
      actualPaidCompletion observation nontrivial half depth ordinal charge •
        D.input observation nontrivial half depth (ordinal+1) := by
  let action := H.modelAction (sourceStep observation nontrivial half)
    (sourceBranches observation nontrivial half)
  let read := modelReadback observation nontrivial half
  let advance := read.comp action
  let coefficient := actualPaidCompletion observation nontrivial half depth ordinal charge
  let current := receivedModel observation nontrivial half depth ordinal
  have nextRead : read (receivedModel observation nontrivial half depth (ordinal+1)) =
      D.input observation nontrivial half depth (ordinal+1) :=
    (congrArg read (factor_source_class observation nontrivial half depth (ordinal+1))).trans
      (model_readback_source observation nontrivial half _)
  have native : advance current = D.input observation nontrivial half depth (ordinal+1) :=
    (congrArg read (received_model_next observation nontrivial half depth ordinal)).trans nextRead
  have generated : factor observation nontrivial half depth ordinal charge = coefficient • current :=
    actual_paid_completion_factor observation nontrivial half depth ordinal charge
  change advance (factor observation nontrivial half depth ordinal charge) = _
  exact (congrArg advance generated).trans
    ((map_zsmul advance coefficient current).trans
      (congrArg (fun pair : SourcePair => coefficient • pair) native))

theorem actual_factorial_whole_source (charge : SourceCompletion observation nontrivial half depth ordinal) :
    factorialWholeAction observation nontrivial half depth ordinal charge =
      actualPaidCompletion observation nontrivial half depth ordinal charge •
        D.raw observation nontrivial half depth (ordinal+1) := by
  let coefficient := actualPaidCompletion observation nontrivial half depth ordinal charge
  change Inv.pairTotal (factorialPairAction observation nontrivial half depth ordinal charge) = _
  exact (congrArg Inv.pairTotal
    (actual_factorial_pair_source observation nontrivial half depth ordinal charge)).trans
      (map_zsmul Inv.pairTotal coefficient (D.input observation nontrivial half depth (ordinal+1)))

theorem actual_factorial_whole_split (charge : SourceCompletion observation nontrivial half depth ordinal) :
    let whole := factorialWholeAction observation nontrivial half depth ordinal charge
    (P.physicalProjection whole, P.physicalRemainder whole) =
      factorialPairAction observation nontrivial half depth ordinal charge := by
  dsimp only
  let coefficient := actualPaidCompletion observation nontrivial half depth ordinal charge
  let next := D.raw observation nontrivial half depth (ordinal+1)
  let split : BurnolL2 → SourcePair := fun raw => (P.physicalProjection raw, P.physicalRemainder raw)
  have literal : split next = D.input observation nontrivial half depth (ordinal+1) :=
    (congrArg split (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth ordinal)).trans
      (D.next_pair observation nontrivial half depth ordinal).symm
  have scaled : split (coefficient • next) = coefficient • split next :=
    Prod.ext (map_zsmul P.physicalProjection coefficient next) (map_zsmul P.physicalRemainder coefficient next)
  exact (congrArg split (actual_factorial_whole_source observation nontrivial half depth ordinal charge)).trans
    (scaled.trans ((congrArg (fun pair : SourcePair => coefficient • pair) literal).trans
      (actual_factorial_pair_source observation nontrivial half depth ordinal charge).symm))

theorem actual_factorial_whole_unit :
    factorialWholeAction observation nontrivial half depth ordinal
      ((actualPaidCompletion observation nontrivial half depth ordinal).symm 1) =
        D.raw observation nontrivial half depth (ordinal+1) := by
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  let next := D.raw observation nontrivial half depth (ordinal+1)
  have unit := congrArg (fun scale : ℤ => scale • next) (coordinate.apply_symm_apply 1)
  exact (actual_factorial_whole_source observation nontrivial half depth ordinal (coordinate.symm 1)).trans
    (unit.trans (one_zsmul next))

theorem actual_factorial_whole_unit_ne_zero :
    factorialWholeAction observation nontrivial half depth ordinal
      ((actualPaidCompletion observation nontrivial half depth ordinal).symm 1) ≠ 0 :=
  fun erased => KernelWrite.NativeDelta.Terminal.actual_raw_ne_zero observation nontrivial half depth (ordinal+1)
    ((actual_factorial_whole_unit observation nontrivial half depth ordinal).symm.trans erased)

set_option cleanup.letToHave false in
/-- Adjacent original H¹ reads have an exact signed jump in the whole successor field. -/
def actual_paid_factorial_whole_spacing :=
  fun charge (stage : Nat) =>
  let read := actualPaidFactorialHomologyIso observation nontrivial half depth ordinal
  let value := read.hom.hom.toFun charge
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  let field := factorialWholeAction observation nontrivial half depth ordinal
  let representative := factorialBalancedLift coordinate value
  let reads := fun n => (factorial_balanced_lift coordinate value n).1
  let jump := factorial_effect_jump coordinate field value representative reads stage
  let unit := actual_factorial_whole_unit observation nontrivial half depth ordinal
  let left := actual_factorial_whole_split observation nontrivial half depth ordinal (representative stage)
  let right := actual_factorial_whole_split observation nontrivial half depth ordinal (representative (stage+1))
  PProd.mk (representative stage, representative (stage+1))
    (And.intro (reads stage) (And.intro (reads (stage+1)) (And.intro jump (And.intro unit (And.intro left right)))))

set_option cleanup.letToHave false in
/-- The whole successor field's sub-modulus jumps recover the original class and write it back. -/
def actual_paid_factorial_field_next :=
  fun charge =>
  let read := actualPaidFactorialHomologyIso observation nontrivial half depth ordinal
  let value := read.hom.hom.toFun charge
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  let field := factorialWholeAction observation nontrivial half depth ordinal
  let live := actual_factorial_whole_unit_ne_zero observation nontrivial half depth ordinal
  fun small =>
  let original := (factorial_small_effect_recovers_source coordinate field live value).2 small
  let bounded := (factorial_integral_source_iff coordinate value).1 original
  let native := actual_paid_factorial_integral_next observation nontrivial half depth ordinal charge bounded
  let whole := actual_factorial_whole_source observation nontrivial half depth ordinal native.1
  let slots := actual_factorial_whole_split observation nontrivial half depth ordinal native.1
  let division := OriginalKDirectRCofinalDivision.actual_division_position_gap_mixed_next
    observation nontrivial half depth ordinal
  PProd.mk native (And.intro whole (And.intro slots division))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
