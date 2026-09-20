import H0mework.Physics.SynchronizedJoint.GravityTailProfileLocalRegularity
import H0mework.Physics.GravityTail.FixedInputRegularity

/-!
# Fixed P506/L0 specialization of gravity-tail profile regularity

The regularity mechanism is proved once in
`StageNineDiracDualFormNativeCartanECSynchronizedGravityTailProfileLocalRegularity`.
This file retains only the three fixed-lineage public interfaces consumed by
the existing action-selected path.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailLorentzProfileRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailProfileLocalRegularity
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailInputRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineResidualLinearPlebanskiTorsionReduction

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

attribute [local instance] actionSelectedMatterBasePointNormedAddCommGroup
attribute [local instance] actionSelectedMatterBasePointNormedSpace

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Coupled

/-- Fixed-lineage name retained for existing normal-form consumers. -/
theorem
    fixedP506L0ActionSelectedGravityTailProfileCoframeFirstJet_derivative_normalForm
    (contact : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    (cartanECSynchronizedGravityTailProfileCoframeFirstJet
        Source Coupled contact).derivative
        derivativeDirection internal coordinate =
      -coframeConnectionAction (Base.gravityConnection contact)
          derivativeDirection (Base.coframe contact) internal coordinate +
        ((1 : ℝ) / 2) *
          orderedCartanTorsionComponent
            (diracDualFormNativeActionCartanTorsionAt Source Base contact)
            internal derivativeDirection coordinate :=
  cartanECSynchronizedGravityTailProfileCoframeFirstJet_derivative_normalForm
    Source Coupled contact derivativeDirection internal coordinate

/-- Every coordinate one-form of the fixed action-selected coframe profile
is `C¹` on spacetime. -/
theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Coupled contact internal coordinate := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt
    Source Coupled
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_smooth
    contact (by
      rw [
        fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one]
      norm_num)
    internal coordinate

/-- The fixed action-selected Lorentz profile is `C¹` on spacetime. -/
theorem fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzJetCLM_contDiff :
    ContDiff ℝ 1
      (cartanECSynchronizedGravityTailJetCLM Source Coupled) := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact cartanECSynchronizedGravityTailLorentzJetCLM_contDiffAt
    Source Coupled
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_smooth
    contact (by
      rw [
        fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one]
      norm_num)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailLorentzProfileRegularity
