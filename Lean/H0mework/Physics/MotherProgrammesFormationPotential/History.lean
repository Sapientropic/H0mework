import H0mework.Physics.MotherProgrammesFormationPotential.Effects

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Revision Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

/-- The compiler supplies the visit successor. Displacement remains an
explicit lawful operand of the original complete potential action. -/
def nextOperands (visit : MotherVisit) (points displacement : Points) : MotherVisit × Points :=
  (targetVisit visit, points + displacement)

def sourceStep (visit : MotherVisit) (points displacement : Points) : SmoothUnifiedSource :=
  let discrete := toSource (execute (programAt (codeOf visit + 1)) neutralOrigin)
  { discrete with
    stageEight :=
      { discrete.stageEight with coframeLinearCoefficient :=
          (sourceOf visit points).stageEight.coframeLinearCoefficient + coframeMaterials displacement }
    continuousContactResidual :=
      (sourceOf visit points).continuousContactResidual + materials displacement 0 }

theorem source_next_commutes (visit : MotherVisit)
    (afterOrigin : originDepth ≤ temporalDepth visit.history) (points displacement : Points) :
    sourceOf (nextOperands visit points displacement).1 (nextOperands visit points displacement).2 =
      sourceStep visit points displacement := by
  have discrete := (StageEightDiscreteFormation.native_program_next visit afterOrigin).2.2.2
  unfold nextOperands sourceStep sourceOf
  rw [discrete, coframe_increment, materials_increment]
  rfl

theorem discrete_next (visit : MotherVisit)
    (afterOrigin : originDepth ≤ temporalDepth visit.history) (points displacement : Points) :
    readMaterial (sourceOf (targetVisit visit) (points + displacement)) =
      execute (programAt (codeOf visit + 1)) neutralOrigin := by
  rw [show sourceOf (targetVisit visit) (points + displacement) = sourceStep visit points displacement from
    source_next_commutes visit afterOrigin points displacement]
  change readMaterial (toSource (execute (programAt (codeOf visit + 1)) neutralOrigin)) = _
  exact full_material_recovered _

theorem continuous_next (visit : MotherVisit)
    (afterOrigin : originDepth ≤ temporalDepth visit.history) (points displacement : Points) :
    (sourceOf (targetVisit visit) (points + displacement)).stageEight.coframeLinearCoefficient =
        (sourceOf visit points).stageEight.coframeLinearCoefficient + coframeMaterials displacement ∧
      (sourceOf (targetVisit visit) (points + displacement)).continuousContactResidual =
        (sourceOf visit points).continuousContactResidual + materials displacement 0 := by
  rw [show sourceOf (targetVisit visit) (points + displacement) = sourceStep visit points displacement from
    source_next_commutes visit afterOrigin points displacement]
  exact ⟨rfl, rfl⟩

theorem history_step_consumed (visit : MotherVisit)
    (afterOrigin : originDepth ≤ temporalDepth visit.history)
    (points displacement : Points) (center : BasePoint) (epoch : ℕ)
    (point : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    let input := nextOperands visit points displacement
    let source := sourceOf input.1 input.2
    let current := GeneralSourceEvolution.stateAt source center epoch
    let target := GeneralSourceEvolution.stateAt source center (epoch + 1)
    (successor visit).targetCurrent = input.1.current ∧
      (successor visit).ledgerEvolution =
        (Stage9C.Revision.SpinPair.generatedPatch (Recognition.generated visit).occurrence).toLedgerWriteEvolution ∧
      SourceNativeTemporalVisitAt.finite (finiteVisit input.1) = input.1 ∧
      source = sourceStep visit points displacement ∧
      readMaterial source = execute (programAt (codeOf visit + 1)) neutralOrigin ∧
      source.stageEight.coframeLinearCoefficient =
        (sourceOf visit points).stageEight.coframeLinearCoefficient + coframeMaterials displacement ∧
      source.continuousContactResidual =
        (sourceOf visit points).continuousContactResidual + materials displacement 0 ∧
      (∀ slot, generatedMotherPotential Runtime.source (input.2 slot) 1 =
        generatedMotherPotential Runtime.source (points slot) 1 +
          generatedMotherPotential Runtime.source (displacement slot) 1) ∧
      remainders input.2 = remainders points + remainders displacement ∧
      restorePoints (materials input.2) (remainders input.2) = input.2 ∧
      target = GeneralSourceEvolution.next source center current ∧
      target.current = p286CartanNext source current.current current.smooth current.nondegenerate center ∧
      target.current = materialField source ∧
      DiracDualFormNativeJointZeroFiber source target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock source) ∧
      actualRelativeAction source current.current target.current =
        p286CenteredReducedRelativeAction source current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction source current.current target.current = 0 ∧
      target.current.conjugateMatter point (action (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix action) := by
  have native := StageEightDiscreteFormation.native_program_next visit afterOrigin
  have continuous := continuous_next visit afterOrigin points displacement
  refine ⟨native.1, native.2.1, native.2.2.1, source_next_commutes visit afterOrigin points displacement,
    discrete_next visit afterOrigin points displacement, continuous.1, continuous.2,
    fun slot => potential_increment (points slot) (displacement slot), remainders_increment points displacement,
    points_recovered (points + displacement), ?_⟩
  exact (source_native_consumed (targetVisit visit) (points + displacement) center epoch point action).2.2.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation
