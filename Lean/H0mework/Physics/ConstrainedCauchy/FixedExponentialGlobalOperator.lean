import H0mework.Physics.ConstrainedCauchy.FixedExponentialPreparedActual

/-!
# Fixed P506/L0 exponential Cartan--EC Cauchy output

This module specializes the existing three-leg Cartan--EC Cauchy occurrence
to the fixed source-generated exponential prepared actual and records the
resulting global output, field custody, and geometric acceptance laws.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialGlobalOperator

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialPreparedActual
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialPreparedActual

/-- Exact fixed source/current occurrence of the generic three-leg writer. -/
def fixedP506L0CartanECConstraintExponentialCauchyOccurrence :
    CartanECCauchyTemporalOccurrence Source Prepared :=
  sourceActionGeneratedCartanECCauchyTemporalOccurrence Source Prepared

/-- The exact restart emitted by the first leg of the same occurrence. -/
def fixedP506L0CartanECConstraintExponentialRestartActual :
    StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

/-- The final actual emitted after restart, temporal connection, and live
reaction writes of the same occurrence. -/
def fixedP506L0CartanECConstraintExponentialCauchyGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
    Source Prepared

private abbrev Occurrence : CartanECCauchyTemporalOccurrence Source Prepared :=
  fixedP506L0CartanECConstraintExponentialCauchyOccurrence

private abbrev Restart : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialRestartActual

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialCauchyGlobalActual

/-- Every leg is the native action write of the exact source/current
occurrence. -/
theorem fixedP506L0CartanECConstraintExponentialCauchyOccurrence_after_eq_actionWrite
    (leg : CartanECCauchyTemporalWriteLeg) :
    Occurrence.after leg =
      cartanECCauchyTemporalActionWrite Source Prepared leg
        (Occurrence.before leg) :=
  Occurrence.after_eq_actionWrite leg

@[simp] theorem
    fixedP506L0CartanECConstraintExponentialCauchyOccurrence_restart_eq :
    Occurrence.after .cartanRestart = Restart :=
  rfl

@[simp] theorem
    fixedP506L0CartanECConstraintExponentialCauchyOccurrence_final_eq :
    Occurrence.finalActual = Output :=
  rfl

theorem fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_eq_actionOperator :
    Output =
      sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
        positiveSmoothUnifiedSource
        fixedP506L0CartanECConstraintExponentialPreparedActual :=
  rfl

@[simp] theorem
    fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_coframe :
    Output.coframe = Prepared.coframe :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe
    Source Prepared

theorem fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_nondegenerate :
    Output.Nondegenerate := by
  intro point
  rw [fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_coframe]
  exact
    fixedP506L0CartanECConstraintExponentialPreparedActual_nondegenerate point

theorem fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_simplicity :
    FormNativeGravitySimplicityEquation Output :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
    Source Prepared

theorem
    fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_reactionSelfGenerated :
    Output.gravitySimplicityMultiplier =
      formNativeGravityReactionField Output :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_reactionSelfGenerated
    Source Prepared

/-- Exhaustive field custody of the final actual. -/
theorem fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_fieldInventory :
    Output.coframe = Prepared.coframe ∧
      Output.gravityConnection =
        (cartanECCauchyTemporalConnectedActual Source Prepared
          ).gravityConnection ∧
      Output.gravityAuxiliary = (fun point =>
        physicalIIPlusBivector (Prepared.coframe point)) ∧
      Output.gravitySimplicityMultiplier =
        formNativeGravityReactionField Output ∧
      Output.gaugeConnection = Prepared.gaugeConnection ∧
      Output.gaugeAuxiliary = Prepared.gaugeAuxiliary ∧
      Output.scalar = Prepared.scalar ∧
      Output.matter = Prepared.matter ∧
      Output.conjugateMatter = Prepared.conjugateMatter := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact
    fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_reactionSelfGenerated

/-- The occurrence consumes the same fixed P506/L0 source lineage as its
prepared current. -/
theorem fixedP506L0CartanECConstraintExponentialCauchyGlobalActual_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506L0CartanECConstraintExponentialPreparedActual_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialGlobalOperator
