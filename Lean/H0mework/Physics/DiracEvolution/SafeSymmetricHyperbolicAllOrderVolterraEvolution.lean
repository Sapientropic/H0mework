import H0mework.Physics.DiracEvolution.SafeSymmetricHyperbolicAllOrderMollifier
import H0mework.Physics.DiracEvolution.SafeTemporalJetReduction

/-!
# Fixed P506/L0 all-order Volterra evolution

Every spatial word obeys the same source-owned temporal evolution.  The
forcing is exactly the differentiated action defect minus the recursively
generated coefficient commutator.  No derivative order enters as a premise.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderVolterraEvolution

open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCommutator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource

open scoped ContDiff

noncomputable section

set_option autoImplicit false

/-- Every spatial word obeys one forced temporal Volterra law.  The forcing
is entirely the differentiated action defect minus the source-generated
coefficient commutator. -/
theorem fixedSpatialWordDerivative_temporalVolterraDefect
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ (⊤ : ℕ∞) field)
    (point : BasePoint) :
    fieldDirectionalDerivative
          (fixedSpatialWordDerivative word field) point 0 -
        cauchySafeMatterVolterraVelocity
          fixedP506L0CauchySafeMatterGalerkinInputActual
          (fun candidate => matterCoordinateEquiv.symm
            (fixedSpatialWordDerivative word field candidate))
          point =
      fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (fixedSpatialWordDerivative word
            (matterCoordinateFirstOrderOperator
              fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
              field) point -
          fixedMatterAllOrderCommutedForcing word field point) := by
  have derivativeSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fixedSpatialWordDerivative word field) :=
    fixedSpatialWordDerivative_contDiff_infty word field fieldSmooth
  have normalForm :=
    fixedMatterFirstOrderOperator_eq_temporalVolterraDefect
      (fixedSpatialWordDerivative word field) point
      ((derivativeSmooth.differentiable (by simp)).differentiableAt)
  change
    matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        (fixedSpatialWordDerivative word field) point =
      fixedEvolutionPrincipalCoordinateCLM 0 point
        (fieldDirectionalDerivative
            (fixedSpatialWordDerivative word field) point 0 -
          cauchySafeMatterVolterraVelocity
            fixedP506L0CauchySafeMatterGalerkinInputActual
            (fun candidate => matterCoordinateEquiv.symm
              (fixedSpatialWordDerivative word field candidate)) point) at normalForm
  have commuted := fixedMatterAllOrderCommutedActionLaw
    word field fieldSmooth point
  have actionRead :
      matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          (fixedSpatialWordDerivative word field) point =
        fixedSpatialWordDerivative word
            (matterCoordinateFirstOrderOperator
              fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
              field) point -
          fixedMatterAllOrderCommutedForcing word field point := by
    exact eq_sub_of_add_eq commuted.symm
  rw [actionRead] at normalForm
  have mapped := congrArg
    (fixedEvolutionTemporalPrincipalInverseCoordinateCLM point) normalForm
  simpa only [fixedEvolutionTemporalPrincipalInverseCoordinateCLM_left] using
    mapped.symm

/-- On an exact action zero the same all-order evolution has only the
recursively generated source commutator as forcing. -/
theorem fixedSpatialWordDerivative_temporalVolterraDefect_of_actionZero
    (word : List (Fin 3))
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ (⊤ : ℕ∞) field)
    (actionZero : ∀ point,
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point = 0)
    (point : BasePoint) :
    fieldDirectionalDerivative
          (fixedSpatialWordDerivative word field) point 0 -
        cauchySafeMatterVolterraVelocity
          fixedP506L0CauchySafeMatterGalerkinInputActual
          (fun candidate => matterCoordinateEquiv.symm
            (fixedSpatialWordDerivative word field candidate))
          point =
      -fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (fixedMatterAllOrderCommutedForcing word field point) := by
  rw [fixedSpatialWordDerivative_temporalVolterraDefect
    word field fieldSmooth point]
  have actionEq :
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field = 0 := by
    funext candidate
    exact actionZero candidate
  rw [actionEq, fixedSpatialWordDerivative_zero]
  simpa only [zero_sub] using
    (map_neg
      (fixedEvolutionTemporalPrincipalInverseCoordinateCLM point)
      (fixedMatterAllOrderCommutedForcing word field point))

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderVolterraEvolution
