import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKCoefficientBSelfCalculation
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Seed

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKWholeDebtRSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution

abbrev Value := OriginalKBFiniteCalculation.Value
abbrev Var := OriginalKBFiniteCalculation.Var
abbrev E := Expr Value Var ()

private def sourceFactor (h : ℝ) : ℂ := -(Real.exp (h / 4) : ℂ) / 2

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
private def scale (z : ℂ) (input : E) : E :=
  linear (z • ContinuousLinearMap.id ℂ BurnolL2) input
private def sub (left right : E) : E := .add left (scale (-1) right)

/-- The two already generated Pa source waves are inputs; the R result is never a leaf. -/
def waveCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  scale (sourceFactor h)
    (.add (.const (OriginalRieszFinitePairing.CoPoisson.positionWave c h))
      (linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap
        (.const (OriginalRieszFinitePairing.CoPoisson.fourierWave c h))))

/-- K is calculated from the original eta, elementary and unit source subtrees. -/
def debtCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .add
    (sub (waveCode c h)
      (scale (2 * sourceFactor h)
        (linear (pairedBurnolMultiplicativeDilation h)
          (OriginalKCoefficientBSelfCalculation.sourceKernelCode c))))
    (scale (2 * sourceFactor h * pairedMellinTranslationCharacter (star c.value) h)
      (OriginalKCoefficientBSelfCalculation.sourceKernelCode c))

/-- The original R acts on the complete source word before any projection. -/
def code (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  linear (burnolDirectRightResolventCLM c) (debtCode c h)

theorem wave_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (waveCode c h).eval environment = sourceFactor h •
      (OriginalRieszFinitePairing.CoPoisson.positionWave c h +
        fourierL2 (OriginalRieszFinitePairing.CoPoisson.fourierWave c h)) := rfl

theorem debt_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (debtCode c h).eval environment =
      (waveCode c h).eval environment - (2 * sourceFactor h) •
        pairedBurnolMultiplicativeDilation h
          ((OriginalKCoefficientBSelfCalculation.sourceKernelCode c).eval environment) +
        (2 * sourceFactor h * pairedMellinTranslationCharacter (star c.value) h) •
          ((OriginalKCoefficientBSelfCalculation.sourceKernelCode c).eval environment) := by
  change (waveCode c h).eval environment + (-1 : ℂ) •
    ((2 * sourceFactor h) • pairedBurnolMultiplicativeDilation h
      ((OriginalKCoefficientBSelfCalculation.sourceKernelCode c).eval environment)) + _ = _
  rw [neg_one_smul, sub_eq_add_neg]
  rfl

theorem code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (code c h).eval environment =
      burnolDirectRightResolventCLM c ((debtCode c h).eval environment) := rfl

theorem code_effect (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment increment : Env Value Var) :
    (code c h).effect environment increment =
      burnolDirectRightResolventCLM c ((debtCode c h).effect environment increment) := rfl

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    0 < remaining (code c h) := by
  change 0 < remaining (debtCode c h) + 1
  omega

end OriginalKWholeDebtRSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
