import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKCoefficientBSelfCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.PowerWave

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPowerWaveSourceCalculation
open Complex MeasureTheory BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFinitePairing

abbrev Value := OriginalKCoefficientBSelfCalculation.Value
abbrev Var := OriginalKCoefficientBSelfCalculation.Var
abbrev Base := OriginalKCoefficientBSelfCalculation.Base
abbrev Half := OriginalKCoefficientBSelfCalculation.Half
abbrev E := Expr Value Var ()
abbrev sourceEnvironment := OriginalKCoefficientBSelfCalculation.sourceEnvironment
abbrev coordinate := OriginalKCoefficientBSelfCalculation.coordinate
abbrev fixedShift := OriginalKCoefficientBSelfCalculation.fixedShift
abbrev starCoordinate := OriginalKBFiniteCalculation.conjugateCoordinate

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
private def scale (scalar : ℂ) (input : E) : E :=
  linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) input
private def sub (left right : E) : E := .add left (scale (-1) right)
private def fourier (input : E) : E :=
  linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap input
private def dilation (h : ℝ) (input : E) : E :=
  linear (burnolMultiplicativeDilation h).toContinuousLinearEquiv.toContinuousLinearMap input

private theorem sub_eval (left right : E) (environment : Env Value Var) :
    (sub left right).eval environment = left.eval environment - right.eval environment := by
  change left.eval environment + (-1 : ℂ) • right.eval environment = _
  rw [neg_one_smul, sub_eq_add_neg]

/-- The operation is the existing signed Bochner integral on its actual L² input. -/
def nativeAction (lambda : ℂ) (h : ℝ) : BurnolL2 →+ BurnolL2 where
  toFun := fun value => nativeIntegral lambda value h
  map_zero' := by simp [nativeIntegral, nativeIntegrand]
  map_add' := by
    intro left right
    have source : nativeIntegrand lambda (left + right) h =
        fun time => nativeIntegrand lambda left h time + nativeIntegrand lambda right h time := by
      funext time
      simp only [nativeIntegrand, map_add, smul_add]
    change (∫ time : ℝ in (0 : ℝ)..h, nativeIntegrand lambda (left + right) h time) = _
    rw [source, intervalIntegral.integral_add
      (nativeIntegrand_integrable lambda left h) (nativeIntegrand_integrable lambda right h)]
    rfl

private def native (c : BurnolCompletedMellinCoordinate) (h : ℝ) (input : E) : E :=
  .linear (nativeAction (star c.value - 1/2) h) input

def wholeUCode : E := .const Response.wholeU
def wholeVCode : E := .const Response.wholeV
def seedCode : E := .const OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed

/-- The edge primitive is recovered by the paid original seed R action, not inserted as a leaf. -/
def edgeCode (c : BurnolCompletedMellinCoordinate) : E :=
  sub (scale (-((starCoordinate c).value - 1)/2)
    (linear (burnolDirectRightResolventCLM (starCoordinate c)) seedCode)) seedCode

def edgeIntegralCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  sub (dilation h (edgeCode c))
    (scale (fullMellinTranslationCharacter (star c.value) h) (edgeCode c))

/-- Fourier edge keeps its own 2λ integral and its full signed primitive orbit. -/
def fourierEdgeIntegralCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  sub (scale (2*(star c.value - 1/2)) (native c h (fourier (edgeCode c))))
    (sub (dilation h (fourier (edgeCode c)))
      (scale (fullMellinTranslationCharacter (star c.value) h) (fourier (edgeCode c))))

def profileCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  sub (native c h (sub (fourier wholeUCode) wholeVCode)) (edgeIntegralCode c h)
def fourierProfileCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  sub (native c h (sub wholeUCode (fourier wholeVCode))) (fourierEdgeIntegralCode c h)

def singleCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  fourier (.add
    (scale (OriginalWholeDebtRPowerWaveDilationSource.coupling1 c)
      (profileCode (OriginalPrimitiveRankBalance.conjugateCoordinate c) (-h)))
    (scale (OriginalWholeDebtRPowerWaveDilationSource.coupling0 c)
      (fourierProfileCode (OriginalPrimitiveRankBalance.conjugateCoordinate c) (-h))))

def code (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  scale (1/2) (.add (singleCode c h) (singleCode c (-h)))


theorem code_environment (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (before after : Env Value Var) : (code c h).eval before = (code c h).eval after := rfl

theorem code_effect (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment increment : Env Value Var) : (code c h).effect environment increment = 0 := by
  apply add_left_cancel (a := (code c h).eval environment)
  rw [← Expr.eval_update, code_environment c h (environment + increment) environment, add_zero]

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (h : ℝ) : 0 < remaining (code c h) := by
  change 0 < remaining (.add (singleCode c h) (singleCode c (-h))) + 1
  omega

def reader (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  { environment := sourceEnvironment
    expression := code (coordinate observation nontrivial half occurrence) fixedShift }

theorem reader_source (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (reader observation nontrivial half occurrence).environment = sourceEnvironment ∧
      (reader observation nontrivial half occurrence).expression =
        code (coordinate observation nontrivial half occurrence) fixedShift := ⟨rfl, rfl⟩

end OriginalKPowerWaveSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
