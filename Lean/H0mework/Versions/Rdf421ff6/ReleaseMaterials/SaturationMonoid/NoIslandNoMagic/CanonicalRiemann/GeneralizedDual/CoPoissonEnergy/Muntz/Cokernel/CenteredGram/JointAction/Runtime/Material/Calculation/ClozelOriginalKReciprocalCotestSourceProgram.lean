import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram
import H0mework.Versions.V2.Arithmetic.RiemannBandKernel.Sampling
import H0mework.Versions.V2.Arithmetic.MellinTateSource.Isometry

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReciprocalCotestSourceCalculation
open Complex MeasureTheory BurnolPhysicalState SourceOperationEffects SourceOperationExecution

abbrev Value := OriginalKPowerWaveSourceCalculation.Value
abbrev Var := OriginalKPowerWaveSourceCalculation.Var
abbrev Base := OriginalKPowerWaveSourceCalculation.Base
abbrev Half := OriginalKPowerWaveSourceCalculation.Half
abbrev E := OriginalKPowerWaveSourceCalculation.E
abbrev sourceEnvironment := OriginalKPowerWaveSourceCalculation.sourceEnvironment
abbrev coordinate := OriginalKPowerWaveSourceCalculation.coordinate
abbrev fixedShift := OriginalKPowerWaveSourceCalculation.fixedShift

open private linear scale sub from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram

namespace Wave
export OriginalKPowerWaveSourceCalculation
  (wholeUCode wholeVCode nativeAction edgeIntegralCode starCoordinate)
end Wave
namespace Coupling
export OriginalWholeDebtRPowerWaveDilationSource (coupling0 coupling1)
end Coupling

/-- Sampling is the existing annular operation on the evaluated source, not a stored column. -/
private def annulusSamplingAction : BurnolL2 →+ BurnolL2 where
  toFun := fun value => burnolAnnulusSamplingL2 value 0
  map_zero' := by
    apply Lp.ext
    filter_upwards [burnolAnnulusSamplingL2_coeFn (0 : BurnolL2) 0,
      Lp.coeFn_zero ℂ 2 volume] with x sampleRead zeroRead
    rw [sampleRead, zeroRead]
    simp only [burnolAnnulusSamplingRaw, Nat.cast_zero, zero_add, one_mul]
    by_cases inside : x ∈ burnolSamplingAnnulus
    · rw [Set.indicator_of_mem inside, zeroRead]
    · rw [Set.indicator_of_notMem inside]
      rfl
  map_add' := by
    intro left right
    apply Lp.ext
    filter_upwards [burnolAnnulusSamplingL2_coeFn (left + right) 0,
      burnolAnnulusSamplingL2_coeFn left 0, burnolAnnulusSamplingL2_coeFn right 0,
      Lp.coeFn_add left right,
      Lp.coeFn_add (burnolAnnulusSamplingL2 left 0) (burnolAnnulusSamplingL2 right 0)]
      with x sumRead leftRead rightRead inputRead outputRead
    rw [outputRead, Pi.add_apply, sumRead, leftRead, rightRead]
    simp only [burnolAnnulusSamplingRaw, Nat.cast_zero, zero_add, one_mul]
    by_cases inside : x ∈ burnolSamplingAnnulus
    · simp only [Set.indicator_of_mem inside]
      exact inputRead
    · simp only [Set.indicator_of_notMem inside, add_zero]

def nativeInputCode (c : BurnolCompletedMellinCoordinate) : E :=
  sub (scale (Coupling.coupling0 c) Wave.wholeUCode)
    (scale (Coupling.coupling1 c) Wave.wholeVCode)

/-- This is the original signed Profile program's second row, with its own complete edge. -/
def sourceYCode (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : E :=
  sub (.linear (Wave.nativeAction (c.value - 1/2) endpoint) (nativeInputCode c))
    (scale (Coupling.coupling1 c) (Wave.edgeIntegralCode (Wave.starCoordinate c) endpoint))

def secondColumnCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  scale (1/2) (.add (sourceYCode c (-h)) (sourceYCode c h))

def reciprocalCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  linear burnolTateReciprocalL2 (.linear annulusSamplingAction (secondColumnCode c h))

/-- The original R acts after both source branches, annular sampling and Tate. -/
def code (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  scale (2*c.value - 1) (linear (burnolDirectRightResolventCLM c) (reciprocalCode c h))

theorem reciprocal_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (reciprocalCode c h).eval environment =
      burnolTateReciprocalL2
        (burnolAnnulusSamplingL2 ((secondColumnCode c h).eval environment) 0) := rfl

theorem code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (code c h).eval environment = (2*c.value - 1) •
      burnolDirectRightResolventCLM c ((reciprocalCode c h).eval environment) := rfl

theorem code_environment (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (before after : Env Value Var) : (code c h).eval before = (code c h).eval after := rfl

theorem code_effect (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment increment : Env Value Var) : (code c h).effect environment increment = 0 := by
  apply add_left_cancel (a := (code c h).eval environment)
  rw [← Expr.eval_update, code_environment c h (environment + increment) environment, add_zero]

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    0 < remaining (code c h) := by
  change 0 < remaining (reciprocalCode c h) + 1 + 1
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
      (coordinate observation nontrivial half occurrence).value = observation.coordinate ∧
      (reader observation nontrivial half occurrence).expression =
        code (coordinate observation nontrivial half occurrence) fixedShift := ⟨rfl, rfl, rfl⟩

end OriginalKReciprocalCotestSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
