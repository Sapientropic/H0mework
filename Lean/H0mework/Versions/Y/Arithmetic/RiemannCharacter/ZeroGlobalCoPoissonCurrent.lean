import H0mework.Versions.Y.Arithmetic.RiemannCharacter.ZeroIntegralCharacterFullRowCycle
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzZeroGraphCokernel
import H0mework.Arithmetic.CoPoisson.RoleRepresentation

/-!
# Same-zero global co-Poisson coupling current

The common integral character carrier reads two concrete coupling currents.
At the Archimedean square-root scale its radial current is exactly the
existing positive-Mellin radial defect.  At an arithmetic row its prime
current is exactly the selected/reversal character difference consumed by
the existing q-rich full-row cycle.

For each fixed stage and row, these two generated values are installed as a
dependent child of the same-zero global co-Poisson/Müntz occurrence.  The
payload stores no no-flux equation, separator, fixedness, or zero field.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace Character
namespace GlobalCoPoissonCurrent

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open RootedAccountedUnfolding
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open IntegralCharacterGroupRing

noncomputable section

/-- The actual positive square-root scale used by the existing Mellin
dilation readback. -/
def stageSqrtScaleUnit (stage : Nat) : Units NNReal :=
  positiveRealUnit
    (Real.sqrt (QRich.blockQRichSuccessorScale stage : ℝ)) (by
      rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
      positivity)

/-- Difference of the selected and reversal character norms on the common
integral group-ring basis at the Archimedean square-root scale. -/
def groupRingRadialCurrent
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) : ℝ :=
  ‖(zeroOwnedIntegralCharacterOccurrence observation).root.2.1
      (delta (stageSqrtScaleUnit stage))‖ -
    ‖(zeroOwnedIntegralCharacterOccurrence observation).root.2.2
      (delta (stageSqrtScaleUnit stage))‖

theorem groupRingRadialCurrent_eq_zeroOwnedPositiveMellinRadialDefect
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    groupRingRadialCurrent observation stage =
      QRich.zeroOwnedPositiveMellinRadialDefect
        observation nontrivial stage := by
  unfold groupRingRadialCurrent
    QRich.zeroOwnedPositiveMellinRadialDefect stageSqrtScaleUnit
  rw [selected_sqrt_basis_readback observation nontrivial stage,
    reversal_sqrt_basis_readback observation nontrivial stage]

/-- Difference of the same two source-owned character evaluations at the
actual prime attached to a factor row. -/
def groupRingPrimeCurrent
    (observation : GeneratedRiemannZeroObservation)
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  (zeroOwnedIntegralCharacterOccurrence observation).root.2.1
      (delta (rowPrimeScaleUnit row)) -
    (zeroOwnedIntegralCharacterOccurrence observation).root.2.2
      (delta (rowPrimeScaleUnit row))

theorem groupRingPrimeCurrent_fullRow_readback
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    QRich.pointFullRowCycleCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (zeroIntegralCharacterPointFullRowCycle observation stage
          (delta (rowPrimeScaleUnit row))) =
      -(quotientCoefficient row : ℂ) *
        groupRingPrimeCurrent observation row := by
  exact zeroIntegralCharacterPointFullRowCycle_readback observation stage row
    (delta (rowPrimeScaleUnit row))

/-- The nonzero row coefficient makes the existing full-row readback a
faithful detector of the prime current.  This does not prove either side is
zero. -/
theorem groupRingPrimeCurrent_eq_zero_iff_fullRowReadback_eq_zero
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    QRich.pointFullRowCycleCReadback
          (mathlibZeroPoint observation.coordinate observation.mathlibZero)
          stage row
          (zeroIntegralCharacterPointFullRowCycle observation stage
            (delta (rowPrimeScaleUnit row))) = 0 ↔
      groupRingPrimeCurrent observation row = 0 := by
  rw [groupRingPrimeCurrent_fullRow_readback]
  have coefficientNe : -(quotientCoefficient row : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (Nat.cast_ne_zero.mpr
      (QRich.blockQRichQuotientCoefficient_ne_zero stage row))
  constructor
  · intro productZero
    exact (mul_eq_zero.mp productZero).resolve_left coefficientNe
  · intro currentZero
    rw [currentZero, mul_zero]

/-! ## Dependent current occurrence -/

/-- The radial current read directly from the character payload carried by
the co-Poisson occurrence. -/
def sourceRadialCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (stage : Nat) : ℝ :=
  ‖characterEvaluation source.1.2.selected
      (delta (stageSqrtScaleUnit stage))‖ -
    ‖characterEvaluation source.1.2.reversal
      (delta (stageSqrtScaleUnit stage))‖

/-- The arithmetic current read from that same character payload. -/
def sourcePrimeCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  characterEvaluation source.1.2.selected (delta (rowPrimeScaleUnit row)) -
    characterEvaluation source.1.2.reversal (delta (rowPrimeScaleUnit row))

/-- Only the two generated current values are stored. -/
structure GeneratedCurrentValues : Type where
  private mk ::
  radialCurrent : ℝ
  primeCurrent : ℂ

namespace GeneratedCurrentValues

/-- The global module behind every fixed current face is the already
generated integral scale carrier. -/
abbrev GlobalModuleCarrier (_face : GeneratedCurrentValues) :=
  ClozelGeneralizedDual.ThetaJRoleRepresentation.IntegralScaleCarrier

/-- The global remainder role is derived from the existing co-Poisson
coupling; it is not a stored payload field. -/
def remainderRole (_face : GeneratedCurrentValues) :
    GlobalModuleCarrier _face →ₗ[ℤ] ComplexTempered :=
  ClozelGeneralizedDual.GlobalCoPoissonRoleRepresentation.remainderRole

/-- Concrete coupling receipt on the unit basis, inherited from the existing
global role representation. -/
@[simp] theorem remainderRole_delta_one (face : GeneratedCurrentValues) :
    face.remainderRole
        (delta (1 : Units NNReal)) =
      clozelTemperedRemainder :=
  ClozelGeneralizedDual.GlobalCoPoissonRoleRepresentation.remainderRole_delta_one

end GeneratedCurrentValues

def generateCurrentValues
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    GeneratedCurrentValues :=
  ⟨sourceRadialCurrent observation nontrivial source stage,
    sourcePrimeCurrent observation nontrivial source row⟩

abbrev ZeroOwnedGlobalCoPoissonCurrentPayload
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  Σ _source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial,
    GeneratedCurrentValues

/-- The current is a dependent readout of the existing same-zero global
co-Poisson occurrence, not a no-flux settlement. -/
def zeroOwnedGlobalCoPoissonCurrentOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    RootedAccountedUnfolding
      (ZeroOwnedGlobalCoPoissonCurrentPayload observation nontrivial) :=
  (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
    observation nontrivial).map fun source =>
      ⟨source,
        generateCurrentValues observation nontrivial source stage row⟩

theorem zeroOwnedGlobalCoPoissonCurrentOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    (zeroOwnedGlobalCoPoissonCurrentOccurrence
        observation nontrivial stage row).map Sigma.fst =
      ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
        observation nontrivial := by
  rw [zeroOwnedGlobalCoPoissonCurrentOccurrence,
    RootedAccountedUnfolding.map_map]
  change (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

/-- Both the co-Poisson source and the integral-character sibling project to
the same multiplicative-character occurrence. -/
theorem zeroOwnedGlobalCoPoissonCurrentOccurrence_projects_to_commonCharacter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    ((zeroOwnedGlobalCoPoissonCurrentOccurrence
        observation nontrivial stage row).map Sigma.fst).map Sigma.fst =
      (zeroOwnedIntegralCharacterOccurrence observation).map Sigma.fst := by
  rw [zeroOwnedGlobalCoPoissonCurrentOccurrence_projects,
    ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence_projects,
    zeroOwnedIntegralCharacterOccurrence_projects]

@[simp] theorem zeroOwnedGlobalCoPoissonCurrentOccurrence_root_radial
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    (zeroOwnedGlobalCoPoissonCurrentOccurrence
        observation nontrivial stage row).root.2.radialCurrent =
      groupRingRadialCurrent observation stage :=
  rfl

@[simp] theorem zeroOwnedGlobalCoPoissonCurrentOccurrence_root_prime
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    (zeroOwnedGlobalCoPoissonCurrentOccurrence
        observation nontrivial stage row).root.2.primeCurrent =
      groupRingPrimeCurrent observation row :=
  rfl

/-- The fixed current face derives the existing global coupling receipt on
its integral-scale carrier; neither the remainder nor this equality is stored
in the occurrence payload. -/
theorem zeroOwnedGlobalCoPoissonCurrentOccurrence_root_remainderRole_delta_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    (zeroOwnedGlobalCoPoissonCurrentOccurrence
        observation nontrivial stage row).root.2.remainderRole
          (delta (1 : Units NNReal)) =
      clozelTemperedRemainder :=
  GeneratedCurrentValues.remainderRole_delta_one _

end
end GlobalCoPoissonCurrent
end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
