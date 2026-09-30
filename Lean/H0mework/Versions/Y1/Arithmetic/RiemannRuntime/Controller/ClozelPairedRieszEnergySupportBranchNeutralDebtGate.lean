import H0mework.Versions.Y1.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Coupling.Representation.OffCenter.Root.LivingLawCanonicalRiemannA1cEnergySupportReceiptRoot
import H0mework.Versions.Y.Arithmetic.PrimeLeakage.NoGo.LivingLawCanonicalRiemannPrimeScaleBaseDebtClosureNoGo

/-!
# Premise-grounded branch-neutral A1c debt gate

The complete receipt root already contains the Euler--Mellin common action,
prime-exponent receipt relation, faithful joint effect, whole ledger and next.
Its energy-support coface chooses the total critical/off-center outcome before
any negative branch is named.  The critical outcome reaches the existing
separator consumer.  The off-center outcome remains attached to that same
rich root and its actual source-boundary write, while the inherited canonical
row is proved unable to serve as its debt lifecycle: it has zero budget and no
terminal.

This gate deliberately does not manufacture a fresh debt row.  Such a row
requires a source-generated admission event whose first write contains an
actual strict payment; the residual itself is only the demand for that event.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction
namespace BranchNeutralDebtGate

open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockEndpointFixedCoordinateReadback
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open InverseZeroFibre
open QRich
open A1cEnergySupportReceiptRoot
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation

noncomputable section

def temporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

@[simp] theorem visitAt_depth
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    temporalDepth?
      ⟨V, A1cEnergySupportReceiptRoot.root observation nontrivial,
        .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)⟩ =
      some depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change some (ProductiveFiniteRootHistoryAt.causalDepth
        (CanonicalUnitArithmeticRoot.finiteVisit depth).history + 1) =
          some (depth + 1)
      have prior : ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history = depth := by
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history) = some depth
            at inductionHypothesis
        exact Option.some.inj inductionHypothesis
      rw [prior]

/-- Exact process of the branch-neutral energy-support root itself. -/
def process
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth =>
    ⟨V, A1cEnergySupportReceiptRoot.root observation nontrivial,
      .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)⟩
  stateAt_injective := by
    intro left right equality
    have depth_eq := congrArg temporalDepth? equality
    rw [visitAt_depth observation nontrivial left,
      visitAt_depth observation nontrivial right] at depth_eq
    exact Option.some.inj depth_eq
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

/-- The inherited canonical row at the exact neutral-root initial current. -/
def baseDebtCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    SourceNativeRootDebtCurrentAt
      (process observation nontrivial)
      (rootLedgerEntry initialCurrent) where
  state := (process observation nontrivial).initial
  entry := rootLedgerEntry initialCurrent
  sameDebt := ⟨rfl, rfl⟩

theorem baseDebtCurrent_budget_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    (baseDebtCurrent observation nontrivial).budget = 0 := by
  rfl

abbrev baseDebtCurrent_noLocalTerminal
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceNativeRootDebtLocalTerminalAt
      (baseDebtCurrent observation nontrivial)) :=
  { false := fun terminal => nomatch terminal.terminal }

abbrev baseDebtCurrent_noPaidContinuation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt
      (baseDebtCurrent observation nontrivial)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero
    (baseDebtCurrent observation nontrivial)
    (baseDebtCurrent_budget_eq_zero observation nontrivial)

/-- Exact no-go at the branch-neutral root, not a neighboring process. -/
abbrev baseDebtCurrent_noNoetherianClosure
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceNativeNoetherianDebtClosureLaw
      (process observation nontrivial)
      (rootLedgerEntry initialCurrent)) :=
  no_noetherianDebtClosureLaw_of_budget_eq_zero_of_noLocalTerminal
    (baseDebtCurrent observation nontrivial)
    (baseDebtCurrent_budget_eq_zero observation nontrivial)
    (baseDebtCurrent_noLocalTerminal observation nontrivial)

/-- Critical root outcome with the complete premise chain and independent
q-rich consumer. -/
structure SupportedAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type where
  critical : observation.coordinate.re = 1 / 2
  outcome_eq :
    installedEnergySupportDisposition observation nontrivial =
      .critical critical
  root_factorizes : type_of%
    (installedFaces_factorize observation nontrivial)
  source_boundary_write : type_of%
    (stageThreeActionBoundary_receiptRootedWrite observation nontrivial)
  separator_zero :
    branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent observation)
        terminalReadbackStage terminalReadbackRow = 0

/-- Off-center root outcome.  It carries the complete actual receipt write,
not a detached failure bit.  It is still only a source-generated demand: the
old canonical row cannot be relabelled as its paid Noetherian debt. -/
structure MeasurementOnlyAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type where
  offCenter : observation.coordinate.re ≠ 1 / 2
  residual : OffCenterEnergySupportObstruction observation nontrivial
  measurementOnly : PairedRieszMeasurementOnlyResidual observation nontrivial
  outcome_eq :
    installedEnergySupportDisposition observation nontrivial =
      .offCenter offCenter residual
  root_factorizes : type_of%
    (installedFaces_factorize observation nontrivial)
  source_boundary_write : type_of%
    (stageThreeActionBoundary_receiptRootedWrite observation nontrivial)
  old_row_no_noetherian_closure :
    IsEmpty (SourceNativeNoetherianDebtClosureLaw
      (process observation nontrivial)
      (rootLedgerEntry initialCurrent))

inductive OutcomeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type where
  | supported (outcome : SupportedAt observation nontrivial)
  | measurementOnly
      (outcome : MeasurementOnlyAt observation nontrivial)

/-- The branch is generated from the root-installed total disposition.  No
`offCenter`, empty fibre or caller-selected outcome enters this constructor. -/
def generate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    OutcomeAt observation nontrivial := by
  generalize outcome_eq :
    installedEnergySupportDisposition observation nontrivial = outcome
  cases outcome with
  | critical critical =>
      exact .supported
        { critical := critical
          outcome_eq := outcome_eq
          root_factorizes := installedFaces_factorize observation nontrivial
          source_boundary_write :=
            stageThreeActionBoundary_receiptRootedWrite
              observation nontrivial
          separator_zero := by
            apply branchNormalizedQRichSeparator_eq_zero_of_radialDefect_zero
              observation nontrivial 0 terminalReadbackStage
                terminalReadbackRow
            exact zeroOwnedPositiveMellinRadialDefect_eq_zero_of_coordinate_re_eq_half
              observation nontrivial 0 critical }
  | offCenter offCenter residual =>
      exact .measurementOnly
        { offCenter := offCenter
          residual := residual
          measurementOnly :=
            pairedRieszMeasurementOnlyResidual_of_offCenter
              observation nontrivial offCenter
          outcome_eq := outcome_eq
          root_factorizes := installedFaces_factorize observation nontrivial
          source_boundary_write :=
            stageThreeActionBoundary_receiptRootedWrite
              observation nontrivial
          old_row_no_noetherian_closure :=
            baseDebtCurrent_noNoetherianClosure
              observation nontrivial }

/-- Exact authority boundary for the negative branch: its root outcome exists,
but neither a payment nor a terminal can be obtained by reusing the old row. -/
theorem MeasurementOnlyAt.old_row_cannot_supply_closure
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (outcome : MeasurementOnlyAt observation nontrivial) :
    IsEmpty (SourceNativeNoetherianDebtClosureLaw
      (process observation nontrivial)
      (rootLedgerEntry initialCurrent)) :=
  outcome.old_row_no_noetherian_closure

end
end BranchNeutralDebtGate
end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
