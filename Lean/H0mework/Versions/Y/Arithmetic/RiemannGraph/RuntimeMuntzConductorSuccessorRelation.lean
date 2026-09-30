import H0mework.Versions.Y.Arithmetic.RiemannGraph.RuntimeMuntzConductorCofinalCurrent

/-!
# Actual conductor-prefix successor relation

The full test/scale-valued Euler-conductor prefix is exposed as an actual
cofinal relation.  Its next prefix is the old prefix plus the generated
increment.  The relation keeps the cutoff and increment receipt; no scalar
summary, completed future or target vanishing law enters the evaluator.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History

open CanonicalUnitArithmeticRoot
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open CofinalHistorySettlement
open Material

noncomputable section

inductive ConductorHistoryRole
  | prefix
  | increment
  deriving DecidableEq

abbrev ConductorHistoryGenerator := Nat × ConductorHistoryRole

/-- The evaluator retains every Schwartz test and every positive-scale
coordinate instead of freezing a caller-selected probe. -/
abbrev ConductorHistoryCarrier := SchwartzMap ℝ ℂ → ℝ → ℂ

def conductorHistoryAtom
    (cutoff : Nat) (role : ConductorHistoryRole) :
    ConductorHistoryGenerator →₀ ℤ :=
  Finsupp.single (cutoff, role) 1

def conductorSuccessorRelation (cutoff : Nat) :
    ConductorHistoryGenerator →₀ ℤ :=
  conductorHistoryAtom (cutoff + 1) .prefix -
    conductorHistoryAtom cutoff .prefix -
      conductorHistoryAtom cutoff .increment

def conductorHistoryGeneratorValue
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    ConductorHistoryGenerator → ConductorHistoryCarrier
  | (cutoff, .prefix) => fun test scale =>
      runtimeFaceConductorDilationPrefix face test scale cutoff
  | (cutoff, .increment) => fun test scale =>
      runtimeFaceConductorDilationTerm face test scale cutoff

def conductorHistoryFreeEvaluation
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    (ConductorHistoryGenerator →₀ ℤ) →ₗ[ℤ]
      ConductorHistoryCarrier :=
  (Finsupp.liftAddHom fun generator =>
    AddMonoidHom.flip (smulAddHom ℤ ConductorHistoryCarrier)
      (conductorHistoryGeneratorValue face generator)).toIntLinearMap

@[simp] theorem conductorHistoryFreeEvaluation_atom
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) (role : ConductorHistoryRole) :
    conductorHistoryFreeEvaluation face
        (conductorHistoryAtom cutoff role) =
      conductorHistoryGeneratorValue face (cutoff, role) := by
  simp [conductorHistoryFreeEvaluation, conductorHistoryAtom]

/-- The exact runtime successor law kills the complete function-valued
relation, not only one selected scalar evaluation. -/
theorem conductorSuccessorRelation_evaluates_zero
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) :
    conductorHistoryFreeEvaluation face
        (conductorSuccessorRelation cutoff) = 0 := by
  funext test scale
  simp only [conductorSuccessorRelation, map_sub,
    conductorHistoryFreeEvaluation_atom, Pi.sub_apply, Pi.zero_apply]
  change runtimeFaceConductorDilationPrefix face test scale (cutoff + 1) -
      runtimeFaceConductorDilationPrefix face test scale cutoff -
        runtimeFaceConductorDilationTerm face test scale cutoff = 0
  rw [runtimeFaceConductorDilationPrefix_succ]
  ring

def conductorHistoryShiftGenerator :
    ConductorHistoryGenerator → ConductorHistoryGenerator
  | (cutoff, role) => (cutoff + 1, role)

def conductorHistoryShiftRelation
    (relation : ConductorHistoryGenerator →₀ ℤ) :
    ConductorHistoryGenerator →₀ ℤ :=
  relation.mapDomain conductorHistoryShiftGenerator

@[simp] theorem conductorHistoryShiftRelation_atom
    (cutoff : Nat) (role : ConductorHistoryRole) :
    conductorHistoryShiftRelation (conductorHistoryAtom cutoff role) =
      conductorHistoryAtom (cutoff + 1) role := by
  simp [conductorHistoryShiftRelation, conductorHistoryAtom,
    conductorHistoryShiftGenerator]

@[simp] theorem conductorHistoryShiftRelation_successor
    (cutoff : Nat) :
    conductorHistoryShiftRelation (conductorSuccessorRelation cutoff) =
      conductorSuccessorRelation (cutoff + 1) := by
  simp [conductorHistoryShiftRelation, conductorSuccessorRelation,
    conductorHistoryAtom, conductorHistoryShiftGenerator,
    Finsupp.mapDomain_sub]

def conductorSuccessorPresentedEvent (cutoff : Nat) :
    PresentedRelationEventAt ConductorHistoryGenerator :=
  .relation (conductorSuccessorRelation cutoff)

def conductorHistorySeedAt (cutoff : Nat) :
    RootedAccountedUnfolding
      (PresentedRelationEventAt ConductorHistoryGenerator) :=
  RootedAccountedUnfolding.zero (conductorSuccessorPresentedEvent cutoff)

def conductorHistoryContinuationAt :
    PresentedRelationEventAt ConductorHistoryGenerator →
      RootedAccountedUnfolding
        (PresentedRelationEventAt ConductorHistoryGenerator)
  | .generator generator =>
      RootedAccountedUnfolding.zero
        (.generator (conductorHistoryShiftGenerator generator))
  | .relation relation =>
      RootedAccountedUnfolding.zero
        (.relation (conductorHistoryShiftRelation relation))

def conductorHistoryContinuation : RootedAccountedUnfolding
    (PresentedRelationEventAt ConductorHistoryGenerator →
      RootedAccountedUnfolding
        (PresentedRelationEventAt ConductorHistoryGenerator)) :=
  RootedAccountedUnfolding.zero conductorHistoryContinuationAt

@[simp] theorem conductorHistoryContinuationAt_successor
    (cutoff : Nat) :
    conductorHistoryContinuationAt
        (conductorSuccessorPresentedEvent cutoff) =
      conductorHistorySeedAt (cutoff + 1) := by
  simp [conductorHistoryContinuationAt,
    conductorSuccessorPresentedEvent, conductorHistorySeedAt]

end
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
