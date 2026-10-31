import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Future.RelationIndexedFuture
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.ActionableFreedomChange

/-!
# Capture-adjusted actionable exit cones

An actionable exit is not a nominal balance and not an observer quote.  It is
an inhabited, non-idle continuation in an existing source-generated relation
future which survives every capture barrier generated at the exact open
settlement currently backing purchasing power.

The finite carrier below is the relation compiler's existing current code
carrier.  No future table, price value, affordability oracle, actor registry,
or settlement ledger is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UBI

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power

universe u v w x q

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {actorFace : M0BoundaryFace.{u, v, w} occurrenceOf}
variable
  {relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, w, x}
    occurrenceOf game actorFace}

/-- A source-fixed capture classifier at one exact open settlement.

A positive capture verdict must return that very settlement.  Hence the
classifier cannot manufacture a price value, substitute a sibling
settlement, or turn an observer readout into authority. -/
structure SourceOwnedPriceCaptureCompilerAt
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, w, x}
      occurrenceOf game actorFace)
    (OpenSettlement : Type q)
    (openSettlement : OpenSettlement) : Type (max x q) where
  Captures : relationCompiler.FutureCode → Prop
  capturesDecidable : DecidablePred Captures
  captureSettlement : ∀ code, Captures code → OpenSettlement
  captureSettlement_eq : ∀ code captured,
    captureSettlement code captured = openSettlement

namespace SourceOwnedPriceCaptureCompilerAt

variable {OpenSettlement : Type q} {openSettlement : OpenSettlement}

/-- Codes that remain actionable after the exact settlement's source-owned
capture classifier has run. -/
noncomputable def survivingExitCodes
    (capture : SourceOwnedPriceCaptureCompilerAt relationCompiler
      OpenSettlement openSettlement)
    (relation : relationCompiler.GeneratedRelation) :
    Finset relationCompiler.FutureCode := by
  classical
  exact (relationCompiler.actionableFutureCodesAt relation .target).filter
    fun code => ¬ capture.Captures code

theorem mem_survivingExitCodes_iff
    (capture : SourceOwnedPriceCaptureCompilerAt relationCompiler
      OpenSettlement openSettlement)
    (relation : relationCompiler.GeneratedRelation)
    (code : relationCompiler.FutureCode) :
    code ∈ capture.survivingExitCodes relation ↔
      code ∈ relationCompiler.futureCodeCarrier ∧
      Nonempty
        (relationCompiler.FutureContinuationAt relation.1 .target code) ∧
      ¬ relationCompiler.futureIdle code ∧
      ¬ capture.Captures code := by
  classical
  simp only [survivingExitCodes, Finset.mem_filter,
    SourceOwnedRelationRoleCompiler.mem_actionableFutureCodesAt_iff]
  tauto

end SourceOwnedPriceCaptureCompilerAt

/-- Exact beneficiary/relation incidence whose target future is evaluated
against one source-owned capture classifier. -/
structure CaptureAdjustedExitConeAt
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, w, x}
      occurrenceOf game actorFace)
    (actor : relationCompiler.Actor)
    (relation : relationCompiler.GeneratedRelation)
    {OpenSettlement : Type q}
    {openSettlement : OpenSettlement}
    (capture : SourceOwnedPriceCaptureCompilerAt relationCompiler
      OpenSettlement openSettlement) : Type (max x q) where
  interest : relationCompiler.GeneratedInterestAt actor relation

namespace CaptureAdjustedExitConeAt

variable {actor : relationCompiler.Actor}
variable {relation : relationCompiler.GeneratedRelation}
variable {OpenSettlement : Type q} {openSettlement : OpenSettlement}
variable {capture : SourceOwnedPriceCaptureCompilerAt relationCompiler
  OpenSettlement openSettlement}

/-- Sole cone producer from the existing generated-interest incidence. -/
def generate
    (interest : relationCompiler.GeneratedInterestAt actor relation) :
    CaptureAdjustedExitConeAt relationCompiler actor relation capture :=
  ⟨interest⟩

noncomputable def survivingCodes
    (_cone : CaptureAdjustedExitConeAt
      relationCompiler actor relation capture) :
    Finset relationCompiler.FutureCode :=
  capture.survivingExitCodes relation

/-- A surviving code is the actual exit witness.  The carrier is a subtype
of the compiler-generated target future, not a caller-selected future set. -/
def ActionableExitAt
    (cone : CaptureAdjustedExitConeAt
      relationCompiler actor relation capture) :=
  { code : relationCompiler.FutureCode // code ∈ cone.survivingCodes }

/-- Complete capture means every generated target-side actionable code is
captured by an exact open-settlement witness. -/
def FullPriceCaptureAt
    (_cone : CaptureAdjustedExitConeAt
      relationCompiler actor relation capture) : Prop :=
  ∀ code,
    ActionableAt relationCompiler.futureIdle
      (relationCompiler.futureCodesAt relation .target) code →
    capture.Captures code

variable (cone : CaptureAdjustedExitConeAt
  relationCompiler actor relation capture)

theorem actionableExit_nonempty_iff :
    Nonempty cone.ActionableExitAt ↔
      ∃ code,
        code ∈ relationCompiler.futureCodeCarrier ∧
        Nonempty
          (relationCompiler.FutureContinuationAt relation.1 .target code) ∧
        ¬ relationCompiler.futureIdle code ∧
        ¬ capture.Captures code := by
  constructor
  · rintro ⟨⟨code, member⟩⟩
    exact ⟨code,
      (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
        capture relation code).mp member⟩
  · rintro ⟨code, generated⟩
    exact ⟨⟨code,
      (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
        capture relation code).mpr generated⟩⟩

/-- Every actionable exit carries the original domain-native continuation
witness generated by the relation compiler. -/
theorem actionableExit_has_witnessed_continuation
    (exit : cone.ActionableExitAt) :
    ∃ continuation :
        relationCompiler.FutureContinuationAt relation.1 .target exit.1,
      relationCompiler.FutureContinuationWitnessAt relation.1 .target exit.1
        continuation := by
  have generated :=
    (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
      capture relation exit.1).mp exit.2
  have futureMember :
      exit.1 ∈ relationCompiler.futureCodesAt relation .target :=
    (relationCompiler.mem_futureCodesAt_iff relation .target exit.1).mpr
      ⟨generated.1, generated.2.1⟩
  exact relationCompiler.futureCode_has_witnessed_continuation relation
    futureMember

/-- Full capture is exactly the absence of actionable exit capacity. -/
theorem isEmpty_actionableExit_iff_fullPriceCapture :
    IsEmpty cone.ActionableExitAt ↔ cone.FullPriceCaptureAt := by
  constructor
  · intro empty code actionable
    by_contra uncaptured
    have generated :
        code ∈ relationCompiler.futureCodeCarrier ∧
          Nonempty
            (relationCompiler.FutureContinuationAt relation.1 .target code) ∧
          ¬ relationCompiler.futureIdle code ∧
          ¬ capture.Captures code := by
      have future :=
        (relationCompiler.mem_futureCodesAt_iff relation .target code).mp
          actionable.1
      exact ⟨future.1, future.2, actionable.2, uncaptured⟩
    exact empty.false ⟨code,
      (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
        capture relation code).mpr generated⟩
  · intro full
    exact ⟨fun exit => by
      have generated :=
        (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
          capture relation exit.1).mp exit.2
      have actionable : ActionableAt relationCompiler.futureIdle
          (relationCompiler.futureCodesAt relation .target) exit.1 := by
        exact ⟨
          (relationCompiler.mem_futureCodesAt_iff relation .target exit.1).mpr
            ⟨generated.1, generated.2.1⟩,
          generated.2.2.1⟩
      exact generated.2.2.2 (full exit.1 actionable)⟩

/-- A positive capture verdict is always witnessed by the same exact open
settlement that indexed the cone. -/
theorem capturedCode_returns_exact_openSettlement
    (code : relationCompiler.FutureCode)
    (captured : capture.Captures code) :
    capture.captureSettlement code captured = openSettlement :=
  capture.captureSettlement_eq code captured

end CaptureAdjustedExitConeAt

end UBI
end Society
end ProcessGame
end SaturationMonoid
