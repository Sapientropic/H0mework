/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityProcess
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Space.SourceGeneratedCrossing

/-!
# M11 generated-crossing fixture

This fixture interprets the three recurrent M10 queue occurrences as directed
crossings.  The first and recurrent positions store the same process state,
but receive different site lineages and flow payloads while sharing one
generated boundary lineage.  Thus neither state equality nor endpoint gauge
can erase actual crossing identity.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M11GeneratedSocialSpaceCrossingFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space
open M10OccurrenceCapacityProcessFixture

/-- Generated site-lineage labels for the three fixture crossings. -/
inductive SiteLabel where
  | aprilJayYork
  | springQueensPlaza
  | winterClintonJoralemon
  | manhattanSouthFlowCore
  | manhattanMidtownFlowCore
  deriving DecidableEq, Repr

/-- A site seed remembers the exact state where the source emitted it. -/
structure SiteSeed where
  state : State
  label : SiteLabel
  deriving DecidableEq, Repr

def siteSeedAt (_source : Source) (state : State) (seed : SiteSeed) : Prop :=
  seed.state = state

abbrev SiteLineage (_source : Source) := SiteLabel

def siteLineageOf (source : Source)
    (seed : SourceSeed occurrenceOf SiteSeed siteSeedAt source) :
    SiteLineage source :=
  seed.1.label

/-- Position-sensitive source readout.  The recurrent false state is assigned
a different station lineage from the initial false state. -/
def originLabelAt (position : TracePosition game) : SiteLabel :=
  if position = firstPosition then .aprilJayYork
  else if position = middlePosition then .springQueensPlaza
  else .winterClintonJoralemon

def targetLabelAt (position : TracePosition game) : SiteLabel :=
  if position = middlePosition then .manhattanMidtownFlowCore
  else .manhattanSouthFlowCore

/-- Flow is a source payload of the exact crossing, not an edge weight later
attached to a graph. -/
structure FlowPayload where
  monthlyEvents : Nat
  deriving DecidableEq, Repr

def flowAt (position : TracePosition game) : FlowPayload :=
  if position = firstPosition then ⟨8754⟩
  else if position = middlePosition then ⟨9070⟩
  else ⟨2757⟩

/-- The shared mechanism class is generated as a boundary lineage. -/
inductive BoundaryLabel where
  | nearEastRiverBridgeOrWaterfront
  deriving DecidableEq, Repr

structure BoundarySeed where
  state : State
  label : BoundaryLabel
  deriving DecidableEq, Repr

def boundarySeedAt
    (_source : Source) (state : State) (seed : BoundarySeed) : Prop :=
  seed.state = state

abbrev BoundaryLineage (_source : Source) := BoundaryLabel

def boundaryLineageOf (source : Source)
    (seed : SourceSeed occurrenceOf BoundarySeed boundarySeedAt source) :
    BoundaryLineage source :=
  seed.1.label

/-- All three exact fixture crossings activate the same boundary mechanism.
The classifier is total because this is a positive regression fixture. -/
abbrev rateCompiler : SourceOwnedOccurrenceRateCompiler.{0, 0, 0, 0, 0}
    game Seed seedAt Lineage lineageOf focalSeed :=
  M10OccurrenceCapacityProcessFixture.compiler

def crossingCompiler : SourceOwnedCrossingCompiler.{0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0} rateCompiler where
  SiteSeed := SiteSeed
  SiteSeedAt := siteSeedAt
  SiteLineage := SiteLineage
  siteLineageOf := siteLineageOf
  originSeedAt := fun crossing =>
    ⟨crossing.state, originLabelAt crossing.position⟩
  targetSeedAt := fun crossing =>
    ⟨crossing.state, targetLabelAt crossing.position⟩
  originSeedIncidence := by
    intro crossing
    rfl
  targetSeedIncidence := by
    intro crossing
    rfl
  FlowPayloadAt := fun _crossing => FlowPayload
  flowPayloadAt := fun crossing => flowAt crossing.position
  BoundarySeed := BoundarySeed
  BoundarySeedAt := boundarySeedAt
  BoundaryLineage := BoundaryLineage
  boundaryLineageOf := boundaryLineageOf
  BoundaryActiveAt := fun _crossing => PUnit
  BoundaryInactiveAt := fun _crossing => PEmpty
  classifyBoundary := fun _crossing => .inl PUnit.unit
  boundarySeedAt := fun crossing _active =>
    ⟨crossing.state, .nearEastRiverBridgeOrWaterfront⟩
  boundarySeedIncidence := by
    intro crossing active
    cases active
    rfl

def firstCrossing : crossingCompiler.ExactCrossing := firstExactUnit

def middleCrossing : crossingCompiler.ExactCrossing := middleExactUnit

def recurrentCrossing : crossingCompiler.ExactCrossing := recurrentExactUnit

@[simp] theorem first_origin_lineage :
    (firstCrossing.originSite crossingCompiler).1 = .aprilJayYork := by
  rfl

@[simp] theorem middle_origin_lineage :
    (middleCrossing.originSite crossingCompiler).1 = .springQueensPlaza := by
  rfl

@[simp] theorem recurrent_origin_lineage :
    (recurrentCrossing.originSite crossingCompiler).1 =
      .winterClintonJoralemon := by
  rfl

@[simp] theorem first_target_lineage :
    (firstCrossing.targetSite crossingCompiler).1 =
      .manhattanSouthFlowCore := by
  rfl

@[simp] theorem recurrent_target_lineage :
    (recurrentCrossing.targetSite crossingCompiler).1 =
      .manhattanSouthFlowCore := by
  rfl

@[simp] theorem first_flow_events :
    (firstCrossing.flowPayload crossingCompiler).monthlyEvents = 8754 := by
  rfl

@[simp] theorem recurrent_flow_events :
    (recurrentCrossing.flowPayload crossingCompiler).monthlyEvents = 2757 := by
  rfl

/-- The recurring process state does not imply station-bearer persistence. -/
theorem recurrent_state_same_but_origin_lineage_changes :
    firstCrossing.state = recurrentCrossing.state ∧
      firstCrossing.originSite crossingCompiler ≠
        recurrentCrossing.originSite crossingCompiler := by
  refine ⟨rfl, ?_⟩
  intro equality
  have valueEquality := congrArg Subtype.val equality
  simp at valueEquality

/-- The two seasonal crossings share a target site while remaining distinct
actual crossing occurrences. -/
theorem same_target_does_not_collapse_crossing :
    firstCrossing.targetSite crossingCompiler =
        recurrentCrossing.targetSite crossingCompiler ∧
      firstCrossing ≠ recurrentCrossing := by
  refine ⟨by apply Subtype.ext; rfl, ?_⟩
  exact SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
    recurrent_positions_are_distinct

end
end M11GeneratedSocialSpaceCrossingFixture
end Society
end ProcessGame
end SaturationMonoid
