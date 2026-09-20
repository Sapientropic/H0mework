import H0mework.Physics.Admission.SU7A6DirectionsStandingAudit
import H0mework.Realization.CyclicMemory.P126

/-!
# Dependency-light SU(7) source/phase/field anchor core

This module contains the immutable physical lineage coordinates: the actual
endpoint-stable A6 source derivation, componentwise phase/H1 ledger, sigma,
color-loop field, and origin/current endpoint pair.  It does not import the
generated endpoint-repair relation or its terminal responsibility transport.

`SU7RicherLineageResponsibility` adds the repair transporter downstream while
the Stage-4 physical source imports only this core.
-/

namespace SaturationMonoid.PhysicsCore.SU7RicherLineageResponsibility

open StandardModelConstraint

noncomputable section

abbrev ComponentPhaseCochain :=
  Sum ThreeCycleTime ThreeCycleTime →
    Sum ThreeCycleTime ThreeCycleTime → Int

abbrev ComponentH1Ledger := Int × Int

def componentH1Ledger
    (cochain : ComponentPhaseCochain) : ComponentH1Ledger :=
  (threeAgentRingResidual (leftSelectedCochain cochain),
    threeAgentRingResidual (rightSelectedCochain cochain))

def ComponentH1Closed (cochain : ComponentPhaseCochain) : Prop :=
  componentH1Ledger cochain = 0

theorem componentH1Closed_iff_selectedEdgeExact
    (cochain : ComponentPhaseCochain) :
    ComponentH1Closed cochain ↔
      CycleEdgePotentialExplained
        (sumPerm threeCycleNext threeCycleNext) cochain := by
  rw [twoThreeCycleExact_iff_component_residuals_zero]
  simp [ComponentH1Closed, componentH1Ledger]

abbrev SourcePathData :=
  SU7A6GaugeStableRootGraphAdapter.StableDerivationState

structure SourcePhaseFieldAnchor where
  sourceRoot : SU7A6WeightLabel
  sourcePathData : SourcePathData
  sourcePath :
    (SU7A6GaugeStableRootGraphAdapter.sourceSystem
      sourceRoot sourcePathData).ReachableFrom 0 sourcePathData
  phaseCochain : ComponentPhaseCochain
  h1Closed : ComponentH1Closed phaseCochain
  sigma : Real
  field : ColorLoopField

namespace SourcePhaseFieldAnchor

def h1Ledger (anchor : SourcePhaseFieldAnchor) : ComponentH1Ledger :=
  componentH1Ledger anchor.phaseCochain

theorem h1Ledger_eq_zero (anchor : SourcePhaseFieldAnchor) :
    anchor.h1Ledger = 0 :=
  anchor.h1Closed

def ofStandingState
    (scale : RawAffineScaleValidity)
    (state : SU7A6SevenDirectionStandingAudit.State scale)
    (phaseCochain : ComponentPhaseCochain)
    (h1Closed : ComponentH1Closed phaseCochain) :
    SourcePhaseFieldAnchor where
  sourceRoot := state.six.base.rootLabel
  sourcePathData := state.six.base.moves
  sourcePath :=
    SU7A6GaugeStableRootGraphAdapter.reachableFrom_zero
      state.six.base.rootLabel state.six.base.moves state.six.base.moves
  phaseCochain := phaseCochain
  h1Closed := h1Closed
  sigma := scale.sigma
  field := state.six.base.field

end SourcePhaseFieldAnchor

structure RichSourcePhaseFieldLineage where
  anchor : SourcePhaseFieldAnchor
  originEndpoint : Nat × Nat
  endpoint : Nat × Nat

namespace RichSourcePhaseFieldLineage

def withEndpoint
    (lineage : RichSourcePhaseFieldLineage) (endpoint : Nat × Nat) :
    RichSourcePhaseFieldLineage where
  anchor := lineage.anchor
  originEndpoint := lineage.originEndpoint
  endpoint := endpoint

@[simp] theorem withEndpoint_anchor
    (lineage : RichSourcePhaseFieldLineage) (endpoint : Nat × Nat) :
    (lineage.withEndpoint endpoint).anchor = lineage.anchor :=
  rfl

@[simp] theorem withEndpoint_endpoint
    (lineage : RichSourcePhaseFieldLineage) (endpoint : Nat × Nat) :
    (lineage.withEndpoint endpoint).endpoint = endpoint :=
  rfl

@[simp] theorem withEndpoint_originEndpoint
    (lineage : RichSourcePhaseFieldLineage) (endpoint : Nat × Nat) :
    (lineage.withEndpoint endpoint).originEndpoint =
      lineage.originEndpoint :=
  rfl

@[simp] theorem withEndpoint_self
    (lineage : RichSourcePhaseFieldLineage) :
    lineage.withEndpoint lineage.endpoint = lineage := by
  cases lineage
  rfl

end RichSourcePhaseFieldLineage

end
end SaturationMonoid.PhysicsCore.SU7RicherLineageResponsibility
