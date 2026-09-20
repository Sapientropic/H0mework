import Mathlib.Tactic
import H0mework.Physics.MixingSources.P582

/-!
# Proposition 583: the selected SU(7) discrete seed carries the depth table

P582 produced the CKM depth sum from a named nine-row Yukawa depth table.  P276
already had the right structural socket for such data:

`DiscreteStandardModelSeed.su7.yukawaDepth : YukawaParameter -> Nat`.

This file plugs the P582 table into that socket and exposes the corresponding
finite target seed.  This is not yet the deeper representation-theoretic proof
that SU(7) breaking *forces* the nine integers.  It is the producer target that
such a proof must hit, with no remaining ambiguity about where the integers
live in the Standard-Model certificate stack.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## A concrete sector schedule target -/

/-- The selected coarse consolidation stage for each SU(7)-side sector.

The stages are finite producer data.  They keep the intended order visible
while the deeper SU(7)-breaking dynamics proof remains open.
-/
def selectedSectorStage : ConsolidationSector -> Nat
  | .unifiedFiber => 0
  | .color => 1
  | .weak => 2
  | .hypercharge => 3
  | .higgs => 4
  | .yukawa => 5
  | .flavor => 6

/-- THEOREM 1: the selected sector stages are strictly ordered from unified
fiber through flavor. -/
theorem selectedSectorStage_chain :
    selectedSectorStage .unifiedFiber <
        selectedSectorStage .color ∧
      selectedSectorStage .color <
        selectedSectorStage .weak ∧
      selectedSectorStage .weak <
        selectedSectorStage .hypercharge ∧
      selectedSectorStage .hypercharge <
        selectedSectorStage .higgs ∧
      selectedSectorStage .higgs <
        selectedSectorStage .yukawa ∧
      selectedSectorStage .yukawa <
        selectedSectorStage .flavor := by
  norm_num [selectedSectorStage]

/-! ## Selected CKM finite depths -/

/-- Finite CKM depth fields induced by the P582 Jarlskog depth producer.

The three angle slots store the positive magnitudes of the named quark-depth
differences; the `delta` slot stores the full Jarlskog four-product depth sum.
-/
def selectedCKMIntegerDepth : CKMParameter -> Nat
  | .theta12 => ckmDepthDelta_us_fromYukawaDepths.natAbs
  | .theta23 => ckmDepthDelta_cb_fromYukawaDepths.natAbs
  | .theta13 => ckmDepthDelta_ub_conj_fromYukawaDepths.natAbs
  | .delta => ckmCPDepthSum

/-- THEOREM 2: the selected CKM finite depths are `226,143,562,386`. -/
theorem selectedCKMIntegerDepth_values :
    selectedCKMIntegerDepth .theta12 = 226 ∧
      selectedCKMIntegerDepth .theta23 = 143 ∧
      selectedCKMIntegerDepth .theta13 = 562 ∧
      selectedCKMIntegerDepth .delta = 386 := by
  norm_num [selectedCKMIntegerDepth, ckmDepthDelta_us_fromYukawaDepths,
    ckmDepthDelta_cb_fromYukawaDepths,
    ckmDepthDelta_ub_conj_fromYukawaDepths, selectedYukawaIntegerDepthZ,
    selectedYukawaIntegerDepth, ckmCPDepthSum]

/-! ## The selected SU(7) discrete consolidation data -/

/-- The finite SU(7)-side consolidation data targeted by the current
Standard-Model producer chain. -/
def selectedSU7DiscreteConsolidationData :
    SU7DiscreteConsolidationData where
  sectorStage := selectedSectorStage
  yukawaDepth := selectedYukawaIntegerDepth
  ckmDepth := selectedCKMIntegerDepth

/-- THEOREM 3: the selected SU(7) data carries the P582 Yukawa depth table. -/
theorem selectedSU7_yukawaDepth_eq
    (y : YukawaParameter) :
    selectedSU7DiscreteConsolidationData.yukawaDepth y =
      selectedYukawaIntegerDepth y := by
  rfl

/-- THEOREM 4: the selected SU(7) data carries the P582 mass-order display. -/
theorem selectedSU7_yukawaDepth_massOrder_eq :
    [ selectedSU7DiscreteConsolidationData.yukawaDepth .top
    , selectedSU7DiscreteConsolidationData.yukawaDepth .bottom
    , selectedSU7DiscreteConsolidationData.yukawaDepth .tau
    , selectedSU7DiscreteConsolidationData.yukawaDepth .charm
    , selectedSU7DiscreteConsolidationData.yukawaDepth .muon
    , selectedSU7DiscreteConsolidationData.yukawaDepth .strange
    , selectedSU7DiscreteConsolidationData.yukawaDepth .down
    , selectedSU7DiscreteConsolidationData.yukawaDepth .up
    , selectedSU7DiscreteConsolidationData.yukawaDepth .electron
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rfl

/-- THEOREM 5: the selected SU(7) data carries the CKM delta depth `386`. -/
theorem selectedSU7_ckmDeltaDepth_eq :
    selectedSU7DiscreteConsolidationData.ckmDepth .delta =
      ckmCPDepthSum := by
  rfl

/-- THEOREM 6: the selected SU(7) data carries nondegenerate Yukawa depths;
in particular it is not the all-zero toy depth assignment. -/
theorem selectedSU7_yukawaDepth_top_ne_zero :
    selectedSU7DiscreteConsolidationData.yukawaDepth .top ≠ 0 := by
  norm_num [selectedSU7DiscreteConsolidationData,
    selectedYukawaIntegerDepth]

/-! ## The selected discrete Standard-Model seed -/

/-- The selected Boolean facet assignment for the current finite target seed:
all seven semantic obligations are active. -/
def selectedSemanticBoolState : SemanticBoolState where
  sourceReachability := true
  authorityMonotonicity := true
  graphConfluence := true
  gaugeInvariance := true
  contractionCertification := true
  omegaGluing := true
  freshnessValidity := true

/-- The finite target seed for the current Standard-Model producer chain. -/
def selectedDiscreteStandardModelSeed : DiscreteStandardModelSeed where
  facets := selectedSemanticBoolState
  su7 := selectedSU7DiscreteConsolidationData

/-- THEOREM 7: the selected discrete seed exposes the same SU(7) depth data. -/
theorem selectedSeed_su7_eq :
    selectedDiscreteStandardModelSeed.su7 =
      selectedSU7DiscreteConsolidationData := by
  rfl

/-- THEOREM 8: the selected discrete seed carries the P582 CKM depth producer. -/
theorem selectedSeed_ckmDepthSum_eq :
    selectedDiscreteStandardModelSeed.su7.ckmDepth .delta =
      ckmCPDepthSum := by
  rfl

/-- A compact receipt for the selected finite seed. -/
structure SelectedDiscreteSeedDepthReceipt where
  sector_chain :
    selectedSectorStage .unifiedFiber < selectedSectorStage .color ∧
      selectedSectorStage .color < selectedSectorStage .weak ∧
      selectedSectorStage .weak < selectedSectorStage .hypercharge ∧
      selectedSectorStage .hypercharge < selectedSectorStage .higgs ∧
      selectedSectorStage .higgs < selectedSectorStage .yukawa ∧
      selectedSectorStage .yukawa < selectedSectorStage .flavor
  yukawa_table :
    [ selectedDiscreteStandardModelSeed.su7.yukawaDepth .top
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .bottom
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .tau
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .charm
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .muon
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .strange
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .down
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .up
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .electron
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_delta_depth :
    selectedDiscreteStandardModelSeed.su7.ckmDepth .delta =
      ckmCPDepthSum
  nondegenerate :
    selectedDiscreteStandardModelSeed.su7.yukawaDepth .top ≠ 0

/-- THEOREM 9: selected finite seed depth receipt. -/
theorem selectedDiscreteSeedDepthReceipt :
    SelectedDiscreteSeedDepthReceipt where
  sector_chain := selectedSectorStage_chain
  yukawa_table := by rfl
  ckm_delta_depth := selectedSeed_ckmDepthSum_eq
  nondegenerate := by
    norm_num [selectedDiscreteStandardModelSeed,
      selectedSU7DiscreteConsolidationData, selectedYukawaIntegerDepth]

end StandardModelConstraint
end SaturationMonoid
