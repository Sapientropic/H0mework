import Mathlib.Tactic
import H0mework.Physics.MixingSources.P278
import H0mework.Physics.YukawaSources.P424

/-!
# Proposition 582: CKM depth sum from named Yukawa depths

P278 closed the CKM CP arithmetic with the four Jarlskog depth deltas

`(-226) + (-143) + 562 + 193 = 386`.

This file moves that receipt down one producer layer.  The deltas are not
primitive constants here: they are read from the same nine-row Yukawa depth
table used by the sigma-lock harness.  In particular,

* `n_s - n_u = 682 - 908 = -226`;
* `n_b - n_c = 346 - 489 = -143`;
* `n_u - n_b = 908 - 346 = 562`;
* `n_s - n_c = 682 - 489 = 193`.

Thus the P278 depth sum `386` is the Jarlskog four-product phase sum induced by
the named up/down Yukawa depth assignment.

Boundary: this is still a finite depth-table producer, not the deeper
SU(7)-representation / consolidation-order derivation of the nine integers.
It removes the CKM "naked delta" debt and exposes the next remaining debt:
produce the table itself.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The finite nine-row Yukawa depth table -/

/-- The selected integer consolidation depth of each Yukawa row.

The values are ordered by the named Standard-Model Yukawa carrier, not by
numeric size.  Numeric mass-order display is exposed below as a separate
theorem so the table can serve both the CKM phase producer and the Yukawa
sigma-lock harness.
-/
def selectedYukawaIntegerDepth : YukawaParameter -> Nat
  | .up => 908
  | .charm => 489
  | .top => 50
  | .down => 880
  | .strange => 682
  | .bottom => 346
  | .electron => 982
  | .muon => 583
  | .tau => 372

/-- The same table in the documented mass-order display used by the current
verification harness:

`top, bottom, tau, charm, muon, strange, down, up, electron`.
-/
def selectedYukawaDepthMassOrder : List Nat :=
  [ selectedYukawaIntegerDepth .top
  , selectedYukawaIntegerDepth .bottom
  , selectedYukawaIntegerDepth .tau
  , selectedYukawaIntegerDepth .charm
  , selectedYukawaIntegerDepth .muon
  , selectedYukawaIntegerDepth .strange
  , selectedYukawaIntegerDepth .down
  , selectedYukawaIntegerDepth .up
  , selectedYukawaIntegerDepth .electron
  ]

/-- THEOREM 1: the finite depth table has the documented nine values. -/
theorem selectedYukawaDepthMassOrder_eq :
    selectedYukawaDepthMassOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rfl

/-- Read a Yukawa depth as an integer so CKM phase differences can be signed. -/
def selectedYukawaIntegerDepthZ (y : YukawaParameter) : Int :=
  (selectedYukawaIntegerDepth y : Int)

/-! ## CKM deltas induced by the table -/

/-- The Jarlskog `V_us` phase-depth contribution, read as `n_s - n_u`. -/
def ckmDepthDelta_us_fromYukawaDepths : Int :=
  selectedYukawaIntegerDepthZ .strange -
    selectedYukawaIntegerDepthZ .up

/-- The Jarlskog `V_cb` phase-depth contribution, read as `n_b - n_c`. -/
def ckmDepthDelta_cb_fromYukawaDepths : Int :=
  selectedYukawaIntegerDepthZ .bottom -
    selectedYukawaIntegerDepthZ .charm

/-- The conjugated `V_ub` phase-depth contribution, read as `n_u - n_b`. -/
def ckmDepthDelta_ub_conj_fromYukawaDepths : Int :=
  selectedYukawaIntegerDepthZ .up -
    selectedYukawaIntegerDepthZ .bottom

/-- The conjugated `V_cs` phase-depth contribution, read as `n_s - n_c`. -/
def ckmDepthDelta_cs_conj_fromYukawaDepths : Int :=
  selectedYukawaIntegerDepthZ .strange -
    selectedYukawaIntegerDepthZ .charm

/-- THEOREM 2: `n_s - n_u = -226`. -/
theorem ckmDepthDelta_us_fromYukawaDepths_eq :
    ckmDepthDelta_us_fromYukawaDepths = ckmCPDepthDelta_us := by
  norm_num [ckmDepthDelta_us_fromYukawaDepths, selectedYukawaIntegerDepthZ,
    selectedYukawaIntegerDepth, ckmCPDepthDelta_us]

/-- THEOREM 3: `n_b - n_c = -143`. -/
theorem ckmDepthDelta_cb_fromYukawaDepths_eq :
    ckmDepthDelta_cb_fromYukawaDepths = ckmCPDepthDelta_cb := by
  norm_num [ckmDepthDelta_cb_fromYukawaDepths, selectedYukawaIntegerDepthZ,
    selectedYukawaIntegerDepth, ckmCPDepthDelta_cb]

/-- THEOREM 4: `n_u - n_b = 562`. -/
theorem ckmDepthDelta_ub_conj_fromYukawaDepths_eq :
    ckmDepthDelta_ub_conj_fromYukawaDepths =
      ckmCPDepthDelta_ub_conj := by
  norm_num [ckmDepthDelta_ub_conj_fromYukawaDepths,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth,
    ckmCPDepthDelta_ub_conj]

/-- THEOREM 5: `n_s - n_c = 193`. -/
theorem ckmDepthDelta_cs_conj_fromYukawaDepths_eq :
    ckmDepthDelta_cs_conj_fromYukawaDepths =
      ckmCPDepthDelta_cs_conj := by
  norm_num [ckmDepthDelta_cs_conj_fromYukawaDepths,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth,
    ckmCPDepthDelta_cs_conj]

/-- The Jarlskog four-product depth sum induced by the named Yukawa depths. -/
def ckmDepthSum_fromYukawaDepths : Int :=
  ckmDepthDelta_us_fromYukawaDepths +
    ckmDepthDelta_cb_fromYukawaDepths +
    ckmDepthDelta_ub_conj_fromYukawaDepths +
    ckmDepthDelta_cs_conj_fromYukawaDepths

/-- THEOREM 6: the named Yukawa depth table induces the P278 CKM depth sum
`386`. -/
theorem ckmDepthSum_fromYukawaDepths_eq_386 :
    ckmDepthSum_fromYukawaDepths = (ckmCPDepthSum : Int) := by
  norm_num [ckmDepthSum_fromYukawaDepths,
    ckmDepthDelta_us_fromYukawaDepths,
    ckmDepthDelta_cb_fromYukawaDepths,
    ckmDepthDelta_ub_conj_fromYukawaDepths,
    ckmDepthDelta_cs_conj_fromYukawaDepths,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth,
    ckmCPDepthSum]

/-- THEOREM 7: the producer-level sum agrees with P278's delta-sum theorem. -/
theorem ckmDepthSum_fromYukawaDepths_eq_P278_sum :
    ckmDepthSum_fromYukawaDepths =
      ckmCPDepthDelta_us + ckmCPDepthDelta_cb +
        ckmCPDepthDelta_ub_conj + ckmCPDepthDelta_cs_conj := by
  rw [ckmDepthSum_fromYukawaDepths_eq_386,
    ckmCPDepthDeltas_sum_eq_depthSum]

/-! ## Compact receipt -/

/-- A compact receipt saying that the P278 CKM phase depth sum is produced by
the named nine-row Yukawa depth assignment. -/
structure CKMDepthFromYukawaDepthReceipt where
  depth_table :
    selectedYukawaDepthMassOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  delta_us :
    ckmDepthDelta_us_fromYukawaDepths = ckmCPDepthDelta_us
  delta_cb :
    ckmDepthDelta_cb_fromYukawaDepths = ckmCPDepthDelta_cb
  delta_ub_conj :
    ckmDepthDelta_ub_conj_fromYukawaDepths =
      ckmCPDepthDelta_ub_conj
  delta_cs_conj :
    ckmDepthDelta_cs_conj_fromYukawaDepths =
      ckmCPDepthDelta_cs_conj
  depth_sum :
    ckmDepthSum_fromYukawaDepths = (ckmCPDepthSum : Int)

/-- THEOREM 8: CKM depth-sum producer receipt from the named Yukawa depth
table. -/
theorem ckmDepthFromYukawaDepthReceipt :
    CKMDepthFromYukawaDepthReceipt where
  depth_table := selectedYukawaDepthMassOrder_eq
  delta_us := ckmDepthDelta_us_fromYukawaDepths_eq
  delta_cb := ckmDepthDelta_cb_fromYukawaDepths_eq
  delta_ub_conj := ckmDepthDelta_ub_conj_fromYukawaDepths_eq
  delta_cs_conj := ckmDepthDelta_cs_conj_fromYukawaDepths_eq
  depth_sum := ckmDepthSum_fromYukawaDepths_eq_386

end StandardModelConstraint
end SaturationMonoid
