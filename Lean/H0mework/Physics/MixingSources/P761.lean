import Mathlib.Data.Matrix.Basic
import H0mework.Physics.SourceForms.P760
import H0mework.Physics.MixingSources.P582

/-!
# Proposition 761: CKM phase-depth matrix producer

P760 closes the current finite producer values at the canonical three-nail
surface:

* `alpha_s` inverse residual `-89000/128511`;
* nine Yukawa depths `[50,346,372,489,583,682,880,908,982]`;
* CKM/Jarlskog depth sum `386`.

This file pushes the CKM nail one level deeper.  Instead of only retaining the
scalar Jarlskog sum, it builds the 3x3 CKM phase-depth matrix from the same
named Yukawa depth table:

`depth(V_ij) = n_down_j - n_up_i`.

The Jarlskog four-product is then read as the matrix expression

`V_us + V_cb - V_ub + V_cs = 386`.

Boundary: this is a CKM phase-depth matrix producer.  It is not yet a producer
for physical low-energy CKM moduli, unitarity triangles, or the full
renormalized complex CKM matrix.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## CKM phase-depth matrix -/

/-- Up-type CKM row labels. -/
inductive CKMUpFlavor where
  | up
  | charm
  | top
  deriving DecidableEq, Repr

/-- Down-type CKM column labels. -/
inductive CKMDownFlavor where
  | down
  | strange
  | bottom
  deriving DecidableEq, Repr

/-- The Yukawa row selected by an up-type CKM label. -/
def ckmUpYukawaParameter : CKMUpFlavor -> YukawaParameter
  | .up => .up
  | .charm => .charm
  | .top => .top

/-- The Yukawa row selected by a down-type CKM label. -/
def ckmDownYukawaParameter : CKMDownFlavor -> YukawaParameter
  | .down => .down
  | .strange => .strange
  | .bottom => .bottom

/-- The CKM phase-depth matrix generated from the named Yukawa depths. -/
def ckmPhaseDepthMatrix (u : CKMUpFlavor) (d : CKMDownFlavor) : Int :=
  selectedYukawaIntegerDepthZ (ckmDownYukawaParameter d) -
    selectedYukawaIntegerDepthZ (ckmUpYukawaParameter u)

/-- Closed 3x3 phase-depth matrix.  Rows are `(u,c,t)` and columns are
`(d,s,b)`. -/
def ckmPhaseDepthMatrixClosed : CKMUpFlavor -> CKMDownFlavor -> Int
  | .up, .down => -28
  | .up, .strange => -226
  | .up, .bottom => -562
  | .charm, .down => 391
  | .charm, .strange => 193
  | .charm, .bottom => -143
  | .top, .down => 830
  | .top, .strange => 632
  | .top, .bottom => 296

/-- THEOREM 1: the Yukawa-depth definition equals the closed 3x3 matrix. -/
theorem ckmPhaseDepthMatrix_eq_closed :
    ckmPhaseDepthMatrix = ckmPhaseDepthMatrixClosed := by
  funext u d
  cases u <;> cases d <;>
    norm_num [ckmPhaseDepthMatrix, ckmPhaseDepthMatrixClosed,
      ckmUpYukawaParameter, ckmDownYukawaParameter,
      selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth]

/-- The CKM phase-depth matrix as a Mathlib `Matrix` object. -/
def ckmPhaseDepthMatrixObject : Matrix CKMUpFlavor CKMDownFlavor Int :=
  fun u d => ckmPhaseDepthMatrix u d

/-- The closed CKM phase-depth matrix as a Mathlib `Matrix` object. -/
def ckmPhaseDepthClosedMatrixObject : Matrix CKMUpFlavor CKMDownFlavor Int :=
  fun u d => ckmPhaseDepthMatrixClosed u d

/-- THEOREM 2: the actual `Matrix` object equals the closed `Matrix` object. -/
theorem ckmPhaseDepthMatrixObject_eq_closed :
    ckmPhaseDepthMatrixObject = ckmPhaseDepthClosedMatrixObject := by
  ext u d
  exact congrFun (congrFun ckmPhaseDepthMatrix_eq_closed u) d

/-- The closed matrix as display rows `(u,c,t) x (d,s,b)`. -/
def ckmPhaseDepthMatrixRows : List (List Int) :=
  [ [ckmPhaseDepthMatrix .up .down,
      ckmPhaseDepthMatrix .up .strange,
      ckmPhaseDepthMatrix .up .bottom]
  , [ckmPhaseDepthMatrix .charm .down,
      ckmPhaseDepthMatrix .charm .strange,
      ckmPhaseDepthMatrix .charm .bottom]
  , [ckmPhaseDepthMatrix .top .down,
      ckmPhaseDepthMatrix .top .strange,
      ckmPhaseDepthMatrix .top .bottom]
  ]

/-- THEOREM 2: the CKM phase-depth matrix rows are fixed. -/
theorem ckmPhaseDepthMatrixRows_eq :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]] := by
  norm_num [ckmPhaseDepthMatrixRows, ckmPhaseDepthMatrix,
    ckmUpYukawaParameter, ckmDownYukawaParameter,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth]

/-! ## Jarlskog four-product from the matrix -/

/-- The matrix-level Jarlskog phase-depth expression.

The `V_ub` contribution is conjugated by the subtraction.  The `V_cs` sign is
the convention already used by the P278/P582 typed factor receipt.
-/
def ckmJarlskogDepthFromMatrix : Int :=
  ckmPhaseDepthMatrix .up .strange +
    ckmPhaseDepthMatrix .charm .bottom -
      ckmPhaseDepthMatrix .up .bottom +
        ckmPhaseDepthMatrix .charm .strange

/-- THEOREM 3: the matrix-level Jarlskog depth is `386`. -/
theorem ckmJarlskogDepthFromMatrix_eq_386 :
    ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) := by
  norm_num [ckmJarlskogDepthFromMatrix, ckmPhaseDepthMatrix,
    ckmUpYukawaParameter, ckmDownYukawaParameter,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth, ckmCPDepthSum]

/-- THEOREM 4: the matrix-level Jarlskog depth agrees with the selected
Yukawa-depth table producer. -/
theorem ckmJarlskogDepthFromMatrix_eq_selectedTable :
    ckmJarlskogDepthFromMatrix =
      ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate := by
  rw [ckmJarlskogDepthFromMatrix_eq_386,
    su7YukawaCKMProducerCertificate.ckm_depth_sum]

/-- THEOREM 5: the matrix-level Jarlskog depth matches the canonical P710/P760
surface readout. -/
theorem ckmJarlskogDepthFromMatrix_matches_canonicalSurface
    (Clause Var : Type) [Fintype Clause] :
    (ckmJarlskogDepthFromMatrix : ℚ) =
      ((GrandUnification.canonicalHamiltonianSATPhysicalProducerPair
        Clause Var).2.2.ckmDepthSum) := by
  calc
    (ckmJarlskogDepthFromMatrix : ℚ) = (ckmCPDepthSum : ℚ) := by
      exact_mod_cast ckmJarlskogDepthFromMatrix_eq_386
    _ = (386 : ℚ) := by
      norm_num [ckmCPDepthSum]
    _ =
      ((GrandUnification.canonicalHamiltonianSATPhysicalProducerPair
        Clause Var).2.2.ckmDepthSum) := by
      exact (GrandUnification.canonicalSurface_ckmDepthSum Clause Var).symm

/-! ## Jarlskog four-product from the Matrix object -/

/-- The Jarlskog phase-depth expression read from the actual `Matrix` object. -/
def ckmJarlskogDepthFromMatrixObject : Int :=
  ckmPhaseDepthMatrixObject .up .strange +
    ckmPhaseDepthMatrixObject .charm .bottom -
      ckmPhaseDepthMatrixObject .up .bottom +
        ckmPhaseDepthMatrixObject .charm .strange

/-- THEOREM 6: the object-level Jarlskog readout is definitionally the
function-level matrix expression. -/
theorem ckmJarlskogDepthFromMatrixObject_eq_matrix :
    ckmJarlskogDepthFromMatrixObject = ckmJarlskogDepthFromMatrix :=
  rfl

/-- THEOREM 7: the object-level Jarlskog depth is `386`. -/
theorem ckmJarlskogDepthFromMatrixObject_eq_386 :
    ckmJarlskogDepthFromMatrixObject = (ckmCPDepthSum : Int) := by
  rw [ckmJarlskogDepthFromMatrixObject_eq_matrix,
    ckmJarlskogDepthFromMatrix_eq_386]

/-- THEOREM 8: the object-level Jarlskog depth agrees with the selected
Yukawa-depth table producer. -/
theorem ckmJarlskogDepthFromMatrixObject_eq_selectedTable :
    ckmJarlskogDepthFromMatrixObject =
      ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate := by
  rw [ckmJarlskogDepthFromMatrixObject_eq_matrix,
    ckmJarlskogDepthFromMatrix_eq_selectedTable]

/-- THEOREM 9: the object-level Jarlskog depth matches the canonical P710/P760
surface readout. -/
theorem ckmJarlskogDepthFromMatrixObject_matches_canonicalSurface
    (Clause Var : Type) [Fintype Clause] :
    (ckmJarlskogDepthFromMatrixObject : ℚ) =
      ((GrandUnification.canonicalHamiltonianSATPhysicalProducerPair
        Clause Var).2.2.ckmDepthSum) := by
  rw [ckmJarlskogDepthFromMatrixObject_eq_matrix]
  exact ckmJarlskogDepthFromMatrix_matches_canonicalSurface Clause Var

/-! ## Matrix producer certificate -/

/-- A finite producer certificate for the CKM phase-depth matrix generated by
the SU(7) Yukawa depth table. -/
structure CKMPhaseDepthMatrixProducerCertificate where
  yukawa_ckm_producer :
    SU7YukawaCKMProducerCertificate
  matrix_closed :
    ckmPhaseDepthMatrix = ckmPhaseDepthMatrixClosed
  matrix_object_closed :
    ckmPhaseDepthMatrixObject = ckmPhaseDepthClosedMatrixObject
  matrix_rows :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]]
  jarlskog_depth :
    ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int)
  jarlskog_object_depth :
    ckmJarlskogDepthFromMatrixObject = (ckmCPDepthSum : Int)
  jarlskog_agrees_selected_table :
    ckmJarlskogDepthFromMatrix =
      ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate
  jarlskog_object_agrees_selected_table :
    ckmJarlskogDepthFromMatrixObject =
      ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate
  jarlskog_matches_canonical_surface :
    ∀ Clause Var : Type, [Fintype Clause] ->
      (ckmJarlskogDepthFromMatrix : ℚ) =
        ((GrandUnification.canonicalHamiltonianSATPhysicalProducerPair
          Clause Var).2.2.ckmDepthSum)
  jarlskog_object_matches_canonical_surface :
    ∀ Clause Var : Type, [Fintype Clause] ->
      (ckmJarlskogDepthFromMatrixObject : ℚ) =
        ((GrandUnification.canonicalHamiltonianSATPhysicalProducerPair
          Clause Var).2.2.ckmDepthSum)

/-- THEOREM 6: canonical CKM phase-depth matrix producer certificate. -/
def ckmPhaseDepthMatrixProducerCertificate :
    CKMPhaseDepthMatrixProducerCertificate where
  yukawa_ckm_producer := su7YukawaCKMProducerCertificate
  matrix_closed := ckmPhaseDepthMatrix_eq_closed
  matrix_object_closed := ckmPhaseDepthMatrixObject_eq_closed
  matrix_rows := ckmPhaseDepthMatrixRows_eq
  jarlskog_depth := ckmJarlskogDepthFromMatrix_eq_386
  jarlskog_object_depth := ckmJarlskogDepthFromMatrixObject_eq_386
  jarlskog_agrees_selected_table :=
    ckmJarlskogDepthFromMatrix_eq_selectedTable
  jarlskog_object_agrees_selected_table :=
    ckmJarlskogDepthFromMatrixObject_eq_selectedTable
  jarlskog_matches_canonical_surface := by
    intro Clause Var hClause
    exact ckmJarlskogDepthFromMatrix_matches_canonicalSurface Clause Var
  jarlskog_object_matches_canonical_surface := by
    intro Clause Var hClause
    exact ckmJarlskogDepthFromMatrixObject_matches_canonicalSurface Clause Var

end StandardModelConstraint
end SaturationMonoid
