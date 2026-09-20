import Mathlib.Data.Matrix.Basic
import H0mework.Physics.YukawaSources.P793
import H0mework.Physics.MixingSources.P766

/-!
# Proposition 794: SU(7) CKM matrix generator

P793 turns primitive SU(7) Yukawa data into the nine-depth table. P761 then
builds the CKM phase-depth matrix from the selected table. This file removes
the remaining constant-table seam: a CKM matrix is generated from a Yukawa-depth
generator datum plus explicit up/down flavor assignments.

Canonical SU(7) data gives the closed matrix, Jarlskog depth `386`, the exact
running-sigma raw phase, and the complement-branch `delta_CP` reading.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Generator data -/

/-- SU(7) CKM matrix generator data: a Yukawa-depth generator datum plus the
up/down flavor assignments used to read a CKM phase-depth matrix. -/
structure SU7CKMMatrixGeneratorData where
  depthData : SU7YukawaDepthGeneratorData
  upAssignment : CKMUpFlavor -> YukawaParameter
  downAssignment : CKMDownFlavor -> YukawaParameter

/-- CKM phase-depth matrix generated from depth data and flavor assignments. -/
def su7CKMMatrixGenerator
    (D : SU7CKMMatrixGeneratorData)
    (u : CKMUpFlavor) (d : CKMDownFlavor) : Int :=
  (su7YukawaDepthGeneratorTable D.depthData).depth (D.downAssignment d) -
    (su7YukawaDepthGeneratorTable D.depthData).depth (D.upAssignment u)

/-- Generated matrix as a Mathlib `Matrix` object. -/
def su7CKMMatrixGeneratorObject
    (D : SU7CKMMatrixGeneratorData) : Matrix CKMUpFlavor CKMDownFlavor Int :=
  fun u d => su7CKMMatrixGenerator D u d

/-- Generated matrix display rows `(u,c,t) x (d,s,b)`. -/
def su7CKMMatrixGeneratorRows
    (D : SU7CKMMatrixGeneratorData) : List (List Int) :=
  [ [su7CKMMatrixGenerator D .up .down,
      su7CKMMatrixGenerator D .up .strange,
      su7CKMMatrixGenerator D .up .bottom]
  , [su7CKMMatrixGenerator D .charm .down,
      su7CKMMatrixGenerator D .charm .strange,
      su7CKMMatrixGenerator D .charm .bottom]
  , [su7CKMMatrixGenerator D .top .down,
      su7CKMMatrixGenerator D .top .strange,
      su7CKMMatrixGenerator D .top .bottom]
  ]

/-- Jarlskog four-product depth read from the generated matrix. -/
def su7CKMJarlskogDepthFromGenerator
    (D : SU7CKMMatrixGeneratorData) : Int :=
  su7CKMMatrixGenerator D .up .strange +
    su7CKMMatrixGenerator D .charm .bottom -
      su7CKMMatrixGenerator D .up .bottom +
        su7CKMMatrixGenerator D .charm .strange

/-- CKM phase-depth matrix read directly from the SU(7) carrier coefficient
grid.  This is the table-free face of the CKM producer: every entry is the
down-type carrier depth minus the up-type carrier depth. -/
def su7CKMMatrixCarrierGridGenerator
    (u : CKMUpFlavor) (d : CKMDownFlavor) : ℚ :=
  su7YukawaDepthCarrierGridGenerator (ckmDownYukawaParameter d) -
    su7YukawaDepthCarrierGridGenerator (ckmUpYukawaParameter u)

/-- Carrier-grid CKM rows `(u,c,t) x (d,s,b)`. -/
def su7CKMMatrixCarrierGridRows : List (List ℚ) :=
  [ [su7CKMMatrixCarrierGridGenerator .up .down,
      su7CKMMatrixCarrierGridGenerator .up .strange,
      su7CKMMatrixCarrierGridGenerator .up .bottom]
  , [su7CKMMatrixCarrierGridGenerator .charm .down,
      su7CKMMatrixCarrierGridGenerator .charm .strange,
      su7CKMMatrixCarrierGridGenerator .charm .bottom]
  , [su7CKMMatrixCarrierGridGenerator .top .down,
      su7CKMMatrixCarrierGridGenerator .top .strange,
      su7CKMMatrixCarrierGridGenerator .top .bottom]
  ]

/-- Jarlskog four-product depth read directly from the carrier-grid CKM
matrix. -/
def su7CKMJarlskogDepthFromCarrierGrid : ℚ :=
  su7CKMMatrixCarrierGridGenerator .up .strange +
    su7CKMMatrixCarrierGridGenerator .charm .bottom -
      su7CKMMatrixCarrierGridGenerator .up .bottom +
        su7CKMMatrixCarrierGridGenerator .charm .strange

/-- Canonical CKM generator data from P793 plus the Standard-Model flavor
assignment. -/
def canonicalSU7CKMMatrixGeneratorData :
    SU7CKMMatrixGeneratorData where
  depthData := canonicalSU7YukawaDepthData
  upAssignment := ckmUpYukawaParameter
  downAssignment := ckmDownYukawaParameter

/-! ## Canonical output -/

/-- THEOREM 1: the canonical SU(7) CKM generator is P761's CKM phase-depth
matrix. -/
theorem su7CKMMatrixGenerator_canonical_eq_ckmPhaseDepthMatrix :
    su7CKMMatrixGenerator canonicalSU7CKMMatrixGeneratorData =
      ckmPhaseDepthMatrix := by
  funext u d
  unfold su7CKMMatrixGenerator canonicalSU7CKMMatrixGeneratorData
  rw [su7YukawaDepthGeneratorTable_canonical_eq_selected]
  rfl

/-- THEOREM 2: the canonical generated matrix object is P761's matrix object. -/
theorem su7CKMMatrixGeneratorObject_canonical_eq_ckmObject :
    su7CKMMatrixGeneratorObject canonicalSU7CKMMatrixGeneratorData =
      ckmPhaseDepthMatrixObject := by
  ext u d
  exact congrFun (congrFun su7CKMMatrixGenerator_canonical_eq_ckmPhaseDepthMatrix u) d

/-- THEOREM 3: the canonical generated rows are the closed CKM matrix rows. -/
theorem su7CKMMatrixGeneratorRows_canonical_eq :
    su7CKMMatrixGeneratorRows canonicalSU7CKMMatrixGeneratorData =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]] := by
  unfold su7CKMMatrixGeneratorRows
  rw [su7CKMMatrixGenerator_canonical_eq_ckmPhaseDepthMatrix]
  exact ckmPhaseDepthMatrixRows_eq

/-- THEOREM 4: the generated matrix is the closed 3x3 matrix. -/
theorem su7CKMMatrixGenerator_canonical_eq_closed :
    su7CKMMatrixGenerator canonicalSU7CKMMatrixGeneratorData =
      ckmPhaseDepthMatrixClosed := by
  rw [su7CKMMatrixGenerator_canonical_eq_ckmPhaseDepthMatrix,
    ckmPhaseDepthMatrix_eq_closed]

/-- THEOREM 5: the generated Jarlskog depth is P761's matrix-level Jarlskog
depth. -/
theorem su7CKMJarlskogDepthFromGenerator_canonical_eq_matrix :
    su7CKMJarlskogDepthFromGenerator canonicalSU7CKMMatrixGeneratorData =
      ckmJarlskogDepthFromMatrix := by
  unfold su7CKMJarlskogDepthFromGenerator ckmJarlskogDepthFromMatrix
  rw [su7CKMMatrixGenerator_canonical_eq_ckmPhaseDepthMatrix]

/-- THEOREM 6: the generated Jarlskog depth is `386`. -/
theorem su7CKMJarlskogDepthFromGenerator_canonical_eq_386 :
    su7CKMJarlskogDepthFromGenerator canonicalSU7CKMMatrixGeneratorData =
      (ckmCPDepthSum : Int) := by
  rw [su7CKMJarlskogDepthFromGenerator_canonical_eq_matrix,
    ckmJarlskogDepthFromMatrix_eq_386]

/-- THEOREM 6b: the generated CKM/Jarlskog depth is the carrier coefficient
grid's CKM/Jarlskog readout. -/
theorem su7CKMJarlskogDepthFromGenerator_canonical_eq_carrierGrid :
    (su7CKMJarlskogDepthFromGenerator
        canonicalSU7CKMMatrixGeneratorData : ℚ) =
      ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid := by
  rw [su7CKMJarlskogDepthFromGenerator_canonical_eq_386,
    carrierCoefficientYukawaDepthGrid_jarlskogDepthSum_eq_386]
  norm_num [ckmCPDepthSum]

/-- THEOREM 6c: every generated CKM matrix entry is the direct carrier-grid
entry. -/
theorem su7CKMMatrixGenerator_canonical_eq_carrierGrid
    (u : CKMUpFlavor) (d : CKMDownFlavor) :
    (su7CKMMatrixGenerator canonicalSU7CKMMatrixGeneratorData u d : ℚ) =
      su7CKMMatrixCarrierGridGenerator u d := by
  unfold su7CKMMatrixGenerator su7CKMMatrixCarrierGridGenerator
    canonicalSU7CKMMatrixGeneratorData
  rw [su7YukawaDepthGeneratorTable_canonical_eq_selected]
  unfold su7YukawaDepthCarrierGridGenerator
  rw [carrierCoefficientYukawaDepthGrid_eq_selected]
  cases u <;> cases d <;>
    norm_num [su7YukawaDepthCarrierGridGenerator, rationalGridDepthOf,
      selectedYukawaDepthTableCandidate, selectedYukawaDepthGrid,
      selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth,
      yukawaMatrixCoordinates, yukawaMatrixParameter,
      ckmUpYukawaParameter, ckmDownYukawaParameter]

/-- THEOREM 6d: the carrier-grid CKM rows are the closed matrix rows. -/
theorem su7CKMMatrixCarrierGridRows_eq :
    su7CKMMatrixCarrierGridRows =
      ([[-28, -226, -562], [391, 193, -143], [830, 632, 296]] :
        List (List ℚ)) := by
  unfold su7CKMMatrixCarrierGridRows su7CKMMatrixCarrierGridGenerator
    su7YukawaDepthCarrierGridGenerator
  rw [carrierCoefficientYukawaDepthGrid_eq_selected]
  norm_num [rationalGridDepthOf, selectedYukawaDepthGrid,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth,
    yukawaMatrixCoordinates, yukawaMatrixParameter,
    ckmUpYukawaParameter, ckmDownYukawaParameter]

/-- THEOREM 6e: the carrier-grid Jarlskog readout is the rational-grid
Jarlskog expression. -/
theorem su7CKMJarlskogDepthFromCarrierGrid_eq_rationalGrid :
    su7CKMJarlskogDepthFromCarrierGrid =
      ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid := by
  unfold su7CKMJarlskogDepthFromCarrierGrid
    su7CKMMatrixCarrierGridGenerator
    su7YukawaDepthCarrierGridGenerator
    ckmJarlskogDepthSumFromRationalGrid
  simp [ckmUpYukawaParameter, ckmDownYukawaParameter]
  ring

/-- THEOREM 6f: the carrier-grid Jarlskog depth is `386`. -/
theorem su7CKMJarlskogDepthFromCarrierGrid_eq_386 :
    su7CKMJarlskogDepthFromCarrierGrid = (386 : ℚ) := by
  rw [su7CKMJarlskogDepthFromCarrierGrid_eq_rationalGrid,
    carrierCoefficientYukawaDepthGrid_jarlskogDepthSum_eq_386]

/-- THEOREM 6g: the generated Jarlskog depth and the carrier-grid Jarlskog
depth are the same readout. -/
theorem su7CKMJarlskogDepthFromGenerator_canonical_eq_carrierGridReadout :
    (su7CKMJarlskogDepthFromGenerator
        canonicalSU7CKMMatrixGeneratorData : ℚ) =
      su7CKMJarlskogDepthFromCarrierGrid := by
  rw [su7CKMJarlskogDepthFromGenerator_canonical_eq_carrierGrid,
    su7CKMJarlskogDepthFromCarrierGrid_eq_rationalGrid]

/-- Running-sigma equation for the generated CKM/Jarlskog depth. -/
def SU7CKMGeneratorRunningSigmaSolution (σ : ℚ) : Prop :=
  (su7CKMJarlskogDepthFromGenerator
      canonicalSU7CKMMatrixGeneratorData : ℚ) * σ =
    cpRawPhaseClaim ℚ

/-- THEOREM 7: the generated matrix phase equation uniquely selects exact
running sigma. -/
theorem su7CKMGeneratorRunningSigmaSolution_iff_exact (σ : ℚ) :
    SU7CKMGeneratorRunningSigmaSolution σ ↔
      σ = sigmaGUTTwoLoopExact ℚ := by
  unfold SU7CKMGeneratorRunningSigmaSolution
  rw [su7CKMJarlskogDepthFromGenerator_canonical_eq_matrix]
  exact ckmMatrixRunningSigmaSolution_iff_exact σ

/-- THEOREM 8: generated depth times exact running sigma gives raw phase. -/
theorem su7CKMJarlskogDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim :
    (su7CKMJarlskogDepthFromGenerator
        canonicalSU7CKMMatrixGeneratorData : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  rw [su7CKMJarlskogDepthFromGenerator_canonical_eq_matrix]
  exact ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim

/-- THEOREM 8b: the carrier-grid Jarlskog readout times exact running sigma
gives the raw phase. -/
theorem su7CKMCarrierGridJarlskog_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim :
    su7CKMJarlskogDepthFromCarrierGrid * sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  rw [← su7CKMJarlskogDepthFromGenerator_canonical_eq_carrierGridReadout]
  exact su7CKMJarlskogDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim

/-- THEOREM 9: generated matrix phase gives the complement-branch CKM
`delta_CP` reading. -/
theorem cpDeltaCPClaim_eq_tauProxy_minus_su7GeneratedCKMPhase :
    cpDeltaCPClaim ℚ =
      cpTauProxy ℚ -
        (su7CKMJarlskogDepthFromGenerator
          canonicalSU7CKMMatrixGeneratorData : ℚ) *
          sigmaGUTTwoLoopExact ℚ := by
  rw [su7CKMJarlskogDepthFromGenerator_canonical_eq_matrix]
  exact cpDeltaCPClaim_eq_tauProxy_minus_ckmMatrixPhase

/-! ## Bundled certificate -/

/-- Generator-centered CKM certificate.  The matrix, Jarlskog depth, running
sigma, and `delta_CP` chain are all read from canonical P793 Yukawa-depth
generator data plus the up/down flavor assignment. -/
structure SU7CKMMatrixGeneratorCertificate : Prop where
  yukawa_depth_generator :
    SU7YukawaDepthGeneratorCertificate
  generator_eq_matrix :
    su7CKMMatrixGenerator canonicalSU7CKMMatrixGeneratorData =
      ckmPhaseDepthMatrix
  generator_object_eq_matrix_object :
    su7CKMMatrixGeneratorObject canonicalSU7CKMMatrixGeneratorData =
      ckmPhaseDepthMatrixObject
  rows_closed :
    su7CKMMatrixGeneratorRows canonicalSU7CKMMatrixGeneratorData =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]]
  generator_eq_closed :
    su7CKMMatrixGenerator canonicalSU7CKMMatrixGeneratorData =
      ckmPhaseDepthMatrixClosed
  jarlskog_eq_matrix :
    su7CKMJarlskogDepthFromGenerator canonicalSU7CKMMatrixGeneratorData =
      ckmJarlskogDepthFromMatrix
  jarlskog_depth :
    su7CKMJarlskogDepthFromGenerator canonicalSU7CKMMatrixGeneratorData =
      (ckmCPDepthSum : Int)
  jarlskog_depth_from_carrier_grid :
    (su7CKMJarlskogDepthFromGenerator
        canonicalSU7CKMMatrixGeneratorData : ℚ) =
      ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid
  entries_from_carrier_grid :
    ∀ u : CKMUpFlavor, ∀ d : CKMDownFlavor,
      (su7CKMMatrixGenerator canonicalSU7CKMMatrixGeneratorData u d : ℚ) =
        su7CKMMatrixCarrierGridGenerator u d
  rows_from_carrier_grid :
    su7CKMMatrixCarrierGridRows =
      ([[-28, -226, -562], [391, 193, -143], [830, 632, 296]] :
        List (List ℚ))
  jarlskog_carrier_grid :
    su7CKMJarlskogDepthFromCarrierGrid = (386 : ℚ)
  jarlskog_generator_eq_carrier_grid :
    (su7CKMJarlskogDepthFromGenerator
        canonicalSU7CKMMatrixGeneratorData : ℚ) =
      su7CKMJarlskogDepthFromCarrierGrid
  running_sigma_solution_iff_exact :
    ∀ σ : ℚ,
      SU7CKMGeneratorRunningSigmaSolution σ ↔
        σ = sigmaGUTTwoLoopExact ℚ
  exact_sigma_raw_phase :
    (su7CKMJarlskogDepthFromGenerator
        canonicalSU7CKMMatrixGeneratorData : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ
  exact_sigma_raw_phase_from_carrier_grid :
    su7CKMJarlskogDepthFromCarrierGrid * sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ
  delta_cp_from_generated_phase :
    cpDeltaCPClaim ℚ =
      cpTauProxy ℚ -
        (su7CKMJarlskogDepthFromGenerator
          canonicalSU7CKMMatrixGeneratorData : ℚ) *
          sigmaGUTTwoLoopExact ℚ

/-- THEOREM 10: canonical SU(7) CKM matrix generator certificate. -/
theorem su7CKMMatrixGeneratorCertificate :
    SU7CKMMatrixGeneratorCertificate where
  yukawa_depth_generator := su7YukawaDepthGeneratorCertificate
  generator_eq_matrix := su7CKMMatrixGenerator_canonical_eq_ckmPhaseDepthMatrix
  generator_object_eq_matrix_object :=
    su7CKMMatrixGeneratorObject_canonical_eq_ckmObject
  rows_closed := su7CKMMatrixGeneratorRows_canonical_eq
  generator_eq_closed := su7CKMMatrixGenerator_canonical_eq_closed
  jarlskog_eq_matrix := su7CKMJarlskogDepthFromGenerator_canonical_eq_matrix
  jarlskog_depth := su7CKMJarlskogDepthFromGenerator_canonical_eq_386
  jarlskog_depth_from_carrier_grid :=
    su7CKMJarlskogDepthFromGenerator_canonical_eq_carrierGrid
  entries_from_carrier_grid := by
    intro u d
    exact su7CKMMatrixGenerator_canonical_eq_carrierGrid u d
  rows_from_carrier_grid := su7CKMMatrixCarrierGridRows_eq
  jarlskog_carrier_grid := su7CKMJarlskogDepthFromCarrierGrid_eq_386
  jarlskog_generator_eq_carrier_grid :=
    su7CKMJarlskogDepthFromGenerator_canonical_eq_carrierGridReadout
  running_sigma_solution_iff_exact :=
    su7CKMGeneratorRunningSigmaSolution_iff_exact
  exact_sigma_raw_phase :=
    su7CKMJarlskogDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
  exact_sigma_raw_phase_from_carrier_grid :=
    su7CKMCarrierGridJarlskog_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
  delta_cp_from_generated_phase :=
    cpDeltaCPClaim_eq_tauProxy_minus_su7GeneratedCKMPhase

end StandardModelConstraint
end SaturationMonoid
