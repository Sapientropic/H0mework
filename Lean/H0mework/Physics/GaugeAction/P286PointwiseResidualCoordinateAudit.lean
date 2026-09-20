import Mathlib.LinearAlgebra.Dual.Basis
import H0mework.Physics.GaugeAction.P286PointwiseResidualLinearCarrier
import H0mework.Physics.Cartan.P286ColorCartanQuadraticResidualSupportBoundary

/-!
# S9-C3h81a: exhaustive coordinate audit of the full P286 residual

C3h80 packages the complete pointwise P286 connection residual as an actual
dual.  This module gives that dual a finite exhaustive readout using the
coordinate model that already exists in `StageNineHolonomicField`.

The inner `P286CoordinateIndex` was itself obtained from
`Module.Free.chooseBasis`; consequently the particular support set and its
cardinality are not representation-covariant physical data.  Only exhaustive
statements such as "the support is empty iff the dual is zero" are used here.
No second arbitrary basis, first-nonzero coordinate, order, argmax, witness,
or repair selector is introduced.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286PointwiseResidualCoordinateAudit

open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286ColorCartanOffsetBoundary
open StageNineP286ColorCartanConstitutiveResponse
open StageNineP286ColorCartanQuadraticResidualSupportBoundary
open StageNineP286PointwiseResidualLinearCarrier
open StageNineResidualLimitP286BFBalanceDecision
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- Sigma index of the existing P286 coordinate basis in each one-form
direction.  This is an audit index, not a physical label. -/
abbrev P286GaugeOneFormCoordinateIndex :=
  Σ _ : LorentzianIndex, P286CoordinateIndex

/-- Product basis obtained from the already-declared P286 coordinate model.
No second `chooseBasis` is performed on the one-form space. -/
def p286GaugeOneFormAuditBasis :
    Module.Basis P286GaugeOneFormCoordinateIndex ℝ P286GaugeOneForm :=
  Pi.basis fun _ : LorentzianIndex =>
    (EuclideanSpace.basisFun P286CoordinateIndex ℝ).toBasis

@[simp] theorem p286GaugeOneFormAuditBasis_apply
    (coordinate : P286GaugeOneFormCoordinateIndex) :
    p286GaugeOneFormAuditBasis coordinate =
      Pi.single coordinate.1
        (EuclideanSpace.single coordinate.2 (1 : ℝ)) := by
  classical
  simp [p286GaugeOneFormAuditBasis]

/-- Exhaustive coordinate readout of an already-generated residual dual. -/
def p286PointwiseResidualCoordinateReadout
    (residual : Module.Dual ℝ P286GaugeOneForm)
    (coordinate : P286GaugeOneFormCoordinateIndex) : ℝ :=
  residual (p286GaugeOneFormAuditBasis coordinate)

/-- Finite coordinate support in the existing, noncanonical P286 audit chart.
This finset must not be used to select a physical repair direction. -/
def p286PointwiseResidualCoordinateSupport
    (residual : Module.Dual ℝ P286GaugeOneForm) :
    Finset P286GaugeOneFormCoordinateIndex :=
  (p286GaugeOneFormAuditBasis.dualBasis.repr residual).support

@[simp] theorem p286PointwiseResidualCoordinate_mem_support_iff
    (residual : Module.Dual ℝ P286GaugeOneForm)
    (coordinate : P286GaugeOneFormCoordinateIndex) :
    coordinate ∈ p286PointwiseResidualCoordinateSupport residual ↔
      p286PointwiseResidualCoordinateReadout residual coordinate ≠ 0 := by
  classical
  simp [p286PointwiseResidualCoordinateSupport,
    p286PointwiseResidualCoordinateReadout]

theorem p286PointwiseResidual_eq_zero_iff_forall_coordinateReadout_eq_zero
    (residual : Module.Dual ℝ P286GaugeOneForm) :
    residual = 0 ↔
      ∀ coordinate : P286GaugeOneFormCoordinateIndex,
        p286PointwiseResidualCoordinateReadout residual coordinate = 0 := by
  constructor
  · intro residualZero coordinate
    rw [residualZero]
    rfl
  · intro everyCoordinateZero
    exact p286GaugeOneFormAuditBasis.ext fun coordinate => by
      simpa [p286PointwiseResidualCoordinateReadout] using
        everyCoordinateZero coordinate

@[simp] theorem p286PointwiseResidualCoordinateSupport_eq_empty_iff
    (residual : Module.Dual ℝ P286GaugeOneForm) :
    p286PointwiseResidualCoordinateSupport residual = ∅ ↔ residual = 0 := by
  classical
  rw [p286PointwiseResidualCoordinateSupport, Finsupp.support_eq_empty]
  constructor
  · intro representationZero
    apply p286GaugeOneFormAuditBasis.dualBasis.repr.injective
    simpa using representationZero
  · intro residualZero
    rw [residualZero]
    exact map_zero _

@[simp] theorem p286PointwiseResidualCoordinateSupport_nonempty_iff
    (residual : Module.Dual ℝ P286GaugeOneForm) :
    (p286PointwiseResidualCoordinateSupport residual).Nonempty ↔ residual ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty]
  exact not_congr (p286PointwiseResidualCoordinateSupport_eq_empty_iff residual)

/-! ## Actual C3h78 repair specialization -/

/-- Complete origin residual dual of the deterministic C3h78 repair. -/
def colorCartanQuadraticResidualRepairOriginResidual :
    Module.Dual ℝ P286GaugeOneForm :=
  p286GaugeConnectionEulerLagrangeAt positiveSmoothUnifiedSource
    colorCartanQuadraticResidualRepair
    colorCartanQuadraticResidualRepair_smooth
    colorCartanQuadraticResidualRepair_nondegenerate 0

theorem colorCartanQuadraticResidualRepairOriginResidual_colorCartan_eq_zero :
    colorCartanQuadraticResidualRepairOriginResidual
        colorCartanMuZeroDirection = 0 := by
  rw [colorCartanQuadraticResidualRepairOriginResidual,
    p286GaugeConnectionEulerLagrangeAt_apply,
    colorCartanQuadraticResidualRepair_colorCartanMuZero_EL_eq_zero]

theorem colorCartanQuadraticResidualRepairOriginResidual_commutator_eq_neg_three :
    colorCartanQuadraticResidualRepairOriginResidual p286CommutatorProbe =
      -3 := by
  rw [colorCartanQuadraticResidualRepairOriginResidual,
    p286GaugeConnectionEulerLagrangeAt_apply,
    colorCartanQuadraticResidualRepair_probe_EL_eq_neg_three]

theorem colorCartanQuadraticResidualRepairOriginResidual_ne_zero :
    colorCartanQuadraticResidualRepairOriginResidual ≠ 0 := by
  intro residualZero
  have probeZero := congrArg
    (fun residual : Module.Dual ℝ P286GaugeOneForm =>
      residual p286CommutatorProbe) residualZero
  rw [colorCartanQuadraticResidualRepairOriginResidual_commutator_eq_neg_three]
    at probeZero
  norm_num at probeZero

theorem colorCartanQuadraticResidualRepairOriginCoordinateSupport_nonempty :
    (p286PointwiseResidualCoordinateSupport
      colorCartanQuadraticResidualRepairOriginResidual).Nonempty :=
  (p286PointwiseResidualCoordinateSupport_nonempty_iff _).mpr
    colorCartanQuadraticResidualRepairOriginResidual_ne_zero

end

end SaturationMonoid.PhysicsCore.StageNineP286PointwiseResidualCoordinateAudit
