import H0mework.Physics.Admission.JointResidualResponseSnapshot

/-!
# S9-C3h20: required differential-response transport

Four current Euler--Lagrange coordinates have the literal response form
`A - D`, where `A` is the algebraic response and `D` is a differential
momentum divergence.  Here `D` is not the physical lift defect `D_U`.

For the existing source keep `K = 1 - sigma`, holding `A` fixed makes the
required endpoint divergence uniquely

`D' = D + sigma * (A - D)`.

This is equivalent to `A - D' = (1 - sigma) * (A - D)`.  The module applies
that forced normal form to the Lorentz, P286, scalar, and matter entries of the
existing pointwise response snapshot.  It leaves the action jet, algebraic
responses, conjugate-matter residual, coframe stress, and all three algebraic
joint residual coordinates unchanged.

The output is a required-response readout.  It is not a holonomic
configuration, source field, local solution, state update, or stationarity
receipt, and no theorem here claims that a physical field realizes it.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineRequiredDifferentialResponseTransport

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointResidualResponseSnapshot
open StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariation

noncomputable section

set_option autoImplicit false

/-! ## Abstract forced response and uniqueness -/

def requiredDifferentialResponse
    {Direction : Type*}
    (sigma : ℝ)
    (algebraic divergence : Direction → ℝ) : Direction → ℝ :=
  fun direction =>
    divergence direction +
      sigma * (algebraic direction - divergence direction)

theorem requiredDifferentialResponse_transport
    {Direction : Type*}
    (sigma : ℝ)
    (algebraic divergence : Direction → ℝ)
    (direction : Direction) :
    algebraic direction -
        requiredDifferentialResponse sigma algebraic divergence direction =
      (1 - sigma) *
        (algebraic direction - divergence direction) := by
  unfold requiredDifferentialResponse
  ring

/-- With the algebraic response fixed, the first formula leaves no branch
choice for the endpoint differential response. -/
theorem candidate_eq_requiredDifferentialResponse_iff_transport
    {Direction : Type*}
    (sigma : ℝ)
    (algebraic divergence candidate : Direction → ℝ) :
    candidate = requiredDifferentialResponse sigma algebraic divergence ↔
      ∀ direction,
        algebraic direction - candidate direction =
          (1 - sigma) *
            (algebraic direction - divergence direction) := by
  constructor
  · intro candidateEquality direction
    rw [candidateEquality]
    exact requiredDifferentialResponse_transport sigma algebraic divergence
      direction
  · intro transport
    funext direction
    have pointTransport := transport direction
    unfold requiredDifferentialResponse
    linarith

/-! ## Source-sigma specialization on the actual response snapshot -/

/-- Replace only the four differential divergence readouts by the unique
values required by the existing source sigma. -/
def sourceSigmaRequiredDifferentialResponseSnapshot
    (source : CurrentSmoothUnifiedSource)
    (snapshot : PointwiseResidualResponseSnapshot) :
    PointwiseResidualResponseSnapshot :=
  { snapshot with
    lorentzBFDifferentialMomentumDivergence :=
      requiredDifferentialResponse source.legacy.sigma
        snapshot.lorentzAlgebraicResponse
        snapshot.lorentzBFDifferentialMomentumDivergence
    p286BFDifferentialMomentumDivergence :=
      requiredDifferentialResponse source.legacy.sigma
        snapshot.p286AlgebraicResponse
        snapshot.p286BFDifferentialMomentumDivergence
    scalarDifferentialMomentumDivergence :=
      requiredDifferentialResponse source.legacy.sigma
        snapshot.scalarAlgebraicResponse
        snapshot.scalarDifferentialMomentumDivergence
    matterDifferentialMomentumDivergence :=
      requiredDifferentialResponse source.legacy.sigma
        snapshot.matterAlgebraicResponse
        snapshot.matterDifferentialMomentumDivergence }

@[simp] theorem sourceSigmaRequiredSnapshot_actionJet
    (source : CurrentSmoothUnifiedSource)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (sourceSigmaRequiredDifferentialResponseSnapshot source snapshot).actionJet =
      snapshot.actionJet :=
  rfl

@[simp] theorem sourceSigmaRequiredSnapshot_lorentzAlgebraic
    (source : CurrentSmoothUnifiedSource)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (sourceSigmaRequiredDifferentialResponseSnapshot source
        snapshot).lorentzAlgebraicResponse =
      snapshot.lorentzAlgebraicResponse :=
  rfl

@[simp] theorem sourceSigmaRequiredSnapshot_p286Algebraic
    (source : CurrentSmoothUnifiedSource)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (sourceSigmaRequiredDifferentialResponseSnapshot source
        snapshot).p286AlgebraicResponse =
      snapshot.p286AlgebraicResponse :=
  rfl

@[simp] theorem sourceSigmaRequiredSnapshot_scalarAlgebraic
    (source : CurrentSmoothUnifiedSource)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (sourceSigmaRequiredDifferentialResponseSnapshot source
        snapshot).scalarAlgebraicResponse =
      snapshot.scalarAlgebraicResponse :=
  rfl

@[simp] theorem sourceSigmaRequiredSnapshot_matterAlgebraic
    (source : CurrentSmoothUnifiedSource)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (sourceSigmaRequiredDifferentialResponseSnapshot source
        snapshot).matterAlgebraicResponse =
      snapshot.matterAlgebraicResponse :=
  rfl

theorem sourceSigmaRequiredSnapshot_lorentzResidual_transport
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.lorentzConnection =
      (1 - source.legacy.sigma) •
        (pointwiseJointResidualOfResponseSnapshot source point
          snapshot).eulerLagrange.lorentzConnection := by
  funext direction
  change _ = (1 - source.legacy.sigma) * _
  exact requiredDifferentialResponse_transport source.legacy.sigma
    snapshot.lorentzAlgebraicResponse
    snapshot.lorentzBFDifferentialMomentumDivergence direction

theorem sourceSigmaRequiredSnapshot_p286Residual_transport
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.p286GaugeConnection =
      (1 - source.legacy.sigma) •
        (pointwiseJointResidualOfResponseSnapshot source point
          snapshot).eulerLagrange.p286GaugeConnection := by
  funext direction
  change _ = (1 - source.legacy.sigma) * _
  exact requiredDifferentialResponse_transport source.legacy.sigma
    snapshot.p286AlgebraicResponse
    snapshot.p286BFDifferentialMomentumDivergence direction

theorem sourceSigmaRequiredSnapshot_scalarResidual_transport
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.scalar =
      (1 - source.legacy.sigma) •
        (pointwiseJointResidualOfResponseSnapshot source point
          snapshot).eulerLagrange.scalar := by
  funext direction
  change _ = (1 - source.legacy.sigma) * _
  exact requiredDifferentialResponse_transport source.legacy.sigma
    snapshot.scalarAlgebraicResponse
    snapshot.scalarDifferentialMomentumDivergence direction

theorem sourceSigmaRequiredSnapshot_matterResidual_transport
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.matter =
      (1 - source.legacy.sigma) •
        (pointwiseJointResidualOfResponseSnapshot source point
          snapshot).eulerLagrange.matter := by
  funext direction
  change _ = (1 - source.legacy.sigma) * _
  exact requiredDifferentialResponse_transport source.legacy.sigma
    snapshot.matterAlgebraicResponse
    snapshot.matterDifferentialMomentumDivergence direction

/-- All four `A-D` coordinates obey the source-generated residual keep on the
required-response snapshot. -/
theorem sourceSigmaRequiredSnapshot_fourResiduals_transport
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.lorentzConnection =
        (1 - source.legacy.sigma) •
          (pointwiseJointResidualOfResponseSnapshot source point
            snapshot).eulerLagrange.lorentzConnection ∧
      (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.p286GaugeConnection =
        (1 - source.legacy.sigma) •
          (pointwiseJointResidualOfResponseSnapshot source point
            snapshot).eulerLagrange.p286GaugeConnection ∧
      (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.scalar =
        (1 - source.legacy.sigma) •
          (pointwiseJointResidualOfResponseSnapshot source point
            snapshot).eulerLagrange.scalar ∧
      (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.matter =
        (1 - source.legacy.sigma) •
          (pointwiseJointResidualOfResponseSnapshot source point
            snapshot).eulerLagrange.matter :=
  ⟨sourceSigmaRequiredSnapshot_lorentzResidual_transport source point snapshot,
    sourceSigmaRequiredSnapshot_p286Residual_transport source point snapshot,
    sourceSigmaRequiredSnapshot_scalarResidual_transport source point snapshot,
    sourceSigmaRequiredSnapshot_matterResidual_transport source point snapshot⟩

/-- The response normal form does not move the three algebraic residuals. -/
theorem sourceSigmaRequiredSnapshot_algebraic_unchanged
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).algebraic =
      (pointwiseJointResidualOfResponseSnapshot source point
        snapshot).algebraic :=
  rfl

/-- Conjugate matter is an action-jet readout and is outside this four-channel
required-response normal form. -/
theorem sourceSigmaRequiredSnapshot_conjugateMatter_unchanged
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.conjugateMatter =
      (pointwiseJointResidualOfResponseSnapshot source point
        snapshot).eulerLagrange.conjugateMatter :=
  rfl

/-- Coframe stress is also an action-jet readout rather than an independently
replaceable differential divergence. -/
theorem sourceSigmaRequiredSnapshot_coframe_unchanged
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    (pointwiseJointResidualOfResponseSnapshot source point
        (sourceSigmaRequiredDifferentialResponseSnapshot source
          snapshot)).eulerLagrange.coframe =
      (pointwiseJointResidualOfResponseSnapshot source point
        snapshot).eulerLagrange.coframe :=
  rfl

end

end SaturationMonoid.PhysicsCore.StageNineRequiredDifferentialResponseTransport
