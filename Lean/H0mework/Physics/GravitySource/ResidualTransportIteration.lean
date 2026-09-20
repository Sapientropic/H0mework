import H0mework.Physics.GravitySource.TransportCurvature

/-!
# S9-C3h4: canonical gravity-mouth residual transport iteration

This file stays entirely downstream of the already derived residual carrier
and upstream of every configuration lift.  The only dynamics is repeated
application of the existing source-generated keep `K`:

`r_(n+1) = K r_n`,

`r_n = K r_n + (I-K) r_n`.

The accumulated trace is forced by those one-step splits.  It is not a source
slot, branch receipt, or replacement field.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthResidualTransportIteration

open Filter
open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle
open StageNinePositiveSourceGravityMouthObstruction
open StageNinePositiveSourceGravityMouthSpinOrbitCarrier
open StageNinePositiveSourceGravityMouthTransportCurvature
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open scoped BigOperators

noncomputable section

set_option autoImplicit false

abbrev GravityMouthResponsibilityCarrier :=
  PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier

/-- Canonical finite iteration of the already derived keep on its actual
Spin-stable responsibility carrier. -/
def gravityMouthResidualIterate
    (initial : GravityMouthResponsibilityCarrier) :
    ℕ → GravityMouthResponsibilityCarrier
  | 0 => initial
  | n + 1 =>
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        (gravityMouthResidualIterate initial n)

@[simp] theorem gravityMouthResidualIterate_zero
    (initial : GravityMouthResponsibilityCarrier) :
    gravityMouthResidualIterate initial 0 = initial :=
  rfl

@[simp] theorem gravityMouthResidualIterate_succ
    (initial : GravityMouthResponsibilityCarrier) (n : ℕ) :
    gravityMouthResidualIterate initial (n + 1) =
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        (gravityMouthResidualIterate initial n) :=
  rfl

/-- The iterate is exactly `K^n r`, with no independently supplied step
coefficient. -/
theorem gravityMouthResidualIterate_eq_pow_smul
    (initial : GravityMouthResponsibilityCarrier) :
    ∀ n : ℕ,
      gravityMouthResidualIterate initial n =
        ((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n) • initial := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [gravityMouthResidualIterate_succ, ih, pow_succ]
      change
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
            (((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n) • initial) =
          (((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n) *
            (1 - positiveSmoothUnifiedSource.legacy.sigma)) • initial
      rw [smul_smul, mul_comm]

/-- Every finite iterate commutes with the restricted actual Spin action. -/
theorem gravityMouthResidualIterate_equivariant
    (groupElement : SpinPlus13)
    (initial : GravityMouthResponsibilityCarrier) :
    ∀ n : ℕ,
      positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
          (gravityMouthResidualIterate initial n) =
        gravityMouthResidualIterate
          (positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
            initial) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [gravityMouthResidualIterate_succ,
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep_equivariant,
        ih, gravityMouthResidualIterate_succ]

/-- Generic forced step trace, retained on the same responsibility carrier. -/
def gravityMouthResidualStepTrace
    (initial : GravityMouthResponsibilityCarrier)
    (n : ℕ) : GravityMouthResponsibilityCarrier :=
  linearResidualTrace
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep
    (gravityMouthResidualIterate initial n)

/-- Forced traces inherit covariance from `K`; no independent trace action is
supplied. -/
theorem gravityMouthResidualStepTrace_equivariant
    (groupElement : SpinPlus13)
    (initial : GravityMouthResponsibilityCarrier)
    (n : ℕ) :
    positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
        (gravityMouthResidualStepTrace initial n) =
      gravityMouthResidualStepTrace
        (positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
          initial) n := by
  rw [gravityMouthResidualStepTrace,
    positiveSourceGravityMouthSpinOrbitResponsibilityTrace_equivariant,
    gravityMouthResidualIterate_equivariant,
    gravityMouthResidualStepTrace]

/-- Generic accumulated responsibility for the first `n` steps. -/
def gravityMouthCumulativeTrace
    (initial : GravityMouthResponsibilityCarrier)
    (n : ℕ) : GravityMouthResponsibilityCarrier :=
  ∑ k ∈ Finset.range n, gravityMouthResidualStepTrace initial k

/-- Finite trace accumulation is covariant because every forced summand is. -/
theorem gravityMouthCumulativeTrace_equivariant
    (groupElement : SpinPlus13)
    (initial : GravityMouthResponsibilityCarrier)
    (n : ℕ) :
    positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
        (gravityMouthCumulativeTrace initial n) =
      gravityMouthCumulativeTrace
        (positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
          initial) n := by
  simp [gravityMouthCumulativeTrace,
    gravityMouthResidualStepTrace_equivariant]

/-- The actual positive-source sequence starts at the generated obstruction;
it does not accept an external initial residual. -/
def positiveSourceGravityMouthResidualIterate
    (n : ℕ) : GravityMouthResponsibilityCarrier :=
  gravityMouthResidualIterate
    carriedPositiveSourceGravityMouthSpinOrbitObstruction n

@[simp] theorem positiveSourceGravityMouthResidualIterate_zero :
    positiveSourceGravityMouthResidualIterate 0 =
      carriedPositiveSourceGravityMouthSpinOrbitObstruction :=
  rfl

@[simp] theorem positiveSourceGravityMouthResidualIterate_succ (n : ℕ) :
    positiveSourceGravityMouthResidualIterate (n + 1) =
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        (positiveSourceGravityMouthResidualIterate n) :=
  rfl

theorem positiveSourceGravityMouthResidualIterate_eq_pow_smul (n : ℕ) :
    positiveSourceGravityMouthResidualIterate n =
      ((1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n) •
        carriedPositiveSourceGravityMouthSpinOrbitObstruction :=
  gravityMouthResidualIterate_eq_pow_smul
    carriedPositiveSourceGravityMouthSpinOrbitObstruction n

/-- The transport rate is generated by the existing source and is not a new
free parameter. -/
theorem positiveSmoothUnifiedSource_legacy_sigma_eq_half :
    positiveSmoothUnifiedSource.legacy.sigma = (1 / 2 : ℝ) := by
  norm_num [positiveSmoothUnifiedSource, SmoothUnifiedSource.legacy,
    SmoothUnifiedSource.forget, StageEightProofFreeSource.Source.toPhysicalSource,
    ProofFreeRicherAnholonomicSource.Source.sigma,
    StageEightProofFreeSource.canonicalSource]

/-- No finite transport iterate may be relabelled as terminal closure. -/
theorem positiveSourceGravityMouthResidualIterate_ne_zero (n : ℕ) :
    positiveSourceGravityMouthResidualIterate n ≠ 0 := by
  rw [positiveSourceGravityMouthResidualIterate_eq_pow_smul]
  exact smul_ne_zero
    (pow_ne_zero n (ne_of_gt (sub_pos.mpr
      positiveSmoothUnifiedSource.legacy.sigma_lt_one)))
    carriedPositiveSourceGravityMouthSpinOrbitObstruction_ne_zero

/-- Per-step trace is forced as `(I-K)r_n`. -/
def positiveSourceGravityMouthResidualStepTrace
    (n : ℕ) : GravityMouthResponsibilityCarrier :=
  gravityMouthResidualStepTrace
    carriedPositiveSourceGravityMouthSpinOrbitObstruction n

/-- Literal one-step root split at every finite stage. -/
theorem positiveSourceGravityMouthResidualIterate_split (n : ℕ) :
    positiveSourceGravityMouthResidualIterate n =
      positiveSourceGravityMouthResidualIterate (n + 1) +
        positiveSourceGravityMouthResidualStepTrace n := by
  rw [positiveSourceGravityMouthResidualIterate_succ]
  exact residualTransportCore_residual_split
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep
    (positiveSourceGravityMouthResidualIterate n)

/-- The one-step split uniquely determines every trace. -/
theorem positiveSourceGravityMouthResidualStepTrace_unique
    (n : ℕ) (trace : GravityMouthResponsibilityCarrier) :
    positiveSourceGravityMouthResidualIterate n =
        positiveSourceGravityMouthResidualIterate (n + 1) + trace ↔
      trace = positiveSourceGravityMouthResidualStepTrace n := by
  rw [positiveSourceGravityMouthResidualIterate_succ]
  exact residualTransportCore_trace_unique
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep
    (positiveSourceGravityMouthResidualIterate n) trace

theorem positiveSourceGravityMouthResidualStepTrace_eq_sub (n : ℕ) :
    positiveSourceGravityMouthResidualStepTrace n =
      positiveSourceGravityMouthResidualIterate n -
        positiveSourceGravityMouthResidualIterate (n + 1) := by
  rfl

/-- Every finite stage remains active: neither a fixed residual nor a zero
trace can form a naked terminal sink. -/
theorem positiveSourceGravityMouthResidualIterate_has_no_finite_terminal_sink
    (n : ℕ) :
    (¬ ResidualTransportFixed
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        (positiveSourceGravityMouthResidualIterate n)) ∧
      positiveSourceGravityMouthResidualStepTrace n ≠ 0 := by
  constructor
  · intro fixed
    exact positiveSourceGravityMouthResidualIterate_ne_zero n
      ((residualTransport_fixed_iff_zero_residual
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep_active
        (positiveSourceGravityMouthResidualIterate n)).mp fixed)
  · change
      linearResidualTrace
          (scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma)
          (positiveSourceGravityMouthResidualIterate n) ≠ 0
    rw [residualTransportCore_scalar_trace]
    exact smul_ne_zero (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)
      (positiveSourceGravityMouthResidualIterate_ne_zero n)

/-- Forced responsibility accumulated during the first `n` transport steps. -/
def positiveSourceGravityMouthCumulativeTrace
    (n : ℕ) : GravityMouthResponsibilityCarrier :=
  gravityMouthCumulativeTrace
    carriedPositiveSourceGravityMouthSpinOrbitObstruction n

/-- Finite trace accumulation telescopes exactly; no responsibility can leave
the carrier through a third sink. -/
theorem positiveSourceGravityMouthCumulativeTrace_eq_sub :
    ∀ n : ℕ,
      positiveSourceGravityMouthCumulativeTrace n =
        carriedPositiveSourceGravityMouthSpinOrbitObstruction -
          positiveSourceGravityMouthResidualIterate n := by
  intro n
  induction n with
  | zero =>
      simp [positiveSourceGravityMouthCumulativeTrace,
        gravityMouthCumulativeTrace]
  | succ n ih =>
      calc
        positiveSourceGravityMouthCumulativeTrace (n + 1) =
            positiveSourceGravityMouthCumulativeTrace n +
              positiveSourceGravityMouthResidualStepTrace n := by
          simpa [positiveSourceGravityMouthCumulativeTrace,
            gravityMouthCumulativeTrace,
            positiveSourceGravityMouthResidualStepTrace] using
            (Finset.sum_range_succ
              (fun k => gravityMouthResidualStepTrace
                carriedPositiveSourceGravityMouthSpinOrbitObstruction k) n)
        _ = carriedPositiveSourceGravityMouthSpinOrbitObstruction -
            positiveSourceGravityMouthResidualIterate (n + 1) := by
          rw [ih, positiveSourceGravityMouthResidualStepTrace_eq_sub]
          abel

/-- Iterated root split in the framework orientation. -/
theorem positiveSourceGravityMouthIteratedResidual_split (n : ℕ) :
    carriedPositiveSourceGravityMouthSpinOrbitObstruction =
      positiveSourceGravityMouthResidualIterate n +
        positiveSourceGravityMouthCumulativeTrace n := by
  rw [positiveSourceGravityMouthCumulativeTrace_eq_sub]
  abel

/-- The whole cumulative trace is forced by the finite successor residual; it
cannot encode a branch choice. -/
theorem positiveSourceGravityMouthCumulativeTrace_unique
    (n : ℕ) (trace : GravityMouthResponsibilityCarrier) :
    carriedPositiveSourceGravityMouthSpinOrbitObstruction =
        positiveSourceGravityMouthResidualIterate n + trace ↔
      trace = positiveSourceGravityMouthCumulativeTrace n := by
  rw [positiveSourceGravityMouthCumulativeTrace_eq_sub]
  constructor
  · intro equality
    calc
      trace = (positiveSourceGravityMouthResidualIterate n + trace) -
          positiveSourceGravityMouthResidualIterate n := by abel
      _ = carriedPositiveSourceGravityMouthSpinOrbitObstruction -
          positiveSourceGravityMouthResidualIterate n := by rw [← equality]
  · intro equality
    rw [equality]
    abel

/-- Actual source-generated subunit transport contracts the carried residual
to zero.  This is a residual-carrier limit, not yet a configuration witness. -/
theorem tendsto_positiveSourceGravityMouthResidualIterate_zero :
    Tendsto positiveSourceGravityMouthResidualIterate atTop
      (nhds (0 : GravityMouthResponsibilityCarrier)) := by
  have residualFactor_nonneg :
      0 ≤ 1 - positiveSmoothUnifiedSource.legacy.sigma := by
    linarith [positiveSmoothUnifiedSource.legacy.sigma_lt_one]
  have residualFactor_lt_one :
      1 - positiveSmoothUnifiedSource.legacy.sigma < 1 := by
    linarith [positiveSmoothUnifiedSource.legacy.sigma_pos]
  have scalarLimit :
      Tendsto
        (fun n : ℕ =>
          (1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n)
        atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      residualFactor_nonneg residualFactor_lt_one
  have carriedLimit := scalarLimit.smul_const
    carriedPositiveSourceGravityMouthSpinOrbitObstruction
  have closedForm :
      positiveSourceGravityMouthResidualIterate =
        fun n : ℕ =>
          (1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n •
            carriedPositiveSourceGravityMouthSpinOrbitObstruction := by
    funext n
    exact positiveSourceGravityMouthResidualIterate_eq_pow_smul n
  rw [closedForm]
  simpa using carriedLimit

/-- Hausdorff uniqueness forbids replacing the zero residual limit by a
branch-choice witness. -/
theorem positiveSourceGravityMouthResidualIterate_limit_unique
    (limit : GravityMouthResponsibilityCarrier)
    (limitLaw :
      Tendsto positiveSourceGravityMouthResidualIterate atTop (nhds limit)) :
    limit = 0 :=
  tendsto_nhds_unique limitLaw
    tendsto_positiveSourceGravityMouthResidualIterate_zero

/-- In the same canonical limit, the cumulative trace converges to the entire
original residual.  Vanishing of `K^n r` therefore loses no responsibility. -/
theorem tendsto_positiveSourceGravityMouthCumulativeTrace_original :
    Tendsto positiveSourceGravityMouthCumulativeTrace atTop
      (nhds carriedPositiveSourceGravityMouthSpinOrbitObstruction) := by
  have limit :
      Tendsto
        (fun n : ℕ =>
          carriedPositiveSourceGravityMouthSpinOrbitObstruction -
            positiveSourceGravityMouthResidualIterate n)
        atTop
        (nhds
          (carriedPositiveSourceGravityMouthSpinOrbitObstruction -
            (0 : GravityMouthResponsibilityCarrier))) :=
    tendsto_const_nhds.sub
      tendsto_positiveSourceGravityMouthResidualIterate_zero
  have closedForm :
      positiveSourceGravityMouthCumulativeTrace =
        fun n : ℕ =>
          carriedPositiveSourceGravityMouthSpinOrbitObstruction -
            positiveSourceGravityMouthResidualIterate n := by
    funext n
    exact positiveSourceGravityMouthCumulativeTrace_eq_sub n
  rw [closedForm]
  simpa using limit

/-- The retained total responsibility has no alternative limit branch. -/
theorem positiveSourceGravityMouthCumulativeTrace_limit_unique
    (limit : GravityMouthResponsibilityCarrier)
    (limitLaw :
      Tendsto positiveSourceGravityMouthCumulativeTrace atTop (nhds limit)) :
    limit = carriedPositiveSourceGravityMouthSpinOrbitObstruction :=
  tendsto_nhds_unique limitLaw
    tendsto_positiveSourceGravityMouthCumulativeTrace_original

/-! ## Downstream curvature-obligation readout -/

/-- Curvature obligation read from the `n`-th residual.  It is not stored in
the source and does not assert existence of a realizing connection. -/
def positiveSourceGravityMouthIteratedCurvatureObligation
    (n : ℕ) : PhysicalBivector :=
  positiveSourceGravityMouthConstitutiveCurvature +
    (positiveSourceGravityMouthResidualIterate n : PhysicalBivector)

@[simp] theorem positiveSourceGravityMouthIteratedCurvatureObligation_zero :
    positiveSourceGravityMouthIteratedCurvatureObligation 0 =
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin := by
  rw [positiveSourceGravityMouthIteratedCurvatureObligation,
    positiveSourceGravityMouthResidualIterate_zero]
  change
    positiveSourceGravityMouthConstitutiveCurvature +
        positiveSourceGravityMouthObstruction =
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin
  rw [positiveSourceGravityMouthObstruction_eq_source_sub_constitutive]
  abel

/-- C3g7a's first required curvature is exactly the first point of this
canonical residual-transport orbit. -/
@[simp] theorem positiveSourceGravityMouthIteratedCurvatureObligation_one :
    positiveSourceGravityMouthIteratedCurvatureObligation 1 =
      positiveSourceGravityMouthRequiredCurvature := by
  rfl

theorem positiveSourceGravityMouthIteratedCurvatureObligation_residual
    (n : ℕ) :
    positiveSourceGravityMouthIteratedCurvatureObligation n -
        positiveSourceGravityMouthConstitutiveCurvature =
      (positiveSourceGravityMouthResidualIterate n : PhysicalBivector) := by
  rw [positiveSourceGravityMouthIteratedCurvatureObligation]
  abel

/-- No finite curvature obligation is falsely identified with the exact
gravity-shell curvature. -/
theorem positiveSourceGravityMouthFiniteCurvatureObligation_ne_constitutive
    (n : ℕ) :
    positiveSourceGravityMouthIteratedCurvatureObligation n ≠
      positiveSourceGravityMouthConstitutiveCurvature := by
  intro equality
  apply positiveSourceGravityMouthResidualIterate_ne_zero n
  apply Subtype.ext
  have residual :=
    positiveSourceGravityMouthIteratedCurvatureObligation_residual n
  rw [equality] at residual
  exact calc
    (positiveSourceGravityMouthResidualIterate n : PhysicalBivector) =
        positiveSourceGravityMouthConstitutiveCurvature -
          positiveSourceGravityMouthConstitutiveCurvature := residual.symm
    _ = 0 := sub_self _

/-- Source curvature equals the current curvature obligation plus exactly the
accumulated transported trace. -/
theorem positiveSourceGravityMouthSourceCurvature_eq_iterated_add_trace
    (n : ℕ) :
    positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin =
      positiveSourceGravityMouthIteratedCurvatureObligation n +
        (positiveSourceGravityMouthCumulativeTrace n : PhysicalBivector) := by
  have split := congrArg Subtype.val
    (positiveSourceGravityMouthIteratedResidual_split n)
  change
    positiveSourceGravityMouthObstruction =
      (positiveSourceGravityMouthResidualIterate n : PhysicalBivector) +
        (positiveSourceGravityMouthCumulativeTrace n : PhysicalBivector) at split
  rw [positiveSourceGravityMouthObstruction_eq_source_sub_constitutive] at split
  rw [positiveSourceGravityMouthIteratedCurvatureObligation]
  have restored := (sub_eq_iff_eq_add).mp split
  simpa [add_assoc, add_comm, add_left_comm] using restored

/-- The unique residual limit canonically selects the algebraic gravity-shell
curvature obligation.  Realizing it as a local holonomic connection is a later
Layer-3 theorem. -/
theorem tendsto_positiveSourceGravityMouthIteratedCurvatureObligation :
    Tendsto positiveSourceGravityMouthIteratedCurvatureObligation atTop
      (nhds positiveSourceGravityMouthConstitutiveCurvature) := by
  have residualFactor_nonneg :
      0 ≤ 1 - positiveSmoothUnifiedSource.legacy.sigma := by
    linarith [positiveSmoothUnifiedSource.legacy.sigma_lt_one]
  have residualFactor_lt_one :
      1 - positiveSmoothUnifiedSource.legacy.sigma < 1 := by
    linarith [positiveSmoothUnifiedSource.legacy.sigma_pos]
  have scalarLimit :
      Tendsto
        (fun n : ℕ =>
          (1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n)
        atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      residualFactor_nonneg residualFactor_lt_one
  have ambientResidualLimit :
      Tendsto
        (fun n : ℕ =>
          (1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n •
            positiveSourceGravityMouthObstruction)
        atTop (nhds (0 : PhysicalBivector)) := by
    simpa using scalarLimit.smul_const positiveSourceGravityMouthObstruction
  have curvatureLimit :
      Tendsto
        (fun n : ℕ =>
          positiveSourceGravityMouthConstitutiveCurvature +
            (1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n •
              positiveSourceGravityMouthObstruction)
        atTop
        (nhds
          (positiveSourceGravityMouthConstitutiveCurvature +
            (0 : PhysicalBivector))) :=
    tendsto_const_nhds.add ambientResidualLimit
  have closedForm :
      positiveSourceGravityMouthIteratedCurvatureObligation =
        fun n : ℕ =>
          positiveSourceGravityMouthConstitutiveCurvature +
            (1 - positiveSmoothUnifiedSource.legacy.sigma) ^ n •
              positiveSourceGravityMouthObstruction := by
    funext n
    rw [positiveSourceGravityMouthIteratedCurvatureObligation,
      positiveSourceGravityMouthResidualIterate_eq_pow_smul]
    rfl
  rw [closedForm]
  simpa using curvatureLimit

/-- The constitutive shell curvature is the unique limit obligation; no
observable branch constant can replace it. -/
theorem positiveSourceGravityMouthIteratedCurvatureObligation_limit_unique
    (limit : PhysicalBivector)
    (limitLaw :
      Tendsto positiveSourceGravityMouthIteratedCurvatureObligation atTop
        (nhds limit)) :
    limit = positiveSourceGravityMouthConstitutiveCurvature :=
  tendsto_nhds_unique limitLaw
    tendsto_positiveSourceGravityMouthIteratedCurvatureObligation

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthResidualTransportIteration
