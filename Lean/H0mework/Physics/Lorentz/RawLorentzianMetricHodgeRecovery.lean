import H0mework.Realization.Relations.FintypeDerivation
import Mathlib

/-!
# Computed Lorentzian coframe--metric--Hodge recovery

This module upgrades the Euclidean lower-bound geometry slice used during the
initial reconstruction.  A coframe is a real `4 × 4` matrix and the spacetime
metric is computed from the fixed internal form

`eta = diag(-1, 1, 1, 1)`

as `eᵀ eta e`.  Two-form components are expressed in the oriented coframe
basis `(01, 02, 03, 23, 31, 12)`.  In that basis the Lorentzian Hodge operator
is computed explicitly, rather than accepted merely because its square has
the right sign.

The raw state stores only the coframe and two reported candidates.  The four
laws are coframe nondegeneracy, orientation branch, metric recovery, and Hodge
recovery.  The Lorentzian law `star² = -id` is derived from Hodge recovery and
is therefore not counted a second time.

Boundary: the component convention is a coframe-basis construction.  This
does not yet build Mathlib's full exterior algebra, smooth tetrad field, or a
global Lorentzian manifold.
-/

namespace SaturationMonoid
namespace PhysicsCore

abbrev LorentzianCoframe := Matrix (Fin 4) (Fin 4) ℝ
abbrev LorentzianMetric := Matrix (Fin 4) (Fin 4) ℝ
abbrev LorentzianTwoForm := Fin 6 → ℝ
abbrev LorentzianTwoFormHodgeOperator :=
  LorentzianTwoForm →ₗ[ℝ] LorentzianTwoForm

/-- Fixed internal metric with the `(-,+,+,+)` convention. -/
def minkowskiInternalMetric : LorentzianMetric :=
  Matrix.diagonal ![-1, 1, 1, 1]

/-- Spacetime metric computed from a coframe and the fixed Lorentzian internal
form. -/
def lorentzianMetricOfCoframe
    (coframe : LorentzianCoframe) : LorentzianMetric :=
  coframe.transpose * minkowskiInternalMetric * coframe

/-- Lorentzian Hodge star in the oriented coframe component order
`(01,02,03,23,31,12)`. -/
def lorentzianCoframeHodge : LorentzianTwoFormHodgeOperator where
  toFun := fun ω => ![ω 3, ω 4, ω 5, -ω 0, -ω 1, -ω 2]
  map_add' := by
    intro ω τ
    funext i
    fin_cases i <;> simp [add_comm]
  map_smul' := by
    intro c ω
    funext i
    fin_cases i <;> simp

theorem lorentzianCoframeHodge_square :
    lorentzianCoframeHodge.comp lorentzianCoframeHodge =
      -(LinearMap.id : LorentzianTwoFormHodgeOperator) := by
  ext ω i
  fin_cases i <;> rfl

/-- Raw candidates before any geometry law is proved. -/
structure RawLorentzianMetricHodgeRecovery where
  coframe : LorentzianCoframe
  reportedMetric : LorentzianMetric
  reportedHodge : LorentzianTwoFormHodgeOperator

namespace RawLorentzianMetricHodgeRecovery

def CoframeNondegenerate (S : RawLorentzianMetricHodgeRecovery) : Prop :=
  Matrix.det S.coframe ≠ 0

/-- Together with nondegeneracy this weak inequality selects the positive
orientation branch while keeping degeneracy independently falsifiable. -/
def OrientationBranchNonnegative
    (S : RawLorentzianMetricHodgeRecovery) : Prop :=
  0 ≤ Matrix.det S.coframe

def MetricRecoveredFromCoframe
    (S : RawLorentzianMetricHodgeRecovery) : Prop :=
  S.reportedMetric = lorentzianMetricOfCoframe S.coframe

def HodgeRecoveredFromCoframeBasis
    (S : RawLorentzianMetricHodgeRecovery) : Prop :=
  S.reportedHodge = lorentzianCoframeHodge

def LorentzianMetricHodgeAdmissible
    (S : RawLorentzianMetricHodgeRecovery) : Prop :=
  S.CoframeNondegenerate ∧
    S.OrientationBranchNonnegative ∧
      S.MetricRecoveredFromCoframe ∧
        S.HodgeRecoveredFromCoframeBasis

inductive LorentzianMetricHodgeCoordinate where
  | coframeNondegeneracy
  | orientationBranch
  | metricRecovery
  | hodgeRecovery
  deriving DecidableEq, Repr, FintypeViaProxy

def CoordinateHolds
    (S : RawLorentzianMetricHodgeRecovery) :
    LorentzianMetricHodgeCoordinate → Prop
  | .coframeNondegeneracy => S.CoframeNondegenerate
  | .orientationBranch => S.OrientationBranchNonnegative
  | .metricRecovery => S.MetricRecoveredFromCoframe
  | .hodgeRecovery => S.HodgeRecoveredFromCoframeBasis

theorem lorentzianMetricHodgeAdmissible_iff_all_coordinates
    (S : RawLorentzianMetricHodgeRecovery) :
    S.LorentzianMetricHodgeAdmissible ↔ ∀ c, S.CoordinateHolds c := by
  constructor
  · rintro ⟨hnondegenerate, horientation, hmetric, hhodge⟩ c
    cases c with
    | coframeNondegeneracy => exact hnondegenerate
    | orientationBranch => exact horientation
    | metricRecovery => exact hmetric
    | hodgeRecovery => exact hhodge
  · intro hall
    exact ⟨hall .coframeNondegeneracy, hall .orientationBranch,
      hall .metricRecovery, hall .hodgeRecovery⟩

theorem not_lorentzianMetricHodgeAdmissible_iff_exists_failed_coordinate
    (S : RawLorentzianMetricHodgeRecovery) :
    ¬ S.LorentzianMetricHodgeAdmissible ↔
      ∃ c, ¬ S.CoordinateHolds c := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot
      (S.lorentzianMetricHodgeAdmissible_iff_all_coordinates.mpr hnone)
  · rintro ⟨c, hc⟩ hadmissible
    exact hc
      (S.lorentzianMetricHodgeAdmissible_iff_all_coordinates.mp
        hadmissible c)

def OnlyFails
    (S : RawLorentzianMetricHodgeRecovery)
    (failed : LorentzianMetricHodgeCoordinate) : Prop :=
  ¬ S.CoordinateHolds failed ∧
    ∀ c, c ≠ failed → S.CoordinateHolds c

/-- The recovered coframe-basis Hodge operator automatically has the
Lorentzian square law. -/
theorem hodgeAntiInvolutive_of_recovered
    (S : RawLorentzianMetricHodgeRecovery)
    (hrecovered : S.HodgeRecoveredFromCoframeBasis) :
    S.reportedHodge.comp S.reportedHodge =
      -(LinearMap.id : LorentzianTwoFormHodgeOperator) := by
  rw [hrecovered]
  exact lorentzianCoframeHodge_square

namespace RawLorentzianMetricHodgeRecoveryToy

def orientationReversingCoframe : LorentzianCoframe :=
  Matrix.diagonal (fun i : Fin 4 => if i = 0 then -1 else 1)

theorem orientationReversingCoframe_det :
    Matrix.det orientationReversingCoframe = -1 := by
  rw [orientationReversingCoframe, Matrix.det_diagonal]
  simp

theorem identityCoframe_metric :
    lorentzianMetricOfCoframe 1 = minkowskiInternalMetric := by
  simp [lorentzianMetricOfCoframe]

theorem zeroCoframe_metric :
    lorentzianMetricOfCoframe 0 = 0 := by
  simp [lorentzianMetricOfCoframe]

theorem orientationReversingCoframe_metric :
    lorentzianMetricOfCoframe orientationReversingCoframe =
      minkowskiInternalMetric := by
  simp [lorentzianMetricOfCoframe, orientationReversingCoframe,
    minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
  intro i
  fin_cases i <;> norm_num

def admissibleSystem : RawLorentzianMetricHodgeRecovery where
  coframe := 1
  reportedMetric := minkowskiInternalMetric
  reportedHodge := lorentzianCoframeHodge

def degeneracyFailureSystem : RawLorentzianMetricHodgeRecovery where
  coframe := 0
  reportedMetric := 0
  reportedHodge := lorentzianCoframeHodge

def orientationFailureSystem : RawLorentzianMetricHodgeRecovery where
  coframe := orientationReversingCoframe
  reportedMetric := minkowskiInternalMetric
  reportedHodge := lorentzianCoframeHodge

def metricFailureSystem : RawLorentzianMetricHodgeRecovery where
  coframe := 1
  reportedMetric := 0
  reportedHodge := lorentzianCoframeHodge

def hodgeFailureSystem : RawLorentzianMetricHodgeRecovery where
  coframe := 1
  reportedMetric := minkowskiInternalMetric
  reportedHodge := 0

theorem admissibleSystem_nondegenerate :
    admissibleSystem.CoframeNondegenerate := by
  simp [CoframeNondegenerate, admissibleSystem]

theorem admissibleSystem_orientation :
    admissibleSystem.OrientationBranchNonnegative := by
  simp [OrientationBranchNonnegative, admissibleSystem]

theorem admissibleSystem_metric :
    admissibleSystem.MetricRecoveredFromCoframe := by
  simp [MetricRecoveredFromCoframe, admissibleSystem,
    identityCoframe_metric]

theorem admissibleSystem_hodge :
    admissibleSystem.HodgeRecoveredFromCoframeBasis :=
  rfl

theorem admissibleSystem_admissible :
    admissibleSystem.LorentzianMetricHodgeAdmissible :=
  ⟨admissibleSystem_nondegenerate, admissibleSystem_orientation,
    admissibleSystem_metric, admissibleSystem_hodge⟩

theorem degeneracyFailureSystem_not_nondegenerate :
    ¬ degeneracyFailureSystem.CoframeNondegenerate := by
  simp [CoframeNondegenerate, degeneracyFailureSystem]

theorem degeneracyFailureSystem_orientation :
    degeneracyFailureSystem.OrientationBranchNonnegative := by
  simp [OrientationBranchNonnegative, degeneracyFailureSystem]

theorem degeneracyFailureSystem_metric :
    degeneracyFailureSystem.MetricRecoveredFromCoframe := by
  simp [MetricRecoveredFromCoframe, degeneracyFailureSystem,
    zeroCoframe_metric]

theorem degeneracyFailureSystem_hodge :
    degeneracyFailureSystem.HodgeRecoveredFromCoframeBasis :=
  rfl

theorem orientationFailureSystem_nondegenerate :
    orientationFailureSystem.CoframeNondegenerate := by
  simp [CoframeNondegenerate, orientationFailureSystem,
    orientationReversingCoframe_det]

theorem orientationFailureSystem_not_orientation :
    ¬ orientationFailureSystem.OrientationBranchNonnegative := by
  simp [OrientationBranchNonnegative, orientationFailureSystem,
    orientationReversingCoframe_det]

theorem orientationFailureSystem_metric :
    orientationFailureSystem.MetricRecoveredFromCoframe := by
  simp [MetricRecoveredFromCoframe, orientationFailureSystem,
    orientationReversingCoframe_metric]

theorem orientationFailureSystem_hodge :
    orientationFailureSystem.HodgeRecoveredFromCoframeBasis :=
  rfl

theorem metricFailureSystem_nondegenerate :
    metricFailureSystem.CoframeNondegenerate := by
  simp [CoframeNondegenerate, metricFailureSystem]

theorem metricFailureSystem_orientation :
    metricFailureSystem.OrientationBranchNonnegative := by
  simp [OrientationBranchNonnegative, metricFailureSystem]

theorem metricFailureSystem_not_metric :
    ¬ metricFailureSystem.MetricRecoveredFromCoframe := by
  intro hmetric
  have hvalue := congrArg (fun M : LorentzianMetric => M 0 0) hmetric
  norm_num [MetricRecoveredFromCoframe, metricFailureSystem,
    identityCoframe_metric, minkowskiInternalMetric] at hvalue

theorem metricFailureSystem_hodge :
    metricFailureSystem.HodgeRecoveredFromCoframeBasis :=
  rfl

theorem hodgeFailureSystem_nondegenerate :
    hodgeFailureSystem.CoframeNondegenerate := by
  simp [CoframeNondegenerate, hodgeFailureSystem]

theorem hodgeFailureSystem_orientation :
    hodgeFailureSystem.OrientationBranchNonnegative := by
  simp [OrientationBranchNonnegative, hodgeFailureSystem]

theorem hodgeFailureSystem_metric :
    hodgeFailureSystem.MetricRecoveredFromCoframe := by
  simp [MetricRecoveredFromCoframe, hodgeFailureSystem,
    identityCoframe_metric]

theorem hodgeFailureSystem_not_hodge :
    ¬ hodgeFailureSystem.HodgeRecoveredFromCoframeBasis := by
  intro hhodge
  have hvalue := LinearMap.congr_fun hhodge (fun _ => 1)
  have hcomponent := congrFun hvalue 0
  norm_num [hodgeFailureSystem, lorentzianCoframeHodge] at hcomponent

theorem degeneracyFailureSystem_onlyFails :
    degeneracyFailureSystem.OnlyFails .coframeNondegeneracy := by
  refine ⟨degeneracyFailureSystem_not_nondegenerate, ?_⟩
  intro c hc
  cases c with
  | coframeNondegeneracy => exact (hc rfl).elim
  | orientationBranch => exact degeneracyFailureSystem_orientation
  | metricRecovery => exact degeneracyFailureSystem_metric
  | hodgeRecovery => exact degeneracyFailureSystem_hodge

theorem orientationFailureSystem_onlyFails :
    orientationFailureSystem.OnlyFails .orientationBranch := by
  refine ⟨orientationFailureSystem_not_orientation, ?_⟩
  intro c hc
  cases c with
  | coframeNondegeneracy => exact orientationFailureSystem_nondegenerate
  | orientationBranch => exact (hc rfl).elim
  | metricRecovery => exact orientationFailureSystem_metric
  | hodgeRecovery => exact orientationFailureSystem_hodge

theorem metricFailureSystem_onlyFails :
    metricFailureSystem.OnlyFails .metricRecovery := by
  refine ⟨metricFailureSystem_not_metric, ?_⟩
  intro c hc
  cases c with
  | coframeNondegeneracy => exact metricFailureSystem_nondegenerate
  | orientationBranch => exact metricFailureSystem_orientation
  | metricRecovery => exact (hc rfl).elim
  | hodgeRecovery => exact metricFailureSystem_hodge

theorem hodgeFailureSystem_onlyFails :
    hodgeFailureSystem.OnlyFails .hodgeRecovery := by
  refine ⟨hodgeFailureSystem_not_hodge, ?_⟩
  intro c hc
  cases c with
  | coframeNondegeneracy => exact hodgeFailureSystem_nondegenerate
  | orientationBranch => exact hodgeFailureSystem_orientation
  | metricRecovery => exact hodgeFailureSystem_metric
  | hodgeRecovery => exact (hc rfl).elim

theorem every_coordinate_has_only_one_failure_model
    (c : LorentzianMetricHodgeCoordinate) :
    ∃ S : RawLorentzianMetricHodgeRecovery, S.OnlyFails c := by
  cases c with
  | coframeNondegeneracy =>
      exact ⟨degeneracyFailureSystem, degeneracyFailureSystem_onlyFails⟩
  | orientationBranch =>
      exact ⟨orientationFailureSystem, orientationFailureSystem_onlyFails⟩
  | metricRecovery =>
      exact ⟨metricFailureSystem, metricFailureSystem_onlyFails⟩
  | hodgeRecovery =>
      exact ⟨hodgeFailureSystem, hodgeFailureSystem_onlyFails⟩

theorem coordinate_cardinality :
    Fintype.card LorentzianMetricHodgeCoordinate = 4 := by
  decide

end RawLorentzianMetricHodgeRecoveryToy

end RawLorentzianMetricHodgeRecovery
end PhysicsCore
end SaturationMonoid
