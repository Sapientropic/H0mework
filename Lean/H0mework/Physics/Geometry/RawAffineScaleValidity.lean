import H0mework.Realization.Relations.FintypeDerivation
import Mathlib
import H0mework.Realization.Relaxation.P232
import H0mework.Physics.Admission.StandingAuditBasis

/-!
# Affine scale validity and derived contraction

For the native relaxation operation

`x ↦ x + σ (target - x)`,

Proposition 232 already proves exact distance scaling by `|1-σ|`.  This module
therefore does not store an arbitrary evolution map or a caller-provided
contraction certificate.  The raw state contains only the target and scale;
the evolution is computed by `relaxModule`.

On the intended interval `0 < σ < 1`, strict contraction is a theorem.  It is
not an additional independent coordinate.  The two endpoint laws are
independent, while a concrete over-relaxation `σ = 3/2` shows that contraction
alone does not imply the intended subunit scale domain.  No timestamp or
causal-age operation exists here, so none of these laws is renamed
"freshness".
-/

namespace SaturationMonoid
namespace PhysicsCore

open AffineRelaxation

noncomputable section

structure RawAffineScaleValidity where
  target : ℝ
  sigma : ℝ

namespace RawAffineScaleValidity

def evolution (S : RawAffineScaleValidity) (x : ℝ) : ℝ :=
  relaxModule S.target S.sigma x

def SigmaPositive (S : RawAffineScaleValidity) : Prop :=
  0 < S.sigma

def SigmaSubunit (S : RawAffineScaleValidity) : Prop :=
  S.sigma < 1

def ScaleValid (S : RawAffineScaleValidity) : Prop :=
  S.SigmaPositive ∧ S.SigmaSubunit

/-- A fixed metric definition, not a supplied certificate type. -/
def StrictContraction (S : RawAffineScaleValidity) : Prop :=
  ∃ c : ℝ,
    0 ≤ c ∧ c < 1 ∧
      ∀ x y : ℝ,
        dist (S.evolution x) (S.evolution y) ≤ c * dist x y

inductive ScaleCoordinate where
  | sigmaPositive
  | sigmaSubunit
  deriving DecidableEq, Repr, FintypeViaProxy

def CoordinateHolds
    (S : RawAffineScaleValidity) : ScaleCoordinate → Prop
  | .sigmaPositive => S.SigmaPositive
  | .sigmaSubunit => S.SigmaSubunit

theorem scaleValid_iff_all_coordinates (S : RawAffineScaleValidity) :
    S.ScaleValid ↔ ∀ c, S.CoordinateHolds c := by
  constructor
  · rintro ⟨hpositive, hsubunit⟩ c
    cases c with
    | sigmaPositive => exact hpositive
    | sigmaSubunit => exact hsubunit
  · intro hall
    exact ⟨hall .sigmaPositive, hall .sigmaSubunit⟩

theorem not_scaleValid_iff_exists_failed_coordinate
    (S : RawAffineScaleValidity) :
    ¬ S.ScaleValid ↔ ∃ c, ¬ S.CoordinateHolds c := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot (S.scaleValid_iff_all_coordinates.mpr hnone)
  · rintro ⟨c, hc⟩ hvalid
    exact hc (S.scaleValid_iff_all_coordinates.mp hvalid c)

/-- Contraction is derived from the two scale-domain coordinates. -/
theorem strictContraction_of_scaleValid
    (S : RawAffineScaleValidity) (hvalid : S.ScaleValid) :
    S.StrictContraction := by
  rcases hvalid with ⟨hpositive, hsubunit⟩
  change 0 < S.sigma at hpositive
  change S.sigma < 1 at hsubunit
  refine ⟨1 - S.sigma, by linarith, by linarith, ?_⟩
  intro x y
  change dist (relaxModule S.target S.sigma x)
    (relaxModule S.target S.sigma y) ≤ (1 - S.sigma) * dist x y
  rw [dist_relaxModule_real]
  rw [abs_of_nonneg (by linarith)]

/-! ## Contraction as a native standing operation -/

/-- One affine relaxation step on the value presentation carrier. -/
def standingOperations (S : RawAffineScaleValidity) :
    NativeStandingOperations ℝ Unit where
  apply := fun _ value => some (S.evolution value)

/-- On the valid scale interval, a relaxation output equals the target exactly
when its input already equals the target. -/
theorem eq_target_iff_evolution_eq_target
    (S : RawAffineScaleValidity) (hvalid : S.ScaleValid) (value : ℝ) :
    value = S.target ↔ S.evolution value = S.target := by
  rcases hvalid with ⟨hpositive, hsubunit⟩
  change S.sigma < 1 at hsubunit
  constructor
  · intro hvalue
    subst value
    simp [evolution, relaxModule_target_absorbing]
  · intro hevolved
    have hdistance : dist (S.evolution value) S.target = 0 := by
      rw [hevolved]
      simp
    rw [evolution, dist_relaxModule_target_real] at hdistance
    have hcoefficient : 0 < |1 - S.sigma| := by
      apply abs_pos.mpr
      linarith
    have hvalueDistance : dist value S.target = 0 := by
      have hnonnegative : 0 ≤ dist value S.target := dist_nonneg
      nlinarith
    exact dist_eq_zero.mp hvalueDistance

theorem eqTarget_nativeMoveInvariant
    (S : RawAffineScaleValidity) (hvalid : S.ScaleValid) :
    NativeMoveInvariant (S.standingOperations)
      (fun value => value = S.target) := by
  intro move source result happlies
  change some (S.evolution source) = some result at happlies
  injection happlies with hresult
  subst result
  exact S.eq_target_iff_evolution_eq_target hvalid source

/-- Target membership is standing-relevant under valid native contraction. -/
theorem eqTarget_standingInvariant
    (S : RawAffineScaleValidity) (hvalid : S.ScaleValid) :
    StandingInvariant (generatedStandingIdentity S.standingOperations)
      (fun value => value = S.target) :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    S.standingOperations (fun value => value = S.target)).mpr
      (S.eqTarget_nativeMoveInvariant hvalid)

def OnlyFails
    (S : RawAffineScaleValidity) (failed : ScaleCoordinate) : Prop :=
  ¬ S.CoordinateHolds failed ∧
    ∀ c, c ≠ failed → S.CoordinateHolds c

namespace RawAffineScaleValidityToy

def admissibleSystem : RawAffineScaleValidity where
  target := 0
  sigma := 1 / 2

def positivityFailureSystem : RawAffineScaleValidity where
  target := 0
  sigma := 0

def subunitFailureSystem : RawAffineScaleValidity where
  target := 0
  sigma := 1

def overRelaxingContractionSystem : RawAffineScaleValidity where
  target := 0
  sigma := 3 / 2

theorem admissibleSystem_valid : admissibleSystem.ScaleValid := by
  constructor <;>
    norm_num [SigmaPositive, SigmaSubunit, admissibleSystem]

theorem admissibleSystem_contraction : admissibleSystem.StrictContraction :=
  admissibleSystem.strictContraction_of_scaleValid admissibleSystem_valid

theorem positivityFailureSystem_not_positive :
    ¬ positivityFailureSystem.SigmaPositive := by
  norm_num [SigmaPositive, positivityFailureSystem]

theorem positivityFailureSystem_subunit :
    positivityFailureSystem.SigmaSubunit := by
  norm_num [SigmaSubunit, positivityFailureSystem]

theorem subunitFailureSystem_positive :
    subunitFailureSystem.SigmaPositive := by
  norm_num [SigmaPositive, subunitFailureSystem]

theorem subunitFailureSystem_not_subunit :
    ¬ subunitFailureSystem.SigmaSubunit := by
  norm_num [SigmaSubunit, subunitFailureSystem]

theorem overRelaxingContractionSystem_contraction :
    overRelaxingContractionSystem.StrictContraction := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro x y
  change dist (relaxModule overRelaxingContractionSystem.target
    overRelaxingContractionSystem.sigma x)
    (relaxModule overRelaxingContractionSystem.target
      overRelaxingContractionSystem.sigma y) ≤ 1 / 2 * dist x y
  rw [dist_relaxModule_real]
  norm_num [overRelaxingContractionSystem, abs_of_nonneg]

theorem overRelaxingContractionSystem_not_subunit :
    ¬ overRelaxingContractionSystem.SigmaSubunit := by
  norm_num [SigmaSubunit, overRelaxingContractionSystem]

/-- Strict contraction does not recover the intended `σ < 1` domain. -/
theorem contraction_does_not_force_sigmaSubunit :
    ∃ S : RawAffineScaleValidity,
      S.StrictContraction ∧ ¬ S.SigmaSubunit :=
  ⟨overRelaxingContractionSystem,
    overRelaxingContractionSystem_contraction,
    overRelaxingContractionSystem_not_subunit⟩

theorem positivityFailureSystem_onlyFails :
    positivityFailureSystem.OnlyFails .sigmaPositive := by
  refine ⟨positivityFailureSystem_not_positive, ?_⟩
  intro c hc
  cases c with
  | sigmaPositive => exact (hc rfl).elim
  | sigmaSubunit => exact positivityFailureSystem_subunit

theorem subunitFailureSystem_onlyFails :
    subunitFailureSystem.OnlyFails .sigmaSubunit := by
  refine ⟨subunitFailureSystem_not_subunit, ?_⟩
  intro c hc
  cases c with
  | sigmaPositive => exact subunitFailureSystem_positive
  | sigmaSubunit => exact (hc rfl).elim

theorem every_scaleCoordinate_has_only_one_failure_model
    (c : ScaleCoordinate) :
    ∃ S : RawAffineScaleValidity, S.OnlyFails c := by
  cases c with
  | sigmaPositive =>
      exact ⟨positivityFailureSystem, positivityFailureSystem_onlyFails⟩
  | sigmaSubunit =>
      exact ⟨subunitFailureSystem, subunitFailureSystem_onlyFails⟩

end RawAffineScaleValidityToy

end RawAffineScaleValidity
end
end PhysicsCore
end SaturationMonoid
