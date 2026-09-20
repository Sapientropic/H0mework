import H0mework.Physics.AlphaSources.P532

/-!
# Proposition 533: all-target Yukawa leave-one-out run

P522/P525 prove the leave-one-out theorem once a candidate sigma is supplied:
if the eight non-target slots lock sigma, that candidate predicts the held-out
slot.

This file packages the actual run shape demanded by the roadmap.  A frozen
GUT-scale Yukawa table supplies, for each held-out target, a sigma candidate
judged only by the other eight slots.  Under an all-target lock, every run
candidate is forced to be the table sigma and predicts its target exactly.

Boundary: this still does not supply the physical GUT-scale Yukawa numbers,
integer depths, or RG extraction.  It closes the formal harness shape that such
a table must satisfy.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Leave-one-out run shape -/

/-- A complete leave-one-out run: every Yukawa slot is held out once, and each
run produces a sigma candidate using only the other slots. -/
structure AllTargetYukawaLeaveOneOutRun
    (T : FrozenGUTScaleYukawaTable) where
  candidate :
    ∀ target : YukawaParameter, YukawaLeaveOneOutCandidate T target

namespace FrozenGUTScaleYukawaTable

/-- The table's own sigma gives the canonical existence witness for a
leave-one-out candidate.  It is not the independent physics fit; it proves the
candidate surface is inhabited for any well-formed frozen table. -/
def tableSigmaCandidate
    (T : FrozenGUTScaleYukawaTable)
    (target : YukawaParameter) :
    YukawaLeaveOneOutCandidate T target where
  sigma := T.sigma
  matches_eight := by
    intro y _hy
    exact T.observed_eq_predictionAt y

end FrozenGUTScaleYukawaTable

/-- The canonical all-target run carried by the table's own sigma. -/
def canonicalAllTargetYukawaLeaveOneOutRun
    (T : FrozenGUTScaleYukawaTable) :
    AllTargetYukawaLeaveOneOutRun T where
  candidate := T.tableSigmaCandidate

namespace AllTargetYukawaLeaveOneOutRun

/-- THEOREM 1: under an all-target lock, every run candidate's sigma is the
frozen table sigma. -/
theorem candidate_sigma_eq_table_sigma
    {T : FrozenGUTScaleYukawaTable}
    (R : AllTargetYukawaLeaveOneOutRun T)
    (L : AllTargetYukawaLeaveOneOutLock T)
    (target : YukawaParameter) :
    (R.candidate target).sigma = T.sigma :=
  (R.candidate target).sigma_eq_table_sigma (L.lock_at target)

/-- THEOREM 2: under an all-target lock, every run candidate predicts its
held-out Yukawa slot exactly. -/
theorem predicts_every_target
    {T : FrozenGUTScaleYukawaTable}
    (R : AllTargetYukawaLeaveOneOutRun T)
    (L : AllTargetYukawaLeaveOneOutLock T)
    (target : YukawaParameter) :
    T.observed target =
      T.predictionAt ((R.candidate target).sigma) target :=
  (R.candidate target).predicts_target (L.lock_at target)

/-- THEOREM 3: under an all-target lock, a run candidate and any other
eight-slot candidate give the same held-out target prediction. -/
theorem prediction_unique_against_any_candidate
    {T : FrozenGUTScaleYukawaTable}
    (R : AllTargetYukawaLeaveOneOutRun T)
    (L : AllTargetYukawaLeaveOneOutLock T)
    (target : YukawaParameter)
    (C : YukawaLeaveOneOutCandidate T target) :
    T.predictionAt ((R.candidate target).sigma) target =
      T.predictionAt C.sigma target :=
  (R.candidate target).target_prediction_unique (L.lock_at target) C

end AllTargetYukawaLeaveOneOutRun

/-! ## Bundled run certificate -/

/-- A compact certificate that a frozen Yukawa table passes the complete
all-target leave-one-out run. -/
structure AllTargetYukawaLeaveOneOutRunCertificate
    (T : FrozenGUTScaleYukawaTable) where
  all_target_lock :
    AllTargetYukawaLeaveOneOutLock T
  run :
    AllTargetYukawaLeaveOneOutRun T
  run_sigma_eq_table_sigma :
    ∀ target : YukawaParameter,
      (run.candidate target).sigma = T.sigma
  run_predicts_every_target :
    ∀ target : YukawaParameter,
      T.observed target =
        T.predictionAt ((run.candidate target).sigma) target
  run_prediction_unique_against_any_candidate :
    ∀ target : YukawaParameter,
      ∀ C : YukawaLeaveOneOutCandidate T target,
        T.predictionAt ((run.candidate target).sigma) target =
          T.predictionAt C.sigma target

/-- DEFINITION/THEOREM 4: any all-target lock plus any complete run supplies the
all-target run certificate. -/
def allTargetYukawaLeaveOneOutRunCertificate_of_lock_and_run
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T)
    (R : AllTargetYukawaLeaveOneOutRun T) :
    AllTargetYukawaLeaveOneOutRunCertificate T where
  all_target_lock := L
  run := R
  run_sigma_eq_table_sigma := fun target =>
    R.candidate_sigma_eq_table_sigma L target
  run_predicts_every_target := fun target =>
    R.predicts_every_target L target
  run_prediction_unique_against_any_candidate := fun target C =>
    R.prediction_unique_against_any_candidate L target C

/-- DEFINITION/THEOREM 5: every all-target locked frozen table has a canonical complete
leave-one-out run certificate. -/
def canonicalAllTargetYukawaLeaveOneOutRunCertificate
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T) :
    AllTargetYukawaLeaveOneOutRunCertificate T :=
  allTargetYukawaLeaveOneOutRunCertificate_of_lock_and_run
    L (canonicalAllTargetYukawaLeaveOneOutRun T)

/-- DEFINITION/THEOREM 6: the linear-anchor family is enough to run the full all-target
leave-one-out harness. -/
def canonicalAllTargetYukawaLeaveOneOutRunCertificate_of_linear_anchor_family
    {T : FrozenGUTScaleYukawaTable}
    (hanchor :
      ∀ target : YukawaParameter,
        ∃ anchor : YukawaParameter,
          anchor ≠ target ∧
            T.exponent anchor = 1 ∧
              T.amplitude anchor ≠ 0) :
    AllTargetYukawaLeaveOneOutRunCertificate T :=
  canonicalAllTargetYukawaLeaveOneOutRunCertificate
    (allTargetYukawaLeaveOneOutLock_of_linear_anchor_family hanchor)

end StandardModelConstraint
end SaturationMonoid
