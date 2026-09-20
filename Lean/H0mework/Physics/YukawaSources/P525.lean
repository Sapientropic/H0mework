import H0mework.Realization.Relations.P524

/-!
# Proposition 525: all-target Yukawa leave-one-out certificate

P522 proves the single-target leave-one-out theorem: if the eight non-target
Yukawa slots lock sigma, then any candidate matching those eight slots predicts
the held-out target.

This file lifts that contract to the full nine-slot table.  A concrete physics
producer can now supply one all-target lock certificate instead of nine
separate ad hoc arguments.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## All-target lock -/

/-- Every Yukawa target has an eight-slot sigma lock against the other slots. -/
structure AllTargetYukawaLeaveOneOutLock
    (T : FrozenGUTScaleYukawaTable) : Prop where
  lock :
    ∀ target : YukawaParameter,
      EightSlotSigmaLock target T.observed T.amplitude T.exponent

namespace AllTargetYukawaLeaveOneOutLock

/-- THEOREM 1: an all-target lock gives the single-target lock at every
held-out Yukawa slot. -/
theorem lock_at
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T)
    (target : YukawaParameter) :
    EightSlotSigmaLock target T.observed T.amplitude T.exponent :=
  L.lock target

/-- THEOREM 2: under an all-target lock, any two candidates for the same
held-out slot have the same sigma. -/
theorem candidate_sigma_unique
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T)
    (target : YukawaParameter)
    (C₁ C₂ : YukawaLeaveOneOutCandidate T target) :
    C₁.sigma = C₂.sigma := by
  rw [C₁.sigma_eq_table_sigma (L.lock_at target),
    C₂.sigma_eq_table_sigma (L.lock_at target)]

/-- THEOREM 3: under an all-target lock, every leave-one-out candidate predicts
its held-out slot exactly. -/
theorem predicts_every_target
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T)
    (target : YukawaParameter)
    (C : YukawaLeaveOneOutCandidate T target) :
    T.observed target = T.predictionAt C.sigma target :=
  C.predicts_target (L.lock_at target)

end AllTargetYukawaLeaveOneOutLock

/-! ## A reusable all-target sufficient condition -/

/-- THEOREM 4: if every held-out target has one non-target linear anchor with
nonzero amplitude, then the whole frozen table has all-target leave-one-out
locks. -/
theorem allTargetYukawaLeaveOneOutLock_of_linear_anchor_family
    {T : FrozenGUTScaleYukawaTable}
    (hanchor :
      ∀ target : YukawaParameter,
        ∃ anchor : YukawaParameter,
          anchor ≠ target ∧
            T.exponent anchor = 1 ∧
              T.amplitude anchor ≠ 0) :
    AllTargetYukawaLeaveOneOutLock T where
  lock := by
    intro target
    rcases hanchor target with ⟨anchor, hne, hexp, hamp⟩
    exact
      eightSlotSigmaLock_of_linear_anchor
        (observed := T.observed)
        (amplitude := T.amplitude)
        (exponent := T.exponent)
        hne hexp hamp

/-! ## Bundled all-target prediction receipt -/

/-- A compact receipt that a frozen Yukawa table passes the all-target
leave-one-out prediction contract. -/
structure AllTargetYukawaLeaveOneOutPredictionCertificate
    (T : FrozenGUTScaleYukawaTable) : Prop where
  all_target_lock : AllTargetYukawaLeaveOneOutLock T
  candidate_sigma_unique :
    ∀ target : YukawaParameter,
      ∀ C₁ C₂ : YukawaLeaveOneOutCandidate T target,
        C₁.sigma = C₂.sigma
  predicts_every_target :
    ∀ target : YukawaParameter,
      ∀ C : YukawaLeaveOneOutCandidate T target,
        T.observed target = T.predictionAt C.sigma target

/-- THEOREM 5: an all-target lock supplies the all-target leave-one-out
prediction certificate. -/
theorem allTargetYukawaLeaveOneOutPredictionCertificate_of_lock
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T) :
    AllTargetYukawaLeaveOneOutPredictionCertificate T where
  all_target_lock := L
  candidate_sigma_unique := L.candidate_sigma_unique
  predicts_every_target := L.predicts_every_target

/-- THEOREM 6: the linear-anchor family supplies the all-target prediction
certificate. -/
theorem allTargetYukawaLeaveOneOutPredictionCertificate_of_linear_anchor_family
    {T : FrozenGUTScaleYukawaTable}
    (hanchor :
      ∀ target : YukawaParameter,
        ∃ anchor : YukawaParameter,
          anchor ≠ target ∧
            T.exponent anchor = 1 ∧
              T.amplitude anchor ≠ 0) :
    AllTargetYukawaLeaveOneOutPredictionCertificate T :=
  allTargetYukawaLeaveOneOutPredictionCertificate_of_lock
    (allTargetYukawaLeaveOneOutLock_of_linear_anchor_family hanchor)

end StandardModelConstraint
end SaturationMonoid
