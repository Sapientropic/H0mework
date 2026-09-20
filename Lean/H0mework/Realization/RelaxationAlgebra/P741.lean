import H0mework.Realization.Relaxation.P733
import H0mework.Realization.Residual.P740

/-!
# Proposition 741: six-face structural updates inherit the process monoid

P733 proves that independently supplied structural updates on each face of the
grand-unification diagonal are all forced to the same scalar relaxation law.
P740 proves that scalar-line natural residual processes, modulo extensional
equality, are exactly the noisy-OR rate monoid.

This file welds those two roots.  The new content is cross-face composition:
if one face applies rate `sigma1` and another face applies rate `sigma2` in the
same target chart, the result is exactly a single update on any face at
`satOrField sigma1 sigma2`.

Thus the six words

`information / energy / matter / mathematics / consciousness / physics`

do not merely carry parallel copies of the formula.  Once their local updates
are accepted by the P731 structural laws, cross-face sequential action is forced
through the same residual-process monoid skeleton.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u

/-- THEOREM 1: every accepted face-local scalar update is the state display of
the canonical natural residual process at the same rate. -/
theorem faceLocal_update_eq_canonical_process_update
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face) (target sigma x : ℝ) :
    F.update face target sigma x =
      residualTransportUpdate
        (ScalarLineNaturalResidualProcess.canonical (E := ℝ) sigma).keepE
        target x := by
  rw [faceLocal_update_eq_relaxTo F face]
  symm
  rw [ScalarLineNaturalResidualProcess.update_forced_relaxModule]
  rw [ScalarLineNaturalResidualProcess.canonical_rate]
  unfold relaxTo relaxModule
  simp [smul_eq_mul]

/-- THEOREM 2: composing updates from any two faces in the same target chart is
one update on any chosen face at the noisy-OR rate. -/
theorem faceLocal_crossFace_sameTarget_compose
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₂ face₁ face₃ : Face)
    (target x sigma1 sigma2 : ℝ) :
    F.update face₂ target sigma2 (F.update face₁ target sigma1 x) =
      F.update face₃ target (satOrField sigma1 sigma2) x := by
  rw [faceLocal_update_eq_relaxTo F face₂]
  rw [faceLocal_update_eq_relaxTo F face₁]
  rw [faceLocal_update_eq_relaxTo F face₃]
  exact relaxTo_compose target x sigma1 sigma2

/-- THEOREM 3: cross-face same-target updates commute. -/
theorem faceLocal_crossFace_sameTarget_comm
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₂ face₁ : Face)
    (target x sigma1 sigma2 : ℝ) :
    F.update face₂ target sigma2 (F.update face₁ target sigma1 x) =
      F.update face₁ target sigma1 (F.update face₂ target sigma2 x) := by
  rw [faceLocal_update_eq_relaxTo F face₂]
  rw [faceLocal_update_eq_relaxTo F face₁]
  exact relaxTo_compose_comm target x sigma1 sigma2

/-- THEOREM 4: three cross-face same-target updates associate through noisy-OR
into one update on any chosen output face. -/
theorem faceLocal_crossFace_sameTarget_assoc
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₃ face₂ face₁ face₄ : Face)
    (target x sigma1 sigma2 sigma3 : ℝ) :
    F.update face₃ target sigma3
        (F.update face₂ target sigma2
          (F.update face₁ target sigma1 x)) =
      F.update face₄ target
        (satOrField sigma1 (satOrField sigma2 sigma3)) x := by
  rw [faceLocal_update_eq_relaxTo F face₃]
  rw [faceLocal_update_eq_relaxTo F face₂]
  rw [faceLocal_update_eq_relaxTo F face₁]
  rw [faceLocal_update_eq_relaxTo F face₄]
  exact relaxTo_compose_assoc target x sigma1 sigma2 sigma3

/-- THEOREM 5: every accepted face has rate zero as no-op. -/
theorem faceLocal_zero_rate_noop
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face) (target x : ℝ) :
    F.update face target 0 x = x := by
  rw [faceLocal_update_eq_relaxTo F face]
  exact relaxTo_zero target x

/-- THEOREM 6: every accepted face has rate one as target hit. -/
theorem faceLocal_one_rate_hits_target
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face) (target x : ℝ) :
    F.update face target 1 x = target := by
  rw [faceLocal_update_eq_relaxTo F face]
  exact relaxTo_one target x

/-- THEOREM 7: every accepted face absorbs the target state. -/
theorem faceLocal_target_absorbing
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face) (target sigma : ℝ) :
    F.update face target sigma target = target := by
  rw [faceLocal_update_eq_relaxTo F face]
  exact relaxTo_target_absorbing target sigma

/-- THEOREM 8: the six named grand-unification faces inherit the cross-face
same-target noisy-OR law. -/
theorem grandUnifiedSixFace_crossFace_sameTarget_compose
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (face₂ face₁ face₃ : GrandUnifiedProjectionFace)
    (target x sigma1 sigma2 : ℝ) :
    F.update face₂ target sigma2 (F.update face₁ target sigma1 x) =
      F.update face₃ target (satOrField sigma1 sigma2) x :=
  faceLocal_crossFace_sameTarget_compose F face₂ face₁ face₃
    target x sigma1 sigma2

/-- THEOREM 9: the six named grand-unification faces inherit cross-face
same-target commutativity. -/
theorem grandUnifiedSixFace_crossFace_sameTarget_comm
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (face₂ face₁ : GrandUnifiedProjectionFace)
    (target x sigma1 sigma2 : ℝ) :
    F.update face₂ target sigma2 (F.update face₁ target sigma1 x) =
      F.update face₁ target sigma1 (F.update face₂ target sigma2 x) :=
  faceLocal_crossFace_sameTarget_comm F face₂ face₁
    target x sigma1 sigma2

/-- THEOREM 10: the six named grand-unification faces inherit cross-face
same-target associativity through noisy-OR. -/
theorem grandUnifiedSixFace_crossFace_sameTarget_assoc
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (face₃ face₂ face₁ face₄ : GrandUnifiedProjectionFace)
    (target x sigma1 sigma2 sigma3 : ℝ) :
    F.update face₃ target sigma3
        (F.update face₂ target sigma2
          (F.update face₁ target sigma1 x)) =
      F.update face₄ target
        (satOrField sigma1 (satOrField sigma2 sigma3)) x :=
  faceLocal_crossFace_sameTarget_assoc F face₃ face₂ face₁ face₄
    target x sigma1 sigma2 sigma3

/-- P741 certificate: six-face structural updates are governed by the same
P740 residual-process monoid skeleton, and cross-face same-target composition
is noisy-OR. -/
structure SixFaceStructuralUpdateProcessMonoidCertificate : Prop where
  every_face_update_is_canonical_process_update :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face : Face, ∀ target sigma x : ℝ,
          F.update face target sigma x =
            residualTransportUpdate
              (ScalarLineNaturalResidualProcess.canonical (E := ℝ) sigma).keepE
              target x
  cross_face_same_target_compose :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face₂ face₁ face₃ : Face,
          ∀ target x sigma1 sigma2 : ℝ,
            F.update face₂ target sigma2
                (F.update face₁ target sigma1 x) =
              F.update face₃ target (satOrField sigma1 sigma2) x
  cross_face_same_target_comm :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face₂ face₁ : Face,
          ∀ target x sigma1 sigma2 : ℝ,
            F.update face₂ target sigma2
                (F.update face₁ target sigma1 x) =
              F.update face₁ target sigma1
                (F.update face₂ target sigma2 x)
  cross_face_same_target_assoc :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face₃ face₂ face₁ face₄ : Face,
          ∀ target x sigma1 sigma2 sigma3 : ℝ,
            F.update face₃ target sigma3
                (F.update face₂ target sigma2
                  (F.update face₁ target sigma1 x)) =
              F.update face₄ target
                (satOrField sigma1 (satOrField sigma2 sigma3)) x
  zero_rate_noop :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face : Face, ∀ target x : ℝ,
          F.update face target 0 x = x
  one_rate_hits_target :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face : Face, ∀ target x : ℝ,
          F.update face target 1 x = target
  target_absorbing :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face : Face, ∀ target sigma : ℝ,
          F.update face target sigma target = target
  grand_unified_six_face_compose :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ face₂ face₁ face₃ : GrandUnifiedProjectionFace,
        ∀ target x sigma1 sigma2 : ℝ,
          F.update face₂ target sigma2
              (F.update face₁ target sigma1 x) =
            F.update face₃ target (satOrField sigma1 sigma2) x
  grand_unified_six_face_comm :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ face₂ face₁ : GrandUnifiedProjectionFace,
        ∀ target x sigma1 sigma2 : ℝ,
          F.update face₂ target sigma2
              (F.update face₁ target sigma1 x) =
            F.update face₁ target sigma1
              (F.update face₂ target sigma2 x)
  grand_unified_six_face_assoc :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ face₃ face₂ face₁ face₄ : GrandUnifiedProjectionFace,
        ∀ target x sigma1 sigma2 sigma3 : ℝ,
          F.update face₃ target sigma3
              (F.update face₂ target sigma2
                (F.update face₁ target sigma1 x)) =
            F.update face₄ target
              (satOrField sigma1 (satOrField sigma2 sigma3)) x
  process_monoid_skeleton :
    ScalarLineNaturalProcessMonoidSkeletonCertificate ℝ

/-- THEOREM 11: six-face structural updates are governed by the same
residual-process monoid skeleton. -/
theorem sixFaceStructuralUpdateProcessMonoidCertificate :
    SixFaceStructuralUpdateProcessMonoidCertificate where
  every_face_update_is_canonical_process_update :=
    faceLocal_update_eq_canonical_process_update
  cross_face_same_target_compose :=
    faceLocal_crossFace_sameTarget_compose
  cross_face_same_target_comm :=
    faceLocal_crossFace_sameTarget_comm
  cross_face_same_target_assoc :=
    faceLocal_crossFace_sameTarget_assoc
  zero_rate_noop := faceLocal_zero_rate_noop
  one_rate_hits_target := faceLocal_one_rate_hits_target
  target_absorbing := faceLocal_target_absorbing
  grand_unified_six_face_compose :=
    grandUnifiedSixFace_crossFace_sameTarget_compose
  grand_unified_six_face_comm :=
    grandUnifiedSixFace_crossFace_sameTarget_comm
  grand_unified_six_face_assoc :=
    grandUnifiedSixFace_crossFace_sameTarget_assoc
  process_monoid_skeleton :=
    scalarLineNaturalProcessMonoidSkeletonCertificate

end AffineRelaxation
end SaturationMonoid
