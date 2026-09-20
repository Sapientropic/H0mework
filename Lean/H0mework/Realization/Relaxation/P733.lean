import H0mework.Realization.Relaxation.P732

/-!
# Proposition 733: face-local structural updates collapse to one law

P732 still starts with one unnamed scalar update `f` shared by all faces.
This file removes that shared-update assumption.

Each face may carry its own scalar update `f face`.  If every face-local update
satisfies the P731 target-chart complement law plus the target-one rate
readout, then every `f face` is forced to be the same `relaxTo`.  Therefore
face observers that commute only with their own local update still commute with
the canonical relaxation algebra, and the P730/P732 common residual core
applies.

This is the strong form of the formula diagonal: the common update is not
chosen first.  It is forced independently at each face and only then becomes
one shared residual core.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u

/-- A wider named face set for the current grand-unification diagonal.  The
generic theorems below work for any face type; this finite spine gives a
citeable information/energy/matter/mathematics/consciousness/physics surface. -/
inductive GrandUnifiedProjectionFace where
  | information
  | energy
  | matter
  | mathematics
  | consciousness
  | physics
  deriving DecidableEq, Repr

/-- A face family where each face is allowed to bring its own initially unnamed
scalar update.  The only accepted laws are structural: target-chart complement
transport and target-one rate readout. -/
structure FaceLocalStructuralUpdateObserverFamily
    (Face : Type u) where
  target : ℝ
  faceTarget : Face -> ℝ
  update : Face -> ℝ -> ℝ -> ℝ -> ℝ
  observe : Face -> ℝ -> ℝ
  update_chart :
    ∀ face : Face, IsTargetChartComplementLinearUpdate (update face)
  update_rate_readout :
    ∀ face : Face, ∀ sigma : ℝ, update face 1 sigma 0 = sigma
  commutes_with_face_update :
    ∀ face : Face, CommutesWithScalarUpdate (update face) (observe face)
  centered_target_commutes :
    ∀ face : Face,
      centeredRelaxObserver (observe face) (faceTarget face) = target

/-- THEOREM 1: every structurally valid face-local update is the canonical
target-general scalar relaxation law. -/
theorem faceLocal_update_eq_relaxTo
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face) :
    F.update face = fun target sigma x => relaxTo target sigma x := by
  funext target sigma x
  exact relaxTo_unique_of_targetChartComplementLinear_rateReadout
    (F.update face)
    (F.update_chart face)
    (F.update_rate_readout face)
    target sigma x

/-- THEOREM 2: any two accepted face-local updates are extensionally equal.
The common formula is not an input; it is forced face by face. -/
theorem faceLocal_updates_pairwise_equal
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₁ face₂ : Face) :
    F.update face₁ = F.update face₂ := by
  rw [faceLocal_update_eq_relaxTo F face₁]
  rw [faceLocal_update_eq_relaxTo F face₂]

/-- THEOREM 3: a face-local family canonically becomes a relaxation-commuting
observer family after the face-local updates are forced to `relaxTo`. -/
def FaceLocalStructuralUpdateObserverFamily.toRelaxCommutingFaceObserverFamily
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face) :
    RelaxCommutingFaceObserverFamily ℝ ℝ Face where
  target := F.target
  faceTarget := F.faceTarget
  observe := F.observe
  commutes := by
    intro face
    exact commutesWithRealRelaxModule_of_commutesWith_structuralScalarUpdate
      (F.update face)
      (F.update_chart face)
      (F.update_rate_readout face)
      (F.observe face)
      (F.commutes_with_face_update face)
  centered_target_commutes := F.centered_target_commutes

/-- THEOREM 4: face-local structural updates still force one common residual
core. -/
theorem faceLocalStructuralUpdate_commonCore
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face) :
    LinearProjectedFaceFamilyCertificate
      F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  relaxCommutingObservers_force_commonResidualCore
    F.toRelaxCommutingFaceObserverFamily

/-- THEOREM 5: on the scalar core, face-local structural updates still force
the same residual-energy scaling law. -/
theorem faceLocalStructuralUpdate_commonScalarEnergy
    {Face : Type u}
    (F : FaceLocalStructuralUpdateObserverFamily Face) :
    LinearProjectedFaceFamilyScalarEnergyCertificate
      F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  relaxCommutingObservers_force_commonScalarEnergy
    F.toRelaxCommutingFaceObserverFamily

/-- THEOREM 6: the six named grand-unification faces inherit the same common
core from independently supplied structural updates. -/
theorem grandUnifiedSixFace_faceLocalStructuralUpdate_commonCore
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace) :
    LinearProjectedFaceFamilyCertificate
      F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  faceLocalStructuralUpdate_commonCore F

/-- THEOREM 7: the six named grand-unification faces inherit the same scalar
energy law from independently supplied structural updates. -/
theorem grandUnifiedSixFace_faceLocalStructuralUpdate_commonScalarEnergy
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace) :
    LinearProjectedFaceFamilyScalarEnergyCertificate
      F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  faceLocalStructuralUpdate_commonScalarEnergy F

/-- P733 certificate: even when every face starts with its own unnamed scalar
update, the P731 structure forces all updates to `relaxTo`, hence all accepted
faces share the P730 residual core. -/
structure FaceLocalStructuralUpdateCollapseCertificate : Prop where
  every_face_update_is_relaxTo :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face : Face,
          F.update face = fun target sigma x => relaxTo target sigma x
  any_two_face_updates_are_equal :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face₁ face₂ : Face,
          F.update face₁ = F.update face₂
  face_local_common_core :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        LinearProjectedFaceFamilyCertificate
          F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily
  face_local_common_scalar_energy :
    ∀ {Face : Type u},
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        LinearProjectedFaceFamilyScalarEnergyCertificate
          F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily
  grand_unified_six_face_common_core :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      LinearProjectedFaceFamilyCertificate
        F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily
  grand_unified_six_face_common_scalar_energy :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      LinearProjectedFaceFamilyScalarEnergyCertificate
        F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily

/-- THEOREM 8: face-local structural updates collapse to the canonical
grand-unification relaxation diagonal. -/
theorem faceLocalStructuralUpdateCollapseCertificate :
    FaceLocalStructuralUpdateCollapseCertificate where
  every_face_update_is_relaxTo :=
    faceLocal_update_eq_relaxTo
  any_two_face_updates_are_equal :=
    faceLocal_updates_pairwise_equal
  face_local_common_core :=
    faceLocalStructuralUpdate_commonCore
  face_local_common_scalar_energy :=
    faceLocalStructuralUpdate_commonScalarEnergy
  grand_unified_six_face_common_core :=
    grandUnifiedSixFace_faceLocalStructuralUpdate_commonCore
  grand_unified_six_face_common_scalar_energy :=
    grandUnifiedSixFace_faceLocalStructuralUpdate_commonScalarEnergy

end AffineRelaxation
end SaturationMonoid
