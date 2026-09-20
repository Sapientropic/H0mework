import H0mework.Realization.Relaxation.P731

/-!
# Proposition 732: structurally forced updates drive the four-face core

P730 says four face observers that commute with `relaxModule` are forced into
one common residual projection core.

P731 says an unknown scalar update satisfying target-chart complement transport
and target-one rate readout is not really unknown: it is `relaxTo`.

This file composes those facts.  A face observer only has to commute with the
structurally specified update `f`; if `f` satisfies the P731 structural laws,
then the observer automatically commutes with `relaxModule`, and the P730
four-face common-core theorem applies.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-- A scalar observer commutes with an arbitrary scalar target-general update
`f`.  This is deliberately stated before naming `relaxTo`; P732 will force
that name from the structural laws. -/
def CommutesWithScalarUpdate
    (f : ℝ -> ℝ -> ℝ -> ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ target sigma x : ℝ,
    g (f target sigma x) = f (g target) sigma (g x)

/-- THEOREM 1: if the scalar update is structurally valid in the P731 sense,
then any observer commuting with that update also commutes with the canonical
real `relaxModule`. -/
theorem commutesWithRealRelaxModule_of_commutesWith_structuralScalarUpdate
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : ℝ, f 1 sigma 0 = sigma)
    (g : ℝ -> ℝ)
    (hcomm : CommutesWithScalarUpdate f g) :
    CommutesWithRealRelaxModule g := by
  intro target sigma x
  have hf := relaxTo_unique_of_targetChartComplementLinear_rateReadout
    f hchart hrate
  calc
    g (relaxModule target sigma x)
        = g (f target sigma x) := by
          congr 1
          rw [hf target sigma x]
          unfold relaxModule relaxTo
          ring
    _ = f (g target) sigma (g x) := hcomm target sigma x
    _ = relaxModule (g target) sigma (g x) := by
          rw [hf (g target) sigma (g x)]
          unfold relaxModule relaxTo
          ring

/-- A four-face observer family driven by an initially unnamed scalar update
`f`.  The update is required only to satisfy P731's structural laws, and the
face observers are required only to commute with that update. -/
structure ScalarUpdateDrivenFourFaceObserverFamily
    (f : ℝ -> ℝ -> ℝ -> ℝ) where
  target : ℝ
  faceTarget : UnifiedProjectionFace -> ℝ
  observe : UnifiedProjectionFace -> ℝ -> ℝ
  update_chart : IsTargetChartComplementLinearUpdate f
  update_rate_readout : ∀ sigma : ℝ, f 1 sigma 0 = sigma
  commutes_with_update :
    ∀ face : UnifiedProjectionFace, CommutesWithScalarUpdate f (observe face)
  centered_target_commutes :
    ∀ face : UnifiedProjectionFace,
      centeredRelaxObserver (observe face) (faceTarget face) = target

/-- THEOREM 2: a four-face family driven by a structurally valid unnamed update
canonically becomes a P730 relaxation-commuting face family. -/
def ScalarUpdateDrivenFourFaceObserverFamily.toRelaxCommutingFaceObserverFamily
    {f : ℝ -> ℝ -> ℝ -> ℝ}
    (F : ScalarUpdateDrivenFourFaceObserverFamily f) :
    RelaxCommutingFaceObserverFamily ℝ ℝ UnifiedProjectionFace where
  target := F.target
  faceTarget := F.faceTarget
  observe := F.observe
  commutes := by
    intro face
    exact commutesWithRealRelaxModule_of_commutesWith_structuralScalarUpdate
      f F.update_chart F.update_rate_readout
      (F.observe face) (F.commutes_with_update face)
  centered_target_commutes := F.centered_target_commutes

/-- THEOREM 3: four faces commuting with an unnamed but structurally valid
scalar update are forced into the P730 common residual core. -/
theorem structuralScalarUpdate_fourFace_commonCore
    {f : ℝ -> ℝ -> ℝ -> ℝ}
    (F : ScalarUpdateDrivenFourFaceObserverFamily f) :
    LinearProjectedFaceFamilyCertificate
      F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  fourFace_relaxCommutingObservers_force_commonResidualCore
    F.toRelaxCommutingFaceObserverFamily

/-- THEOREM 4: on the scalar core, the same structural-update-driven four-face
family inherits the forced residual-energy scaling law. -/
theorem structuralScalarUpdate_fourFace_commonScalarEnergy
    {f : ℝ -> ℝ -> ℝ -> ℝ}
    (F : ScalarUpdateDrivenFourFaceObserverFamily f) :
    LinearProjectedFaceFamilyScalarEnergyCertificate
      F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily :=
  fourFace_relaxCommutingObservers_force_commonScalarEnergy
    F.toRelaxCommutingFaceObserverFamily

/-- P732 certificate: an unnamed scalar update satisfying P731's structural
laws is enough to drive the P730 four-face common-core theorem. -/
structure StructuralUpdateDrivenFourFaceCoreCertificate : Prop where
  observer_commuting_with_structural_update_commutes_with_relaxModule :
    ∀ (f : ℝ -> ℝ -> ℝ -> ℝ),
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : ℝ, f 1 sigma 0 = sigma) ->
      ∀ g : ℝ -> ℝ,
        CommutesWithScalarUpdate f g ->
        CommutesWithRealRelaxModule g
  structural_update_four_face_common_core :
    ∀ {f : ℝ -> ℝ -> ℝ -> ℝ},
      ∀ F : ScalarUpdateDrivenFourFaceObserverFamily f,
        LinearProjectedFaceFamilyCertificate
          F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily
  structural_update_four_face_common_scalar_energy :
    ∀ {f : ℝ -> ℝ -> ℝ -> ℝ},
      ∀ F : ScalarUpdateDrivenFourFaceObserverFamily f,
        LinearProjectedFaceFamilyScalarEnergyCertificate
          F.toRelaxCommutingFaceObserverFamily.toZeroBasedFamily.toLinearProjectedFaceFamily

/-- THEOREM 5: the structural-update-driven four-face bridge is machine
checked on the real scalar carrier. -/
theorem structuralUpdateDrivenFourFaceCoreCertificate :
    StructuralUpdateDrivenFourFaceCoreCertificate where
  observer_commuting_with_structural_update_commutes_with_relaxModule :=
    commutesWithRealRelaxModule_of_commutesWith_structuralScalarUpdate
  structural_update_four_face_common_core :=
    structuralScalarUpdate_fourFace_commonCore
  structural_update_four_face_common_scalar_energy :=
    structuralScalarUpdate_fourFace_commonScalarEnergy

end AffineRelaxation
end SaturationMonoid
