import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.Dissipation
import H0mework.Versions.Y.Arithmetic.RiemannNativeCurrent.Laplace

/-! The original head coupling consumes the same Pa source Green energy and the unchanged physical Laplace read. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaHeadCoupling_source_energy {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
    let psi := burnolTateReciprocalL2 (burnolMobiusSourceL2
      (burnolPaSourceCorrection probe ⟨p, Submodule.starProjection_apply_mem _ _⟩));
    ‖((1 / 4 : ℝ) : ℂ) ^ (probe.value - 1)‖ ^ 2 *
      ‖∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (probe.value / 2) h *
        inner ℂ (Z : BurnolPaAmbientCarrier) (burnolPairedAmbientCompression (h / 2) p)‖ ^ 2 =
      ‖inner ℂ (Z : BurnolL2) (burnolUnitTailResponse probe 4)‖ ^ 2 *
        (-8 * (inner ℂ psi (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))).re -
          2 * (2 * probe.value.re - 1) * ‖psi‖ ^ 2) := by
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
  let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
  let M := burnolPaResolventSourceCoefficient probe p
  let G := inner ℂ (Z : BurnolL2) (burnolUnitTailResponse probe 4)
  let psi := burnolTateReciprocalL2 (burnolMobiusSourceL2
    (burnolPaSourceCorrection probe ⟨p, Submodule.starProjection_apply_mem _ _⟩))
  have energy := burnolPaSourceGreen probe p (Submodule.starProjection_apply_mem _ _)
  change -4 * (inner ℂ psi (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))).re =
    (2 * probe.value.re - 1) * ‖psi‖ ^ 2 +
      (1 / 2 : ℝ) * ‖((1 / 4 : ℝ) : ℂ) ^ (probe.value - 1) * M‖ ^ 2 at energy
  rw [norm_mul, mul_pow] at energy
  have laplace := burnolPaHeadCoupling_laplace_source observation nontrivial rightHalf probe
  change (∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (probe.value / 2) h *
    inner ℂ (Z : BurnolPaAmbientCarrier) (burnolPairedAmbientCompression (h / 2) p)) = -M * G at laplace
  dsimp only
  rw [laplace, norm_mul, norm_neg, mul_pow]
  change ‖((1 / 4 : ℝ) : ℂ) ^ (probe.value - 1)‖ ^ 2 * (‖M‖ ^ 2 * ‖G‖ ^ 2) =
    ‖G‖ ^ 2 * (-8 * (inner ℂ psi (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))).re -
      2 * (2 * probe.value.re - 1) * ‖psi‖ ^ 2)
  linear_combination -2 * ‖G‖ ^ 2 * energy

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
