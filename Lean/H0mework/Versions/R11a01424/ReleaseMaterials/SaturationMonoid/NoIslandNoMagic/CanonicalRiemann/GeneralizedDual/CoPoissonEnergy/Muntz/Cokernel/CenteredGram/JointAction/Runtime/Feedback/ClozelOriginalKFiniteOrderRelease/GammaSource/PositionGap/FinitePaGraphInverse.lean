import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OriginalPaOrbitRank
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear

open BurnolPhysicalState HilbertInventory.SecondConductorStock.SingleSlot
open scoped InnerProductSpace

namespace Gram
export SourceGeneratedFiniteGram (Coordinates action coefficients equation)
export SourceGeneratedFiniteGram.Projection (gram rhs synthesis action_read kernel_synthesis)
end Gram

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "actualPa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "paSlots" => (fun (indices : Finset Nat) (i : indices) => actualPa (Subtype.val i))

private theorem pa_gram_action_injective (indices : Finset Nat) :
    Function.Injective (Gram.action (Gram.gram (paSlots indices))) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a inKernel
  have gone : Gram.synthesis (paSlots indices) a = 0 :=
    Gram.kernel_synthesis (paSlots indices) inKernel
  have rank := (actual_division_Pa_linearIndependent observation nontrivial half depth).comp
    (Subtype.val : indices → Nat) Subtype.val_injective
  have coefficientsZero := (Fintype.linearIndependent_iff.mp rank) (fun i => a i) gone
  change a = 0
  ext i
  exact coefficientsZero i

/-- The existing source Gram solver accepts the actual Pa prices on an arbitrary finite set of literal slots. -/
def paCoordinates (indices : Finset Nat) (prices : Gram.Coordinates indices) : Gram.Coordinates indices :=
  Gram.coefficients (Gram.gram (paSlots indices)) (Matrix.isHermitian_gram ℂ (paSlots indices)) prices
    (fun a silent => by
      have erased := pa_gram_action_injective observation nontrivial half depth indices
        (silent.trans (map_zero _).symm)
      rw [erased, inner_zero_left])

private theorem pa_coordinates_exact (indices : Finset Nat) (a : Gram.Coordinates indices) :
    paCoordinates observation nontrivial half depth indices
      (Gram.rhs (paSlots indices) (Gram.synthesis (paSlots indices) a)) = a := by
  let prices := Gram.rhs (paSlots indices) (Gram.synthesis (paSlots indices) a)
  have paid : Gram.action (Gram.gram (paSlots indices))
      (paCoordinates observation nontrivial half depth indices prices) = prices := by
    unfold paCoordinates
    exact Gram.equation _ _ _ _
  apply pa_gram_action_injective observation nontrivial half depth indices
  refine paid.trans ?_
  ext i
  exact (Gram.action_read (paSlots indices) a i).symm

/-- Reconstruct the complete source graph from finite prices in the original Pa projection. -/
def paGraphInverse (indices : Finset Nat) (prices : Gram.Coordinates indices) : Wide :=
  let a := paCoordinates observation nontrivial half depth indices prices
  ∑ i : indices, a i • stock i.val

/-- The same finite original Pa data recovers both the generated combination and its exact native R write. -/
theorem actual_finite_Pa_graph_inverse (indices : Finset Nat) (a : Gram.Coordinates indices) :
    let prices := Gram.rhs (paSlots indices) (Gram.synthesis (paSlots indices) a);
    let recovered := paGraphInverse observation nontrivial half depth indices prices;
    recovered = (∑ i : indices, a i • stock i.val) ∧
      advanceWide c observation.mathlibZero recovered = (∑ i : indices, a i • stock (i.val+1)) := by
  let prices := Gram.rhs (paSlots indices) (Gram.synthesis (paSlots indices) a)
  have recovered : paGraphInverse observation nontrivial half depth indices prices =
      (∑ i : indices, a i • stock i.val) := by
    unfold paGraphInverse prices
    rw [pa_coordinates_exact]
  refine ⟨recovered, ?_⟩
  rw [recovered, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, actual_wide_next]

end OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
