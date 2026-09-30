import H0mework.Versions.Y.Arithmetic.RieszGreen.Eta

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex
open scoped InnerProductSpace
open OriginalRieszSource

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "b" => burnolRieszSingleFourierSource
local notation "S" => burnolMeanZeroTruncatedFourier

private theorem source_inner_smul_left (left right : BurnolQuarterMeanZeroCarrier) (scalar : ℂ) :
    inner ℂ (scalar • left) right = star scalar * inner ℂ left right :=
  inner_smul_left left right scalar

private theorem source_inner_smul_right (left right : BurnolQuarterMeanZeroCarrier) (scalar : ℂ) :
    inner ℂ left (scalar • right) = scalar * inner ℂ left right :=
  inner_smul_right left right scalar

private theorem response_cross (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ Response.u (S (b coordinate)) = inner ℂ Response.v (b coordinate) := by
  exact (meanZero_fourier_pairing_of_reflection Response.u (b coordinate)
    (burnolRieszSingleFourierSource_reflection_fixed coordinate)).symm

private theorem response_read (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ Response.u (b coordinate) - inner ℂ Response.v (S (b coordinate)) =
      (1 / 2 : ℂ) * burnolRieszReturnRaw coordinate q := by
  rw [← meanZero_fourier_pairing_of_reflection Response.v (b coordinate)
    (burnolRieszSingleFourierSource_reflection_fixed coordinate), ← inner_sub_left]
  have source : Response.u - S Response.v = Response.eta := Response.source_pair_equation
  rw [source, eta_source_read]

/-- Algebraic assembly of the two actual interval Green identities. -/
theorem source_green_from_green (left right : BurnolCompletedMellinCoordinate)
    (bGreen : inner ℂ (Euler.sourceEuler left) (b right) +
        inner ℂ (b left) (Euler.sourceEuler right) =
      (1 / 2 : ℂ) * star (Kernel.beta left) * Kernel.beta right)
    (rGreen : inner ℂ (Constructor.returnEuler left) (S (b right)) +
        inner ℂ (S (b left)) (Constructor.returnEuler right) =
      (1 / 2 : ℂ) * star (burnolRieszReturnRaw left q) * burnolRieszReturnRaw right q) :
    (left.value + star right.value - 1) *
        (inner ℂ (b left) (b right) - inner ℂ (S (b left)) (S (b right))) =
      (1 / 2 : ℂ) *
        (star (Kernel.beta left) * Kernel.beta right -
          star (Kernel.A left) * Kernel.A right +
          star (star left.value * GapEuler.gapMean q left) *
            (star right.value * GapEuler.gapMean q right)) := by
  have responseRight := response_read right
  have responseLeft := congrArg (starRingEnd ℂ) (response_read left)
  have crossRight := response_cross right
  have crossLeft := congrArg (starRingEnd ℂ) (response_cross left)
  simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat, inner_conj_symm] at responseLeft
  simp only [inner_conj_symm] at crossLeft
  simp only [starRingEnd_apply] at responseLeft
  rw [Euler.sourceEuler_eq, Euler.sourceEuler_eq] at bGreen
  rw [Euler.returnEuler_eq, Euler.returnEuler_eq] at rGreen
  simp only [inner_add_left, inner_sub_left, source_inner_smul_left, inner_add_right,
    inner_sub_right, source_inner_smul_right, star_sub, star_neg, star_div₀,
    star_one, star_ofNat, star_star] at bGreen rGreen
  have balance : (left.value + star right.value - 1) *
      (inner ℂ (b left) (b right) - inner ℂ (S (b left)) (S (b right))) =
      (1 / 2 : ℂ) * (star (Kernel.beta left) * Kernel.beta right +
        star (burnolRieszReturnRaw left q) * burnolRieszReturnRaw right q -
        star (Kernel.A left) * burnolRieszReturnRaw right q -
        Kernel.A right * star (burnolRieszReturnRaw left q)) := by
    linear_combination bGreen + rGreen - star (Kernel.A left) * responseRight -
      Kernel.A right * responseLeft - star (Kernel.beta left) * crossRight -
      Kernel.beta right * crossLeft
  rw [balance]
  unfold Kernel.A
  simp only [star_add, star_mul, star_star]
  ring

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
