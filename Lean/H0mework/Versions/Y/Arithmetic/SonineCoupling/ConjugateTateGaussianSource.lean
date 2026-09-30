import H0mework.Versions.Y.Arithmetic.MellinBoundary.PositiveMellinQuarterMaterial
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzZeroGraphCokernel
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzRieszDilation
import H0mework.Versions.Y.Arithmetic.SonineCoupling.ConjugateTateRelationGraphEquivalence

/-!
# Conjugate--Tate source identity of the zero-owned Gaussian state

The generated Gaussian remainder, rather than the normalized nonzero probe,
is the actual zero-owned source state.  Its selected and reversal convergence
receipts come from the same generated zero occurrence.  Reality and the
source Poisson--Tate law make its independently generated reversal face
literally the conjugate--Tate image of its selected face.

The normalized no-go shell remains a valid Riesz detector, but its Mellin
coordinate is one whereas the Gaussian source coordinate is zero.  It cannot
be substituted for the source state when constructing a root effect.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedFunctionalGraphCokernel

noncomputable section

theorem positiveGeneratedClozelGaussianRemainder_star
    (owner : GlobalGermOwner) (t : PositiveMellinReal) :
    star (positiveGeneratedClozelGaussianRemainder owner t) =
      positiveGeneratedClozelGaussianRemainder owner t := by
  change star (generatedClozelGaussianRemainderKernel owner t.1) =
    generatedClozelGaussianRemainderKernel owner t.1
  rw [generatedClozelGaussianRemainderKernel_eq_scalarRemainder owner t.1 t.2]
  simp

theorem pointwiseConjugation_positiveGeneratedClozelGaussianRemainder
    (owner : GlobalGermOwner) :
    positiveMellinPointwiseConjugation
        (positiveGeneratedClozelGaussianRemainder owner) =
      positiveGeneratedClozelGaussianRemainder owner := by
  funext t
  exact positiveGeneratedClozelGaussianRemainder_star owner t

def selectedGaussianQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (selectedCoPoissonMuntzParameter observation) :=
  let zeroIncidence :=
    generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial
  let relation := positiveClozelMellinRelation owner
    (selectedCoPoissonMuntzParameter observation) zeroIncidence.1
  ⟨relation.1,
    ⟨by
      change positiveGeneratedClozelGaussianRemainder owner ∈
        positiveMellinQuarterL2Submodule
      exact positiveGeneratedClozelGaussianRemainder_mem_quarterL2 owner,
      relation.2⟩⟩

theorem selectedGaussianQuarterTest_functional_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation)
      (selectedGaussianQuarterTest observation nontrivial) = 0 := by
  unfold selectedGaussianQuarterTest selectedCoPoissonMuntzParameter
  change positiveMellinFunctional (observation.coordinate / 2)
      (restrictPositiveMellin _
        ⟨generatedClozelGaussianRemainderKernel owner,
          (generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
            observation nontrivial).1⟩) = 0
  rw [positiveMellinFunctional_restrictPositive]
  exact (generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
    observation nontrivial).2

/-- The actual zero-generated Gaussian state is not the normalized nonzero
probe used to exhibit the Riesz coordinate. -/
theorem selectedGaussianQuarterTest_ne_normalizedProbe
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedGaussianQuarterTest observation nontrivial ≠
      normalizedCoPoissonMuntzQuarterShellTest
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial) := by
  intro equality
  have functionalEquality := congrArg
    (quarterMellinL2Functional
      (selectedCoPoissonMuntzParameter observation)) equality
  rw [selectedGaussianQuarterTest_functional_zero,
    quarterMellinL2Functional_normalizedShell] at functionalEquality
  norm_num at functionalEquality

def generatedHighGaussianQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation)) :=
  conjugateTateQuarterMellinTest
    (selectedCoPoissonMuntzParameter observation)
    (selectedGaussianQuarterTest observation nontrivial)

theorem generatedHighGaussianQuarterTest_value
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (generatedHighGaussianQuarterTest observation nontrivial).1 =
      positiveGeneratedClozelGaussianRemainder owner := by
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation
        (positiveGeneratedClozelGaussianRemainder owner)) = _
  rw [pointwiseConjugation_positiveGeneratedClozelGaussianRemainder]
  exact positiveTateInvolution_clozelRelation owner

theorem gaussian_conjugateTateParameter_eq_reversal
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation) =
      reversalCoPoissonMuntzParameter observation := by
  unfold selectedCoPoissonMuntzParameter
    reversalCoPoissonMuntzParameter conjugateTateMellinParameter
    coordinateReversal
  change (1 / 2 : ℂ) -
      (starRingEnd ℂ) (observation.coordinate / 2) =
    (1 - (starRingEnd ℂ) observation.coordinate) / 2
  rw [map_div₀, map_ofNat]
  norm_num
  ring

/-- Independent target face of the same Gaussian occurrence.  Its carrier
proof comes from the reversal zero, not from conjugate--Tate transport. -/
def independentHighGaussianQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation)) :=
  let convergent : MellinConvergent
      (generatedClozelGaussianRemainderKernel owner)
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation)) := by
    rw [gaussian_conjugateTateParameter_eq_reversal observation]
    exact (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial).1
  let relation := positiveClozelMellinRelation owner
    (conjugateTateMellinParameter
      (selectedCoPoissonMuntzParameter observation)) convergent
  ⟨relation.1,
    ⟨by
      change positiveGeneratedClozelGaussianRemainder owner ∈
        positiveMellinQuarterL2Submodule
      exact positiveGeneratedClozelGaussianRemainder_mem_quarterL2 owner,
      relation.2⟩⟩

theorem independentHighGaussianQuarterTest_value
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (independentHighGaussianQuarterTest observation nontrivial).1 =
      positiveGeneratedClozelGaussianRemainder owner := by
  rfl

theorem generatedHighGaussianQuarterTest_eq_independent
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedHighGaussianQuarterTest observation nontrivial =
      independentHighGaussianQuarterTest observation nontrivial := by
  apply Subtype.ext
  rw [generatedHighGaussianQuarterTest_value,
    independentHighGaussianQuarterTest_value]

def selectedGaussianGraphClass
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SelectedCoPoissonMuntzGraphCokernel observation nontrivial :=
  coPoissonMuntzGraphSourceMap
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (selectedGaussianQuarterTest observation nontrivial)

def generatedHighGaussianGraphClass
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ConjugateTateGeneratedHighGraphCokernel
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial) :=
  coPoissonMuntzGraphSourceMap
    (conjugateTateMellinParameter
      (selectedCoPoissonMuntzParameter observation))
    (conjugateTateMellinParameter_re_pos
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
    (conjugateTateMellinParameter_re_lt_half
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))
    (independentHighGaussianQuarterTest observation nontrivial)

theorem conjugateTate_selectedGaussianGraphClass
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    conjugateTateCoPoissonMuntzQuotientIsometricEquiv
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (selectedGaussianGraphClass observation nontrivial) =
      generatedHighGaussianGraphClass observation nontrivial := by
  unfold selectedGaussianGraphClass generatedHighGaussianGraphClass
  rw [conjugateTateCoPoissonMuntzQuotientIsometricEquiv_source]
  exact congrArg
    (coPoissonMuntzGraphSourceMap
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation))
      (conjugateTateMellinParameter_re_pos
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
      (conjugateTateMellinParameter_re_lt_half
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)))
    (generatedHighGaussianQuarterTest_eq_independent observation nontrivial)

theorem gaussianIdentityEndpointResidual_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedHighGaussianGraphClass observation nontrivial -
      conjugateTateCoPoissonMuntzQuotientIsometricEquiv
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (selectedGaussianGraphClass observation nontrivial) = 0 := by
  rw [conjugateTate_selectedGaussianGraphClass, sub_self]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
