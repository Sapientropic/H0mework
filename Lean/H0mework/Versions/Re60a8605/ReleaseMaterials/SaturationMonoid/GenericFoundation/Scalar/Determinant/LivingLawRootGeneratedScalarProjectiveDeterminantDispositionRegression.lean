import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarBoundedProjectiveDeterminantDispositionKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarConstantRankDeterminantRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarRankComponentDispositionRegression

/-!
# Scalar projective determinant disposition regression

The automatic producer selects the constant/Picard branch for the actual
elliptic Picard line and the rank-varying branch for a disconnected product
source.  The bounded observation consumer reaches the same producer without
supplying a determinant premise.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarProjectiveDeterminantDispositionRegression

open SourceGeneratedScalarProjectiveDeterminantDisposition
open SourceGeneratedScalarNontrivialPicardLineRegression

noncomputable section

theorem ellipticPicardLine_automatic_constant :
    ∃ (readout : SourceGeneratedScalarConstantRankDeterminant.Readout
        (R := RationalRing) (M := RationalPicLine))
      (picard : readout.PicardDisposition),
      settle (inferInstance : Module.Finite RationalRing RationalPicLine)
          (inferInstance : Module.Projective RationalRing RationalPicLine) =
        .constant readout picard := by
  exact settle_constant_of_constantRank
    (inferInstance : Module.Finite RationalRing RationalPicLine)
    (inferInstance : Module.Projective RationalRing RationalPicLine)
    1 SourceGeneratedScalarConstantRankDeterminant.invertible_rankAtStalk

theorem ellipticPicardObservation_reaches_projectiveDisposition :
    ∃ (equivalence :
        SourceGeneratedScalarPerfectification.PerfectificationCarrier
            rationalPicEvaluation ≃ₗ[RationalRing] RationalPicLine)
      (finite : Module.Finite RationalRing RationalPicLine)
      (projective : Module.Projective RationalRing RationalPicLine)
      (duality : SourceGeneratedScalarFiniteProjectiveDuality.TensorDuality
        (R := RationalRing) RationalPicLine),
      SourceGeneratedScalarBoundedProjectiveDeterminantDisposition.settle
          (observation := rationalPicObservation)
          (.boundedDualizable (observation := rationalPicObservation)
            equivalence finite projective duality) =
        .boundedProjective equivalence finite projective duality
          (settle finite projective) ∧
      ∃ (readout : SourceGeneratedScalarConstantRankDeterminant.Readout
          (R := RationalRing) (M := RationalPicLine))
        (picard : readout.PicardDisposition),
        settle finite projective = .constant readout picard := by
  obtain ⟨equivalence, finite, projective, duality, _, _, _⟩ :=
    rationalPicLine_settles_projectiveNonfree
  exact ⟨equivalence, finite, projective, duality, rfl,
    settle_constant_of_constantRank finite projective 1
      SourceGeneratedScalarConstantRankDeterminant.invertible_rankAtStalk⟩

namespace ZeroCoefficient

abbrev R1 := ZMod 1

theorem constantRankZero :
    Module.rankAtStalk R1 = fun _ : PrimeSpectrum R1 => 0 := by
  have noPrime : ¬ Nonempty (PrimeSpectrum R1) := by
    intro prime
    exact not_nontrivial R1
      (PrimeSpectrum.nonempty_iff_nontrivial.mp prime)
  funext prime
  exact (noPrime ⟨prime⟩).elim

theorem automatic_constant :
    ∃ (readout : SourceGeneratedScalarConstantRankDeterminant.Readout
        (R := R1) (M := R1))
      (picard : readout.PicardDisposition),
      settle (inferInstance : Module.Finite R1 R1)
          (inferInstance : Module.Projective R1 R1) =
        .constant readout picard :=
  settle_constant_of_constantRank
    (inferInstance : Module.Finite R1 R1)
    (inferInstance : Module.Projective R1 R1) 0 constantRankZero

end ZeroCoefficient

namespace ProductFactor

open SourceGeneratedScalarRankComponentDispositionRegression
open SourceGeneratedScalarRankComponentDispositionRegression.ProductFactorDiagnostic

local instance : Algebra ProductBase ℚ :=
  (RingHom.fst ℚ ℚ).toAlgebra

theorem finite : Module.Finite ProductBase ℚ :=
  Module.Finite.of_surjective (Algebra.linearMap ProductBase ℚ)
    (RingHom.fst ℚ ℚ).surjective

theorem projective : Module.Projective ProductBase ℚ := by
  apply Module.Projective.of_split includeLeft (Algebra.linearMap ProductBase ℚ)
  ext value
  change value = value
  rfl

theorem automatic_rankVarying :
    ∃ residual :
        SourceGeneratedScalarRankComponentDisposition.RankVaryingResidualAt
          ProductBase ℚ,
      settle finite projective = .rankVarying residual :=
  settle_rankVarying_of_residual finite projective varyingResidual

end ProductFactor

end
end SourceGeneratedScalarProjectiveDeterminantDispositionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarProjectiveDeterminantDispositionRegression.ellipticPicardLine_automatic_constant
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarProjectiveDeterminantDispositionRegression.ellipticPicardObservation_reaches_projectiveDisposition
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarProjectiveDeterminantDispositionRegression.ZeroCoefficient.automatic_constant
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarProjectiveDeterminantDispositionRegression.ProductFactor.automatic_rankVarying
