import Mathlib.RingTheory.Flat.Rank
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarRankComponentDispositionKernel

/-!
# Scalar rank-component disposition regressions

The first factor `ℚ` over `ℚ × ℚ` is a direct summand of the base ring.  Its
local rank is one on the left spectral component and zero on the right one.
Thus the rank-varying residual branch is mathematical content, not a logical
fallback, and ambient `Module.finrank` cannot replace the local-rank profile.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarRankComponentDispositionRegression

open SourceGeneratedScalarRankComponentDisposition

noncomputable section

namespace ProductFactorDiagnostic

abbrev ProductBase := ℚ × ℚ

local instance : Algebra ProductBase ℚ :=
  (RingHom.fst ℚ ℚ).toAlgebra

noncomputable def includeLeft : ℚ →ₗ[ProductBase] ProductBase where
  toFun x := (x, 0)
  map_add' x y := by
    ext <;> simp
  map_smul' r x := by
    change (r.1 * x, 0) = (r.1 * x, r.2 * 0)
    simp

local instance : Module.Finite ProductBase ℚ :=
  Module.Finite.of_surjective (Algebra.linearMap ProductBase ℚ)
    (RingHom.fst ℚ ℚ).surjective

local instance : Module.Projective ProductBase ℚ := by
  apply Module.Projective.of_split includeLeft (Algebra.linearMap ProductBase ℚ)
  ext x
  change x = x
  rfl

noncomputable def rationalPrime : PrimeSpectrum ℚ :=
  ⟨⊥, Ideal.isPrime_bot⟩

noncomputable def leftPrime : PrimeSpectrum ProductBase :=
  (PrimeSpectrum.primeSpectrumProd ℚ ℚ).symm (Sum.inl rationalPrime)

noncomputable def rightPrime : PrimeSpectrum ProductBase :=
  (PrimeSpectrum.primeSpectrumProd ℚ ℚ).symm (Sum.inr rationalPrime)

theorem left_localRank :
    localRank ProductBase ℚ leftPrime = 1 := by
  have hpos : 0 < localRank ProductBase ℚ leftPrime := by
    rw [PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap]
    refine ⟨rationalPrime, ?_⟩
    simpa [leftPrime, ProductBase, RingHom.algebraMap_toAlgebra] using
      (PrimeSpectrum.primeSpectrumProd_symm_inl rationalPrime).symm
  have hAll : ∀ p : PrimeSpectrum ProductBase,
      localRank ProductBase ℚ p ≤ 1 :=
    (Module.rankAtStalk_le_one_iff_surjective
      (R := ProductBase) (S := ℚ)).mpr
        (show Function.Surjective (algebraMap ProductBase ℚ) from
          (RingHom.fst ℚ ℚ).surjective)
  have hle : localRank ProductBase ℚ leftPrime ≤ 1 := hAll leftPrime
  omega

theorem right_not_mem_range_comap :
    rightPrime ∉ Set.range
      (PrimeSpectrum.comap (algebraMap ProductBase ℚ)) := by
  rintro ⟨p, hp⟩
  have hEq :
      (PrimeSpectrum.primeSpectrumProd ℚ ℚ).symm (Sum.inl p) =
        (PrimeSpectrum.primeSpectrumProd ℚ ℚ).symm
          (Sum.inr rationalPrime) := by
    calc
      (PrimeSpectrum.primeSpectrumProd ℚ ℚ).symm (Sum.inl p) =
          PrimeSpectrum.comap (RingHom.fst ℚ ℚ) p :=
        PrimeSpectrum.primeSpectrumProd_symm_inl p
      _ = rightPrime := by
        simpa [ProductBase, RingHom.algebraMap_toAlgebra] using hp
      _ = (PrimeSpectrum.primeSpectrumProd ℚ ℚ).symm
          (Sum.inr rationalPrime) := rfl
  have : Sum.inl p = Sum.inr rationalPrime :=
    (PrimeSpectrum.primeSpectrumProd ℚ ℚ).symm.injective hEq
  contradiction

theorem right_localRank :
    localRank ProductBase ℚ rightPrime = 0 := by
  rw [Module.rankAtStalk_eq_zero_iff_notMem_support]
  intro hSupport
  have hpos : 0 < localRank ProductBase ℚ rightPrime :=
    (Module.rankAtStalk_pos_iff_mem_support rightPrime).mpr hSupport
  rw [PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap] at hpos
  exact right_not_mem_range_comap hpos

noncomputable def varyingResidual :
    RankVaryingResidualAt ProductBase ℚ where
  left := leftPrime
  right := rightPrime
  rank_ne := by rw [left_localRank, right_localRank]; omega

theorem varying_branch_reachable :
    Nonempty (RankVaryingResidualAt ProductBase ℚ) ∧
      ¬ ConstantRankBoundedFaceAt ProductBase ℚ := by
  refine ⟨⟨varyingResidual⟩, ?_⟩
  intro face
  exact varyingResidual.rank_ne
    (face.rank_eq varyingResidual.left varyingResidual.right)

theorem witnesses_different_components :
    varyingResidual.right ∉ connectedComponent varyingResidual.left :=
  varyingResidual.right_not_mem_connectedComponent

theorem no_finrank_globalization :
    ¬ ∀ p : PrimeSpectrum ProductBase,
      localRank ProductBase ℚ p = Module.finrank ProductBase ℚ :=
  varyingResidual.no_finrank_globalization

end ProductFactorDiagnostic

#print axioms SourceGeneratedScalarRankComponentDisposition.localRank_isLocallyConstant
#print axioms SourceGeneratedScalarRankComponentDisposition.exact_outcome
#print axioms SourceGeneratedScalarRankComponentDisposition.generate
#print axioms ProductFactorDiagnostic.varyingResidual
#print axioms ProductFactorDiagnostic.varying_branch_reachable
#print axioms ProductFactorDiagnostic.no_finrank_globalization

end
end SourceGeneratedScalarRankComponentDispositionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
