import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarConstantRankDeterminantKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarRankComponentDispositionKernel

/-!
# Scalar projective determinant disposition

Every finite projective bounded face is settled without a free or determinant
premise.  Its actual stalk-rank profile either varies, yielding explicit
prime coordinates, or is constant, yielding the generated top exterior
Picard line and its exact trivial/nontrivial disposition.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarProjectiveDeterminantDisposition

open SourceGeneratedScalarRankComponentDisposition
open SourceGeneratedScalarConstantRankDeterminant

noncomputable section

universe r m

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]

inductive Disposition : Type (max r m + 1) where
  | constant
      (readout : SourceGeneratedScalarConstantRankDeterminant.Readout
        (R := R) (M := M))
      (picard : readout.PicardDisposition)
  | rankVarying
      (residual : RankVaryingResidualAt R M)

/-- A known constant-rank law enters the generated Picard disposition
without any free or determinant evidence. -/
noncomputable def constantDisposition
    (finite : Module.Finite R M) (projective : Module.Projective R M)
    (rank : ℕ)
    (constantRank : Module.rankAtStalk M =
      fun _ : PrimeSpectrum R => rank) : Disposition (R := R) (M := M) :=
  let readout : SourceGeneratedScalarConstantRankDeterminant.Readout
      (R := R) (M := M) :=
    { finite := finite
      projective := projective
      rank := rank
      constantRank := constantRank }
  .constant readout readout.settle

/-- Materialize a pairwise constant rank face.  Over a nontrivial ring the
degree is read from an actual prime and is independent of that anchor.  Over
the zero ring there is no prime, and the empty rank profile is represented in
degree zero. -/
noncomputable def ofConstantFace
  (finite : Module.Finite R M) (projective : Module.Projective R M)
    (face : ConstantRankBoundedFaceAt R M) :
    Disposition (R := R) (M := M) := by
  classical
  by_cases nontrivial : Nontrivial R
  · letI : Nontrivial R := nontrivial
    let anchor : PrimeSpectrum R :=
      Classical.choice (PrimeSpectrum.nonempty_iff_nontrivial.mpr nontrivial)
    let rank := localRank R M anchor
    have constantRank : Module.rankAtStalk M =
        fun _ : PrimeSpectrum R => rank := by
      funext prime
      exact face.rank_eq prime anchor
    exact constantDisposition finite projective rank constantRank
  · let subsingleton : Subsingleton R :=
      not_nontrivial_iff_subsingleton.mp nontrivial
    letI : Subsingleton R := subsingleton
    have noPrime : ¬ Nonempty (PrimeSpectrum R) := by
      intro prime
      exact not_nontrivial R
        (PrimeSpectrum.nonempty_iff_nontrivial.mp prime)
    have constantRank : Module.rankAtStalk M =
        fun _ : PrimeSpectrum R => 0 := by
      funext prime
      exact (noPrime ⟨prime⟩).elim
    exact constantDisposition finite projective 0 constantRank

/-- Complete automatic finite-projective determinant disposition. -/
noncomputable def settle
    (finite : Module.Finite R M) (projective : Module.Projective R M) :
    Disposition (R := R) (M := M) := by
  letI : Module.Finite R M := finite
  letI : Module.Projective R M := projective
  exact match (SourceGeneratedScalarRankComponentDisposition.generate
      (R := R) (M := M)).outcome with
    | .constant face => ofConstantFace finite projective face
    | .varying residual => .rankVarying residual

theorem settle_total
    (finite : Module.Finite R M) (projective : Module.Projective R M) :
    Nonempty (Disposition (R := R) (M := M)) :=
  ⟨settle finite projective⟩

theorem settle_constant_of_constantRank
    (finite : Module.Finite R M) (projective : Module.Projective R M)
    (rank : ℕ)
    (constantRank : Module.rankAtStalk M =
      fun _ : PrimeSpectrum R => rank) :
    ∃ (readout : SourceGeneratedScalarConstantRankDeterminant.Readout
        (R := R) (M := M))
      (picard : readout.PicardDisposition),
      settle finite projective = .constant readout picard := by
  generalize outcomeEquality : settle finite projective = outcome
  cases outcome with
  | constant readout picard => exact ⟨readout, picard, rfl⟩
  | rankVarying residual =>
      exfalso
      apply residual.no_global_rank rank
      intro prime
      exact congrFun constantRank prime

theorem settle_rankVarying_of_residual
    (finite : Module.Finite R M) (projective : Module.Projective R M)
    (actual : RankVaryingResidualAt R M) :
    ∃ residual : RankVaryingResidualAt R M,
      settle finite projective = .rankVarying residual := by
  generalize outcomeEquality : settle finite projective = outcome
  cases outcome with
  | constant readout picard =>
      exfalso
      have leftRank := congrFun readout.constantRank actual.left
      have rightRank := congrFun readout.constantRank actual.right
      exact actual.rank_ne (leftRank.trans rightRank.symm)
  | rankVarying residual => exact ⟨residual, rfl⟩

end
end SourceGeneratedScalarProjectiveDeterminantDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
