import Mathlib.Analysis.InnerProductSpace.l2Space
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PureCayley
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.GapGram

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open Complex BurnolPhysicalState OriginalRieszSourceGreen
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace lp

open private cayley_power_gap_even cayley_even adjoint_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private source_left_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private even_source_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLiteralEdgeMeanSourcePrice.Source

local notation "q" => burnolUnscaledCommonGapRadius
local notation "G" => locallyConstantFace q
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "T" => sourceCayley
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The position restriction of the original even ambient field. -/
def positionSpace : ClosedSubmodule ℂ BurnolL2 :=
  ⟨G ⊓ evenL2ClosedFace.toSubmodule, (locallyConstantFace_isClosed q).inter evenL2ClosedFace.isClosed⟩

abbrev PositionField := positionSpace.toSubmodule
local notation "S" => PositionField

local instance : CompleteSpace S :=
  IsComplete.completeSpace_coe positionSpace.isClosed.isComplete

private theorem gapState_ne_zero (c : BurnolCompletedMellinCoordinate) : gapState c ≠ 0 := by
  intro gone
  have mean := gapState_gapCoefficient c
  rw [gone, map_zero] at mean
  have edge := OriginalRieszSource.GapEuler.gapMean_primitive q (by norm_num [burnolUnscaledCommonGapRadius]) c
  change 0 = OriginalRieszSource.GapEuler.gapMean q c at mean
  rw [← mean, mul_zero] at edge
  exact (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num [burnolUnscaledCommonGapRadius]))))
    edge.symm

/-- The unit scale of the already generated gap-plus-tail vector. -/
def normalization (c : BurnolCompletedMellinCoordinate) : ℂ := (‖gapState (d c)‖ : ℂ)⁻¹

theorem normalization_ne_zero (c : BurnolCompletedMellinCoordinate) : normalization c ≠ 0 :=
  inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (gapState_ne_zero (d c))))

/-- The normalized existing even gap-plus-tail field. -/
def positionHead (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  normalization c • gapState (d c)

private theorem unit_norm (c : BurnolCompletedMellinCoordinate) : ‖positionHead c‖ = 1 := by
  rw [positionHead, norm_smul, normalization, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (gapState_ne_zero (d c)))]

private theorem unit_gap (c : BurnolCompletedMellinCoordinate) : positionHead c ∈ G := by
  apply (G).smul_mem
  exact mem_locallyConstantFace_iff_exists.mpr
    ⟨_, (gapState_restriction (d c)).symm⟩

private theorem unit_even (c : BurnolCompletedMellinCoordinate) : reflectL2 (positionHead c) = positionHead c := by
  rw [positionHead, map_smul, show reflectL2 (gapState (d c)) = gapState (d c) from burnolAmbientEvenPart_even _]

private theorem unit_read (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (even : reflectL2 v = v) :
    inner ℂ (positionHead c) v = normalization c * M (d c) v := by
  have realScale : (starRingEnd ℂ) (normalization c) = normalization c := by
    change star ((‖gapState (d c)‖ : ℂ)⁻¹) = _
    rw [star_inv₀]
    exact congrArg Inv.inv (Complex.conj_ofReal ‖gapState (d c)‖)
  rw [positionHead, inner_smul_left, realScale]
  unfold gapState
  rw [even_source_read _ _ even, ← burnolAmbientCompletedMellinRieszVector_eq_kernelFormula,
    burnolAmbientCompletedMellinRieszVector_readback]

private def orbit (c : BurnolCompletedMellinCoordinate) (n : Nat) : S :=
  let paid := cayley_power_gap_even c (positionHead c) (unit_gap c) (unit_even c) n
  ⟨((T c)^n) (positionHead c), paid.1, mem_evenL2ClosedFace_iff.mpr paid.2⟩

private theorem orbit_inner (c : BurnolCompletedMellinCoordinate) (v w : BurnolL2) (n : Nat) :
    inner ℂ (((T c)^n) v) (((T c)^n) w) = inner ℂ v w := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n previous => rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, sourceCayley_inner, previous]

private theorem orbit_norm (c : BurnolCompletedMellinCoordinate) (n : Nat) : ‖orbit c n‖ = 1 := by
  change ‖((T c)^n) (positionHead c)‖ = 1
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using unit_norm c
  | succ n previous => rw [pow_succ', mul_apply_eq_comp, sourceCayley_norm, previous]

private theorem orbit_inner_lt (c : BurnolCompletedMellinCoordinate) (i j : Nat) (before : i < j) :
    inner ℂ (orbit c i) (orbit c j) = 0 := by
  change inner ℂ (((T c)^i) (positionHead c)) (((T c)^j) (positionHead c)) = 0
  obtain ⟨k, hk⟩ : ∃ k : Nat, j = i + (k + 1) := ⟨j-i-1, by omega⟩
  rw [hk, pow_add, mul_apply_eq_comp, orbit_inner, unit_read c _
    ((cayley_power_gap_even c _ (unit_gap c) (unit_even c) (k+1)).2),
    pow_succ', mul_apply_eq_comp, actual_gap_cayley_conjugate_zero c _
      ((cayley_power_gap_even c _ (unit_gap c) (unit_even c) k).1), mul_zero]

private theorem orbit_orthonormal (c : BurnolCompletedMellinCoordinate) : Orthonormal ℂ (orbit c) :=
  ⟨orbit_norm c, fun {i j} different => by
    rcases lt_or_gt_of_ne different with ordered | ordered
    · exact orbit_inner_lt c i j ordered
    · exact inner_eq_zero_symm.mp (orbit_inner_lt c j i ordered)⟩

private theorem orbit_adjoint_read (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) (n : Nat) :
    inner ℂ (((T c)^n) (positionHead c)) v =
      normalization c * M (d c) ((((T c).adjoint)^n) v) := by
  induction n generalizing v with
  | zero => simpa only [pow_zero, one_apply_eq_self] using unit_read c v even
  | succ n previous =>
    rw [pow_succ' (T c), mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_right,
      previous _ (adjoint_even c v even), pow_succ, mul_apply_eq_comp]

private theorem orbit_complete (c : BurnolCompletedMellinCoordinate) :
    (Submodule.span ℂ (Set.range (orbit c)))ᗮ = ⊥ := by
  refine le_antisymm (fun v orthogonal => ?_) bot_le
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change (v : BurnolL2) = 0
  by_contra nonzero
  have even := mem_evenL2ClosedFace_iff.mp v.property.2
  obtain ⟨n, _, first, _, _⟩ :=
    actual_gap_cayley_first_escape c v v.property.1 even nonzero
  have vanish := (Submodule.mem_orthogonal _ _).mp orthogonal (orbit c n)
    (Submodule.subset_span ⟨n, rfl⟩)
  change inner ℂ (((T c)^n) (positionHead c)) (v : BurnolL2) = 0 at vanish
  rw [orbit_adjoint_read c _ even n] at vanish
  exact first ((mul_eq_zero.mp vanish).resolve_left (normalization_ne_zero c))

/-- The whole position field is the Hilbert sum of the actual Cayley orbit. -/
def basis (c : BurnolCompletedMellinCoordinate) : HilbertBasis Nat ℂ S :=
  HilbertBasis.mkOfOrthogonalEqBot (orbit_orthonormal c) (orbit_complete c)

private theorem basis_read (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    basis c n = orbit c n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (orbit_orthonormal c) (orbit_complete c)) n

/-- Each coordinate is the original ambient read after the full true adjoint word. -/
theorem actual_coefficient (c : BurnolCompletedMellinCoordinate) (v : S) (n : Nat) :
    (basis c).repr v n = normalization c * M (d c) ((((T c).adjoint)^n) (v : BurnolL2)) := by
  rw [HilbertBasis.repr_apply_apply, basis_read]
  exact orbit_adjoint_read c v (mem_evenL2ClosedFace_iff.mp v.property.2) n

/-- Synthesis restores the complete original field in the ambient norm. -/
theorem actual_synthesis (c : BurnolCompletedMellinCoordinate) (a : ℓ²(Nat, ℂ)) :
    HasSum (fun n => a n • ((T c)^n) (positionHead c)) ((basis c).repr.symm a : BurnolL2) := by
  have sum := ((basis c).hasSum_repr_symm a).mapL positionSpace.toSubmodule.subtypeL
  simp only [map_smul, Submodule.subtypeL_apply, basis_read] at sum
  exact sum

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
