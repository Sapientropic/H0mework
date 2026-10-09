import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Coefficient
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Address
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.All
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.MatrixChecks
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Kinetic
open BasinRefinement SourceFiniteData SharedMatrixChecks
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

/-- Block decomposition of the 4851 ledger addresses: 99 blocks of 49. -/
def finBlockEquiv : Fin 99 × Fin 49 ≃ Fin 4851 :=
  finProdFinEquiv.trans (finCongr (by decide))

/-- The certified density coefficient times the recorded kinetic cell. -/
def recordedTermFin (a : Fin 4851) : ℚ :=
  sourceCoefficientAt a * (((targetAORow a.val)[5]! : ℤ) : ℚ) / 10^12

/-- Per-block recorded sum; small enough for kernel evaluation. -/
def recordedKineticChunk (b : Fin 99) : ℚ :=
  ((List.finRange 49).map fun i => recordedTermFin (finBlockEquiv (b,i))).sum

/-- The recorded kinetic contraction over all 4851 ledger rows. -/
def recordedKineticSum : ℚ :=
  ((List.finRange 99).map recordedKineticChunk).sum

/-- Absolute density weight per address. -/
def weightTermFin (a : Fin 4851) : ℚ := |sourceCoefficientAt a|

/-- Total absolute density weight over all 4851 ledger rows. -/
def kineticRowWeight : ℚ := ∑ a : Fin 4851, weightTermFin a

/-- Bound per ledger address from the integer density bounds. -/
def kineticWeightBoundInt (a : Fin 4851) : ℕ :=
  densityMatrixIntegerBound (targetLeft a.val) (targetRight a.val) +
    if targetLeft a.val = targetRight a.val then 0 else
      densityMatrixIntegerBound (targetRight a.val) (targetLeft a.val)

/-- Per-block integer weight bound; small enough for kernel evaluation. -/
def weightBoundChunk (b : Fin 99) : ℕ :=
  ((List.finRange 49).map fun i => kineticWeightBoundInt (finBlockEquiv (b,i))).sum

/-- Total integer weight bound over all 4851 ledger rows. -/
def kineticWeightBoundTotal : ℕ :=
  ((List.finRange 99).map weightBoundChunk).sum

/-- Finset sums over `Fin n` evaluate as `finRange` list folds. -/
private theorem fin_sum_eq_finRange {α : Type*} [AddCommMonoid α] {n : ℕ} (f : Fin n → α) :
    (∑ i : Fin n, f i) = ((List.finRange n).map f).sum := by
  simp only [Finset.sum]
  show ((Finset.univ.val.map f).sum : α) = _
  change (((List.finRange n : Multiset (Fin n))).map f).sum = _
  rw [Multiset.map_coe, Multiset.sum_coe]

/-- A chunked list sum over the block decomposition agrees with the finset
    sum over all addresses. -/
private theorem chunked_sum_eq {α : Type*} [AddCommMonoid α] (f : Fin 4851 → α)
    (chunk : Fin 99 → α)
    (h : ∀ b : Fin 99, chunk b =
      ((List.finRange 49).map fun i => f (finBlockEquiv (b,i))).sum) :
    ((List.finRange 99).map chunk).sum = ∑ a : Fin 4851, f a := by
  calc ((List.finRange 99).map chunk).sum
      = ∑ b : Fin 99, chunk b := (fin_sum_eq_finRange _).symm
    _ = ∑ b : Fin 99, ∑ i : Fin 49, f (finBlockEquiv (b,i)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [h b, ← fin_sum_eq_finRange]
    _ = ∑ p : Fin 99 × Fin 49, f (finBlockEquiv p) := (Fintype.sum_prod_type (fun p => f (finBlockEquiv p))).symm
    _ = ∑ a : Fin 4851, f a := finBlockEquiv.sum_comp _

/-- The chunked recorded sum agrees with the finset sum over all addresses. -/
theorem recordedKineticSum_eq :
    recordedKineticSum = ∑ a : Fin 4851, recordedTermFin a :=
  chunked_sum_eq _ _ (fun _ => rfl)

/-- The chunked integer weight bound agrees with the finset total. -/
theorem kineticWeightBoundTotal_eq :
    (kineticWeightBoundTotal : ℕ) = ∑ a : Fin 4851, kineticWeightBoundInt a :=
  chunked_sum_eq _ _ (fun _ => rfl)

/-- Per-address the absolute source coefficient is covered by the generated
    integer bounds. -/
theorem kinetic_weight_cell_bound (a : Fin 4851) :
    weightTermFin a ≤ (kineticWeightBoundInt a : ℚ) / 10^12 := by
  have env (i j : Basis) :
      |densityMatrix i j| ≤ (densityMatrixIntegerBound i j : ℚ) / 10^12 := by
    rw [← densityMatrixBound_integer]
    exact original_matrix_envelope i j
  unfold weightTermFin sourceCoefficientAt kineticWeightBoundInt
  by_cases h : targetLeft a.val = targetRight a.val
  · rw [if_pos h, if_pos h]
    simpa only [add_zero] using env (targetLeft a.val) (targetRight a.val)
  · rw [if_neg h, if_neg h]
    calc |densityMatrix (targetLeft a.val) (targetRight a.val) +
            densityMatrix (targetRight a.val) (targetLeft a.val)|
        ≤ |densityMatrix (targetLeft a.val) (targetRight a.val)| +
            |densityMatrix (targetRight a.val) (targetLeft a.val)| := abs_add_le _ _
      _ ≤ (densityMatrixIntegerBound (targetLeft a.val) (targetRight a.val) : ℚ) / 10^12 +
            (densityMatrixIntegerBound (targetRight a.val) (targetLeft a.val) : ℚ) / 10^12 :=
          add_le_add (env _ _) (env _ _)
      _ = _ := by rw [Nat.cast_add]; ring

end
end LAlanine40K2025.UnifiedOrbitals.Kinetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
