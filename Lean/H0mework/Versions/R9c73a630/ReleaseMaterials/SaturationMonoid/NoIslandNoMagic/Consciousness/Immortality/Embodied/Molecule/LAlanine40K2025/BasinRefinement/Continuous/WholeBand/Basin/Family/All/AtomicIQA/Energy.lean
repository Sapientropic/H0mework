import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.ExchangeCells
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Assembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.Kinetic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
open LAlanine40K2025.UnifiedOrbitals LAlanine40K2025.UnifiedAction
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource
open SourceCoulomb Set MeasureTheory Function
open scoped BigOperators
noncomputable section

/-- IQA atom pairs: unordered unordered pairs encoded by the strict filter. -/
def pairSet : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun p : Fin 13 × Fin 13 => p.1 < p.2

/-- In-basin self energy: kinetic + own-nucleus attraction + own electron cell. -/
def selfEnergy (a : Fin 13) : ℝ :=
  OneBody.zoneKinetic (some a) + Nuclear.zoneAttraction (some a) a +
    cellEnergy (some a,some a)

/-- Atom-pair interaction energy: nuclear repulsion, cross attractions and both
    cross electron cells. -/
def interaction (a b : Fin 13) : ℝ :=
  Nuclear.nuclearRepulsion a b + Nuclear.zoneAttraction (some a) b +
    Nuclear.zoneAttraction (some b) a +
    cellEnergy (some a,some b) + cellEnergy (some b,some a)

/-- Classical (Hartree/direct) part of a pair interaction. -/
def classicalInteraction (a b : Fin 13) : ℝ :=
  Nuclear.nuclearRepulsion a b + Nuclear.zoneAttraction (some a) b +
    Nuclear.zoneAttraction (some b) a +
    directCell (some a,some b) + directCell (some b,some a)

/-- Exchange (Fermi-hole) part of a pair interaction. -/
def exchangeInteraction (a b : Fin 13) : ℝ :=
  -(exchangeCell (some a,some b) + exchangeCell (some b,some a))

/-- Residual energy attached to the remainder zone `none`. -/
def residualEnergy : ℝ :=
  OneBody.zoneKinetic none + ∑ a : Fin 13, Nuclear.zoneAttraction none a +
    cellEnergy (none,none) +
    ∑ a : Fin 13, (cellEnergy (none,some a) + cellEnergy (some a,none))

theorem interaction_split (a b : Fin 13) :
    interaction a b = classicalInteraction a b + exchangeInteraction a b := by
  unfold interaction classicalInteraction exchangeInteraction
  rw [cell_energy_direct_exchange (some a,some b),
    cell_energy_direct_exchange (some b,some a)]
  ring

private theorem nuclear_repulsion_symmetric (a b : Fin 13) :
    Nuclear.nuclearRepulsion a b = Nuclear.nuclearRepulsion b a := by
  unfold Nuclear.nuclearRepulsion
  rw [show Nuclear.nuclearCharge a * Nuclear.nuclearCharge b =
      Nuclear.nuclearCharge b * Nuclear.nuclearCharge a from mul_comm _ _]
  congr 1
  unfold SourceCoulomb.kernel SourceCoulomb.distance
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [show (Nuclear.nuclearPosition b - Nuclear.nuclearPosition a) k =
      -((Nuclear.nuclearPosition a - Nuclear.nuclearPosition b) k) from by
    rw [Pi.sub_apply,Pi.sub_apply,neg_sub]]
  rw [neg_sq]

theorem interaction_symmetric (a b : Fin 13) :
    interaction a b = interaction b a := by
  unfold interaction
  rw [nuclear_repulsion_symmetric a b,all_cell_energy_symmetric (some a) (some b),
    all_cell_energy_symmetric (some b) (some a)]
  ring

theorem exchange_interaction_nonpositive (a b : Fin 13) :
    exchangeInteraction a b ≤ 0 := by
  unfold exchangeInteraction
  exact neg_nonpos.mpr (add_nonneg (exchange_cell_nonnegative _)
    (exchange_cell_nonnegative _))

theorem exchange_interaction_bounded (a b : Fin 13) :
    -2 * exchangeInteraction a b ≤
      directCell (some a,some b) + directCell (some b,some a) := by
  unfold exchangeInteraction
  have h1 := exchange_cell_bounded (some a,some b)
  have h2 := exchange_cell_bounded (some b,some a)
  linarith

private theorem option_sum (f : Option (Fin 13) → ℝ) :
    ∑ i : Option (Fin 13), f i = f none + ∑ i : Fin 13, f (some i) := by
  rw [univ_option,Finset.sum_insertNone]

private theorem sum_diag_split (f : Fin 13 → Fin 13 → ℝ) :
    (∑ a : Fin 13, ∑ b : Fin 13, f a b) =
      ∑ a : Fin 13, f a a +
        ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2),
          f p.1 p.2 := by
  have key : (∑ p : Fin 13 × Fin 13, f p.1 p.2) =
      ∑ a : Fin 13, ∑ b : Fin 13, f a b := Fintype.sum_prod_type' fun a b => f a b
  rw [← key]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin 13 × Fin 13 => p.1 = p.2) (fun p => f p.1 p.2)]
  rw [show Finset.univ.filter (fun p : Fin 13 × Fin 13 => ¬p.1 = p.2) =
      Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2) from rfl]
  have hdiag : Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 = p.2) =
      (Finset.univ : Finset (Fin 13)).diag := by
    ext ⟨a,b⟩
    simp [Finset.mem_diag]
  rw [hdiag]
  rw [Finset.sum_diag]

/-- Splitting a symmetric sum over ordered off-diagonal pairs across the
    strict-triangle filter. -/
private theorem sum_lt_pair (f : Fin 13 × Fin 13 → ℝ) :
    ∑ p ∈ pairSet, (f p + f p.swap) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2), f p := by
  have hsplit : Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2) =
      pairSet ∪ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.2 < p.1) := by
    ext ⟨a,b⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
      pairSet]
    constructor
    · intro h
      rcases lt_or_lt_iff_ne.mpr h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
  have hdisj : Disjoint pairSet
      (Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.2 < p.1)) := by
    unfold pairSet
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  rw [hsplit,Finset.sum_union hdisj]
  have hswap : ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.2 < p.1),
        f p =
      ∑ p ∈ pairSet, f p.swap := by
    apply Finset.sum_bij (fun p _ => p.swap)
    · intro p hp
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hp
      simp only [pairSet,Finset.mem_filter,Finset.mem_univ,true_and]
      show p.2 < p.1
      exact hp
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro p hp
      refine ⟨p.swap,?_,by simp⟩
      simp only [pairSet,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
      show p.1 < p.2
      exact hp
    · intro p _
      rfl
  rw [hswap,← Finset.sum_add_distrib]

private theorem attraction_offdiag :
    ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2),
        Nuclear.zoneAttraction (some p.1) p.2 =
      ∑ p ∈ pairSet, (Nuclear.zoneAttraction (some p.1) p.2 +
        Nuclear.zoneAttraction (some p.2) p.1) :=
  (sum_lt_pair fun p => Nuclear.zoneAttraction (some p.1) p.2).symm

private theorem cell_offdiag :
    ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2),
        cellEnergy (some p.1,some p.2) =
      ∑ p ∈ pairSet, (cellEnergy (some p.1,some p.2) +
        cellEnergy (some p.2,some p.1)) :=
  (sum_lt_pair fun p => cellEnergy (some p.1,some p.2)).symm

/-- The IQA atom-resolved decomposition reproduces the zone one-body total plus
    nuclear repulsion plus the whole two-electron ledger. -/
theorem atomic_iqa_total :
    ∑ a : Fin 13, selfEnergy a +
      ∑ p ∈ pairSet, interaction p.1 p.2 + residualEnergy =
      ∑ z : Option (Fin 13), Nuclear.zoneOneBody z + Nuclear.totalRepulsion +
        pairCoulombEnergy.re := by
  classical
  have celltotal : ∑ ij : Option (Fin 13) × Option (Fin 13), cellEnergy ij =
      cellEnergy (none,none) +
        ∑ a : Fin 13, cellEnergy (none,some a) +
        ∑ a : Fin 13, cellEnergy (some a,none) +
        ∑ a : Fin 13, cellEnergy (some a,some a) +
        ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2),
          cellEnergy (some p.1,some p.2) := by
    calc ∑ ij : Option (Fin 13) × Option (Fin 13), cellEnergy ij
        = ∑ i : Option (Fin 13), ∑ j : Option (Fin 13),
            cellEnergy (i,j) :=
          Fintype.sum_prod_type' fun i j => cellEnergy (i,j)
      _ = (∑ j : Option (Fin 13), cellEnergy (none,j)) +
            ∑ i : Fin 13, ∑ j : Option (Fin 13),
              cellEnergy (some i,j) := option_sum _
      _ = (cellEnergy (none,none) +
            ∑ j : Fin 13, cellEnergy (none,some j)) +
            ∑ i : Fin 13, (cellEnergy (some i,none) +
              ∑ j : Fin 13, cellEnergy (some i,some j)) := by
          rw [option_sum fun j => cellEnergy (none,j)]
          rw [Finset.sum_congr rfl fun i _ =>
            option_sum fun j => cellEnergy (some i,j)]
      _ = cellEnergy (none,none) +
            ∑ a : Fin 13, cellEnergy (none,some a) +
            ∑ a : Fin 13, cellEnergy (some a,none) +
            ∑ a : Fin 13, cellEnergy (some a,some a) +
            ∑ p ∈ Finset.univ.filter
              (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2),
              cellEnergy (some p.1,some p.2) := by
          rw [Finset.sum_add_distrib]
          rw [sum_diag_split fun a b => cellEnergy (some a,some b)]
          ring
  rw [← all_energy_exact]
  rw [celltotal,cell_offdiag]
  -- one-body zone expansion
  have zoneExpand : ∑ z : Option (Fin 13),
        (OneBody.zoneKinetic z + ∑ a : Fin 13, Nuclear.zoneAttraction z a) =
      OneBody.zoneKinetic none +
        ∑ a : Fin 13, Nuclear.zoneAttraction none a +
        ∑ a : Fin 13, OneBody.zoneKinetic (some a) +
        ∑ a : Fin 13, ∑ b : Fin 13, Nuclear.zoneAttraction (some a) b := by
    rw [show (∑ z : Option (Fin 13),
        (OneBody.zoneKinetic z + ∑ a : Fin 13, Nuclear.zoneAttraction z a)) =
        ∑ z : Option (Fin 13), OneBody.zoneKinetic z +
          ∑ z : Option (Fin 13), ∑ a : Fin 13, Nuclear.zoneAttraction z a from
      Finset.sum_add_distrib]
    rw [option_sum OneBody.zoneKinetic,
      option_sum fun z => ∑ a : Fin 13, Nuclear.zoneAttraction z a]
    ring
  have attrDiag : ∑ a : Fin 13, ∑ b : Fin 13,
        Nuclear.zoneAttraction (some a) b =
      ∑ a : Fin 13, Nuclear.zoneAttraction (some a) a +
        ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 ≠ p.2),
          Nuclear.zoneAttraction (some p.1) p.2 := by
    exact sum_diag_split fun a b => Nuclear.zoneAttraction (some a) b
  simp only [Nuclear.zoneOneBody]
  rw [zoneExpand,attrDiag,attraction_offdiag]
  -- expand selfEnergy, interaction, residualEnergy
  unfold selfEnergy interaction residualEnergy pairSet
  rw [Finset.sum_add_distrib]
  rw [show ∑ a : Fin 13, (OneBody.zoneKinetic (some a) +
        Nuclear.zoneAttraction (some a) a) =
        ∑ a : Fin 13, OneBody.zoneKinetic (some a) +
        ∑ a : Fin 13, Nuclear.zoneAttraction (some a) a from
      Finset.sum_add_distrib]
  rw [show ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 < p.2),
        (Nuclear.nuclearRepulsion p.1 p.2 +
          Nuclear.zoneAttraction (some p.1) p.2 +
          Nuclear.zoneAttraction (some p.2) p.1 +
          cellEnergy (some p.1,some p.2) + cellEnergy (some p.2,some p.1)) =
        ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 < p.2),
          Nuclear.nuclearRepulsion p.1 p.2 +
        ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 < p.2),
          (Nuclear.zoneAttraction (some p.1) p.2 +
            Nuclear.zoneAttraction (some p.2) p.1) +
        ∑ p ∈ Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 < p.2),
          (cellEnergy (some p.1,some p.2) + cellEnergy (some p.2,some p.1))
      from by
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring]
  rw [show ∑ a : Fin 13, (cellEnergy (none,some a) +
        cellEnergy (some a,none)) =
        ∑ a : Fin 13, cellEnergy (none,some a) +
        ∑ a : Fin 13, cellEnergy (some a,none) from Finset.sum_add_distrib]
  unfold Nuclear.totalRepulsion
  ring

/-- The IQA decomposition reproduces the original AO one-body contraction plus
    nuclear repulsion plus the two-electron ledger. -/
theorem atomic_iqa_original_ao :
    ∑ a : Fin 13, selfEnergy a +
      ∑ p ∈ pairSet, interaction p.1 p.2 + residualEnergy =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j + Nuclear.aoAttraction i j) +
        Nuclear.totalRepulsion + pairCoulombEnergy.re := by
  rw [atomic_iqa_total,Nuclear.one_body_nuclear_total]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
