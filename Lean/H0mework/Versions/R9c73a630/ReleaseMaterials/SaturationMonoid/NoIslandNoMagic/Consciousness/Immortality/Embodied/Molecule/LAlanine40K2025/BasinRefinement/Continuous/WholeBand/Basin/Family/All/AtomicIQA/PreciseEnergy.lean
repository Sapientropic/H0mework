import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionZones.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PreciseRepulsion

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA.PreciseTarget
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource
open SourceCoulomb Set MeasureTheory Function
open scoped BigOperators
noncomputable section

def zoneDelta (z : Option (Fin 13)) (a : Fin 13) : ℝ :=
  Nuclear.PreciseTarget.zoneAttraction z a - Nuclear.zoneAttraction z a

def repulsionDelta (a b : Fin 13) : ℝ :=
  Nuclear.PreciseTarget.nuclearRepulsion a b - Nuclear.nuclearRepulsion a b

def selfEnergy (a : Fin 13) : ℝ :=
  AtomicIQA.selfEnergy a + zoneDelta (some a) a

def interaction (a b : Fin 13) : ℝ :=
  AtomicIQA.interaction a b + repulsionDelta a b +
    zoneDelta (some a) b + zoneDelta (some b) a

def classicalInteraction (a b : Fin 13) : ℝ :=
  AtomicIQA.classicalInteraction a b + repulsionDelta a b +
    zoneDelta (some a) b + zoneDelta (some b) a

def exchangeInteraction (a b : Fin 13) : ℝ :=
  AtomicIQA.exchangeInteraction a b

def residualEnergy : ℝ :=
  AtomicIQA.residualEnergy + ∑ a : Fin 13, zoneDelta none a

theorem self_energy_source (a : Fin 13) :
    selfEnergy a = OneBody.zoneKinetic (some a) +
      Nuclear.PreciseTarget.zoneAttraction (some a) a +
        cellEnergy (some a,some a) := by
  unfold selfEnergy AtomicIQA.selfEnergy zoneDelta
  ring

theorem interaction_source (a b : Fin 13) :
    interaction a b = Nuclear.PreciseTarget.nuclearRepulsion a b +
      Nuclear.PreciseTarget.zoneAttraction (some a) b +
      Nuclear.PreciseTarget.zoneAttraction (some b) a +
      cellEnergy (some a,some b) +
      cellEnergy (some b,some a) := by
  unfold interaction AtomicIQA.interaction zoneDelta repulsionDelta
  ring

theorem residual_energy_source :
    residualEnergy = OneBody.zoneKinetic none +
      ∑ a : Fin 13, Nuclear.PreciseTarget.zoneAttraction none a +
      cellEnergy (none,none) +
      ∑ a : Fin 13,
        (cellEnergy (none,some a) +
          cellEnergy (some a,none)) := by
  unfold residualEnergy AtomicIQA.residualEnergy zoneDelta
  rw [Finset.sum_sub_distrib]
  ring

theorem interaction_split (a b : Fin 13) :
    interaction a b = classicalInteraction a b + exchangeInteraction a b := by
  unfold interaction classicalInteraction exchangeInteraction
  rw [AtomicIQA.interaction_split a b]
  ring

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

private theorem zone_delta_split :
    (∑ z : Option (Fin 13), ∑ a : Fin 13, zoneDelta z a) =
      (∑ a : Fin 13, zoneDelta none a) +
        (∑ a : Fin 13, zoneDelta (some a) a) +
        ∑ p ∈ pairSet,
          (zoneDelta (some p.1) p.2 + zoneDelta (some p.2) p.1) := by
  rw [option_sum (fun z => ∑ a : Fin 13, zoneDelta z a)]
  rw [sum_diag_split (fun a b => zoneDelta (some a) b)]
  rw [← sum_lt_pair (fun p => zoneDelta (some p.1) p.2)]
  simp only [Prod.swap]
  ring

private theorem zone_delta_total :
    (∑ z : Option (Fin 13), ∑ a : Fin 13, zoneDelta z a) =
      (∑ z : Option (Fin 13), ∑ a : Fin 13,
        Nuclear.PreciseTarget.zoneAttraction z a) -
      (∑ z : Option (Fin 13), ∑ a : Fin 13,
        Nuclear.zoneAttraction z a) := by
  unfold zoneDelta
  simp only [Finset.sum_sub_distrib]

private theorem repulsion_delta_total :
    (∑ p ∈ pairSet, repulsionDelta p.1 p.2) =
      Nuclear.PreciseTarget.totalRepulsion - Nuclear.totalRepulsion := by
  unfold repulsionDelta Nuclear.PreciseTarget.totalRepulsion Nuclear.totalRepulsion pairSet
  rw [Finset.sum_sub_distrib]

theorem atomic_iqa_target_total :
    (∑ a : Fin 13, selfEnergy a) +
      (∑ p ∈ pairSet, interaction p.1 p.2) + residualEnergy =
      (∑ z : Option (Fin 13),
        (OneBody.zoneKinetic z +
          ∑ a : Fin 13, Nuclear.PreciseTarget.zoneAttraction z a)) +
      Nuclear.PreciseTarget.totalRepulsion + pairCoulombEnergy.re := by
  calc
    _ = ((∑ a : Fin 13, AtomicIQA.selfEnergy a) +
        (∑ p ∈ pairSet, AtomicIQA.interaction p.1 p.2) +
        AtomicIQA.residualEnergy) +
        (∑ z : Option (Fin 13), ∑ a : Fin 13, zoneDelta z a) +
        (∑ p ∈ pairSet, repulsionDelta p.1 p.2) := by
      rw [zone_delta_split]
      simp only [selfEnergy,interaction,residualEnergy,Finset.sum_add_distrib]
      ring
    _ = (∑ z : Option (Fin 13), Nuclear.zoneOneBody z) +
        Nuclear.totalRepulsion + pairCoulombEnergy.re +
        ((∑ z : Option (Fin 13), ∑ a : Fin 13,
          Nuclear.PreciseTarget.zoneAttraction z a) -
          (∑ z : Option (Fin 13), ∑ a : Fin 13,
            Nuclear.zoneAttraction z a)) +
        (Nuclear.PreciseTarget.totalRepulsion - Nuclear.totalRepulsion) := by
      rw [AtomicIQA.atomic_iqa_total,zone_delta_total,repulsion_delta_total]
    _ = _ := by
      simp only [Nuclear.zoneOneBody,Finset.sum_add_distrib]
      ring

theorem atomic_iqa_target_original_ao :
    (∑ a : Fin 13, selfEnergy a) +
      (∑ p ∈ pairSet, interaction p.1 p.2) + residualEnergy =
      (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j +
          UnifiedOrbitals.Attraction.Precise.aoIntegral i j)) +
      Nuclear.PreciseTarget.totalRepulsion + pairCoulombEnergy.re := by
  have ksum : (∑ z : Option (Fin 13), OneBody.zoneKinetic z) =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        UnifiedOrbitals.kinetic i j := by
    rw [OneBody.zone_kinetic_sum,OneBody.total_kinetic_original_ao]
  rw [atomic_iqa_target_total,Finset.sum_add_distrib,ksum,
    Nuclear.PreciseTarget.zone_total_same_actual,
    UnifiedOrbitals.Attraction.Precise.totalIntegral]
  have hsum :
      (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        UnifiedOrbitals.kinetic i j) +
      (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        UnifiedOrbitals.Attraction.Precise.aoIntegral i j) =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j +
          UnifiedOrbitals.Attraction.Precise.aoIntegral i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA.PreciseTarget
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
