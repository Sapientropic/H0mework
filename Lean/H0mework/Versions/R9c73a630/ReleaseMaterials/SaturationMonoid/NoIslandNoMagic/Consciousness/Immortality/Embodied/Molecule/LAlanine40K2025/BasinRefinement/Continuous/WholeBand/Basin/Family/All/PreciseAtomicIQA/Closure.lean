import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.PreciseEnergy

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open SourceFiniteData
open scoped BigOperators
noncomputable section

structure Material where
  parent : PreciseAttractionZones.Material
  selfEnergy : Fin 13 → ℝ
  interaction : Fin 13 → Fin 13 → ℝ
  residualEnergy : ℝ
  nuclearRepulsion : Fin 13 → Fin 13 → ℝ

def material : Material where
  parent := PreciseAttractionZones.material
  selfEnergy := AtomicIQA.PreciseTarget.selfEnergy
  interaction := AtomicIQA.PreciseTarget.interaction
  residualEnergy := AtomicIQA.PreciseTarget.residualEnergy
  nuclearRepulsion := Nuclear.PreciseTarget.nuclearRepulsion

theorem parent_same_source : material.parent = PreciseAttractionZones.material := rfl
theorem self_same_source (a : Fin 13) :
    material.selfEnergy a = AtomicIQA.PreciseTarget.selfEnergy a := rfl
theorem pair_same_source (a b : Fin 13) :
    material.interaction a b = AtomicIQA.PreciseTarget.interaction a b := rfl
theorem residual_same_source :
    material.residualEnergy = AtomicIQA.PreciseTarget.residualEnergy := rfl
theorem repulsion_same_source (a b : Fin 13) :
    material.nuclearRepulsion a b = Nuclear.PreciseTarget.nuclearRepulsion a b := rfl

theorem total_original_ao :
    (∑ a : Fin 13, material.selfEnergy a) +
      (∑ p ∈ AtomicIQA.pairSet, material.interaction p.1 p.2) +
      material.residualEnergy =
      (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j +
          UnifiedOrbitals.Attraction.Precise.aoIntegral i j)) +
      (∑ p ∈ AtomicIQA.pairSet, material.nuclearRepulsion p.1 p.2) +
      pairCoulombEnergy.re := by
  exact AtomicIQA.PreciseTarget.atomic_iqa_target_original_ao

theorem total_independent_nuclear_ledger :
    |((∑ a : Fin 13, material.selfEnergy a) +
        (∑ p ∈ AtomicIQA.pairSet, material.interaction p.1 p.2) +
        material.residualEnergy) -
      ((∑ z : Option (Fin 13), OneBody.zoneKinetic z) +
        material.parent.parent.independentWeighted +
        Nuclear.PreciseTarget.totalRepulsion + pairCoulombEnergy.re)| ≤
      (1/10^9 : ℝ) := by
  have h := UnifiedOrbitals.Attraction.Precise.complete_attraction_within_independent
  change |UnifiedOrbitals.Attraction.Precise.totalIntegral -
    UnifiedOrbitals.Attraction.Precise.independentElectronNuclear| ≤ _ at h
  convert h using 1
  rw [show (∑ a : Fin 13, material.selfEnergy a) +
      (∑ p ∈ AtomicIQA.pairSet, material.interaction p.1 p.2) +
      material.residualEnergy =
      (∑ z : Option (Fin 13), (OneBody.zoneKinetic z +
        ∑ a : Fin 13, Nuclear.PreciseTarget.zoneAttraction z a)) +
      Nuclear.PreciseTarget.totalRepulsion + pairCoulombEnergy.re from
        AtomicIQA.PreciseTarget.atomic_iqa_target_total]
  rw [Finset.sum_add_distrib,Nuclear.PreciseTarget.zone_total_same_actual]
  rw [show material.parent.parent.independentWeighted =
    UnifiedOrbitals.Attraction.Precise.independentElectronNuclear from rfl]
  congr 1
  ring

structure Closure : Prop where
  parent : PreciseAttractionZones.Closure
  parentIdentity : type_of% parent_same_source
  selfIdentity : type_of% self_same_source
  pairIdentity : type_of% pair_same_source
  residualIdentity : type_of% residual_same_source
  repulsionIdentity : type_of% repulsion_same_source
  targetCentre : type_of% Nuclear.PreciseTarget.centre_same_target
  totalAO : type_of% total_original_ao
  independent : type_of% total_independent_nuclear_ledger

theorem sourceGeneratedClosure : Closure :=
  ⟨PreciseAttractionZones.sourceGeneratedClosure,parent_same_source,
    self_same_source,pair_same_source,residual_same_source,repulsion_same_source,
    Nuclear.PreciseTarget.centre_same_target,total_original_ao,
    total_independent_nuclear_ledger⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
