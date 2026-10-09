import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def lowAddress (slot : Fin 11) : Fin 4851 := ⟨196+slot.val, by omega⟩

theorem low_target_address :
    ∀ slot : Fin 11,
      SourceJoin.targetLeft (lowAddress slot).val = (2 : Basis) ∧
      SourceJoin.targetRight (lowAddress slot).val = lowBasis slot := by
  decide +kernel

def lowAddresses : Finset (Fin 4851) := Finset.univ.image lowAddress

theorem low_addresses_card : lowAddresses.card = 11 := by decide +kernel

def lowAtAddress (address : Fin 4851) : Option (Fin 11) :=
  if h : 196 ≤ address.val ∧ address.val < 207 then
    some ⟨address.val-196, by omega⟩
  else none

theorem low_at_address_complete (slot : Fin 11) :
    lowAtAddress (lowAddress slot) = some slot := by
  unfold lowAtAddress
  have h : 196 ≤ (lowAddress slot).val ∧ (lowAddress slot).val < 207 := by
    dsimp [lowAddress]
    omega
  simp only [dif_pos h]
  congr 1
  apply Fin.ext
  dsimp [lowAddress]
  omega

theorem low_at_address_sound (address : Fin 4851) (slot : Fin 11)
    (identified : lowAtAddress address = some slot) :
    address = lowAddress slot := by
  unfold lowAtAddress at identified
  by_cases h : 196 ≤ address.val ∧ address.val < 207
  · simp only [dif_pos h] at identified
    have hslot := Option.some.inj identified
    apply Fin.ext
    have hval := congrArg Fin.val hslot
    dsimp [lowAddress] at hval ⊢
    omega
  · simp only [dif_neg h] at identified
    cases identified

theorem heat_at_low_address (slot : Fin 11) (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft (lowAddress slot).val)
      (SourceJoin.targetRight (lowAddress slot).val) i j =
        sourceLowQuartet slot i j := by
  rw [(low_target_address slot).1,(low_target_address slot).2]
  rw [← Laplace.electron_repulsion_heat_finite,
    electronRepulsion_first_swap,
    source_low_s_bases_quartet slot i j hi hj]

def targetLowHeatJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      match lowAtAddress address with
      | some slot => sourceLowQuartet slot i j
      | none => Laplace.pairInteractionHeatFinite
          (SourceJoin.targetLeft address.val)
          (SourceJoin.targetRight address.val) i j

theorem target_low_J (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    SourceJoin.material.targetJ i j = targetLowHeatJ i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetLowHeatJ
  apply Finset.sum_congr rfl
  intro address _
  cases identified : lowAtAddress address with
  | none => rfl
  | some slot =>
      have h := low_at_address_sound address slot identified
      subst address
      rw [heat_at_low_address slot i j hi hj]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
