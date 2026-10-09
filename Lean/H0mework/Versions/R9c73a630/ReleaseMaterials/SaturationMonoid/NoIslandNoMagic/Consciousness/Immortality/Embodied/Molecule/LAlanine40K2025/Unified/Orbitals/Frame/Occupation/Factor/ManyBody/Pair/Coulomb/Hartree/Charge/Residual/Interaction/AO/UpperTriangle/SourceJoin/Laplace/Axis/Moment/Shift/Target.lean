import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def shiftBasis (slot : Fin 96) : Basis := ⟨2+slot.val, by omega⟩
def shiftAddress (slot : Fin 96) : Fin 4851 := ⟨195+slot.val, by omega⟩

theorem shift_target_address :
    ∀ slot : Fin 96,
      SourceJoin.targetLeft (shiftAddress slot).val = (2 : Basis) ∧
      SourceJoin.targetRight (shiftAddress slot).val = shiftBasis slot := by
  decide +kernel

def shiftAddresses : Finset (Fin 4851) := Finset.univ.image shiftAddress

theorem shift_addresses_card : shiftAddresses.card = 96 := by decide +kernel

def shiftAtAddress (address : Fin 4851) : Option (Fin 96) :=
  if h : 195 ≤ address.val ∧ address.val < 291 then
    some ⟨address.val-195, by omega⟩
  else none

theorem shift_at_address_complete (slot : Fin 96) :
    shiftAtAddress (shiftAddress slot) = some slot := by
  unfold shiftAtAddress
  have h : 195 ≤ (shiftAddress slot).val ∧ (shiftAddress slot).val < 291 := by
    dsimp [shiftAddress]
    omega
  simp only [dif_pos h]
  congr 1
  apply Fin.ext
  dsimp [shiftAddress]
  omega

theorem shift_at_address_sound (address : Fin 4851) (slot : Fin 96)
    (identified : shiftAtAddress address = some slot) :
    address = shiftAddress slot := by
  unfold shiftAtAddress at identified
  by_cases h : 195 ≤ address.val ∧ address.val < 291
  · simp only [dif_pos h] at identified
    have hslot := Option.some.inj identified
    apply Fin.ext
    have hval := congrArg Fin.val hslot
    dsimp [shiftAddress] at hval ⊢
    omega
  · simp only [dif_neg h] at identified
    cases identified

theorem heat_at_shift_address (slot : Fin 96) (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft (shiftAddress slot).val)
      (SourceJoin.targetRight (shiftAddress slot).val) i j =
        sourceShiftQuartet (shiftBasis slot) i j := by
  rw [(shift_target_address slot).1,(shift_target_address slot).2]
  rw [← Laplace.electron_repulsion_heat_finite,
    electronRepulsion_first_swap,
    source_shift_s_bases_quartet (shiftBasis slot) i j hi hj]

def targetShiftHeatJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      match shiftAtAddress address with
      | some slot => sourceShiftQuartet (shiftBasis slot) i j
      | none => Laplace.pairInteractionHeatFinite
          (SourceJoin.targetLeft address.val)
          (SourceJoin.targetRight address.val) i j

theorem target_shift_J (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    SourceJoin.material.targetJ i j = targetShiftHeatJ i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetShiftHeatJ
  apply Finset.sum_congr rfl
  intro address _
  cases identified : shiftAtAddress address with
  | none => rfl
  | some slot =>
      have h := shift_at_address_sound address slot identified
      subst address
      rw [heat_at_shift_address slot i j hi hj]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
