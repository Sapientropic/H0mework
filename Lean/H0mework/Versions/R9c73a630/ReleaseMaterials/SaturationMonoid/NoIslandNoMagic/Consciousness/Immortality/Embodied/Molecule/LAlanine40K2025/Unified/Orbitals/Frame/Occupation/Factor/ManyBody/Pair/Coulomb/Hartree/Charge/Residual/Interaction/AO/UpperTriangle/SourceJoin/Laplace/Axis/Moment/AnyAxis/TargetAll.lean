import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def pAxisAtAddress (address : Fin 4851) : Option (Fin 3) :=
  if address = pAddress 0 then some 0
  else if address = pAddress 1 then some 1
  else if address = pAddress 2 then some 2
  else none

def pAddresses : Finset (Fin 4851) := Finset.univ.image pAddress

theorem p_addresses_card : pAddresses.card = 3 := by decide +kernel

theorem p_axis_at_address_complete (axis : Fin 3) :
    pAxisAtAddress (pAddress axis) = some axis := by
  fin_cases axis <;> decide

theorem p_axis_at_address_sound (address : Fin 4851) (axis : Fin 3)
    (identified : pAxisAtAddress address = some axis) :
    address = pAddress axis := by
  unfold pAxisAtAddress at identified
  by_cases h0 : address = pAddress 0
  · simp only [if_pos h0] at identified
    have haxis : axis = 0 := by cases identified; rfl
    simpa [haxis] using h0
  · simp only [if_neg h0] at identified
    by_cases h1 : address = pAddress 1
    · simp only [if_pos h1] at identified
      have haxis : axis = 1 := by cases identified; rfl
      simpa [haxis] using h1
    · simp only [if_neg h1] at identified
      by_cases h2 : address = pAddress 2
      · simp only [if_pos h2] at identified
        have haxis : axis = 2 := by cases identified; rfl
        simpa [haxis] using h2
      · simp only [if_neg h2] at identified
        cases identified

theorem heat_at_p_axis_address (axis : Fin 3) (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft (pAddress axis).val)
      (SourceJoin.targetRight (pAddress axis).val) i j =
        sourcePAxisSQuartet axis i j := by
  rw [(p_axis_target_address axis).1,(p_axis_target_address axis).2]
  rw [← Laplace.electron_repulsion_heat_finite,
    electronRepulsion_first_swap,
    source_p_axis_s_bases_quartet axis i j hi hj]

def targetThreePHeatJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      match pAxisAtAddress address with
      | some axis => sourcePAxisSQuartet axis i j
      | none => Laplace.pairInteractionHeatFinite
          (SourceJoin.targetLeft address.val)
          (SourceJoin.targetRight address.val) i j

theorem target_three_p_J (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    SourceJoin.material.targetJ i j = targetThreePHeatJ i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetThreePHeatJ
  apply Finset.sum_congr rfl
  intro address _
  cases identified : pAxisAtAddress address with
  | none => rfl
  | some axis =>
      have h := p_axis_at_address_sound address axis identified
      subst address
      rw [heat_at_p_axis_address axis i j hi hj]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
