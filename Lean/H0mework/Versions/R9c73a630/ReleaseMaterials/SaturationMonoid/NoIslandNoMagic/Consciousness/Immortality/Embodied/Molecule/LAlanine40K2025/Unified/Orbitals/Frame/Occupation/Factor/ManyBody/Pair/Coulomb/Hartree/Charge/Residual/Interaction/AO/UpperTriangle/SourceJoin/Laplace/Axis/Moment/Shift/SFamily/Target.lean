import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def hasSSource (address : Fin 4851) : Prop :=
  SourceJoin.targetLeft address.val ∈ Axis.sourceSBases ∨
    SourceJoin.targetRight address.val ∈ Axis.sourceSBases

def sourceSAddresses : Finset (Fin 4851) :=
  Finset.univ.filter (fun address =>
    (Axis.sourceSChecker (SourceJoin.targetLeft address.val) ||
      Axis.sourceSChecker (SourceJoin.targetRight address.val)) = true)

theorem source_s_addresses_exact (address : Fin 4851) :
    address ∈ sourceSAddresses ↔ hasSSource address := by
  simp [sourceSAddresses,hasSSource,Axis.sourceSBases,Bool.or_eq_true]

def analyticAtAddress (address : Fin 4851) (i j : Basis) : ℝ := by
  classical
  exact if hsRight : SourceJoin.targetRight address.val ∈ Axis.sourceSBases then
      sourceSRightQuartet (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j
    else if hsLeft : SourceJoin.targetLeft address.val ∈ Axis.sourceSBases then
      sourceSRightQuartet (SourceJoin.targetRight address.val)
        (SourceJoin.targetLeft address.val) i j
    else Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft address.val)
      (SourceJoin.targetRight address.val) i j

theorem analytic_at_address_exact (address : Fin 4851) (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft address.val)
      (SourceJoin.targetRight address.val) i j =
        analyticAtAddress address i j := by
  unfold analyticAtAddress
  classical
  by_cases hsRight : SourceJoin.targetRight address.val ∈ Axis.sourceSBases
  · simp only [dif_pos hsRight]
    rw [← Laplace.electron_repulsion_heat_finite]
    exact source_s_right_bases_quartet _ _ i j hsRight hi hj
  · simp only [dif_neg hsRight]
    by_cases hsLeft : SourceJoin.targetLeft address.val ∈ Axis.sourceSBases
    · simp only [dif_pos hsLeft]
      rw [← Laplace.electron_repulsion_heat_finite,
        electronRepulsion_first_swap]
      exact source_s_right_bases_quartet _ _ i j hsLeft hi hj
    · simp only [dif_neg hsLeft]

def targetSHeatJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      analyticAtAddress address i j

theorem target_s_source_J (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    SourceJoin.material.targetJ i j = targetSHeatJ i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetSHeatJ
  apply Finset.sum_congr rfl
  intro address _
  rw [analytic_at_address_exact address i j hi hj]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
