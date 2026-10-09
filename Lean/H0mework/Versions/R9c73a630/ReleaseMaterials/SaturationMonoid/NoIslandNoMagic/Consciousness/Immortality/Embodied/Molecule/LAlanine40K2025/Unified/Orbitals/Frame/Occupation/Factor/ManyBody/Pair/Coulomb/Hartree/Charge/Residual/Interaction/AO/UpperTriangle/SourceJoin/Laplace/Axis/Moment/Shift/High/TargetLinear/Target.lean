import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def isLinearSTarget (i j : Basis) : Prop :=
  (i ∈ targetLinearBases ∧ j ∈ Axis.sourceSBases) ∨
    (j ∈ targetLinearBases ∧ i ∈ Axis.sourceSBases)

def targetLinearEntries : Finset (Basis × Basis) :=
  Finset.univ.filter (fun pair =>
    ((targetLinearChecker pair.1 && Axis.sourceSChecker pair.2) ||
      (targetLinearChecker pair.2 && Axis.sourceSChecker pair.1)) = true)

theorem target_linear_entries_exact (i j : Basis) :
    (i,j) ∈ targetLinearEntries ↔ isLinearSTarget i j := by
  simp [targetLinearEntries,isLinearSTarget,targetLinearBases,
    Axis.sourceSBases,Bool.and_eq_true,Bool.or_eq_true]

def analyticAtTarget (address : Fin 4851) (i j : Basis) : ℝ := by
  classical
  exact if h : i ∈ targetLinearBases ∧ j ∈ Axis.sourceSBases then
      sourceTargetLinearQuartet
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j
    else if h : j ∈ targetLinearBases ∧ i ∈ Axis.sourceSBases then
      sourceTargetLinearQuartet
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) j i
    else Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft address.val)
      (SourceJoin.targetRight address.val) i j

theorem analytic_at_target_exact (address : Fin 4851) (i j : Basis) :
    Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft address.val)
      (SourceJoin.targetRight address.val) i j =
        analyticAtTarget address i j := by
  classical
  unfold analyticAtTarget
  by_cases h1 : i ∈ targetLinearBases ∧ j ∈ Axis.sourceSBases
  · simp only [dif_pos h1]
    rw [← Laplace.electron_repulsion_heat_finite]
    exact source_target_linear_quartet _ _ i j h1.1 h1.2
  · simp only [dif_neg h1]
    by_cases h2 : j ∈ targetLinearBases ∧ i ∈ Axis.sourceSBases
    · simp only [dif_pos h2]
      rw [← Laplace.electron_repulsion_heat_finite,
        electronRepulsion_second_swap]
      exact source_target_linear_quartet _ _ j i h2.1 h2.2
    · simp only [dif_neg h2]

def targetLinearJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      analyticAtTarget address i j

theorem target_linear_J (i j : Basis) :
    SourceJoin.material.targetJ i j = targetLinearJ i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetLinearJ
  apply Finset.sum_congr rfl
  intro address _
  rw [analytic_at_target_exact address i j]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
