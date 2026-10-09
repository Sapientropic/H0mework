import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Spatial

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
open MeasureTheory
noncomputable section

def axisLowIntegrand (power : ℕ) (p q A B t : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.1-A)^power * Axis.coupledAxis p q A B t z.1 z.2

def axisLowClosed (power : ℕ) (p q A B t : ℝ) : ℝ :=
  if power = 0 then Moment.sAxisClosed p q A B t
  else if power = 1 then Moment.firstAxisClosed p q A B t
  else Moment.Second.secondAxisClosed p q A B t

theorem axis_low_integral (power : ℕ) (p q A B t : ℝ)
    (hpower : power < 3) (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, axisLowIntegrand power p q A B t z) =
      axisLowClosed power p q A B t := by
  interval_cases power
  · simp only [axisLowIntegrand,axisLowClosed,pow_zero,one_mul]
    exact Axis.coupled_axis_pair_closed p q A B t hp hq ht
  · simp only [axisLowIntegrand,axisLowClosed,pow_one,
      Nat.one_ne_zero]
    exact Moment.coupled_axis_first_pair p q A B t hp hq ht
  · simp only [axisLowIntegrand,axisLowClosed,Nat.reduceEqDiff]
    exact Moment.Second.coupled_axis_second_pair p q A B t hp hq ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
