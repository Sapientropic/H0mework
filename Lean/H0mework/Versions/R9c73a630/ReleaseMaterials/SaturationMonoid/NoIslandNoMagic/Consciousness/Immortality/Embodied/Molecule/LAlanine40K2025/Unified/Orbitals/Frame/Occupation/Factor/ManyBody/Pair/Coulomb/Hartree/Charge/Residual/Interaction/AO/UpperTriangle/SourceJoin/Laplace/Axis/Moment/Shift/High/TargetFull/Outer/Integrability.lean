import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Primitive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Integrability

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory Set
noncomputable section

theorem source_outer_integrable
    (left right nextLeft nextRight : Term)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hnextLeftDegree : Shift.sourceLowDegree nextLeft)
    (hnextRightDegree : Shift.sourceLowDegree nextRight)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    IntegrableOn
      (TargetFull.targetFullHeatInner left right nextLeft nextRight)
      (Ioi (0 : ℝ)) := by
  have h := (Laplace.primitive_heat_integrable left right nextLeft nextRight
    hleftPos hrightPos hnextLeftPos hnextRightPos).integral_prod_right
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact TargetFull.target_full_heat_inner_closed left right nextLeft nextRight t
    hleftDegree hrightDegree hnextLeftDegree hnextRightDegree
    hleftPos hrightPos hnextLeftPos hnextRightPos ht

theorem compactified_outer_integrable
    (left right nextLeft nextRight : Term)
    (hleftDegree : Shift.sourceLowDegree left)
    (hrightDegree : Shift.sourceLowDegree right)
    (hnextLeftDegree : Shift.sourceLowDegree nextLeft)
    (hnextRightDegree : Shift.sourceLowDegree nextRight)
    (hleftPos : 0 < left.exponent) (hrightPos : 0 < right.exponent)
    (hnextLeftPos : 0 < nextLeft.exponent)
    (hnextRightPos : 0 < nextRight.exponent) :
    IntegrableOn
      (compactifiedHeatInner left right nextLeft nextRight)
      (Ioo (0 : ℝ) 1) := by
  let g := TargetFull.targetFullHeatInner left right nextLeft nextRight
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun u hu => (f_deriv u hu).hasDerivWithinAt)
    f_inj g
  rw [f_image] at hchange
  have h := hchange.mp (source_outer_integrable left right nextLeft nextRight
    hleftDegree hrightDegree hnextLeftDegree hnextRightDegree
    hleftPos hrightPos hnextLeftPos hnextRightPos)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hden : 0 < 1-u := sub_pos.mpr hu.2
  have hpos : 0 < (1/(1-u)^2 : ℝ) := by positivity
  simp only [g,f,abs_of_pos hpos,smul_eq_mul,compactifiedHeatInner]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
