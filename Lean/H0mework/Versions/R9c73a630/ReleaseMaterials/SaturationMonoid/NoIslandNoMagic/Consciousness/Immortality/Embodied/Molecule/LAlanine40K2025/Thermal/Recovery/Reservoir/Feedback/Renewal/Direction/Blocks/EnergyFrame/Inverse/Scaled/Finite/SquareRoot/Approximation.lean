import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Dilation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def restoreRoot (R : LoadedJoint) : LoadedJoint :=
  Quantum.conjugation (star installedLoadFrame) (Quantum.conjugation numericFree R)

def bodyRoot (R : LoadedJoint) : Current.FullJoint := Incidence.bodyObservable (restoreRoot R)

theorem body_root_distance (R S : LoadedJoint) : ‖bodyRoot R-bodyRoot S‖ ≤ ‖R-S‖ := by
  rw [bodyRoot,bodyRoot,← bodyObservable_sub]
  apply (body_observable_norm _).trans
  simp only [restoreRoot,← map_sub]
  exact le_of_eq ((StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint (star installedLoadFrame)) _).trans
    (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint numericFree) _))

theorem restored_sqrt (A : LoadedJoint) (positive : A.PosSemidef) : restoreRoot (CFC.sqrt A)=CFC.sqrt (restoreRoot A) := by
  rw [restoreRoot,restoreRoot,sqrt_conjugation numericFree A positive,
    sqrt_conjugation (star installedLoadFrame) _ (Quantum.conjugation_posSemidef numericFree A positive)]

theorem lifted_sqrt (A : LoadedJoint) (positive : A.PosSemidef) :
    CFC.sqrt (Incidence.bodyObservable (restoreRoot A))=bodyRoot (CFC.sqrt A) := by
  have p := Quantum.conjugation_posSemidef (star installedLoadFrame) _ (Quantum.conjugation_posSemidef numericFree A positive)
  exact (body_observable_sqrt (restoreRoot A) p).symm.trans
    (congrArg Incidence.bodyObservable (restored_sqrt A positive).symm)

theorem finite_body_root_identity : effectRoot finiteBodyEffect=bodyRoot (CFC.sqrt finiteEffect) :=
  lifted_sqrt finiteEffect (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1)

theorem finite_body_complement_identity : complementRoot finiteBodyEffect=bodyRoot (CFC.sqrt (1-finiteEffect)) := by
  have lifted := lifted_sqrt (1-finiteEffect) (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2)
  have restored : restoreRoot (1-finiteEffect)=1-originalFrameEffect := by
    simp only [restoreRoot,conjugated_complement,originalFrameEffect]
  rw [restored] at lifted
  rw [complementRoot,finiteBodyEffect,bodyObservable_complement]
  exact lifted

def approximatedPointer (R S : LoadedJoint) : PointerJoint := rawDilation (bodyRoot R) (bodyRoot S)

theorem finite_approximated_pointer_error (R S : LoadedJoint)
    (first : ‖CFC.sqrt finiteEffect-R‖ ≤ (2/10^7 : ℝ))
    (second : ‖CFC.sqrt (1-finiteEffect)-S‖ ≤ (2/10^7 : ℝ)) :
    ‖(finitePointer : PointerJoint)-approximatedPointer R S‖ ≤ (4/10^7 : ℝ) := by
  change ‖dilationMatrix finiteBodyEffect-rawDilation (bodyRoot R) (bodyRoot S)‖ ≤ _
  rw [← raw_dilation_exact,finite_body_root_identity,finite_body_complement_identity]
  have bound := raw_dilation_error (bodyRoot (CFC.sqrt finiteEffect)) (bodyRoot (CFC.sqrt (1-finiteEffect))) (bodyRoot R) (bodyRoot S)
  exact bound.trans (by linarith [(body_root_distance _ _).trans first,(body_root_distance _ _).trans second])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
