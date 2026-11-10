import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Energy
import H0mework.Versions.R2.Physics.GaugeSpectrum.Singlet

/-! The original full-SU7 singlet acts on the source-filtered preparation.
This supplies a nonzero excitation of the same physical generator. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.NativeReadout

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF
open Stage10.GaugeSpectrum FullPairing NativeSource
open SU7ExteriorMatterRepresentation
noncomputable section

private theorem singlet_source (p : BasePoint) :
    singletAction p = (curvatureScale : ℂ)^3 • flipMatter := by
  apply LinearMap.ext
  intro matter
  funext spin
  rw [singletAction, cubicSpinMatrix_normalForm]
  fin_cases spin <;>
    simp [diracMatrixMatterAction, exchange, flipMatter, Compatibility.spinFlip, Fin.sum_univ_four]

private theorem flip_apply (v : Hilbert) (i : FullPairing.Index) :
    operator flipMatter v i = v (Compatibility.spinFlip i.1, i.2) := by
  have read := operator_coordinates flipMatter (naturalCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at read
  rw [read]
  conv_rhs => rw [← naturalCoordinates.apply_symm_apply v]
  rw [naturalCoordinates_apply, naturalCoordinates_apply]
  rfl

private theorem singlet_apply (p : BasePoint) (v : Hilbert) (i : FullPairing.Index) :
    operator (singletAction p) v i =
      (curvatureScale : ℂ)^3 * v (Compatibility.spinFlip i.1, i.2) := by
  rw [singlet_source]
  change naturalCoordinates (((curvatureScale : ℂ)^3) • flipMatter (naturalCoordinates.symm v)) i = _
  rw [map_smul]
  change (curvatureScale : ℂ)^3 * operator flipMatter v i = _
  rw [flip_apply]

def excitation (p : BasePoint) : Hilbert := operator (singletAction p) normalizedFeature

theorem excitation_full_SU7 (p : BasePoint) (frame : SU7MotherGroup) :
    operator (singletAction p)
      (operator (Source.Frame.gaugeFrame frame).toLinearMap normalizedFeature) =
      operator (Source.Frame.gaugeFrame frame).toLinearMap (excitation p) := by
  simpa [operator, excitation, Source.Frame.gaugeFrame, Source.Frame.representationAction] using congrArg naturalCoordinates
    (singletAction_fullSU7 p frame (naturalCoordinates.symm normalizedFeature))

private theorem singlet_twice (p : BasePoint) (v : Hilbert) :
    operator (singletAction p) (operator (singletAction p) v) =
      (curvatureScale : ℂ)^6 • v := by
  apply PiLp.ext
  intro i
  rw [singlet_apply, singlet_apply, Compatibility.spinFlip_involutive]
  change (curvatureScale : ℂ)^3*((curvatureScale : ℂ)^3*v i) = (curvatureScale : ℂ)^6*v i
  ring

theorem excitation_ne_zero (p : BasePoint) : excitation p ≠ 0 := by
  intro zero
  have square := singlet_twice p normalizedFeature
  change operator (singletAction p) (excitation p) = (curvatureScale : ℂ)^6 • normalizedFeature at square
  rw [zero, map_zero] at square
  have coefficient : (curvatureScale : ℂ)^6 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr curvatureScale_pos.ne')
  have featureZero : normalizedFeature = 0 := (smul_eq_zero.mp square.symm).resolve_left coefficient
  have norm := normalizedFeature_norm
  rw [featureZero, norm_zero] at norm
  exact zero_ne_one norm

private theorem hamiltonian_singlet (p : BasePoint) (v : Hilbert) :
    Quantum.Generator.hamiltonianOperator time (point (operator (singletAction p) v)) =
      -operator (singletAction p) (Quantum.Generator.hamiltonianOperator time (point v)) := by
  rw [hamiltonian_point, hamiltonian_point]
  apply PiLp.ext
  intro i
  change Complex.I*velocity (operator (singletAction p) v) i =
    -operator (singletAction p) (Complex.I • velocity v) i
  rw [velocity_apply, singlet_apply, singlet_apply]
  change Complex.I * ((spinRate i.1 : ℂ)*Complex.I*
    ((curvatureScale : ℂ)^3*v (Compatibility.spinFlip i.1,i.2))) =
      -((curvatureScale : ℂ)^3*(Complex.I*velocity v (Compatibility.spinFlip i.1,i.2)))
  rw [velocity_apply, spinRate_flip]
  push_cast
  ring

theorem positive_energy (p : BasePoint) :
    Quantum.Generator.hamiltonianOperator time (point (excitation p)) +
      (frequency : ℂ) • excitation p = ((2*frequency : ℝ) : ℂ) • excitation p := by
  have ground := normalizedFeature_ground
  change Quantum.Generator.hamiltonianOperator time (point normalizedFeature) =
    -(frequency : ℂ) • normalizedFeature at ground
  have energy := hamiltonian_singlet p normalizedFeature
  rw [ground, map_smul, neg_smul, neg_neg] at energy
  change Quantum.Generator.hamiltonianOperator time (point (excitation p)) =
    (frequency : ℂ) • excitation p at energy
  rw [energy, ← add_smul]
  congr 1
  push_cast
  ring

theorem excitation_source_pair (p : BasePoint) :
    featureWitness.full (star (motherFamily (singletAction p)) * motherFamily (singletAction p)) =
      inner ℂ (excitation p) (excitation p) :=
  (featureWitness_source_pair _ _).trans (feature_source_pair _ _)

end
end SaturationMonoid.PhysicsCore.YangMills.NativeReadout
