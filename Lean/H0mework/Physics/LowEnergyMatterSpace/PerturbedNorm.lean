import H0mework.Physics.LowEnergyMatterSpace.PerturbedExistence
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Genuine finite-coupling developments preserve the source Hilbert norm. -/
set_option autoImplicit false
open Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

theorem interactionGenerator_inner_zero (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (epsilon time : ℝ) (v : MatterL2) :
    (inner ℂ v (interactionGenerator perturbation epsilon time v)).re=0 := by
  have paired := heisenberg_symmetric (perturbation time) (symmetric time) time v v
  have real : star (inner ℂ v (heisenberg (perturbation time) time v))=
      inner ℂ v (heisenberg (perturbation time) time v) :=
    (inner_conj_symm _ _).trans paired
  have imaginary : (inner ℂ v (heisenberg (perturbation time) time v)).im=0 := by
    have same := congrArg Complex.im real
    simp only [Complex.star_def,Complex.conj_im] at same
    linarith
  change (inner ℂ v ((-Complex.I*(epsilon : ℂ)) • heisenberg (perturbation time) time v)).re=0
  rw [inner_smul_right]
  simp [Complex.mul_re,Complex.mul_im,imaginary]

theorem perturbed_norm_derivative (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (epsilon time : ℝ) (curve : ℝ → MatterL2)
    (evolves : HasDerivAt curve (interactionGenerator perturbation epsilon time (curve time)) time) :
    HasDerivAt (fun t => ‖curve t‖^2) 0 time := by
  have right := interactionGenerator_inner_zero perturbation symmetric epsilon time (curve time)
  have left : (inner ℂ (interactionGenerator perturbation epsilon time (curve time)) (curve time)).re=0 := by
    have conjugate := congrArg Complex.re
      (inner_conj_symm (curve time) (interactionGenerator perturbation epsilon time (curve time)))
    change (inner ℂ (interactionGenerator perturbation epsilon time (curve time)) (curve time)).re=
      (inner ℂ (curve time) (interactionGenerator perturbation epsilon time (curve time))).re at conjugate
    exact conjugate.trans right
  have generated := Complex.reCLM.hasFDerivAt.comp_hasDerivAt time (evolves.inner ℂ evolves)
  change HasDerivAt (fun t => (inner ℂ (curve t) (curve t)).re)
    ((inner ℂ (curve time) (interactionGenerator perturbation epsilon time (curve time))+
      inner ℂ (interactionGenerator perturbation epsilon time (curve time)) (curve time)).re) time at generated
  have self (v : MatterL2) : (inner ℂ v v).re=‖v‖^2 := by
    change RCLike.re (inner ℂ v v)=_
    exact inner_self_eq_norm_sq v
  simpa only [self,Complex.add_re,right,left,add_zero] using generated

theorem perturbed_curve_norm (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (epsilon delta : ℝ) (curve : ℝ → MatterL2)
    (evolves : ∀ time ∈ Ioo (-delta) delta,
      HasDerivAt curve (interactionGenerator perturbation epsilon time (curve time)) time)
    (first second : ℝ) (inFirst : first ∈ Ioo (-delta) delta) (inSecond : second ∈ Ioo (-delta) delta) :
    ‖curve first‖=‖curve second‖ := by
  have squared (time : ℝ) (inside : time ∈ Ioo (-delta) delta) :
      HasDerivAt (fun t => ‖curve t‖^2) 0 time :=
    perturbed_norm_derivative perturbation symmetric epsilon time curve (evolves time inside)
  have constant := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-delta) delta).isPreconnected
    (fun time inside => (squared time inside).differentiableAt.differentiableWithinAt)
    (fun time inside => (squared time inside).deriv) inFirst inSecond
  nlinarith [norm_nonneg (curve first),norm_nonneg (curve second)]

theorem perturbed_physical_weak (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (epsilon time : ℝ) (curve : ℝ → MatterL2)
    (evolves : HasDerivAt curve (interactionGenerator perturbation epsilon time (curve time)) time)
    (test : Quantum.Generator.domain spatialAction) :
    HasDerivAt (fun t => inner ℂ (test : MatterL2) (spatialUnitary t (curve t)))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian spatialAction test) (spatialUnitary time (curve time))+
        inner ℂ (test : MatterL2) ((-Complex.I*(epsilon : ℂ)) •
          perturbation time (spatialUnitary time (curve time)))) time := by
  have negd : HasDerivAt (fun t : ℝ => -t) (-1) time := by
    convert! (hasDerivAt_id time).neg using 1
  have left := (spatial_domain_derivative test (-time)).scomp time negd
  have paired := left.inner ℂ evolves
  simp only [Function.comp_apply,neg_smul,one_smul,inner_neg_left] at paired
  have force : spatialUnitary time (interactionGenerator perturbation epsilon time (curve time))=
      (-Complex.I*(epsilon : ℂ)) • perturbation time (spatialUnitary time (curve time)) := by
    change spatialUnitary time ((-Complex.I*(epsilon : ℂ)) •
      spatialUnitary (-time) (perturbation time (spatialUnitary time (curve time))))=_
    rw [map_smul,← spatialUnitary_add,add_neg_cancel,spatialUnitary_zero]
  simp only [spatial_pair_transfer,force] at paired
  convert! paired using 1
  simp [Quantum.Generator.hamiltonian,inner_smul_left]
  ring_nf
  simp [Complex.I_sq]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
