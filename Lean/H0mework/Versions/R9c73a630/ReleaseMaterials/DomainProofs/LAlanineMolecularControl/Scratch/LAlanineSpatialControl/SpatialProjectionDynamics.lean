import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.LAlanineMolecularControl.Scratch.LAlanineSpatialControl.SpatialProjectionAlgebra
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace LAlanineSpatialProjection
open ContinuousLinearMap
noncomputable section
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The ambient projection is total; only its current source Gram needs to be invertible. -/
def totalProjection (B : H →L[ℂ] E) : E →L[ℂ] E :=
  B ∘L Ring.inverse (gram B) ∘L B.adjoint

theorem total_projection_source (B : H →L[ℂ] E) (unit : IsUnit (gram B)) :
    totalProjection B=projection B unit := by
  simp only [totalProjection,projection,Ring.inverse_of_isUnit unit,inverseGram]

def adjointReal : (H →L[ℂ] E) →L[ℝ] (E →L[ℂ] H) where
  toFun := fun A => A.adjoint
  map_add' := by intro A B; exact map_add adjoint A B
  map_smul' := by
    intro r A
    simp only [← Complex.coe_smul,map_smulₛₗ,Complex.conj_ofReal,RingHom.id_apply]
  cont := adjoint.continuous

theorem adjoint_curve_derivative (B : ℝ → H →L[ℂ] E) (D : H →L[ℂ] E) (t : ℝ)
    (motion : HasDerivAt B D t) :
    HasDerivAt (fun s => (B s).adjoint) D.adjoint t := by
  have source : HasFDerivAt (adjointReal : (H →L[ℂ] E) →L[ℝ] (E →L[ℂ] H)) adjointReal (B t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := H →L[ℂ] E) (F := E →L[ℂ] H)
      (adjointReal (H := H) (E := E))
  simpa only [Function.comp_def,adjointReal] using! source.comp_hasDerivAt t motion

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [CompleteSpace H] [CompleteSpace E] in
theorem composition_curve_derivative (B : ℝ → E →L[ℂ] F) (D : E →L[ℂ] F)
    (C : ℝ → H →L[ℂ] E) (V : H →L[ℂ] E) (t : ℝ)
    (left : HasDerivAt B D t) (right : HasDerivAt C V t) :
    HasDerivAt (fun s => B s ∘L C s) (D ∘L C t+B t ∘L V) t := by
  have source := ((compL ℂ H E F).bilinearRestrictScalars ℝ).hasDerivAt_of_bilinear
    (fun _ => left) (fun _ => right)
  simpa only [bilinearRestrictScalars_apply_apply,compL_apply,add_comm] using source

theorem gram_curve_derivative (B : ℝ → H →L[ℂ] E) (D : H →L[ℂ] E) (t : ℝ)
    (motion : HasDerivAt B D t) :
    HasDerivAt (fun s => gram (B s)) (gramRate (B t) D) t :=
  composition_curve_derivative _ _ B D t (adjoint_curve_derivative B D t motion) motion

theorem inverse_gram_curve_derivative (B : ℝ → H →L[ℂ] E) (D : H →L[ℂ] E) (t : ℝ)
    (motion : HasDerivAt B D t) (unit : IsUnit (gram (B t))) :
    HasDerivAt (fun s => Ring.inverse (gram (B s))) (inverseRate (B t) D unit) t := by
  have inverse := hasFDerivAt_ringInverse (𝕜 := ℝ) unit.unit
  rw [unit.unit_spec] at inverse
  have source := inverse.comp_hasDerivAt t (gram_curve_derivative B D t motion)
  simpa only [neg_apply,mulLeftRight_apply,inverseRate,inverseGram,
    ContinuousLinearMap.mul_def,neg_comp,comp_assoc,Function.comp_def] using source

/-- Actual normed frame motion generates the complete spatial projection rate. -/
theorem total_projection_curve_derivative (B : ℝ → H →L[ℂ] E) (D : H →L[ℂ] E) (t : ℝ)
    (motion : HasDerivAt B D t) (unit : IsUnit (gram (B t))) :
    HasDerivAt (fun s => totalProjection (B s)) (projectionRate (B t) D unit) t := by
  have inverse := inverse_gram_curve_derivative B D t motion unit
  have first := composition_curve_derivative B D (fun s => Ring.inverse (gram (B s)))
    (inverseRate (B t) D unit) t motion inverse
  have full := composition_curve_derivative _ _ _ _ t first (adjoint_curve_derivative B D t motion)
  simpa only [totalProjection,projectionRate,Ring.inverse_of_isUnit unit,inverseGram,
    add_comp,comp_assoc] using full

theorem spatial_projection_controlled_equation (B : ℝ → H →L[ℂ] E) (D : H →L[ℂ] E) (t : ℝ)
    (motion : HasDerivAt B D t) (unit : IsUnit (gram (B t))) :
    HasDerivAt (fun s => totalProjection (B s))
      ((-Complex.I) • commutator (hamiltonian (B t) D unit) (totalProjection (B t))) t := by
  rw [total_projection_source (B t) unit,← projection_evolution]
  exact total_projection_curve_derivative B D t motion unit

end
end LAlanineSpatialProjection
