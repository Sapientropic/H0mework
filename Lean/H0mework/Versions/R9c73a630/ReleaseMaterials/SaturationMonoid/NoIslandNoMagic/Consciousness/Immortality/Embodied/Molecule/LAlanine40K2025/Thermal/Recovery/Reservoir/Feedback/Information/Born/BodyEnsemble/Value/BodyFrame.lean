import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Value.Entropy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open Collision SourceGeneratedWorkInformation SourceGeneratedConditionalWork ValueCoarsening
open scoped ENNReal Matrix ComplexOrder
noncomputable section

attribute [local irreducible] Current.loadPulse Current.pulse Live.State.joint
  sourceTarget receivedState firstState contrast


private theorem binary_second {κ : Type*} [Fintype κ]
    (p : PMF (Fin 2 × κ)) (i : κ) :
    (Quantum.sndMarginal p i).toReal =
      (p (0, i)).toReal + (p (1, i)).toReal := by
  classical
  change ((p.map Prod.snd) i).toReal = _
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0 : (∑ y : κ, if i = (0, y).2 then p (0, y) else 0) = p (0, i) := by
    simpa only [Prod.snd] using (Fintype.sum_ite_eq i (fun x => p (0, x)))
  have h1 : (∑ y : κ, if i = (1, y).2 then p (1, y) else 0) = p (1, i) := by
    simpa only [Prod.snd] using (Fintype.sum_ite_eq i (fun x => p (1, x)))
  rw [h0, h1]
  rw [ENNReal.toReal_add (p.apply_ne_top (0, i)) (p.apply_ne_top (1, i))]

theorem original_marginal_diagonal (i : Current.FullIndex) :
    (Quantum.sndMarginal ValueCoarsening.indexedJoint i).toReal =
      ((Quantum.conjugation spectralFrame (bodyRead receivedState.joint)) i i).re := by
  have hm0 : (measured0 i).toReal =
      ((Quantum.conjugation spectralFrame rho0) i i).re :=
    Quantum.diagonalPMF_toReal _ _ _ i
  have hm1 : (measured1 i).toReal =
      ((Quantum.conjugation spectralFrame rho1) i i).re :=
    Quantum.diagonalPMF_toReal _ _ _ i
  rw [binary_second, indexed_left, indexed_right, source_index_left, source_index_right,
    hm0, hm1]
  rw [← source_mixture, map_add, map_smul, map_smul]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.add_re,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem original_body_positive : (bodyRead receivedState.joint).PosSemidef :=
  by
    rw [Resource.body_blocks receivedState]
    exact (Resource.loadBlock_positive receivedState).add
      (Resource.suppliedBlock_positive receivedState)

theorem original_body_trace : (bodyRead receivedState.joint).trace = 1 := by
  have hp : p0 + p1 = 1 := by
    simpa only [p0, p1] using SourceGeneratedConditionalWork.weights_sum receivedState
  rw [Resource.body_blocks receivedState, Matrix.trace_add]
  change sigma0.trace + sigma1.trace = 1
  rw [sigma0_trace, sigma1_trace, ← Complex.ofReal_add, hp]
  rfl

theorem original_marginal_as_body_diagonal :
    Quantum.sndMarginal ValueCoarsening.indexedJoint =
      Quantum.diagonalPMF
        (Quantum.conjugation spectralFrame (bodyRead receivedState.joint))
        (Quantum.conjugation_posSemidef spectralFrame _ original_body_positive)
        ((Quantum.conjugation_trace spectralFrame _).trans original_body_trace) := by
  ext i
  apply (ENNReal.toReal_eq_toReal_iff'
    ((Quantum.sndMarginal ValueCoarsening.indexedJoint).apply_ne_top i)
    ((Quantum.diagonalPMF _ _ _).apply_ne_top i)).mp
  rw [original_marginal_diagonal, Quantum.diagonalPMF_toReal]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
