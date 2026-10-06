import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationFourierDifferentiation

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFourierJets
open PreparationVacuumWeyl PreparationVacuumWeylDecay CanonicalPreparationSquareCutoff
open MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace
attribute [local irreducible] symbolSlice jointSymbol partialFourier

theorem partialFourierJet_readback (n : ℕ) (p k : PhysicalMomentum) :
    partialFourierJet n p k=iteratedFDeriv ℝ n (fun q : PhysicalMomentum => partialFourier q k) p := by
  induction n generalizing p with
  | zero =>
    apply ContinuousMultilinearMap.ext
    intro v
    have empty : v=(0 : Fin 0 → PhysicalMomentum) := Subsingleton.elim _ _
    rw [empty,partialFourierJet_zero_readback,iteratedFDeriv_zero_apply]
  | succ n ih =>
    have same : iteratedFDeriv ℝ n (fun q : PhysicalMomentum => partialFourier q k)=
        (fun q : PhysicalMomentum => partialFourierJet n q k) := by
      funext q
      exact (ih q).symm
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,same,
      (partialFourierJet_hasFDerivAt n p k).fderiv]
    exact ((jetCurry n).symm_apply_apply (partialFourierJet (n+1) p k)).symm

theorem partialFourier_momentum_smooth (k : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun p : PhysicalMomentum => partialFourier p k) := by
  apply contDiff_of_differentiable_iteratedFDeriv
  intro n _
  have same : iteratedFDeriv ℝ n (fun q : PhysicalMomentum => partialFourier q k)=
      (fun q : PhysicalMomentum => partialFourierJet n q k) := by
    funext q
    exact (partialFourierJet_readback n q k).symm
  rw [same]
  exact fun p => (partialFourierJet_hasFDerivAt n p k).differentiableAt

theorem original_partialFourier_pjet_integral (n : ℕ) (p k : PhysicalMomentum) :
    iteratedFDeriv ℝ n (fun q : PhysicalMomentum => partialFourier q k) p=
      ∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) •
        iteratedFDeriv ℝ n (fun q : PhysicalMomentum => symbolSlice q x) p := by
  rw [←partialFourierJet_readback,partialFourierJet_literal]

theorem original_partialFourier_first_derivative (p k v : PhysicalMomentum) :
    fderiv ℝ (fun q : PhysicalMomentum => partialFourier q k) p v=
      ∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) •
        fderiv ℝ (fun q : PhysicalMomentum => symbolSlice q x) p v := by
  have genuine := partialFourierJet_apply 1 p k (fun _ : Fin 1 => v)
  rw [partialFourierJet_readback] at genuine
  simpa only [sourceMomentumJet,iteratedFDeriv_one_apply] using genuine

theorem original_partialFourier_second_derivative (p k v w : PhysicalMomentum) :
    fderiv ℝ (fderiv ℝ (fun q : PhysicalMomentum => partialFourier q k)) p v w=
      ∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) •
        fderiv ℝ (fderiv ℝ (fun q : PhysicalMomentum => symbolSlice q x)) p v w := by
  have genuine := partialFourierJet_apply 2 p k ![v,w]
  rw [partialFourierJet_readback] at genuine
  simpa only [sourceMomentumJet,iteratedFDeriv_two_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one] using genuine

end LowEnergy.PreparationVacuumFourierJets
