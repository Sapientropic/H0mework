import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylDecay
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumFourierJets
open PreparationVacuumWeyl PreparationVacuumWeylDecay CanonicalPreparationSquareCutoff
open MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace
attribute [local irreducible] symbolSlice jointSymbol partialFourier

abbrev MomentumJet (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin n => PhysicalMomentum) ℂ

def sourceMomentumJet (n : ℕ) (xp : PhysicalMomentum × PhysicalMomentum) : MomentumJet n :=
  iteratedFDeriv ℝ n (fun q : PhysicalMomentum => symbolSlice q xp.1) xp.2

theorem sourceMomentumJet_smooth (n : ℕ) : ContDiff ℝ ∞ (sourceMomentumJet n) := by
  induction n with
  | zero =>
    have same : sourceMomentumJet 0=(fun xp : PhysicalMomentum × PhysicalMomentum =>
        (continuousMultilinearCurryFin0 ℝ PhysicalMomentum ℂ).symm (jointSymbol xp)) := by
      funext xp
      apply ContinuousMultilinearMap.ext
      intro v
      simp only [sourceMomentumJet,iteratedFDeriv_zero_apply,
        continuousMultilinearCurryFin0_symm_apply_apply,jointSymbol]
    rw [same]
    exact (continuousMultilinearCurryFin0 ℝ PhysicalMomentum ℂ).symm.toContinuousLinearEquiv.contDiff.comp
      jointSymbol_smooth
  | succ n ih =>
    let curry := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => PhysicalMomentum) ℂ).symm
    have uncurried : ContDiff ℝ ∞
        (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
          sourceMomentumJet n (w.1.1,w.2)) :=
      ih.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    have differentiated : ContDiff ℝ ∞
        (fun xp : PhysicalMomentum × PhysicalMomentum =>
          fderiv ℝ (fun q : PhysicalMomentum => sourceMomentumJet n (xp.1,q)) xp.2) :=
      uncurried.fderiv contDiff_snd (by simp)
    change ContDiff ℝ ∞ (fun xp : PhysicalMomentum × PhysicalMomentum =>
      curry (fderiv ℝ (fun q : PhysicalMomentum => sourceMomentumJet n (xp.1,q)) xp.2))
    exact curry.toContinuousLinearEquiv.contDiff.comp differentiated

theorem sourceMomentumJet_zero_outside (n : ℕ) (p x : PhysicalMomentum) (outside : x∉positionCompact) :
    sourceMomentumJet n (x,p)=0 := by
  have zero : (fun q : PhysicalMomentum => symbolSlice q x)=(fun _ => (0 : ℂ)) := by
    ext q
    by_contra nonzero
    exact outside (symbolSlice_position_support q (subset_closure
      (show x∈Function.support (symbolSlice q) from nonzero)))
  rw [sourceMomentumJet,zero]
  cases n with
  | zero => simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,map_zero]
  | succ n => rw [iteratedFDeriv_succ_const]; rfl

theorem sourceMomentumJet_position_support (n : ℕ) (p : PhysicalMomentum) :
    tsupport (fun x : PhysicalMomentum => sourceMomentumJet n (x,p))⊆positionCompact := by
  apply closure_minimal _ positionCompact_closed
  intro x support
  by_contra outside
  exact support (sourceMomentumJet_zero_outside n p x outside)

theorem sourceMomentumJet_compact (n : ℕ) (p : PhysicalMomentum) :
    HasCompactSupport (fun x : PhysicalMomentum => sourceMomentumJet n (x,p)) :=
  positionCompact_compact.of_isClosed_subset isClosed_closure (sourceMomentumJet_position_support n p)

theorem sourceMomentumJet_x_smooth (n : ℕ) (p : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun x : PhysicalMomentum => sourceMomentumJet n (x,p)) :=
  (sourceMomentumJet_smooth n).comp (contDiff_id.prodMk contDiff_const)

def sourceMomentumJetSchwartz (n : ℕ) (p : PhysicalMomentum) : 𝓢(PhysicalMomentum,MomentumJet n) :=
  (sourceMomentumJet_compact n p).toSchwartzMap (sourceMomentumJet_x_smooth n p)

theorem sourceMomentumJetSchwartz_apply (n : ℕ) (p x : PhysicalMomentum) :
    sourceMomentumJetSchwartz n p x=sourceMomentumJet n (x,p) := rfl

def partialFourierJet (n : ℕ) (p k : PhysicalMomentum) : MomentumJet n :=
  𝓕 (sourceMomentumJetSchwartz n p) k

theorem partialFourierJet_literal (n : ℕ) (p k : PhysicalMomentum) :
    partialFourierJet n p k=∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) •
      iteratedFDeriv ℝ n (fun q : PhysicalMomentum => symbolSlice q x) p := rfl

theorem partialFourierJet_integrable (n : ℕ) (p k : PhysicalMomentum) :
    Integrable (fun x : PhysicalMomentum => 𝐞 (-⟪x,k⟫) • sourceMomentumJet n (x,p)) :=
  (Real.fourierIntegral_convergent_iff k).mpr (sourceMomentumJetSchwartz n p).integrable

theorem partialFourierJet_apply (n : ℕ) (p k : PhysicalMomentum) (v : Fin n → PhysicalMomentum) :
    partialFourierJet n p k v=∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) • sourceMomentumJet n (x,p) v := by
  rw [partialFourierJet_literal]
  change (∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) • sourceMomentumJet n (x,p)) v=_
  rw [ContinuousMultilinearMap.integral_apply (partialFourierJet_integrable n p k)]
  simp only [Circle.smul_def,smul_apply]

theorem partialFourierJet_zero_readback (p k : PhysicalMomentum) :
    partialFourierJet 0 p k 0=partialFourier p k := by
  rw [partialFourierJet_apply,partialFourier,Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with x
  simp only [sourceMomentumJet,iteratedFDeriv_zero_apply]

end LowEnergy.PreparationVacuumFourierJets
