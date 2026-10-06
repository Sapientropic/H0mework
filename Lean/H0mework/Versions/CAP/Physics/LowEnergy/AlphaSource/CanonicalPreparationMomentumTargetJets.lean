import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationFourierReadback
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMomentumHomogeneity

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMomentumFirst
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open CanonicalPreparationSquareCutoff
open MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap
attribute [local irreducible] symbolSlice jointSymbol partialFourier

def restrictPositionJet (j n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum × PhysicalMomentum) (MomentumJet n) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n) :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => ContinuousLinearMap.inl ℝ PhysicalMomentum PhysicalMomentum)

def momentumFirstJet (j n : ℕ) (xp : PhysicalMomentum × PhysicalMomentum) :=
  restrictPositionJet j n (iteratedFDeriv ℝ j (sourceMomentumJet n) xp)

theorem momentumFirstJet_smooth (j n : ℕ) : ContDiff ℝ ∞ (momentumFirstJet j n) := by
  have full : ContDiff ℝ ∞ (iteratedFDeriv ℝ j (sourceMomentumJet n)) :=
    (sourceMomentumJet_smooth n).iteratedFDeriv_right
      (by exact_mod_cast (le_top : (⊤+(j : ℕ∞))≤⊤))
  have lower : ContDiff ℝ ∞ (restrictPositionJet j n) := by
    with_unfolding_all
      exact ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum × PhysicalMomentum) (MomentumJet n))
        (F := ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n))
        (restrictPositionJet j n)
  exact lower.comp full

theorem momentumFirstJet_original (j n : ℕ) (x p : PhysicalMomentum) :
    momentumFirstJet j n (x,p)=iteratedFDeriv ℝ j (fun y : PhysicalMomentum => sourceMomentumJet n (y,p)) x := by
  let inclusion : PhysicalMomentum →L[ℝ] PhysicalMomentum × PhysicalMomentum :=
    ContinuousLinearMap.inl ℝ PhysicalMomentum PhysicalMomentum
  let translated : PhysicalMomentum × PhysicalMomentum → MomentumJet n :=
    fun w => sourceMomentumJet n (w+(0,p))
  have smooth : ContDiff ℝ ∞ translated :=
    (sourceMomentumJet_smooth n).comp (contDiff_id.add contDiff_const)
  have same : (fun y : PhysicalMomentum => sourceMomentumJet n (y,p))=translated ∘ inclusion := by
    ext y
    simp only [translated,inclusion,ContinuousLinearMap.inl_apply,Prod.mk_add_mk,
      add_zero,zero_add,Function.comp_apply]
  rw [same,inclusion.iteratedFDeriv_comp_right smooth x
    (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))]
  have translation : iteratedFDeriv ℝ j translated (inclusion x)=
      iteratedFDeriv ℝ j (sourceMomentumJet n) (x,p) := by
    dsimp only [translated]
    rw [iteratedFDeriv_comp_add_right]
    simp [inclusion]
  rw [translation]
  rfl

theorem momentumFirstJet_zero_outside (j n : ℕ) (x p : PhysicalMomentum) (outside : x∉positionCompact) :
    momentumFirstJet j n (x,p)=0 := by
  rw [momentumFirstJet_original]
  by_contra nonzero
  exact outside (sourceMomentumJet_position_support n p
    (support_iteratedFDeriv_subset j
      (show x∈Function.support (iteratedFDeriv ℝ j
        (fun y : PhysicalMomentum => sourceMomentumJet n (y,p))) from nonzero)))

theorem momentumFirstJet_homothety (j n : ℕ) (x p : PhysicalMomentum) (a : ℝ)
    (positive : 0<a) (high : 1<‖p‖) (scaledHigh : 1<‖a • p‖) :
    a^n • momentumFirstJet j n (x,a • p)=a • momentumFirstJet j n (x,p) := by
  have actual : (fun y : PhysicalMomentum => a^n • sourceMomentumJet n (y,a • p))=
      (fun y : PhysicalMomentum => a • sourceMomentumJet n (y,p)) := by
    funext y
    simpa only [sourceMomentumJet,PreparationMomentumSymbol.momentumSlice] using!
      PreparationMomentumSymbol.momentum_derivative_homothety n y p a positive high scaledHigh
  have paid := congrArg (fun f : PhysicalMomentum → MomentumJet n => iteratedFDeriv ℝ j f x) actual
  have left := iteratedFDeriv_const_smul_apply' (a := a^n) (x := x)
      ((sourceMomentumJet_x_smooth n (a • p)).of_le
        (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))).contDiffAt
  have right := iteratedFDeriv_const_smul_apply' (a := a) (x := x)
      ((sourceMomentumJet_x_smooth n p).of_le
        (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))).contDiffAt
  simpa only [momentumFirstJet_original] using left.symm.trans (paid.trans right)

end LowEnergy.PreparationVacuumMomentumFirst
