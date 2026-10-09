import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferMeromorphic

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open Set
open scoped BigOperators

theorem punctured_real_regular_of_imaginary_witness
    {ι : Type*} [Fintype ι] (f : ℂ → ℂ) (den : ι → ℂ → ℂ)
    (hm : MeromorphicOn f univ) (ha : AnalyticAt ℂ f Complex.I)
    (hn : f Complex.I ≠ 0)
    (hdm : ∀i,MeromorphicOn (den i) univ)
    (hda : ∀i,AnalyticAt ℂ (den i) Complex.I)
    (hdn : ∀i,den i Complex.I ≠ 0) :
    ∃δ : ℝ,0 < δ ∧ ∀x : ℝ,0 < |x| → |x| < δ →
      f x ≠ 0 ∧ ∀i,den i x ≠ 0 := by
  classical
  let g : ℂ → ℂ := fun z => f z * ∏i,den i z
  have hgm : MeromorphicOn g univ := by
    intro z hz
    exact (hm z hz).mul (MeromorphicAt.fun_prod (s := Finset.univ)
      (fun i _ => hdm i z hz))
  have hga : AnalyticAt ℂ g Complex.I :=
    ha.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hda i))
  have hgn : g Complex.I ≠ 0 :=
    mul_ne_zero hn (Finset.prod_ne_zero_iff.mpr (fun i _ => hdn i))
  obtain ⟨δ,hδ,h⟩ := punctured_real_nonzero_of_imaginary_witness g hgm hga hgn
  refine ⟨δ,hδ,?_⟩
  intro x hx hxd
  have hg := mul_ne_zero_iff.mp (h x hx hxd)
  exact ⟨hg.1,fun i => Finset.prod_ne_zero_iff.mp hg.2 i (Finset.mem_univ i)⟩

end LowEnergy.ActualFourBlockRealTransfer
