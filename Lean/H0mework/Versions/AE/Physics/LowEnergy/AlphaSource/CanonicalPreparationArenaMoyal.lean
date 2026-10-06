import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaComplexMoyal
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGStages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open PreparationVacuumMoyalBudget
open scoped BigOperators ContDiff Topology

theorem complexListJet_projection {U : Set Phase} (openU : IsOpen U) (L : ℂ →L[ℝ] ℝ)
    (f : ComplexSymbol) (hf : ContDiffOn ℝ ∞ f U) (vs : List Phase) :
    Set.EqOn (fun x=>L (complexListJet vs f x)) (listJet vs (fun x=>L (f x))) U := by
  induction vs with
  | nil=>intro x _;rfl
  | cons v vs ih=>
    intro x hx
    have germ : listJet vs (fun y=>L (f y))=ᶠ[𝓝 x]
        (fun y=>L (complexListJet vs f y)) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact (ih hy).symm
    have hs:=complexListJet_smooth vs ((hf x hx).contDiffAt (openU.mem_nhds hx))
    have derivative : fderiv ℝ (fun y=>L (complexListJet vs f y)) x=
        L.comp (fderiv ℝ (complexListJet vs f) x) :=
      (L.hasFDerivAt.comp x (hs.differentiableAt (by simp)).hasFDerivAt).fderiv
    change L (fderiv ℝ (complexListJet vs f) x v)=
      fderiv ℝ (listJet vs (fun y=>L (f y))) x v
    rw [germ.fderiv_eq,derivative]
    rfl

theorem complexListJet_components {U : Set Phase} (openU : IsOpen U)
    (f : ComplexSymbol) (hf : ContDiffOn ℝ ∞ f U) (vs : List Phase) (x : Phase) (hx : x∈U) :
    complexListJet vs f x=
      (listJet vs (fun y=>(f y).re) x : ℂ)+Complex.I*(listJet vs (fun y=>(f y).im) x : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.reCLM_apply,Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using
      complexListJet_projection openU Complex.reCLM f hf vs hx
  · simpa only [Complex.imCLM_apply,Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,mul_one,one_mul,zero_add] using
      complexListJet_projection openU Complex.imCLM f hf vs hx

theorem complexCoefficient_arena {U : Set Phase} (openU : IsOpen U)
    (r : ℕ) (f g : ComplexSymbol) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (x : Phase) (hx : x∈U) :
    complexCoefficient r f g x=PreparationVacuumDAGSemantic.complexMoyal r f g x := by
  have fr : ContDiffOn ℝ ∞ (fun y=>(f y).re) U:=
    fun y hy=>Complex.reCLM.contDiff.contDiffAt.comp_contDiffWithinAt y (hf y hy)
  have fi : ContDiffOn ℝ ∞ (fun y=>(f y).im) U:=
    fun y hy=>Complex.imCLM.contDiff.contDiffAt.comp_contDiffWithinAt y (hf y hy)
  have gr : ContDiffOn ℝ ∞ (fun y=>(g y).re) U:=
    fun y hy=>Complex.reCLM.contDiff.contDiffAt.comp_contDiffWithinAt y (hg y hy)
  have gi : ContDiffOn ℝ ∞ (fun y=>(g y).im) U:=
    fun y hy=>Complex.imCLM.contDiff.contDiffAt.comp_contDiffWithinAt y (hg y hy)
  have decomposition : complexContraction r f g x=
      (listContraction r (fun y=>(f y).re) (fun y=>(g y).re) x : ℂ)-
      (listContraction r (fun y=>(f y).im) (fun y=>(g y).im) x : ℂ)+
      Complex.I*((listContraction r (fun y=>(f y).re) (fun y=>(g y).im) x : ℂ)+
        (listContraction r (fun y=>(f y).im) (fun y=>(g y).re) x : ℂ)) := by
    unfold complexContraction listContraction
    simp only [Complex.ofReal_sum]
    rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [complexListJet_components openU f hf _ x hx,complexListJet_components openU g hg _ x hx]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold complexCoefficient PreparationVacuumDAGSemantic.complexMoyal coefficient
  rw [contraction_list openU r _ _ fr gr hx,contraction_list openU r _ _ fi gi hx,
    contraction_list openU r _ _ fr gi hx,contraction_list openU r _ _ fi gr hx,decomposition]
  ring

theorem actual_arena_moyal_list_budget {U : Set Phase} (openU : IsOpen U)
    (r : ℕ) (f g : ComplexSymbol) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (vs : List Phase) (canonical : PreparationVacuumMoyalBudget.CanonicalList vs)
    (x : Phase) (hx : x∈U) (B D : ℕ → ℝ) (nonnegativeB : ∀ m,0≤B m)
    (nonnegativeD : ∀ m,0≤D m)
    (left : ComplexJetBound f (r+vs.length) B x)
    (right : ComplexJetBound g (r+vs.length) D x) :
    ‖complexListJet vs (PreparationVacuumDAGSemantic.complexMoyal r f g) x‖≤
      moyalScale r*convolution vs.length r B D := by
  have germ : complexCoefficient r f g=ᶠ[𝓝 x] PreparationVacuumDAGSemantic.complexMoyal r f g := by
    filter_upwards [openU.mem_nhds hx] with y hy
    exact complexCoefficient_arena openU r f g hf hg y hy
  rw [←(complexListJet_germ germ vs).eq_of_nhds]
  exact complex_coefficient_list_budget openU r f g hf hg vs canonical x hx B D
    nonnegativeB nonnegativeD left right

end LowEnergy.PreparationVacuumArenaBudget
