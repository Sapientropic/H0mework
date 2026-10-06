import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalGroupedSource
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalSymmetry
open PreparationVacuumCanonicalMoyal
open scoped Topology ContDiff

def listJet (vs : List Phase) (f : Symbol) : Symbol :=
  vs.foldr (fun v g x => fderiv ℝ g x v) f

theorem listJet_smooth (vs : List Phase) {f : Symbol} {x : Phase}
    (smooth : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (listJet vs f) x := by
  induction vs with
  | nil => exact smooth
  | cons v vs ih => exact (ih.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem listJet_swap (v w : Phase) (vs : List Phase) {f : Symbol} {x : Phase}
    (smooth : ContDiffAt ℝ ∞ f x) : listJet (v::w::vs) f x=listJet (w::v::vs) f x := by
  have tail := listJet_smooth vs smooth
  have derivative : DifferentiableAt ℝ (fderiv ℝ (listJet vs f)) x :=
    (tail.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (listJet vs f) y w) x v=
    fderiv ℝ (fun y => fderiv ℝ (listJet vs f) y v) x w
  rw [fderiv_clm_apply derivative (differentiableAt_const w),
    fderiv_clm_apply derivative (differentiableAt_const v)]
  have symmetry := (tail.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    have finite (r : ℕ) : (r : ℕ∞ω)<∞ := by exact_mod_cast ENat.natCast_lt_top r
    exact (finite 2).le)).eq v w
  simpa only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
    ContinuousLinearMap.flip_apply] using symmetry

theorem listJet_perm {U : Set Phase} (openU : IsOpen U) {f : Symbol}
    (smooth : ContDiffOn ℝ ∞ f U) {vs ws : List Phase} (permutation : vs.Perm ws) :
    Set.EqOn (listJet vs f) (listJet ws f) U := by
  induction permutation with
  | nil => intro x _; rfl
  | @cons v left right permutation ih =>
    intro x hx
    have germ : listJet left f =ᶠ[𝓝 x] listJet right f := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih hy
    exact congrArg (fun L : Phase →L[ℝ] ℝ => L v) germ.fderiv_eq
  | swap v w vs =>
    intro x hx
    exact listJet_swap w v vs ((smooth x hx).contDiffAt (openU.mem_nhds hx))
  | trans left right ihleft ihright =>
    intro x hx
    exact (ihleft hx).trans (ihright hx)

theorem listJet_ofFn {U : Set Phase} (openU : IsOpen U) {f : Symbol}
    (smooth : ContDiffOn ℝ ∞ f U) (r : ℕ) (v : Fin r → Phase) (x : Phase) (hx : x∈U) :
    listJet (List.ofFn v) f x=iteratedFDeriv ℝ r f x v := by
  induction r generalizing x with
  | zero => simp [listJet]
  | succ r ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (listJet (List.ofFn (Fin.tail v)) f) x (v 0)=_
    have germ : listJet (List.ofFn (Fin.tail v)) f =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ r f y (Fin.tail v)) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih (Fin.tail v) y hy
    rw [germ.fderiv_eq]
    have hf : ContDiffAt ℝ ∞ f x := (smooth x hx).contDiffAt (openU.mem_nhds hx)
    have derivative : DifferentiableAt ℝ (iteratedFDeriv ℝ r f) x :=
      hf.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top r)
    exact derivative.iteratedFDeriv_succ_apply_left'.symm

theorem smooth_iteratedFDeriv_perm {U : Set Phase} (openU : IsOpen U) {f : Symbol}
    (smooth : ContDiffOn ℝ ∞ f U) (r : ℕ) (v : Fin r → Phase) (sigma : Equiv.Perm (Fin r))
    (x : Phase) (hx : x∈U) :
    iteratedFDeriv ℝ r f x (v∘sigma)=iteratedFDeriv ℝ r f x v := by
  rw [←listJet_ofFn openU smooth r (v∘sigma) x hx,←listJet_ofFn openU smooth r v x hx]
  exact listJet_perm openU smooth (sigma.ofFn_comp_perm v) hx

theorem smooth_domDomCongr {U : Set Phase} (openU : IsOpen U) {f : Symbol}
    (smooth : ContDiffOn ℝ ∞ f U) (r : ℕ) (sigma : Equiv.Perm (Fin r))
    (x : Phase) (hx : x∈U) :
    (iteratedFDeriv ℝ r f x).domDomCongr sigma=iteratedFDeriv ℝ r f x := by
  ext v
  exact smooth_iteratedFDeriv_perm openU smooth r v sigma x hx

end LowEnergy.PreparationVacuumMoyalSymmetry
