import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffGram
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice
open FullYSourceCutoffVolterra SourceCutoffDilationWard NativeHistoryGrade
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace
attribute [local irreducible] embed GaussCoreLabel.project

private theorem three_power_difference {R : Type*} [Ring R] (A B : R) (j : Fin 3) :
    B^(j.val+1)-A^(j.val+1)=
      ∑r : Fin (j.val+1),A^r.val*(B-A)*B^(j.val-r.val) := by
  fin_cases j <;> simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero,
    add_zero,pow_zero] <;> norm_num <;> noncomm_ring

/-- Each actual positive grade has one, two or three ordered insertion slots.
The right input varies with F, frequency and the right cutoff. -/
def insertionSlot (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (q : QuantumTest)
    (j : Fin 3) (r : Fin (j.val+1)) : QuantumTest :=
  ((coreStep F m z hz)^r.val * (coreStep F ell z hz-coreStep F m z hz) *
    (coreStep F ell z hz)^(j.val-r.val)) (resolventCore F z hz q)

theorem actual_difference_insertions (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (q : QuantumTest) (j : Fin 3) :
    differenceLeg F m ell z hz q (j.val+1)=∑r : Fin (j.val+1),insertionSlot F m ell z hz q j r := by
  have h := LinearMap.congr_fun
    (three_power_difference (coreStep F m z hz) (coreStep F ell z hz) j)
    (resolventCore F z hz q)
  simpa only [differenceLeg,leg,LinearMap.sub_apply,LinearMap.sum_apply,insertionSlot] using h

/-- This is the complete inverse difference, with its six source-generated insertions. -/
theorem actual_full_response_insertions (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    inverse F ell z (embed q)-inverse F m z (embed q)=
      ∑j : Fin 3,∑r : Fin (j.val+1),embed (insertionSlot F m ell z hz q j r) := by
  rw [actual_response_difference F m ell z hz q hq]
  simp_rw [actual_difference_insertions,map_sum]

theorem actual_full_response_insertion_norm (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖inverse F ell z (embed q)-inverse F m z (embed q)‖^2=
      ∑j : Fin 3,‖∑r : Fin (j.val+1),embed (insertionSlot F m ell z hz q j r)‖^2 := by
  rw [actual_response_difference_norm F m ell z hz q hq]
  simp_rw [actual_difference_insertions,map_sum]

private theorem increment_algebra {R : Type*} [Ring R] (U Y V : R) :
    -(U*Y)-(-(U*V))=-(U*(Y-V)) := by noncomm_ring

/-- The insertion is exactly the original native cutoff difference, in its resolvent order. -/
theorem actual_core_step_difference (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) :
    coreStep F ell z hz-coreStep F m z hz=
      -(resolventCore F z hz*(nativeCutoffAction ell-nativeCutoffAction m)) :=
  increment_algebra _ _ _

end LowEnergy.ActualThreeParticleCutoffGram
