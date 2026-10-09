import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffInsertion
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointCost
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCutoffFrequencyBase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace LowEnergy.ActualThreeParticleJointInsertion
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice
open FullYSourceCutoffVolterra SourceCutoffDilationWard NativeHistoryGrade
open ActualThreeParticleCutoffGram ActualVectorJointCost ActualCutoffFrequencyBase
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace
attribute [local irreducible] embed GaussCoreLabel.project

private theorem core_step_embed (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (q : QuantumTest) :
    embed (coreStep F n z hz q)=step F n z (embed q) := by
  simp only [coreStep,LinearMap.neg_apply,Module.End.mul_apply,map_neg]
  have hr : embed (resolventCore F z hz (nativeCutoffAction n q))=
      finiteResolvent F z (embed (nativeCutoffAction n q)) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [hr,←native_cutoff_core]
  rfl

private theorem core_power_embed (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0)
    (q : QuantumTest) (j : ℕ) : embed (((coreStep F n z hz)^j) q)=((step F n z)^j) (embed q) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ',Module.End.mul_apply,core_step_embed,ih,pow_succ',mul_apply_eq_comp]

private theorem power_intertwines {R : Type*} [Monoid R] (A B U : R) (h : A*U=U*B) (j : ℕ) :
    A^j*U=U*B^j := by
  induction j with
  | zero => simp only [pow_zero,mul_one,one_mul]
  | succ j ih =>
    rw [pow_succ',mul_assoc,ih,←mul_assoc,h,mul_assoc,←pow_succ']

private theorem inverse_intertwines {R : Type*} [Ring R] (U Y : R) (j : ℕ) :
    (-(U*Y))^j*U=U*(-(Y*U))^j :=
  power_intertwines _ _ _ (by noncomm_ring) j

private theorem difference_step {R : Type*} [Ring R] (U Y V : R) :
    -(U*Y)-(-(U*V))=-(U*(Y-V)) := by noncomm_ring

/-- The true right input of an insertion retains the same F, frequency and right cutoff. -/
def rightInput (F : Index) (ell : ℕ) (z : ℂ) (q : QuantumTest) (j : Fin 3)
    (r : Fin (j.val+1)) : H :=
  ((-(cutoff ell*finiteResolvent F z))^(j.val-r.val)) (embed q)

private theorem actual_slot_bounded (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (q : QuantumTest) (j : Fin 3) (r : Fin (j.val+1)) :
    embed (insertionSlot F m ell z hz q j r)=
      -((step F m z)^r.val) (finiteResolvent F z
        ((cutoff ell-cutoff m) (finiteResolvent F z (rightInput F ell z q j r)))) := by
  have he : embed (resolventCore F z hz q)=finiteResolvent F z (embed q) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [insertionSlot,Module.End.mul_apply,core_power_embed,LinearMap.sub_apply,map_sub,core_step_embed,he]
  rw [←map_sub]
  change ((step F m z)^r.val) ((step F ell z-step F m z)
    (((step F ell z)^(j.val-r.val)) (finiteResolvent F z (embed q)))) = _
  have hi := congrArg (fun A : H →L[ℂ] H => A (embed q))
    (inverse_intertwines (finiteResolvent F z) (cutoff ell) (j.val-r.val))
  change ((step F ell z)^(j.val-r.val)) (finiteResolvent F z (embed q))=
    finiteResolvent F z (rightInput F ell z q j r) at hi
  rw [hi]
  have hd : step F ell z-step F m z=-(finiteResolvent F z*(cutoff ell-cutoff m)) := by
    exact difference_step (finiteResolvent F z) (cutoff ell) (cutoff m)
  calc
    _ = ((step F m z)^r.val) ((-(finiteResolvent F z*(cutoff ell-cutoff m)))
        (finiteResolvent F z (rightInput F ell z q j r))) :=
      congrArg (fun A : H →L[ℂ] H => ((step F m z)^r.val)
        (A (finiteResolvent F z (rightInput F ell z q j r)))) hd
    _ = _ := by simp only [neg_apply,mul_apply_eq_comp,map_neg]

/-- Every one of the six slots consumes the literal joint residual and Hardy
particular. Their moving right inputs are not replaced by fixed source vectors. -/
theorem actual_joint_hardy_slot (F : Index) (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (j : Fin 3) (r : Fin (j.val+1)) (w : ℝ) :
    embed (insertionSlot F m ell (frequency advanced μ w) (frequency_nonreal advanced μ hμ w) q j r)=
      -((step F m (frequency advanced μ w))^r.val)
        (jointVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w+
         hardyVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w) := by
  rw [actual_slot_bounded]
  congr 2
  exact actual_increment_vector_split advanced false m ell F μ hμ
    (rightInput F ell (frequency advanced μ w) q j r) w

/-- The original full inverse difference retains coherent joint/Hardy sums
inside each of the three orthogonal physical output grades. -/
theorem actual_joint_hardy_response_norm (F : Index) (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) (w : ℝ) :
    ‖inverse F ell (frequency advanced μ w) (embed q)-
      inverse F m (frequency advanced μ w) (embed q)‖^2=
      ∑j : Fin 3,‖∑r : Fin (j.val+1),
        -((step F m (frequency advanced μ w))^r.val)
          (jointVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w+
           hardyVector advanced false m ell F μ (rightInput F ell (frequency advanced μ w) q j r) w)‖^2 := by
  rw [actual_full_response_insertion_norm F m ell _ (frequency_nonreal advanced μ hμ w) q hq]
  simp_rw [actual_joint_hardy_slot F m ell advanced μ hμ q]

end LowEnergy.ActualThreeParticleJointInsertion
