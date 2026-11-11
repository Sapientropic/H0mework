import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Lattice
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Source
open scoped Topology FourierTransform
local notation "q"=>(1/4:ℝ)

theorem actual_normalized_character (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    (Real.exp (h/2):ℂ)*waveCharacter c h=(Real.exp h:ℂ)^(star c.value):=by
  unfold waveCharacter fullMellinTranslationCharacter
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)),
    ←Complex.ofReal_log (Real.exp_pos h).le,Real.log_exp,Complex.ofReal_exp,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem actual_normalized_raw (c:BurnolCompletedMellinCoordinate) (h x:ℝ):
    (Real.exp (h/2):ℂ)*compactRaw c h x=
      resolvedRaw c (Real.exp (-h)*x)-(Real.exp h:ℂ)^(star c.value)*resolvedRaw c x:=by
  unfold compactRaw
  rw [mul_sub,←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,show h/2+ -h/2=0 by ring,
    Real.exp_zero,Complex.ofReal_one,one_mul,←mul_assoc,actual_normalized_character]

private theorem raw_even (c:BurnolCompletedMellinCoordinate):Function.Even (resolvedRaw c):=by
  intro x
  simp only [resolvedRaw,abs_neg]

private theorem finite_plateau (c:BurnolCompletedMellinCoordinate) (N:ℕ) (pos:0<N)
    (x:ℝ) (inside:|x|≤N):resolvedRaw c (Real.exp (-Real.log (4*N))*x)=resolvedRaw c 0:=by
  have positive:(0:ℝ)<4*N:=by positivity
  have scaled:|Real.exp (-Real.log (4*N))*x|≤q:=by
    rw [abs_mul,abs_of_pos (Real.exp_pos _),Real.exp_neg,Real.exp_log positive]
    apply (inv_mul_le_iff₀ positive).mpr
    nlinarith
  simp only [resolvedRaw,max_eq_left scaled,abs_zero,max_eq_left (by norm_num:(0:ℝ)≤q)]

private theorem resolved_integer_sum (c:BurnolCompletedMellinCoordinate) (N:ℕ):
    ∑n∈Finset.Icc (-(N:ℤ)) N,resolvedRaw c (n:ℝ)=
      resolvedRaw c 0+∑n∈Finset.Ico 1 (N+1),(n:ℂ)^(-star c.value):=by
  rw [Finset.sum_Icc_of_even_eq_range]
  · rw [Finset.sum_range_succ']
    have samples:∑n∈Finset.range N,resolvedRaw c ((n+1:ℕ):ℝ)=
        (1/2:ℂ)*∑n∈Finset.Ico 1 (N+1),(n:ℂ)^(-star c.value):=by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n member
      simpa only [OriginalKElementaryArithmeticAction.PeriodicPower.Lattice.powerSample,Nat.cast_add,Nat.cast_one,add_comm]
        using actual_resolved_positive_sample c n
    simp only [Int.cast_natCast,Int.cast_zero,nsmul_eq_mul]
    rw [samples]
    ring
  · intro n
    simpa only [Int.cast_neg] using raw_even c (n:ℝ)

theorem actual_normalized_lattice (c:BurnolCompletedMellinCoordinate) (N:ℕ) (pos:0<N):
    (Real.exp (Real.log (4*N)/2):ℂ)*∑'n:ℤ,compactRaw c (Real.log (4*N)) (n:ℝ)=
      ((2*N+1:ℕ):ℂ)*resolvedRaw c 0-
      (4*N:ℂ)^(star c.value)*(resolvedRaw c 0+∑n∈Finset.Ico 1 (N+1),(n:ℂ)^(-star c.value)):=by
  have positive:(0:ℝ)<4*N:=by positivity
  have nn:0≤Real.log (4*N):=Real.log_nonneg (by have n:1≤N:=pos;exact_mod_cast (show 1≤4*N by omega))
  have radius:waveRadius (Real.log (4*N))=(N:ℝ):=by
    rw [waveRadius,Real.exp_log positive]
    ring
  rw [tsum_eq_sum (s:=Finset.Icc (-(N:ℤ)) N)]
  · rw [Finset.mul_sum]
    simp_rw [actual_normalized_raw,Real.exp_log positive]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,resolved_integer_sum]
    have plateau:∑n∈Finset.Icc (-(N:ℤ)) N,resolvedRaw c (Real.exp (-Real.log (4*N))*(n:ℝ))=
        ((2*N+1:ℕ):ℂ)*resolvedRaw c 0:=by
      calc
        _=∑n∈Finset.Icc (-(N:ℤ)) N,resolvedRaw c 0:=by
          apply Finset.sum_congr rfl
          intro n member
          exact finite_plateau c N pos (n:ℝ) (by
            have bounds:=Finset.mem_Icc.mp member
            exact abs_le.mpr ⟨by exact_mod_cast bounds.1,by exact_mod_cast bounds.2⟩)
        _=_:=by
          have cardinal:(Finset.Icc (-(N:ℤ)) N).card=2*N+1:=by rw [Int.card_Icc];omega
          simp only [Finset.sum_const,cardinal,nsmul_eq_mul]
    rw [plateau]
    push_cast
    rfl
  · intro n outside
    apply actual_compact_outside c _ nn
    rw [radius]
    exact lt_of_not_ge (fun bound=>outside (Finset.mem_Icc.mpr
      ⟨by exact_mod_cast (abs_le.mp bound).1,by exact_mod_cast (abs_le.mp bound).2⟩))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Lattice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
