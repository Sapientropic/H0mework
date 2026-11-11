import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Programme
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Finite
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Lattice OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Programme
open scoped Topology BigOperators InnerProductSpace
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local notation "q" => ((1/4:ℝ):AddCircle (1:ℝ))

def symmetricMap (c:BurnolCompletedMellinCoordinate) (N:ℕ) : C(AddCircle (1:ℝ),ℂ) :=
 ∑n∈Finset.Ico 1 N,powerCoefficient c n • (_root_.fourier n+_root_.fourier (-n))

private theorem fourier_quarter_step (n:ℤ) :
 _root_.fourier (n+1) q=_root_.fourier n q*Complex.I := by
 rw [_root_.fourier_add]
 congr 1
 rw [_root_.fourier_coe_apply]
 norm_num
 convert Complex.exp_pi_div_two_mul_I using 1
 congr 1
 ring

private theorem fourier_quarter_base : _root_.fourier 0 q=1 := by simp

private theorem fourier_quarter_even (n:ℕ) :
 _root_.fourier (2*n) q=(-1:ℂ)^n := by
 induction n with
 | zero => simp
 | succ n ih =>
  have index:(2*((n+1:ℕ):ℤ))=(2*n:ℤ)+1+1:=by push_cast;ring
  rw [index,fourier_quarter_step,fourier_quarter_step,ih,pow_succ]
  rw [mul_assoc,Complex.I_mul_I]

private theorem fourier_quarter_odd (n:ℕ) :
 _root_.fourier (2*n+1) q=(-1:ℂ)^n*Complex.I := by
 rw [fourier_quarter_step]
 exact congrArg (fun z:ℂ=>z*Complex.I) (fourier_quarter_even n)

def pairNat (n:ℕ) : ℂ := _root_.fourier (n:ℤ) q+_root_.fourier (-(n:ℤ)) q

private theorem paired_even (n:ℕ) : pairNat (2*n)=2*(-1:ℂ)^n := by
 unfold pairNat
 push_cast
 rw [_root_.fourier_neg,fourier_quarter_even,map_pow]
 norm_num
 ring

private theorem paired_odd (n:ℕ) : pairNat (2*n+1)=0 := by
 unfold pairNat
 push_cast
 rw [_root_.fourier_neg,fourier_quarter_odd,map_mul,map_pow]
 norm_num

private theorem powerCoefficient_nat (c:BurnolCompletedMellinCoordinate) (n:ℕ) (positive:0<n) :
 powerCoefficient c n=(1/2:ℂ)*(n:ℂ)^(-star c.value) := by
 obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero positive.ne'
 rw [Nat.cast_succ,powerCoefficient_positive]
 simp only [powerSample,Nat.cast_succ]

def harmonic (s:ℂ) (N:ℕ) : ℂ := ∑n∈Finset.Ico 1 N,(n:ℂ)^(-s)

private theorem symmetric_step (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) :
 symmetricMap c (N+1) q=symmetricMap c N q+
  powerCoefficient c N*pairNat N := by
 rw [symmetricMap,Finset.sum_Ico_succ_top (Nat.succ_le_of_lt positive)]
 simp only [ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
 simp only [symmetricMap,pairNat,ContinuousMap.sum_apply,ContinuousMap.smul_apply,ContinuousMap.add_apply,smul_eq_mul]

private theorem harmonic_step (s:ℂ) (N:ℕ) (positive:0<N) :
 harmonic s (N+1)=harmonic s N+(N:ℂ)^(-s) := by
 rw [harmonic,Finset.sum_Ico_succ_top (Nat.succ_le_of_lt positive)]
 rfl

private theorem power_mul (s:ℂ) (n:ℕ) (_positive:0<n) :
 ((2*n:ℕ):ℂ)^(-s)=(2:ℂ)^(-s)*(n:ℂ)^(-s) := by
 push_cast
 exact Complex.mul_cpow_ofReal_nonneg (by norm_num:(0:ℝ)≤2) (Nat.cast_nonneg n) (-s)

private theorem power_two_exponent (s:ℂ) : (2:ℂ)^(1-s)=2*(2:ℂ)^(-s) := by
 rw [sub_eq_add_neg,Complex.cpow_add _ _ (by norm_num:(2:ℂ)≠0),Complex.cpow_one]

/-- A true finite, noncentral read of the same W programme, with the odd lattice modes actually removed. -/
theorem actual_quarter_finite_read (c:BurnolCompletedMellinCoordinate) (M:ℕ) :
 symmetricMap c (4*(M+1)) q=(2:ℂ)^(-star c.value)*
  ((2:ℂ)^(1-star c.value)*harmonic (star c.value) (M+1)-harmonic (star c.value) (2*(M+1))) := by
 induction M with
 | zero =>
  change symmetricMap c 4 q=_
  rw [symmetric_step c 3 (by decide),symmetric_step c 2 (by decide),symmetric_step c 1 (by decide)]
  have odd1:=paired_odd 0
  have odd3:=paired_odd 1
  have even2:=paired_even 1
  norm_num at odd1 odd3 even2
  rw [odd1,odd3,even2,powerCoefficient_nat c 2 (by decide)]
  simp only [symmetricMap,Finset.Ico_self,Finset.sum_empty,ContinuousMap.zero_apply,
   mul_zero,add_zero,zero_add]
  have h1:harmonic (star c.value) 1=0:=by simp [harmonic]
  have h2:harmonic (star c.value) 2=1:=by
   rw [harmonic_step _ 1 (by decide),h1]
   simp
  rw [h1,h2]
  ring
 | succ M ih =>
  have steps:=symmetric_step c (4*(M+1)+3) (by omega)
  rw [symmetric_step c (4*(M+1)+2) (by omega),
   symmetric_step c (4*(M+1)+1) (by omega),symmetric_step c (4*(M+1)) (by omega)] at steps
  have odd1:(4*(M+1)+1:ℕ)=2*(2*(M+1))+1:=by omega
  have odd3:(4*(M+1)+3:ℕ)=2*(2*(M+1)+1)+1:=by omega
  have even0:(4*(M+1):ℕ)=2*(2*(M+1)):=by omega
  have even2:(4*(M+1)+2:ℕ)=2*(2*(M+1)+1):=by omega
  rw [show 4*(M+1)+3+1=4*(M+1+1) by omega,ih] at steps
  rw [odd3,paired_odd,even2,paired_even,odd1,paired_odd,even0,paired_even] at steps
  simp only [mul_zero,add_zero] at steps
  rw [powerCoefficient_nat c _ (by omega),powerCoefficient_nat c _ (by omega)] at steps
  rw [power_mul _ (2*(M+1)) (by omega),power_mul _ (M+1) (by omega),
   power_mul _ (2*(M+1)+1) (by omega)] at steps
  have signs:(-1:ℂ)^(2*(M+1))=1:=by rw [pow_mul];norm_num
  have next:(-1:ℂ)^(2*(M+1)+1)= -1:=by rw [pow_succ,signs];ring
  rw [signs,next,power_two_exponent] at steps
  rw [harmonic_step _ (M+1) (by omega),
   show 2*(M+1+1)=2*(M+1)+1+1 by omega,
   harmonic_step _ (2*(M+1)+1) (by omega),harmonic_step _ (2*(M+1)) (by omega),
   power_mul _ (M+1) (by omega),power_two_exponent]
  linear_combination steps

/-- The continuous normalizations in the two arithmetic reads cancel at the same finite index. -/
theorem actual_quarter_normalized_read (c:BurnolCompletedMellinCoordinate) (M:ℕ) :
 symmetricMap c (4*(M+1)) q=(2:ℂ)^(-star c.value)*
  ((2:ℂ)^(1-star c.value)*FiniteForcing.coefficient (star c.value) (M+1)-
    FiniteForcing.coefficient (star c.value) (2*(M+1))) := by
 rw [actual_quarter_finite_read]
 unfold FiniteForcing.coefficient
 have product:((2*(M+1):ℕ):ℂ)^(1-star c.value)=
   (2:ℂ)^(1-star c.value)*(M+1:ℂ)^(1-star c.value):=by
  push_cast
  simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat] using
   Complex.mul_cpow_ofReal_nonneg (by norm_num:(0:ℝ)≤2) (by positivity:(0:ℝ)≤M+1) (1-star c.value)
 rw [product]
 dsimp only [harmonic]
 push_cast
 ring

/-- The original zero generates a genuine noncentral finite-programme read, without using L² point evaluation. -/
theorem actual_original_zero_quarter (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 Tendsto (fun M:ℕ=>symmetricMap c (4*(M+1)) q) atTop (𝓝 0) := by
 have original:=(DirichletCoefficient.original_coefficient_limits c zero).1
 have first:=original.comp (tendsto_add_atTop_nat 1)
 have index:Tendsto (fun M:ℕ=>2*(M+1)) atTop atTop:=by
  exact ((strictMono_mul_left_of_pos (by decide:(0:ℕ)<2)).comp (strictMono_nat_of_lt_succ (by intro n;omega))).tendsto_atTop
 have second:=original.comp index
 have joint:=((first.const_mul ((2:ℂ)^(1-star c.value))).sub second).const_mul ((2:ℂ)^(-star c.value))
 simp only [mul_zero,sub_zero] at joint
 apply joint.congr'
 filter_upwards with M
 exact (actual_quarter_normalized_read c M).symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Finite
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
