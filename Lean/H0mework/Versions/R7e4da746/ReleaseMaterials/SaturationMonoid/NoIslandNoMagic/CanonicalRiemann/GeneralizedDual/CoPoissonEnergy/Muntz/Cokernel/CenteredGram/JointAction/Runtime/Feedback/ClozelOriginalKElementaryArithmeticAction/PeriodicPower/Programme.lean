import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Programme
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Lattice OriginalKElementaryArithmeticAction.PeriodicPower.LatticePrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Source
open scoped Topology InnerProductSpace
open private circleValue from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Sampling
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local notation "Hq" => BurnolQuarterIntervalL2
local notation "b" => burnolRieszSingleFourierSource
local notation "E" => burnolQuarterZeroExtension
local notation "D" => burnolMultiplicativeDilation

def finiteMap (c : BurnolCompletedMellinCoordinate) (N : ℕ) : C(AddCircle (1:ℝ),ℂ) :=
  ∑ n∈Finset.range N,
    (powerCoefficient c n • _root_.fourier n+
      powerCoefficient c (-((n:ℤ)+1)) • _root_.fourier (-((n:ℤ)+1)))

def finiteSource (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T:=(1:ℝ))) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (finiteMap c N)

theorem actual_programme_representative (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    (finiteSource c N:AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle] finiteMap c N :=
  ContinuousMap.coeFn_toLp AddCircle.haarAddCircle (finiteMap c N)

/-- The entire period-one source is the strong limit of its actual finite Fourier programme. -/
theorem actual_programme_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (finiteSource c) atTop (𝓝 (periodicPower c)) := by
  have source:=(_root_.fourierBasis.hasSum_repr (periodicPower c)).nat_add_neg_add_one
  have finite:=source.tendsto_sum_nat
  change Tendsto (fun N=>ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (finiteMap c N)) atTop _
  simpa only [actual_periodic_coefficient,finiteMap,map_sum,map_add,map_smul,
    _root_.coe_fourierBasis] using finite

private theorem origin_step (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    finiteMap c (N+1) 0=finiteMap c N 0+powerCoefficient c N+powerSample c N := by
  have negative : powerCoefficient c (-((N:ℤ)+1))=powerSample c N :=
    (powerCoefficient_even c ((N:ℤ)+1)).trans (powerCoefficient_positive c N)
  simp only [finiteMap,Finset.sum_range_succ,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    smul_eq_mul,_root_.fourier_eval_zero,mul_one,negative]
  ring

private theorem origin_sum (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    finiteMap c (N+1) 0=(∑ n∈Finset.range N,(2:ℂ)*powerSample c n)+powerSample c N := by
  induction N with
  | zero =>
    rw [origin_step]
    simp only [finiteMap,Finset.range_zero,Finset.sum_empty,ContinuousMap.zero_apply,
      Nat.cast_zero,powerCoefficient_zero,zero_add]
  | succ N ih =>
    rw [origin_step,ih]
    simp only [Nat.cast_add,Nat.cast_one,powerCoefficient_positive,Finset.sum_range_succ]
    ring

/-- The last half-mode belongs to this actual integer enumeration and is retained in the bill. -/
def originFinitePart (c : BurnolCompletedMellinCoordinate) (N : ℕ) : ℂ :=
  finiteMap c (N+1) 0-powerSample c N-
    ((N+1:ℕ):ℂ)^(1-star c.value)/(1-star c.value)

theorem actual_origin_coefficient (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    originFinitePart c N=FiniteForcing.coefficient (star c.value) (N+1) := by
  rw [originFinitePart,origin_sum,add_sub_cancel_right,FiniteForcing.coefficient,
    Finset.sum_Ico_eq_sum_range]
  congr 1
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro n member
  simp only [powerSample]
  push_cast
  ring

/-- The original theta-zeta zero is read on the same finite Fourier programme, before taking its strong limit. -/
theorem actual_original_zero_origin (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    Tendsto (originFinitePart c) atTop (𝓝 0) := by
  have source:=(DirichletCoefficient.original_coefficient_limits c zero).1
  have next:=source.comp (tendsto_add_atTop_nat 1)
  have same : originFinitePart c=(fun N=>FiniteForcing.coefficient (star c.value) (N+1)) :=
    funext (actual_origin_coefficient c)
  rw [same]
  exact next

theorem actual_power_B_programme (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (bounded : h≤Real.log 2) :
    Tendsto (fun N:ℕ=>(1/2:ℂ)*inner ℂ (finiteSource c N)
      (circleValue (D (-h) (E (b c:Hq))))) atTop (𝓝 (powerBPrice c h)) := by
  rw [actual_power_B_contact c h bounded]
  exact ((actual_programme_tendsto c).inner tendsto_const_nhds).const_mul (1/2:ℂ)

theorem actual_B_power_programme (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N:ℕ=>(1/2:ℂ)*inner ℂ (circleValue (E (b c:Hq)))
      (finiteSource c N)) atTop (𝓝 (bPowerPrice c)) := by
  rw [actual_B_power_contact]
  exact (tendsto_const_nhds.inner (actual_programme_tendsto c)).const_mul (1/2:ℂ)

end OriginalKElementaryArithmeticAction.PeriodicPower.Programme
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
