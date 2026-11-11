import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CoSumLimit
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology

def countedImage (source:ℝ→ℂ) (x:ℝ):ℂ:=
  (x:ℂ)⁻¹*(∑'n:ℕ,source ((n+1:ℕ)/x))-∫u:ℝ in Ioi 0,source u

theorem actual_mass_limit (sources:ℕ→ℝ→ℂ) (source:ℝ→ℂ) (B:ℝ) (nonnegative:0≤B)
    (measurable:∀N,Measurable (sources N))
    (growth:∀N x,‖sources N x‖≤B*|x|)
    (outside:∀N x,(1/2:ℝ) < |x|→sources N x=0)
    (pointwise:∀x,Tendsto (fun N:ℕ=>sources N x) atTop (𝓝 (source x))):
    Tendsto (fun N:ℕ=>∫u:ℝ in Ioi 0,sources N u) atTop (𝓝 (∫u:ℝ in Ioi 0,source u)):=by
  let major:ℝ→ℝ:=(Ioc (0:ℝ) (1/2)).indicator (fun _=>B)
  have majorInt:Integrable major:=
    (integrableOn_const (C:=B) (s:=Ioc (0:ℝ) (1/2))
      (by exact measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  apply tendsto_integral_of_dominated_convergence major
  · intro N
    exact (measurable N).aestronglyMeasurable.restrict
  · exact majorInt.integrableOn
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0<u at hu
    dsimp only [major]
    by_cases inside:u≤1/2
    · rw [indicator_of_mem (show u∈Ioc (0:ℝ) (1/2) from ⟨hu,inside⟩)]
      exact (growth N u).trans (by rw [abs_of_pos hu];nlinarith)
    · rw [indicator_of_notMem (show u∉Ioc (0:ℝ) (1/2) from fun hx=>inside hx.2),
        outside N u (by rw [abs_of_pos hu];exact lt_of_not_ge inside),norm_zero]
  · filter_upwards with u
    exact pointwise u

theorem actual_counted_pointwise_limit (sources:ℕ→ℝ→ℂ) (source:ℝ→ℂ) (B:ℝ) (nonnegative:0≤B)
    (measurable:∀N,Measurable (sources N))
    (growth:∀N x,‖sources N x‖≤B*|x|)
    (outside:∀N x,(1/2:ℝ) < |x|→sources N x=0)
    (pointwise:∀x,Tendsto (fun N:ℕ=>sources N x) atTop (𝓝 (source x)))
    (x:ℝ) (positive:0<x):
    Tendsto (fun N:ℕ=>countedImage (sources N) x) atTop (𝓝 (countedImage source x)):=by
  obtain ⟨M,bound⟩:=exists_nat_gt (x/2)
  have beyond (n:ℕ) (notin:n∉Finset.range M):(1/2:ℝ) < |((n+1:ℕ):ℝ)/x|:=by
    have index:M≤n:=Nat.le_of_not_gt (by simpa only [Finset.mem_range] using notin)
    have scaled:(M:ℝ)≤n:=by exact_mod_cast index
    rw [abs_of_nonneg (by positivity)]
    apply (lt_div_iff₀ positive).mpr
    push_cast
    linarith
  have truncate (raw:ℝ→ℂ) (out:∀t,(1/2:ℝ) < |t|→ raw t=0):
      (∑'n:ℕ,raw ((n+1:ℕ)/x))=∑n∈Finset.range M,raw ((n+1:ℕ)/x):=by
    apply tsum_eq_sum
    intro n notin
    exact out _ (beyond n notin)
  have sourceOutside (t:ℝ) (ht:(1/2:ℝ) < |t|):source t=0:=by
    exact tendsto_nhds_unique (pointwise t)
      ((tendsto_const_nhds: Tendsto (fun _:ℕ=>(0:ℂ)) atTop (𝓝 0)).congr'
        (Eventually.of_forall (fun N=>(outside N t ht).symm)))
  have sumLimit:Tendsto (fun N:ℕ=>∑n∈Finset.range M,sources N ((n+1:ℕ)/x)) atTop
      (𝓝 (∑n∈Finset.range M,source ((n+1:ℕ)/x))):=
    tendsto_finsetSum _ (fun n _=>pointwise _)
  have allLimit: Tendsto (fun N:ℕ=>(x:ℂ)⁻¹*(∑'n:ℕ,sources N ((n+1:ℕ)/x))) atTop
      (𝓝 ((x:ℂ)⁻¹*(∑'n:ℕ,source ((n+1:ℕ)/x)))):=by
    simpa only [truncate source sourceOutside] using
      (sumLimit.const_mul (x:ℂ)⁻¹).congr' (Eventually.of_forall (fun N=>by rw [truncate _ (outside N)]))
  exact allLimit.sub (actual_mass_limit sources source B nonnegative measurable growth outside pointwise)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
