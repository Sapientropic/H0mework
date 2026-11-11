import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletRate
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.CoefficientJet
open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

/-- Positive arithmetic cutoff, independent of the physical-B approximation radius. -/
def finite (N:ℕ) (s:ℂ) : ℂ := FiniteForcing.coefficient s (N+1)
def jet (j N:ℕ) (s:ℂ) : ℂ := iteratedDeriv j (finite N) s
def zetaJet (j:ℕ) (s:ℂ) : ℂ := iteratedDeriv j riemannZeta s
def domain : Set ℂ := {s | 0<s.re ∧ s≠1}
theorem domain_open : IsOpen domain := by
  change IsOpen ({s:ℂ | 0<s.re} ∩ ({1}:Set ℂ)ᶜ)
  exact (isOpen_lt continuous_const continuous_re).inter isClosed_singleton.isOpen_compl

private theorem power_analytic (b:ℂ) (nonzero:b≠0) (s:ℂ) : AnalyticAt ℂ (fun z:ℂ=>b^(-z)) s := by
  simp only [Complex.cpow_def_of_ne_zero nonzero]
  fun_prop
private theorem numerator_analytic (N:ℕ) (s:ℂ) : AnalyticAt ℂ (fun z:ℂ=>((N+1:ℕ):ℂ)^(1-z)) s := by
  have nonzero:((N+1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  simp only [Complex.cpow_def_of_ne_zero nonzero]
  fun_prop
private theorem inverse_analytic (s:ℂ) (notOne:s≠1) : AnalyticAt ℂ (fun z:ℂ=>1/(1-z)) s :=
  analyticAt_const.div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr notOne.symm)

theorem finite_analytic (N:ℕ) : AnalyticOnNhd ℂ (finite N) domain := by
  intro s inside
  unfold finite FiniteForcing.coefficient
  apply AnalyticAt.sub
  · apply Finset.analyticAt_fun_sum
    intro n member
    apply power_analytic
    exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0<1) (Finset.mem_Ico.mp member).1))
  · exact (numerator_analytic N s).div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr inside.2.symm)

private theorem uniform_bound (a M:ℝ) (positive:0<a) (nonnegative:0≤M)
    (s:ℂ) (realBound:a≤s.re) (normBound:‖s‖≤M) (notOne:s≠1) (N:ℕ) :
    ‖finite N s-riemannZeta s‖≤(1+M/a)*((N+1:ℕ):ℝ)^(-a) := by
  have source:=DirichletRate.coefficient_error_bound s (positive.trans_le realBound) notOne (N+1) (by omega)
  have frac:‖s‖/s.re≤M/a :=
    (div_le_div_of_nonneg_right normBound (positive.trans_le realBound).le).trans
      (div_le_div_of_nonneg_left nonnegative positive realBound)
  have powers:((N+1:ℕ):ℝ)^(-s.re)≤((N+1:ℕ):ℝ)^(-a) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)) (neg_le_neg realBound)
  have constant:DirichletRate.constant s≤1+M/a := by unfold DirichletRate.constant; linarith
  exact source.trans ((mul_le_mul_of_nonneg_right constant (Real.rpow_nonneg (by positivity) _)).trans
    (mul_le_mul_of_nonneg_left powers (by positivity)))

theorem uniformly_on_bound (a M:ℝ) (positive:0<a) (nonnegative:0≤M) (region:Set ℂ)
    (realBound:∀s∈region,a≤s.re) (normBound:∀s∈region,‖s‖≤M) (notOne:∀s∈region,s≠1) :
    TendstoUniformlyOn finite riemannZeta atTop region := by
  have indices:Tendsto (fun N:ℕ=>((N+1:ℕ):ℝ)) atTop atTop :=
    by simpa only [Function.comp_def] using (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have decay:Tendsto (fun N:ℕ=>(1+M/a)*((N+1:ℕ):ℝ)^(-a)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop positive).comp indices).const_mul (1+M/a)
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon epsilonPositive
  filter_upwards [decay.eventually (gt_mem_nhds epsilonPositive)] with N small
  intro s inside
  rw [dist_eq_norm,norm_sub_rev]
  exact (uniform_bound a M positive nonnegative s (realBound s inside) (normBound s inside) (notOne s inside) N).trans_lt small

/-- This uses the already-paid Abel bound on Re s>0, not a Re s>1 series argument. -/
theorem locally_uniform : TendstoLocallyUniformlyOn finite riemannZeta atTop domain := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro s inside
  let radius:ℝ:=min (s.re/2) 1
  have radiusPositive:0<radius := lt_min (by linarith [inside.1]) (by norm_num)
  let region:Set ℂ:=domain ∩ Metric.ball s radius
  refine ⟨region,inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Metric.ball_mem_nhds s radiusPositive)),?_⟩
  apply uniformly_on_bound (s.re/2) (‖s‖+1) (by linarith [inside.1]) (by positivity)
  · intro z belongs
    have close:‖z-s‖<radius:=by simpa only [Metric.mem_ball,dist_eq_norm] using belongs.2
    have realClose:=abs_le.mp (Complex.abs_re_le_norm (z-s))
    have bound:radius≤s.re/2:=min_le_left _ _
    simp only [Complex.sub_re] at realClose
    linarith
  · intro z belongs
    have close:‖z-s‖<radius:=by simpa only [Metric.mem_ball,dist_eq_norm] using belongs.2
    have bound:radius≤1:=min_le_right _ _
    calc
      ‖z‖=‖(z-s)+s‖:=by congr 1; abel
      _≤‖z-s‖+‖s‖:=norm_add_le _ _
      _≤‖s‖+1:=by linarith
  · intro z belongs
    exact belongs.1.2

/-- Every observer derivative converges locally uniformly on the actual strip domain. -/
theorem jets_locally_uniform (j:ℕ) : TendstoLocallyUniformlyOn (jet j) (zetaJet j) atTop domain := by
  induction j with
  | zero => exact locally_uniform
  | succ j previous =>
    have analytic:∀ᶠN:ℕ in atTop,DifferentiableOn ℂ (jet j N) domain := by
      filter_upwards with N
      change DifferentiableOn ℂ (iteratedDeriv j (finite N)) domain
      simpa only [iteratedDeriv_eq_iterate] using ((finite_analytic N).iterated_deriv j).differentiableOn
    have derived:=previous.deriv analytic domain_open
    change TendstoLocallyUniformlyOn (fun N=>iteratedDeriv (j+1) (finite N)) (iteratedDeriv (j+1) riemannZeta) atTop domain
    simp only [iteratedDeriv_succ]
    change TendstoLocallyUniformlyOn
      (fun N=>deriv (iteratedDeriv j (finite N)))
      (deriv (iteratedDeriv j riemannZeta)) atTop domain at derived
    exact derived

theorem jet_tendsto (s:ℂ) (positive:0<s.re) (notOne:s≠1) (j:ℕ) :
    Tendsto (fun N=>jet j N s) atTop (𝓝 (zetaJet j s)) :=
  (jets_locally_uniform j).tendsto_at ⟨positive,notOne⟩
run_cmd IO.eprintln "coefficient jet: legitimate strip all-order source limits complete"

private theorem power_jet (b:ℂ) (nonzero:b≠0) (s:ℂ) (j:ℕ) :
    iteratedDeriv j (fun z:ℂ=>b^(-z)) s=(-Complex.log b)^j*b^(-s) := by
  have expression:(fun z:ℂ=>b^(-z))=fun z=>Complex.exp ((-Complex.log b)*z) := by
    ext z
    rw [Complex.cpow_def_of_ne_zero nonzero]
    congr 1
    ring
  rw [expression,iteratedDeriv_cexp_const_mul]
  rw [Complex.cpow_def_of_ne_zero nonzero]
  change (-Complex.log b)^j * Complex.exp ((-Complex.log b)*s) =
    (-Complex.log b)^j * Complex.exp (Complex.log b*(-s))
  rw [show (-Complex.log b)*s=Complex.log b*(-s) by ring]
private theorem inverse_jet (s:ℂ) (notOne:s≠1) (j:ℕ) :
    iteratedDeriv j (fun z:ℂ=>1/(1-z)) s=(j.factorial:ℂ)/(1-s)^(j+1) := by
  induction j generalizing s with
  | zero => simp
  | succ j previous =>
    have near:(iteratedDeriv j (fun z:ℂ=>1/(1-z)))=ᶠ[𝓝 s]
        (fun z:ℂ=>(j.factorial:ℂ)/(1-z)^(j+1)) := by
      filter_upwards [eventually_ne_nhds notOne] with z apart
      exact previous z apart
    rw [iteratedDeriv_succ,near.deriv_eq]
    have source:=((((hasDerivAt_id s).const_sub (1:ℂ)).pow (j+1)).inv
      (pow_ne_zero _ (sub_ne_zero.mpr notOne.symm))).const_mul (j.factorial:ℂ)
    have paid : HasDerivAt (fun z:ℂ=>(j.factorial:ℂ)*((1-z)^(j+1))⁻¹)
        ((j.factorial:ℂ)*(-((j+1:ℂ)*(1-s)^j*(-1))/((1-s)^(j+1))^2)) s := by
      simpa only [Pi.inv_apply,Pi.pow_apply,id_eq,Nat.add_sub_cancel_right,Nat.cast_add,Nat.cast_one] using source
    have expression : (fun z:ℂ=>(j.factorial:ℂ)/(1-z)^(j+1)) =
        (fun z:ℂ=>(j.factorial:ℂ)*((1-z)^(j+1))⁻¹) := by
      funext z
      exact div_eq_mul_inv _ _
    rw [expression,paid.deriv,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp [sub_ne_zero.mpr notOne.symm]
    ring

/-- All counterterm derivatives are source data; none is silently discarded at a zero. -/
def normalizationJet (s:ℂ) (j N:ℕ) : ℂ :=
  ((N+1:ℕ):ℂ)^(1-s)*∑i∈Finset.range (j+1),(j.choose i:ℂ)*(-Complex.log ((N+1:ℕ):ℂ))^i*
    ((j-i).factorial:ℂ)/(1-s)^(j-i+1)
def rawJet (s:ℂ) (j N:ℕ) : ℂ :=
  (∑n∈Finset.Ico 1 (N+1),(-Complex.log (n:ℂ))^j*(n:ℂ)^(-s))-normalizationJet s j N

private theorem numerator_jet (N:ℕ) (s:ℂ) (j:ℕ) :
    iteratedDeriv j (fun z:ℂ=>((N+1:ℕ):ℂ)^(1-z)) s=
      (-Complex.log ((N+1:ℕ):ℂ))^j*((N+1:ℕ):ℂ)^(1-s) := by
  have nonzero:((N+1:ℕ):ℂ)≠0:=by exact_mod_cast Nat.succ_ne_zero N
  have source:(fun z:ℂ=>((N+1:ℕ):ℂ)^(1-z))=fun z=>((N+1:ℕ):ℂ)*((N+1:ℕ):ℂ)^(-z) := by
    ext z
    rw [show 1-z=1+(-z) by ring,Complex.cpow_add _ _ nonzero,Complex.cpow_one]
  rw [source,iteratedDeriv_const_mul_field,power_jet _ nonzero]
  rw [show 1-s=1+(-s) by ring,Complex.cpow_add _ _ nonzero,Complex.cpow_one]
  ring

theorem normalization_source (s:ℂ) (notOne:s≠1) (j N:ℕ) :
    iteratedDeriv j (fun z:ℂ=>((N+1:ℕ):ℂ)^(1-z)/(1-z)) s=normalizationJet s j N := by
  have product:(fun z:ℂ=>((N+1:ℕ):ℂ)^(1-z)/(1-z))=
      fun z=>((N+1:ℕ):ℂ)^(1-z)*(1/(1-z)) := by ext z; simp only [div_eq_mul_inv,one_mul]
  rw [product,iteratedDeriv_fun_mul (numerator_analytic N s).contDiffAt (inverse_analytic s notOne).contDiffAt]
  unfold normalizationJet
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i member
  rw [numerator_jet,inverse_jet s notOne]
  ring

theorem jet_source (s:ℂ) (notOne:s≠1) (j N:ℕ) : jet j N s=rawJet s j N := by
  unfold jet finite FiniteForcing.coefficient rawJet
  rw [iteratedDeriv_fun_sub]
  · rw [iteratedDeriv_fun_sum,normalization_source s notOne]
    · congr 1
      apply Finset.sum_congr rfl
      intro n member
      exact power_jet _ (by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide:0<1) (Finset.mem_Ico.mp member).1))) s j
    · intro n member
      exact (power_analytic _ (by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide:0<1) (Finset.mem_Ico.mp member).1))) s).contDiffAt
  · apply ContDiffAt.sum
    intro n member
    exact (power_analytic _ (by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide:0<1) (Finset.mem_Ico.mp member).1))) s).contDiffAt
  · exact ((numerator_analytic N s).div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr notOne.symm)).contDiffAt
run_cmd IO.eprintln "coefficient jet: literal finite sum and full normalization jet complete"
end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.CoefficientJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env=>Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CountedSchur.CoefficientJet"
