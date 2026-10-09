import H0mework.Physics.LowEnergy.BosonCausal.Pair
import H0mework.Physics.SpinPair.Parameters

/-! Original physical-time coefficients, obtained from the source g00 numerator.
The contact acts on the current source value, separately from the half-axis integral. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open MeasureTheory
noncomputable section

def oscillation : ℝ := 18*Real.sqrt 10/25
def growth : ℝ := 5*Real.sqrt 6/3
def contact : ℂ := -36*(Real.sqrt 30 : ℂ)/625
def oscillationWeight : ℂ := -5832*(Real.sqrt 30 : ℂ)/390625
def growthWeight : ℂ := -192*(Real.sqrt 30 : ℂ)/125

def memory (time : ℝ) : ℂ :=
  oscillationWeight*pairKernel (Complex.I*(oscillation : ℂ)) time+
    growthWeight*pairKernel (growth : ℂ) time

def originalRational (parameter : ℂ) : ℂ :=
  -108*(Real.sqrt 30 : ℂ)*(625*parameter^4+9652*parameter^2+29700)/
    (3125*(3*parameter^2-50)*(125*parameter^2+648))

theorem oscillation_positive : 0<oscillation := by unfold oscillation; positivity
theorem growth_positive : 0<growth := by unfold growth; positivity

theorem oscillation_squared : oscillation^2=(648/125 : ℝ) := by
  norm_num [oscillation,mul_pow,div_pow,Real.sq_sqrt]

theorem growth_squared : growth^2=(50/3 : ℝ) := by
  norm_num [growth,mul_pow,div_pow,Real.sq_sqrt]

theorem source_memory_shape (time : ℝ) : memory time=
    oscillationWeight*(Complex.sin ((oscillation : ℂ)*(time : ℂ))/(oscillation : ℂ))+
      growthWeight*(Complex.sinh ((growth : ℂ)*(time : ℂ))/(growth : ℂ)) := by
  rw [memory,pair_oscillatory,pair_hyperbolic]

theorem source_memory_integrable (energy damping : ℝ) (beyondGrowth : growth<damping) :
    IntegrableOn (fun t => weight energy damping t*memory t) (Set.Ioi 0) := by
  have positive : 0<damping := lt_trans growth_positive beyondGrowth
  have oscillatory := pair_integrable (Complex.I*(oscillation : ℂ)) energy damping (by simpa using positive) (by simpa using positive)
  have growing := pair_integrable (growth : ℂ) energy damping (by simpa using beyondGrowth)
    (by simp only [Complex.neg_re,Complex.ofReal_re]; linarith [growth_positive])
  have generated := (oscillatory.const_mul oscillationWeight).add (growing.const_mul growthWeight)
  have same (t : ℝ) : weight energy damping t*memory t=
      oscillationWeight*(weight energy damping t*pairKernel (Complex.I*(oscillation : ℂ)) t)+
      growthWeight*(weight energy damping t*pairKernel (growth : ℂ) t) := by unfold memory; ring
  change Integrable (fun t => oscillationWeight*(weight energy damping t*pairKernel (Complex.I*(oscillation : ℂ)) t)+growthWeight*(weight energy damping t*pairKernel (growth : ℂ) t)) _ at generated
  change Integrable (fun t => weight energy damping t*memory t) _
  convert generated using 1
  funext t
  exact same t

theorem rational_partial_fraction (parameter : ℂ)
    (oscillatory : 125*parameter^2+648≠0) (growing : 3*parameter^2-50≠0) :
    contact+oscillationWeight/(parameter^2+(648/125 : ℂ))+growthWeight/(parameter^2-(50/3 : ℂ))=
      originalRational parameter := by
  have first : parameter^2+(648/125 : ℂ)≠0 := by
    intro zero
    apply oscillatory
    linear_combination 125*zero
  have second : parameter^2-(50/3 : ℂ)≠0 := by
    intro zero
    apply growing
    linear_combination 3*zero
  unfold contact oscillationWeight growthWeight originalRational
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) growing) oscillatory)).mpr
  rw [show 3*parameter^2-50=3*(parameter^2-(50/3 : ℂ)) by ring,
    show 125*parameter^2+648=125*(parameter^2+(648/125 : ℂ)) by ring]
  field_simp [first, second]
  have normalizedFirst : (648 : ℂ)+parameter^2*125≠0 := by simpa only [add_comm,mul_comm] using oscillatory
  have normalizedSecond : (-50 : ℂ)+parameter^2*3≠0 := by simpa only [sub_eq_add_neg,add_comm,mul_comm] using growing
  ring_nf
  field_simp [normalizedFirst,normalizedSecond]
  ring

private theorem quadratic_nonzero (rate : ℂ) (energy damping : ℝ)
    (plus : rate.re<damping) (minus : (-rate).re<damping) :
    (laplaceParameter energy damping)^2-rate^2≠0 := by
  have left : laplaceParameter energy damping-rate≠0 := by
    intro same
    have real := congrArg Complex.re same
    simp [laplaceParameter] at real
    linarith
  have right : laplaceParameter energy damping+rate≠0 := by
    intro same
    have real := congrArg Complex.re same
    simp [laplaceParameter] at real
    simp only [Complex.neg_re] at minus
    linarith
  rw [show (laplaceParameter energy damping)^2-rate^2=
    (laplaceParameter energy damping-rate)*(laplaceParameter energy damping+rate) by ring]
  exact mul_ne_zero left right

theorem source_causal_transform (energy damping : ℝ) (beyondGrowth : growth<damping) :
    contact+(∫ t : ℝ in Set.Ioi 0, weight energy damping t*memory t)=
      originalRational (laplaceParameter energy damping) := by
  have positive : 0<damping := lt_trans growth_positive beyondGrowth
  have op : (Complex.I*(oscillation : ℂ)).re<damping := by simpa using positive
  have om : (-(Complex.I*(oscillation : ℂ))).re<damping := by simpa using positive
  have gp : (growth : ℂ).re<damping := beyondGrowth
  have gm : (-(growth : ℂ)).re<damping := by simp only [Complex.neg_re,Complex.ofReal_re]; linarith [growth_positive]
  have onz : Complex.I*(oscillation : ℂ)≠0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr oscillation_positive.ne')
  have gnz : (growth : ℂ)≠0 := Complex.ofReal_ne_zero.mpr growth_positive.ne'
  have same (t : ℝ) : weight energy damping t*memory t=
      oscillationWeight*(weight energy damping t*pairKernel (Complex.I*(oscillation : ℂ)) t)+
      growthWeight*(weight energy damping t*pairKernel (growth : ℂ) t) := by unfold memory; ring
  simp_rw [same]
  rw [integral_add ((pair_integrable _ _ _ op om).const_mul _)
    ((pair_integrable _ _ _ gp gm).const_mul _),integral_const_mul,integral_const_mul,
    pair_transform _ onz _ _ op om,pair_transform _ gnz _ _ gp gm]
  have os : (Complex.I*(oscillation : ℂ))^2= -(648/125 : ℂ) := by
    rw [mul_pow,Complex.I_sq,← Complex.ofReal_pow,oscillation_squared]
    norm_num
  have gs : (growth : ℂ)^2=(50/3 : ℂ) := by rw [← Complex.ofReal_pow,growth_squared]; norm_num
  have q1 := quadratic_nonzero (Complex.I*(oscillation : ℂ)) energy damping op om
  have q2 := quadratic_nonzero (growth : ℂ) energy damping gp gm
  rw [os,sub_neg_eq_add] at q1 ⊢
  rw [gs] at q2 ⊢
  have d1 : 125*(laplaceParameter energy damping)^2+648≠0 := by
    intro same
    apply q1
    linear_combination same/125
  have d2 : 3*(laplaceParameter energy damping)^2-50≠0 := by
    intro same
    apply q2
    linear_combination same/3
  simpa only [div_eq_mul_inv,add_assoc] using rational_partial_fraction _ d1 d2

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
