import H0mework.Physics.LowEnergy.LightKernel.Source
import H0mework.Physics.SpinPair.Parameters

/-! The original g00 source selects the actual axial phase within the common
three-dimensional quadratic kernel and retains its static complement term. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
open Stage9C.Material.SpinPair
noncomputable section

def metricReader (u : ℂ) : Fin 3 → ℂ := ![0,0,-36*u/25]
def metricSource (u : ℂ) : Fin 3 → ℂ := ![0,0,36*u/25]
def metricSolution (u q : ℂ) : Fin 3 → ℂ :=
  ![0,0,729*u/(125*(125*q^2-162*u^2))]

theorem source_metric_solution (u q : ℂ) (regular : 125*q^2-162*u^2≠0) :
    core u q*ᵥmetricSolution u q=metricSource u := by
  ext i
  fin_cases i <;> simp [core,metricSolution,metricSource,axialKernel]
  have factor : 2500*q^2/81-40*u^2=(20/81 : ℂ)*(125*q^2-162*u^2) := by ring
  rw [factor]
  generalize hd : 125*q^2-162*u^2=d at *
  field_simp [regular]
  ring

theorem source_metric_orthogonal (u : ℂ) :
    dotProduct (metricReader u) (![1,0,0] : Fin 3 → ℂ)=0 ∧
    dotProduct (metricReader u) (![0,1,0] : Fin 3 → ℂ)=0 ∧
    dotProduct (metricReader u) (![0,0,1] : Fin 3 → ℂ)= -36*u/25 := by
  simp [dotProduct,Fin.sum_univ_succ,metricReader]

theorem source_axial_visible (u : ℂ) (nonzero : u≠0) :
    dotProduct (metricReader u) (![0,0,1] : Fin 3 → ℂ)≠0 := by
  rw [(source_metric_orthogonal u).2.2]
  exact div_ne_zero (mul_ne_zero (by norm_num) nonzero) (by norm_num)

def metricContact : ℂ := 18*(lapse : ℂ)/125
def metricLeading (u q : ℂ) : ℂ :=
  metricContact*(297*u^2-125*q^2)/(162*u^2-125*q^2)

theorem original_metric_response (u q : ℂ) (regular : 125*q^2-162*u^2≠0) :
    metricContact+dotProduct (metricReader u) (metricSolution u q)/(lapse : ℂ)=metricLeading u q := by
  have lapseNonzero : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  have square : (lapse : ℂ)^2=(54/125 : ℂ) := by rw [← Complex.ofReal_pow,lapse_sq]; norm_num
  simp [metricReader,metricSolution,dotProduct,Fin.sum_univ_succ]
  unfold metricLeading metricContact
  rw [show 162*u^2-125*q^2= -(125*q^2-162*u^2) by ring]
  generalize hd : 125*q^2-162*u^2=d at *
  field_simp [lapseNonzero,regular]
  rw [← hd]
  ring_nf
  simp only [square]
  ring

theorem metric_divisor_physical (u q : ℝ) :
    125*q^2-162*u^2=0 ↔ (lapse*Real.sqrt 2*u)^2=(Real.sqrt 2*q)^2/3 := by
  have sq2 : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  simp only [mul_pow,lapse_sq,sq2]
  constructor <;> intro same <;> nlinarith

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
