import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Bounds and derivatives are generated from the finite original polynomial
coefficients; root locations and eigenvectors are not inputs. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
noncomputable section

structure Term where
  rPower : ℕ
  wPower : ℕ
  coefficient : ℝ

def value : List Term → ℝ → ℝ → ℝ
  | [],_,_ => 0
  | x::xs,r,w => x.coefficient*r^x.rPower*w^x.wPower+value xs r w

def differentiate : List Term → List Term
  | [] => []
  | x::xs => ⟨x.rPower-1,x.wPower,x.coefficient*x.rPower⟩::differentiate xs

def coefficientBound : List Term → ℝ
  | [] => 0
  | x::xs => |x.coefficient| *2^x.rPower+coefficientBound xs

theorem coefficientBound_nonnegative (terms : List Term) : 0≤coefficientBound terms := by
  induction terms with
  | nil => rfl
  | cons x xs ih => simp only [coefficientBound]; positivity

theorem value_bound (terms : List Term) (r w : ℝ) (hr : |r|≤2) (hw : |w|≤1) :
    |value terms r w|≤coefficientBound terms := by
  induction terms with
  | nil => simp [value,coefficientBound]
  | cons x xs ih =>
    have rp : |r|^x.rPower≤2^x.rPower := pow_le_pow_left₀ (abs_nonneg _) hr _
    have wp : |w|^x.wPower≤1 := by simpa using pow_le_pow_left₀ (abs_nonneg _) hw x.wPower
    calc
      _ ≤ |x.coefficient*r^x.rPower*w^x.wPower|+|value xs r w| := abs_add_le _ _
      _ ≤ |x.coefficient| *2^x.rPower+coefficientBound xs := by
        rw [abs_mul,abs_mul,abs_pow,abs_pow]
        have product : |x.coefficient| * |r|^x.rPower*|w|^x.wPower≤|x.coefficient| * 2^x.rPower*1 := by
          gcongr
        simpa only [mul_one] using add_le_add product ih
      _ = _ := rfl

theorem value_continuous (terms : List Term) : Continuous (fun p : ℝ×ℝ => value terms p.1 p.2) := by
  induction terms with
  | nil => exact continuous_const
  | cons x xs ih => simp only [value]; fun_prop

theorem value_derivative (terms : List Term) (r w : ℝ) :
    HasDerivAt (fun x => value terms x w) (value (differentiate terms) r w) r := by
  induction terms with
  | nil => simpa only [value,differentiate] using hasDerivAt_const r (0 : ℝ)
  | cons x xs ih =>
    have generated := ((((hasDerivAt_id r).pow x.rPower).const_mul x.coefficient).mul_const (w^x.wPower)).add ih
    convert! generated using 1
    simp only [differentiate,value,id_eq]
    ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
