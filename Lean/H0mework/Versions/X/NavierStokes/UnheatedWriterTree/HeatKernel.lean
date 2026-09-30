import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RieszControl

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatKernel
open NativeUnheatedSexticLatticePower NativeUnheatedTreeRieszKernel
noncomputable section

def kernel (a b : ℝ) (p q : Wave) : ℝ :=
  mass (p+q)^((a+b+1/2)/2)*mass p^(-a/2)*mass q^(-b/2)/(mass p+mass q)

theorem kernel_nonnegative (a b : ℝ) (p q : Wave) : 0 ≤ kernel a b p q := by
  unfold kernel
  positivity [mass_positive p, mass_positive q, mass_positive (p+q)]

theorem mass_add (p q : Wave) : mass (p+q) ≤ 2*(mass p+mass q) := by
  unfold mass
  linarith [NativeUnheatedRieszKernel.norm_square_add p q]

theorem numerator_factor (a b : ℝ) (p q : Wave) :
    mass (p+q)^((a+b+1/2)/2)*mass p^(-a/2)*mass q^(-b/2) =
    (mass (p+q)^((a+b+1)/2)*mass p^((1-2*a)/4)*mass q^((1-2*b)/4))*
      (density 1 p*density 1 q*density 1 (p+q)) := by
  simp only [density_rpow, Nat.cast_one]
  calc
    _ = mass (p+q)^(((a+b+1)/2)+(-1/4))*
        mass p^(((1-2*a)/4)+(-1/4))*mass q^(((1-2*b)/4)+(-1/4)) := by
      rw [show (a+b+1)/2+(-1/4) = (a+b+1/2)/2 by ring,
        show (1-2*a)/4+(-1/4) = -a/2 by ring,
        show (1-2*b)/4+(-1/4) = -b/2 by ring]
    _ = _ := by
      rw [Real.rpow_add (mass_positive (p+q)), Real.rpow_add (mass_positive p),
        Real.rpow_add (mass_positive q)]
      ring

theorem kernel_bound (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2)
    (total : -1 ≤ a+b) (p q : Wave) :
    kernel a b p q ≤ 2*(density 1 p*density 1 q*density 1 (p+q)) := by
  have positive : 0 < mass p+mass q := add_pos (mass_positive p) (mass_positive q)
  have parent := Real.rpow_le_rpow (mass_positive (p+q)).le (mass_add p q)
    (show 0 ≤ (a+b+1)/2 by linarith)
  have left := Real.rpow_le_rpow (mass_positive p).le
    (show mass p ≤ 2*(mass p+mass q) by linarith [mass_positive p, mass_positive q])
    (show 0 ≤ (1-2*a)/4 by linarith)
  have right := Real.rpow_le_rpow (mass_positive q).le
    (show mass q ≤ 2*(mass p+mass q) by linarith [mass_positive p, mass_positive q])
    (show 0 ≤ (1-2*b)/4 by linarith)
  have paid := mul_le_mul (mul_le_mul parent left
    (Real.rpow_pos_of_pos (mass_positive p) _).le
    (Real.rpow_pos_of_pos (by positivity : 0 < 2*(mass p+mass q)) _).le) right
    (Real.rpow_pos_of_pos (mass_positive q) _).le
    (by positivity : 0 ≤ (2*(mass p+mass q))^((a+b+1)/2)*(2*(mass p+mass q))^((1-2*a)/4))
  rw [← Real.rpow_add (by positivity : 0 < 2*(mass p+mass q)),
    ← Real.rpow_add (by positivity : 0 < 2*(mass p+mass q)),
    show ((a+b+1)/2+(1-2*a)/4)+(1-2*b)/4 = 1 by ring,
    Real.rpow_one] at paid
  unfold kernel
  apply (div_le_iff₀ positive).mpr
  rw [numerator_factor]
  have density0 : 0 ≤ density 1 p*density 1 q*density 1 (p+q) :=
    mul_nonneg (mul_nonneg (density_positive 1 p).le (density_positive 1 q).le)
      (density_positive 1 (p+q)).le
  exact (mul_le_mul_of_nonneg_right paid density0).trans_eq (by ring)

def term (a b : ℝ) (L M T : E) (index : Wave × Wave) : ℝ :=
  kernel a b index.1 index.2 * |L index.1| * |M index.2| * |T (index.1+index.2)|

theorem term_nonnegative (a b : ℝ) (L M T : E) (index : Wave × Wave) :
    0 ≤ term a b L M T index := by
  unfold term
  positivity [kernel_nonnegative a b index.1 index.2]

theorem term_bound (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2)
    (total : -1 ≤ a+b) (L M T : E) (index : Wave × Wave) :
    term a b L M T index ≤ 2*NativeUnheatedTreeRiesz.term L M T index := by
  have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (kernel_bound a b first last total index.1 index.2)
      (abs_nonneg (L index.1))) (abs_nonneg (M index.2))) (abs_nonneg (T (index.1+index.2)))
  exact paid.trans_eq (by unfold NativeUnheatedTreeRiesz.term; ring)

theorem summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2)
    (total : -1 ≤ a+b) (L M T : E) : Summable (term a b L M T) :=
  ((NativeUnheatedTreeRiesz.summable L M T).mul_left 2).of_nonneg_of_le
    (term_nonnegative a b L M T) (term_bound a b first last total L M T)

theorem bound (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2)
    (total : -1 ≤ a+b) (L M T : E) : (∑' index, term a b L M T index) ≤
    6*Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by
  have paid := (summable a b first last total L M T).tsum_le_tsum
    (term_bound a b first last total L M T) ((NativeUnheatedTreeRiesz.summable L M T).mul_left 2)
  rw [tsum_mul_left] at paid
  exact paid.trans ((mul_le_mul_of_nonneg_left (NativeUnheatedTreeRiesz.bound L M T)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatKernel
