import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatKernel
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Leaf
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeLocalHeat
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeUnheatedSexticLatticePower NativeUnheatedStressPairEvolution
open NativeUnheatedTriadChannels NativeUnheatedTriadKernel NativeUnheatedTreeTime
noncomputable section

def cap (nu : Viscosity) : ℝ := 3/(nu.coeff*(2*Real.pi)^2)

theorem cap_positive (nu : Viscosity) : 0 < cap nu := by
  unfold cap
  positivity [nu.coeff_pos]

theorem decay_nonnegative (nu : Viscosity) (p q : IntegerWavevector) : 0 ≤ decay nu p q :=
  mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative p) (multiplier_nonnegative q))

theorem inverse_mass (nu : Viscosity) (p q : IntegerWavevector) :
    (decay nu p q)⁻¹ ≤ cap nu/(mass p+mass q) := by
  have floor0 : 0 < nu.coeff*(2*Real.pi)^2 := by positivity [nu.coeff_pos]
  have mass0 : 0 < mass p+mass q := add_pos (mass_positive p) (mass_positive q)
  by_cases nonzero : p ≠ 0 ∨ q ≠ 0
  · have lattice : 1 ≤ integerWaveNormSq p+integerWaveNormSq q := by
      rcases nonzero with left | right
      · linarith [one_le_integerWaveNormSq p left, integerWaveNormSq_nonneg q]
      · linarith [one_le_integerWaveNormSq q right, integerWaveNormSq_nonneg p]
    have lower : nu.coeff*(2*Real.pi)^2*(mass p+mass q)/3 ≤ decay nu p q := by
      have paid := mul_le_mul_of_nonneg_left (show mass p+mass q ≤
        3*(integerWaveNormSq p+integerWaveNormSq q) by unfold mass; linarith) floor0.le
      unfold decay integerWaveViscousMultiplier
      nlinarith only [paid]
    have positive : 0 < nu.coeff*(2*Real.pi)^2*(mass p+mass q)/3 := by positivity
    exact (inv_anti₀ positive lower).trans_eq (by unfold cap; field_simp)
  · push Not at nonzero
    rcases nonzero with ⟨rfl, rfl⟩
    simp only [decay, integerWaveViscousMultiplier, integerWaveNormSq, Pi.zero_apply,
      Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero,
      add_zero, inv_zero]
    exact div_nonneg (cap_positive nu).le mass0.le

theorem pressure_mass (k : IntegerWavevector) (i j output : Coordinate) :
    ‖pressure k i j output‖ ≤ (2*Real.pi)*mass k^(1/2 : ℝ) := by
  have paid := pressure_bound k i j output
  rw [integerWaveViscousMultiplier, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2*Real.pi)] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left
    ((Real.sqrt_le_sqrt (show integerWaveNormSq k ≤ mass k by unfold mass; linarith)).trans_eq
      (Real.sqrt_eq_rpow _)) (by positivity))

theorem pressure_rate_bound (nu : Viscosity) (rate : ℝ) (p q : IntegerWavevector)
    (i j output : Coordinate) (lower : decay nu p q ≤ rate) :
    ‖rate⁻¹ • pressure (p+q) i j output‖ ≤
      (cap nu*(2*Real.pi))*mass (p+q)^(1/2 : ℝ)/(mass p+mass q) := by
  by_cases nonzero : p ≠ 0 ∨ q ≠ 0
  · have floor := NativeUnheatedPairInverseKernel.decay_floor (nu := nu) p q nonzero
    have positive : 0 < decay nu p q := lt_of_lt_of_le (by positivity [nu.coeff_pos]) floor
    have inverse := (inv_anti₀ positive lower).trans (inverse_mass nu p q)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (positive.le.trans lower))]
    exact (mul_le_mul inverse (pressure_mass (p+q) i j output) (norm_nonneg _)
      (div_nonneg (cap_positive nu).le (add_pos (mass_positive p) (mass_positive q)).le)).trans_eq (by ring)
  · push Not at nonzero
    rcases nonzero with ⟨rfl, rfl⟩
    have zero : pressure 0 i j output = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [integerWaveViscousMultiplier, integerWaveNormSq, Pi.zero_apply,
        Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero,
        Real.sqrt_zero] using pressure_bound 0 i j output
    rw [add_zero, zero, smul_zero, norm_zero]
    positivity [cap_positive nu, mass_positive (0 : IntegerWavevector)]

theorem split_rate_lower {n : ℕ} (nu : Viscosity) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (i j : Coordinate) (inside : IntegerWavevector) :
    decay nu inside ((nodes leaf).1-inside) ≤
      sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf i j inside) := by
  have remainder : 0 ≤ ∑ number : Fin n, integerWaveViscousMultiplier (nodes (leaf.succAbove number)).1 :=
    Finset.sum_nonneg fun number _ => multiplier_nonnegative _
  unfold sumRate NativeUnheatedTreeLeaf.slots
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  unfold decay
  nlinarith only [mul_nonneg nu.coeff_pos.le remainder]

theorem weighted_pressure (nu : Viscosity) (rate a b : ℝ) (p q : IntegerWavevector)
    (i j output : Coordinate) (lower : decay nu p q ≤ rate) :
    mass (p+q)^((a+b-1/2)/2)*mass p^(-a/2)*mass q^(-b/2)*
      ‖rate⁻¹ • pressure (p+q) i j output‖ ≤
    (cap nu*(2*Real.pi))*NativeUnheatedTreeHeatKernel.kernel a b p q := by
  have factor0 : 0 ≤ mass (p+q)^((a+b-1/2)/2)*mass p^(-a/2)*mass q^(-b/2) := by
    positivity [mass_positive p, mass_positive q, mass_positive (p+q)]
  apply (mul_le_mul_of_nonneg_left (pressure_rate_bound nu rate p q i j output lower) factor0).trans_eq
  unfold NativeUnheatedTreeHeatKernel.kernel
  rw [show (a+b+1/2)/2 = (a+b-1/2)/2+(1/2) by ring,
    Real.rpow_add (mass_positive (p+q))]
  ring

theorem weighted_split {n : ℕ} (nu : Viscosity) (a b : ℝ) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (i j : Coordinate) (inside : IntegerWavevector) :
    mass (nodes leaf).1^((a+b-1/2)/2)*mass inside^(-a/2)*mass ((nodes leaf).1-inside)^(-b/2)*
      ‖(sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf i j inside))⁻¹ •
        pressure (nodes leaf).1 i j (nodes leaf).2‖ ≤
    (cap nu*(2*Real.pi))*NativeUnheatedTreeHeatKernel.kernel a b inside ((nodes leaf).1-inside) := by
  simpa only [add_sub_cancel] using weighted_pressure nu
    (sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf i j inside)) a b inside
    ((nodes leaf).1-inside) i j (nodes leaf).2 (split_rate_lower nu nodes leaf i j inside)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeLocalHeat
