import H0mework.NavierStokes.WindowEnergyJoint.LowPressure

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceHalfKernel
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativeUnheatedSexticLatticePower (radical density)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem finite_norm_square {E : Type*} [NormedAddCommGroup E] (F : Finset IntegerWavevector) (a : IntegerWavevector→E) :
    ‖∑ k∈F,lp.single (2 : ℝ≥0∞) k (a k)‖^2=∑ k∈F,‖a k‖^2 := by
  have read (k : IntegerWavevector) : (∑ p∈F,lp.single (2 : ℝ≥0∞) p (a p)) k=if k∈F then a k else 0 := by
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  have normed := lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ℝ≥0∞).toReal) (∑ k∈F,lp.single (2 : ℝ≥0∞) k (a k))
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at normed
  rw [normed,tsum_eq_sum (s := F) (fun k outside => by rw [read,if_neg outside,norm_zero,zero_pow (by decide : 2≠0)])]
  exact Finset.sum_congr rfl fun k inside => by rw [read,if_pos inside]

theorem scalar_norm_square (F : Finset IntegerWavevector) (a : IntegerWavevector→ℂ) :
    ‖field (finiteSequence F a)‖^2=∑ k∈F,‖a k‖^2 := by
  rw [field,LinearIsometryEquiv.norm_map]
  exact finite_norm_square F a

def diagonal (z : ℂ) : NativeCompleteStressCarrier.Tensor :=
  NativeCompleteStressCarrier.tensor (fun output input => if output=input then z else 0)

theorem diagonal_norm (z : ℂ) : ‖diagonal z‖^2=3*‖z‖^2 := by
  rw [diagonal,NativeCompleteStressCarrier.tensor_norm_sq]
  have row (output : Coordinate) : (∑ input : Coordinate,‖if output=input then z else 0‖^2)=‖z‖^2 := by
    calc
      _=∑ input : Coordinate,if output=input then ‖z‖^2 else 0 := by
        apply Finset.sum_congr rfl
        intro input _
        split_ifs <;> simp
      _=_ := by simp
  simp only [row,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]

def test (F : Finset IntegerWavevector) (a : IntegerWavevector→ℂ) : NativeCompleteStressCarrier.Space :=
  ∑ k∈F,lp.single 2 k (radical k • diagonal (a k))

theorem test_apply (F : Finset IntegerWavevector) (a : IntegerWavevector→ℂ) (k : IntegerWavevector) (output input : Coordinate) :
    test F a k (output,input)=if k∈F then if output=input then (radical k : ℂ)*a k else 0 else 0 := by
  simp only [test,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs <;> simp [*,diagonal,NativeCompleteStressCarrier.tensor,PiLp.smul_apply,Complex.real_smul]

theorem test_read (F : Finset IntegerWavevector) (a : IntegerWavevector→ℂ) (i : Coordinate) (k : IntegerWavevector) :
    (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (field (finiteSequence F a)) k=
      (density 1 k : ℂ)*NativeWindowPressureLowSource.component (test F a) i i k := by
  rw [field,LinearIsometryEquiv.apply_symm_apply]
  change finiteSequence F a k=(density 1 k : ℂ)*test F a k (i,i)
  rw [finiteSequence_apply,test_apply,if_pos (rfl : i=i)]
  by_cases inside : k∈F
  · simp only [if_pos inside,density,pow_one,Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr (NativeUnheatedSexticLatticePower.radical_positive k).ne']
  · simp only [if_neg inside,mul_zero]

theorem radical_energy (k : IntegerWavevector) : radical k^2≤1+integerWaveViscousMultiplier k := by
  rw [NativeUnheatedSexticLatticePower.radical_square]
  have mass : 1≤NativeUnheatedSexticLatticePower.mass k := NativeUnheatedSexticLatticePower.mass_one k
  have root : Real.sqrt (NativeUnheatedSexticLatticePower.mass k)≤NativeUnheatedSexticLatticePower.mass k := by
    have square := Real.sq_sqrt (by linarith : 0≤NativeUnheatedSexticLatticePower.mass k)
    have nonnegative := Real.sqrt_nonneg (NativeUnheatedSexticLatticePower.mass k)
    nlinarith only [square,nonnegative,mass]
  have spatial := integerWaveNormSq_nonneg k
  have pi := Real.pi_gt_three
  unfold NativeUnheatedSexticLatticePower.mass integerWaveViscousMultiplier at *
  have scale : 1≤(2*Real.pi)^2 := by nlinarith only [pi,sq_nonneg (2*Real.pi-1)]
  nlinarith only [root,mul_nonneg (sub_nonneg.mpr scale) spatial]

theorem test_norm_square (F : Finset IntegerWavevector) (a : IntegerWavevector→ℂ) :
    ‖test F a‖^2≤3*(‖field (finiteSequence F a)‖^2+
      ∑ j : Coordinate,‖field (finiteJet F a j 1)‖^2) := by
  rw [test,finite_norm_square]
  simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,diagonal_norm]
  have row (k : IntegerWavevector) : radical k^2*(3*‖a k‖^2)≤(1+integerWaveViscousMultiplier k)*(3*‖a k‖^2) :=
    mul_le_mul_of_nonneg_right (radical_energy k) (by positivity)
  apply (Finset.sum_le_sum fun k _ => row k).trans_eq
  simp only [scalar_norm_square,finiteJet,scalar_norm_square,pow_one,norm_mul,mul_pow]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,NativePhysicalGradient.multiplier_sum_norm_sq,← Finset.sum_add_distrib,
    Finset.mul_sum,integerWaveViscousMultiplier]
  exact Finset.sum_congr rfl fun k _ => by ring

end
end SaturationMonoid.NavierStokes.NativeWindowTraceHalfKernel
