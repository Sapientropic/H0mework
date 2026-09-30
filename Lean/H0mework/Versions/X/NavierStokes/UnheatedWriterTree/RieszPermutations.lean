import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RieszKernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeRieszPermutations
open NativeUnheatedTreeRieszKernel NativeUnheatedSexticLatticePower
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
noncomputable section

def flip (L : E) : E := ⟨fun p => L (-p), memℓp_gen
  ((Equiv.neg Wave).summable_iff.mpr ((memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp (lp.memℓp L)))⟩

theorem flip_apply (L : E) (p : Wave) : flip L p = L (-p) := rfl

theorem flip_norm (L : E) : ‖flip L‖ = ‖L‖ := by
  have square (M : E) : ‖M‖^2 = ∑' p, |M p|^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) M
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [square, square]
  exact (Equiv.neg Wave).tsum_eq (fun p => |L p|^2)

theorem density_neg (n : ℕ) (p : Wave) : density n (-p) = density n p := by
  simp only [density, radical, mass, integerWaveNormSq, Pi.neg_apply, Int.cast_neg, neg_sq]

def outputEquiv : (Wave × Wave) ≃ (Wave × Wave) where
  toFun index := (index.1+index.2,index.1)
  invFun index := (index.2,index.1-index.2)
  left_inv index := by ext <;> simp
  right_inv index := by ext <;> simp

def firstEquiv : (Wave × Wave) ≃ (Wave × Wave) where
  toFun index := (index.1,-index.2)
  invFun index := (index.1,-index.2)
  left_inv index := by ext <;> simp
  right_inv index := by ext <;> simp

def secondEquiv : (Wave × Wave) ≃ (Wave × Wave) where
  toFun index := (index.2,-index.1)
  invFun index := (-index.2,index.1)
  left_inv index := by ext <;> simp
  right_inv index := by ext <;> simp

def outputTerm (L M T : E) (index : Wave × Wave) : ℝ :=
  radical (index.1+index.2)*density 2 index.1*density 2 index.2 *
    |L index.1| * |M index.2| * |T (index.1+index.2)|

def firstTerm (L M T : E) (index : Wave × Wave) : ℝ :=
  radical index.1*density 2 index.2*density 2 (index.1+index.2) *
    |L index.1| * |M index.2| * |T (index.1+index.2)|

def secondTerm (L M T : E) (index : Wave × Wave) : ℝ :=
  radical index.2*density 2 index.1*density 2 (index.1+index.2) *
    |L index.1| * |M index.2| * |T (index.1+index.2)|

theorem output_recognition (L M T : E) (index : Wave × Wave) :
    outputTerm L M T index = term L M T (outputEquiv index) := by
  simp only [outputTerm, term, kernel, outputEquiv, Equiv.coe_fn_mk, add_sub_cancel_left]

theorem first_recognition (L M T : E) (index : Wave × Wave) :
    firstTerm L M T index = term (flip M) T L (firstEquiv index) := by
  simp only [firstTerm, term, kernel, firstEquiv, Equiv.coe_fn_mk, density_neg, sub_neg_eq_add,
    flip_apply, neg_neg]
  ring

theorem second_recognition (L M T : E) (index : Wave × Wave) :
    secondTerm L M T index = term (flip L) T M (secondEquiv index) := by
  simp only [secondTerm, term, kernel, secondEquiv, Equiv.coe_fn_mk, density_neg, sub_neg_eq_add,
    flip_apply, neg_neg, add_comm index.2 index.1]
  ring

theorem output_summable (L M T : E) : Summable (outputTerm L M T) := by
  change Summable (fun index => outputTerm L M T index)
  simp_rw [output_recognition]
  exact outputEquiv.summable_iff.mpr (summable L M T)

theorem first_summable (L M T : E) : Summable (firstTerm L M T) := by
  change Summable (fun index => firstTerm L M T index)
  simp_rw [first_recognition]
  exact firstEquiv.summable_iff.mpr (summable (flip M) T L)

theorem second_summable (L M T : E) : Summable (secondTerm L M T) := by
  change Summable (fun index => secondTerm L M T index)
  simp_rw [second_recognition]
  exact secondEquiv.summable_iff.mpr (summable (flip L) T M)

theorem output_bound (L M T : E) : (∑' index, outputTerm L M T index) ≤
    Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by
  simp_rw [output_recognition]
  rw [outputEquiv.tsum_eq]
  exact bound L M T

theorem first_bound (L M T : E) : (∑' index, firstTerm L M T index) ≤
    Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by
  simp_rw [first_recognition]
  rw [firstEquiv.tsum_eq]
  exact (bound (flip M) T L).trans_eq (by rw [flip_norm]; ring)

theorem second_bound (L M T : E) : (∑' index, secondTerm L M T index) ≤
    Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by
  simp_rw [second_recognition]
  rw [secondEquiv.tsum_eq]
  exact (bound (flip L) T M).trans_eq (by rw [flip_norm]; ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeRieszPermutations
