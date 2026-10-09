import H0mework.Physics.LowEnergy.PacketField.Quadratic

/-! The primitive current quadratic form contracts the actual pole columns
before the continuous source Gram is read. All ordered growth pairs remain. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def contractedPair (current : Matrix ι ι ℝ) (columns : Bool → ι → ℂ) (first second : Bool) : ℂ :=
  ∑ row, ∑ column, (current row column : ℂ)*(starRingEnd ℂ) (columns first row)*columns second column

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem four_sum (term : ι → ι → Bool → Bool → ℂ) :
    (∑ row, ∑ column, ∑ first, ∑ second, term row column first second)=
      ∑ first, ∑ second, ∑ row, ∑ column, term row column first second := by
  simp only [Fintype.sum_bool,Finset.sum_add_distrib]

theorem complex_current_pullback (current : Matrix ι ι ℝ) (columns : Bool → ι → ℂ) (branch : Bool → E) :
    (∑ row, ∑ column, (current row column : ℂ)*
      inner ℂ (-(∑ sign, columns sign row • branch sign)) (-(∑ sign, columns sign column • branch sign)))=
      ∑ first, ∑ second, contractedPair current columns first second*inner ℂ (branch first) (branch second) := by
  calc
    _ = ∑ row, ∑ column, ∑ first, ∑ second,
        (current row column : ℂ)*(starRingEnd ℂ) (columns first row)*columns second column*
          inner ℂ (branch first) (branch second) := by
      simp only [inner_neg_left]
      simp only [inner_neg_right,neg_neg]
      simp only [sum_inner,inner_smul_left]
      simp only [inner_sum,inner_smul_right,Finset.mul_sum,mul_assoc]
    _ = ∑ first, ∑ second, ∑ row, ∑ column,
        (current row column : ℂ)*(starRingEnd ℂ) (columns first row)*columns second column*
          inner ℂ (branch first) (branch second) := four_sum _
    _ = _ := by simp only [contractedPair,Finset.sum_mul]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem quadraticDensity_pullback (current : Matrix ι ι ℝ) (columns : Bool → ι → ℂ) (branch : Bool → FullMatterL2) :
    quadraticDensity current (fun row => -(∑ sign, columns sign row • branch sign))=
      (1/2 : ℝ)*∑ first, ∑ second,
        (contractedPair current columns first second*inner ℂ (branch first) (branch second)).re := by
  unfold quadraticDensity
  congr 1
  have generated := congrArg Complex.re (complex_current_pullback current columns branch)
  simpa only [Complex.re_sum,Complex.re_ofReal_mul] using generated

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem quadraticDensity_fourGram (current : Matrix ι ι ℝ) (columns : Bool → ι → ℂ)
    (same opposite : ℝ) (sourcePairing : ∀ first second, contractedPair current columns first second=
      ((if first=second then same else opposite : ℝ) : ℂ)) (branch : Bool → FullMatterL2) :
    quadraticDensity current (fun row => -(∑ sign, columns sign row • branch sign))=fourGram same opposite branch := by
  rw [quadraticDensity_pullback]
  simp_rw [sourcePairing,Complex.re_ofReal_mul]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
