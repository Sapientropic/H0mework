import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.LAlanineMolecularControl.Scratch.LAlanineSpatialControl.TranslationRemainder
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.SpatialControl
open BasinRefinement SourceGaussianModel MeasureTheory Asymptotics Filter
open scoped Topology
noncomputable section

abbrev RealField := Lp ℝ 2 (volume : Measure Point)

theorem shifted_field_zero (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) : shiftedField terms positive jet 0=baseField terms positive jet := by
  unfold shiftedField baseField
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x => by simp

theorem directional_memLp (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) : MemLp (directional terms jet d) 2 volume := by
  have each (k : Fin 3) : MemLp (fun x : Point => d k*orbital terms (raise jet k) x) 2 volume := by
    simpa only [Pi.smul_apply,smul_eq_mul] using! (base_memLp terms positive (raise jet k)).const_smul (d k)
  simpa only [directional,Pi.neg_apply] using! (memLp_finsetSum Finset.univ (fun k _ => each k)).neg

theorem directional_toLp (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) :
    (directional_memLp terms positive jet d).toLp (directional terms jet d)=
      -(∑ k : Fin 3, d k • baseField terms positive (raise jet k)) := by
  have h0 := (base_memLp terms positive (raise jet 0)).const_smul (d 0)
  have h1 := (base_memLp terms positive (raise jet 1)).const_smul (d 1)
  have h2 := (base_memLp terms positive (raise jet 2)).const_smul (d 2)
  calc
    _ = ((h0.add h1).add h2).neg.toLp
        (-(((d 0) • orbital terms (raise jet 0)+(d 1) • orbital terms (raise jet 1))+
          (d 2) • orbital terms (raise jet 2))) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall fun x => by
        simp only [directional,Fin.sum_univ_three,Pi.neg_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    _ = _ := by
      rw [MemLp.toLp_neg ((h0.add h1).add h2),MemLp.toLp_add (h0.add h1) h2,MemLp.toLp_add h0 h1,
        MemLp.toLp_const_smul (d 0) (base_memLp terms positive (raise jet 0)),
        MemLp.toLp_const_smul (d 1) (base_memLp terms positive (raise jet 1)),
        MemLp.toLp_const_smul (d 2) (base_memLp terms positive (raise jet 2))]
      simp only [Fin.sum_univ_three,baseField]

/-- The derivative uses the same shifted raised Gaussian jets as the mother field. -/
def translationDerivative (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (a : Point) : Point →L[ℝ] RealField :=
  -(∑ k : Fin 3, (ContinuousLinearMap.proj k : Point →L[ℝ] ℝ).smulRight
    (shiftedField terms positive (raise jet k) a))

theorem translation_derivative_apply (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (a v : Point) :
    translationDerivative terms positive jet a v=
      -(∑ k : Fin 3, v k • shiftedField terms positive (raise jet k) a) := by
  simp only [translationDerivative,neg_apply,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

theorem translation_remainder_field_square (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (d : Point) :
    ‖shiftedField terms positive jet d-baseField terms positive jet-
      translationDerivative terms positive jet 0 d‖^2 ≤
      (∑ k : Fin 3, (d k)^2)^2*curvatureEnergy terms jet := by
  rw [translation_derivative_apply]
  simp_rw [shifted_field_zero]
  rw [← directional_toLp]
  unfold shiftedField baseField
  rw [← MemLp.toLp_sub,← MemLp.toLp_sub,real_field_norm_sq]
  exact translation_remainder_square_bound terms positive jet d

theorem point_square_bound (d : Point) : (∑ k : Fin 3, (d k)^2) ≤ 3*‖d‖^2 := by
  calc
    _ ≤ ∑ _k : Fin 3, ‖d‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Real.norm_eq_abs,sq_abs] using
        pow_le_pow_left₀ (norm_nonneg (d k)) (norm_le_pi_norm d k) 2
    _ = _ := by simp

theorem translation_remainder_field_norm (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (d : Point) :
    ‖shiftedField terms positive jet d-baseField terms positive jet-
      translationDerivative terms positive jet 0 d‖ ≤ 3*Real.sqrt (curvatureEnergy terms jet)*‖d‖^2 := by
  have a : 0 ≤ ∑ k : Fin 3, (d k)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have c := curvature_energy_nonnegative terms jet
  have squared := translation_remainder_field_square terms positive jet d
  have root : ‖shiftedField terms positive jet d-baseField terms positive jet-
      translationDerivative terms positive jet 0 d‖ ≤ (∑ k : Fin 3, (d k)^2)*Real.sqrt (curvatureEnergy terms jet) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg a (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt c] using squared
  calc
    _ ≤ _ := root
    _ ≤ (3*‖d‖^2)*Real.sqrt (curvatureEnergy terms jet) :=
      mul_le_mul_of_nonneg_right (point_square_bound d) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem sub_preserving (a : Point) : MeasurePreserving (fun x : Point => x-a) volume volume := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Point) (-a)

def shiftOperator (a : Point) : RealField →L[ℝ] RealField :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : Point => x-a) (sub_preserving a)).toContinuousLinearMap

theorem shift_operator_norm (a : Point) (f : RealField) : ‖shiftOperator a f‖=‖f‖ :=
  Lp.norm_compMeasurePreserving f (sub_preserving a)

theorem shift_operator_field (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (a b : Point) :
    shiftOperator a (shiftedField terms positive jet b)=shiftedField terms positive jet (a+b) := by
  change Lp.compMeasurePreserving (fun x : Point => x-a) (sub_preserving a)
    ((shifted_memLp terms positive jet b).toLp _)=_
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x => by
    change orbital terms jet ((x-a)-b)=orbital terms jet (x-(a+b))
    congr 1
    abel

theorem shift_operator_derivative (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (a d : Point) :
    shiftOperator a (translationDerivative terms positive jet 0 d)=translationDerivative terms positive jet a d := by
  simp only [translation_derivative_apply,map_neg,map_sum,map_smul,shift_operator_field,add_zero]

theorem translation_remainder_norm (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (a d : Point) :
    ‖shiftedField terms positive jet (a+d)-shiftedField terms positive jet a-
      translationDerivative terms positive jet a d‖ ≤ 3*Real.sqrt (curvatureEnergy terms jet)*‖d‖^2 := by
  have transport : shiftedField terms positive jet (a+d)-shiftedField terms positive jet a-
      translationDerivative terms positive jet a d=
      shiftOperator a (shiftedField terms positive jet d-baseField terms positive jet-
        translationDerivative terms positive jet 0 d) := by
    simp only [map_sub,shift_operator_derivative,shift_operator_field]
    rw [← shifted_field_zero terms positive jet,shift_operator_field,add_zero]
  rw [transport,shift_operator_norm]
  exact translation_remainder_field_norm terms positive jet d

/-- The original positive Gaussian mother fields generate their complete L² translation derivative. -/
theorem shifted_field_hasFDerivAt (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (a : Point) :
    HasFDerivAt (shiftedField terms positive jet) (translationDerivative terms positive jet a) a := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  have quadratic : (fun d : Point => shiftedField terms positive jet (a+d)-shiftedField terms positive jet a-
      translationDerivative terms positive jet a d) =O[𝓝 0] (fun d : Point => ‖d‖^2) := by
    apply IsBigO.of_bound (3*Real.sqrt (curvatureEnergy terms jet))
    exact Filter.Eventually.of_forall fun d => by
      simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using translation_remainder_norm terms positive jet a d
  exact quadratic.trans_isLittleO (isLittleO_norm_pow_id (by decide : 1 < (2 : ℕ)))

theorem shifted_field_curve_derivative (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (centre : ℝ → Point)
    (velocity : Point) (t : ℝ) (motion : HasDerivAt centre velocity t) :
    HasDerivAt (fun s => shiftedField terms positive jet (centre s))
      (-(∑ k : Fin 3, velocity k • shiftedField terms positive (raise jet k) (centre t))) t := by
  simpa only [Function.comp_def,translation_derivative_apply] using!
    (shifted_field_hasFDerivAt terms positive jet (centre t)).comp_hasDerivAt t motion

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.SpatialControl
