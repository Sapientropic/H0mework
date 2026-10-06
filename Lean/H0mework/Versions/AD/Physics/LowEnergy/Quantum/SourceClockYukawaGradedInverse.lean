import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaGradedRadial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGradedInverse
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussCoreLabel NativeHistoryGrade GaussRadialDomain GaussYukawaOperator GaussYukawaCoefficient
open SourceClockYukawaGradedRadial
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open MeasureTheory
open scoped BigOperators InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
local instance labelFintype : Fintype Label := Fintype.ofFinite _

/-- The original smooth core keeps the growing inverse powers on each actual label. -/
def inverseWeightCore (sharp : Bool) : End :=
  ∑ g : Label,(radiusAction^exponent sharp g)*project g

private theorem real_fock_smul (c : ℝ) (v : FockFiber) : c • v=(c:ℂ) • v := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private theorem radius_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((radiusAction^n) f) z=(radius z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change radius z • (((radiusAction^n) f) z)=_
    rw [real_fock_smul,ih,pow_succ',mul_smul]

private def coordinate (z : SourceCoordinateSlice) (word : Occupation) : QuantumTest →ₗ[ℂ] ℂ where
  toFun f := f z word
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem radial_coordinate (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice)
    (word : Occupation) :
    radialWeightCore sharp f z word=(reciprocal z:ℂ)^exponent sharp (sourceLabel word)*f z word := by
  change coordinate z word (radialWeightCore sharp f)=_
  simp only [radialWeightCore,LinearMap.sum_apply,Module.End.mul_apply,map_sum]
  have he (g : Label) : coordinate z word ((inverseAction^exponent sharp g) (project g f))=
      (reciprocal z:ℂ)^exponent sharp g*(if sourceLabel word=g then f z word else 0) := by
    change ((inverseAction^exponent sharp g) (project g f)) z word=_
    rw [inverse_power_apply]
    change (reciprocal z:ℂ)^exponent sharp g*(project g f z word)=_
    rw [project_apply,fiberPiece_apply]
  simp_rw [he]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]

private theorem inverse_coordinate (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice)
    (word : Occupation) :
    inverseWeightCore sharp f z word=(radius z:ℂ)^exponent sharp (sourceLabel word)*f z word := by
  change coordinate z word (inverseWeightCore sharp f)=_
  simp only [inverseWeightCore,LinearMap.sum_apply,Module.End.mul_apply,map_sum]
  have he (g : Label) : coordinate z word ((radiusAction^exponent sharp g) (project g f))=
      (radius z:ℂ)^exponent sharp g*(if sourceLabel word=g then f z word else 0) := by
    change ((radiusAction^exponent sharp g) (project g f)) z word=_
    rw [radius_power_apply]
    change (radius z:ℂ)^exponent sharp g*(project g f z word)=_
    rw [project_apply,fiberPiece_apply]
  simp_rw [he]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]

/-- A fixed core source k is exactly T_s applied to its original growing core inverse U_s k. -/
theorem original_inverse_radial_weight (sharp : Bool) :
    radialWeightCore sharp*inverseWeightCore sharp=(1 : End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change radialWeightCore sharp (inverseWeightCore sharp f) z word=f z word
  rw [radial_coordinate,inverse_coordinate,←mul_assoc,←mul_pow]
  have hr : (radius z:ℂ)≠0 := by exact_mod_cast (radius_pos z).ne'
  have he : (reciprocal z:ℂ)*(radius z:ℂ)=1 := by
    simp only [reciprocal,Complex.ofReal_inv,inv_mul_cancel₀ hr]
  rw [he,one_pow,one_mul]

/-- The same actual label multipliers pair in the original Number-weighted source Hilbert core. -/
theorem original_radial_weight_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (radialWeightCore sharp q)=sourcePair (radialWeightCore sharp p) q := by
  rw [sourcePair_integral,sourcePair_integral]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [densityPair_sum,densityPair_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [radial_coordinate,radial_coordinate]
  simp only [star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  ring

end LowEnergy.SourceClockYukawaGradedInverse
