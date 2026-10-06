import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaGradedEuler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGradedContact
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussLiveMomentum GaussNativeEnergy GaussRadialDomain GaussYukawaCoefficient GaussDiagonalHistory GaussUnitaryHistory
open SourceClockYukawaGradedRadial SourceClockYukawaGradedEuler SourceScalarRadialContact
open SourcePhysicalKineticSquare SourceScalarDoubleCurrent SourceScalarPairedTransport
open GaussCoreLabel NativeHistoryGrade SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open MeasureTheory
open scoped ContDiff InnerProductSpace BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
local instance labelFintype : Fintype Label := Fintype.ofFinite _

/-- The mixed actual grade weights return a pure scalar source contact. -/
def gradedContact (sharp : Bool) : End := ((sourceTime 0:ℂ)/4) •
  (inverseVolumeAction*∑ g : Label,(exponent sharp g*exponent (!sharp) g:ℂ) •
    ((inverseAction^58-inverseAction^60)*project g))

private def radialEuler (sharp : Bool) : End := ∑ g : Label,(exponent sharp g:ℂ) •
  (inverseAction^exponent sharp g*(inverseAction^2-1)*project g)

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

private theorem euler_inverse : bracket scalarEulerAction inverseAction=inverseAction^3-inverseAction := by
  have hd (z : SourceCoordinateSlice) : fderiv ℝ reciprocal z (scalarEuler z)=reciprocal z^3-reciprocal z := by
    rw [GaussRadialMomentum.reciprocal_derivative]
    change -inner ℝ (z.2.1:Scalar) (z.2.1:Scalar)/(4*radius z^3)=_
    rw [real_inner_self_eq_norm_sq]
    have hs := Real.sq_sqrt (show 0≤1+‖(z.2.1:Scalar)‖^2/4 by positivity)
    change radius z^2=1+‖(z.2.1:Scalar)‖^2/4 at hs
    unfold reciprocal
    field_simp [(radius_pos z).ne']
    nlinarith only [hs]
  have he (f : QuantumTest) (z : SourceCoordinateSlice) :
      scalarEulerAction (inverseAction f) z=reciprocal z • scalarEulerAction f z+
        (reciprocal z^3-reciprocal z) • f z := by
    rw [scalar_euler_apply,GaussRadialMomentum.inverseAction_real,
      fderiv_fun_smul (reciprocal_smooth.differentiable (by simp)).differentiableAt
        (f.contDiff.differentiable (by simp)).differentiableAt]
    change reciprocal z • fderiv ℝ f z (scalarEuler z)+
      fderiv ℝ reciprocal z (scalarEuler z) • f z=_
    rw [hd,scalar_euler_apply]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change scalarEulerAction (inverseAction f) z-inverseAction (scalarEulerAction f) z=
    ((inverseAction^3) f) z-inverseAction f z
  rw [he,inverse_power_apply]
  change reciprocal z • scalarEulerAction f z+(reciprocal z^3-reciprocal z) • f z-
    (reciprocal z:ℂ) • scalarEulerAction f z=
      (reciprocal z:ℂ)^3 • f z-(reciprocal z:ℂ) • f z
  rw [real_fock_smul,real_fock_smul]
  push_cast
  module

private theorem bracket_product (A B C : End) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket;noncomm_ring

private theorem euler_power (n : ℕ) :
    bracket scalarEulerAction (inverseAction^n)=(n:ℂ) • (inverseAction^n*(inverseAction^2-1)) := by
  induction n with
  | zero => simp [bracket]
  | succ n ih =>
    rw [pow_succ,bracket_product,ih,euler_inverse]
    have he : inverseAction^n*(inverseAction^3-inverseAction)=inverseAction^(n+1)*(inverseAction^2-1) := by
      rw [pow_succ]
      noncomm_ring
    have hn : (inverseAction^n*(inverseAction^2-1))*inverseAction=inverseAction^(n+1)*(inverseAction^2-1) := by
      rw [pow_succ]
      noncomm_ring
    simp only [Nat.cast_succ,add_smul,one_smul,smul_mul_assoc]
    rw [he,hn]
    simp only [pow_succ]

private theorem euler_project (g : Label) : Commute scalarEulerAction (project g) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change scalarEulerAction (project g f) z=project g (scalarEulerAction f) z
  rw [scalar_euler_apply,derivative_project,project_apply,scalar_euler_apply]


private theorem euler_weight (sharp : Bool) :
    bracket scalarEulerAction (radialWeightCore sharp)=radialEuler sharp := by
  have h (g : Label) : bracket scalarEulerAction ((inverseAction^exponent sharp g)*project g)=
      (exponent sharp g:ℂ) • (inverseAction^exponent sharp g*(inverseAction^2-1)*project g) := by
    rw [bracket_product,euler_power]
    have hz : bracket scalarEulerAction (project g)=0 := by
      unfold bracket
      rw [(euler_project g).eq,sub_self]
    rw [hz,mul_zero,add_zero,smul_mul_assoc]
  unfold radialWeightCore radialEuler
  simp only [bracket,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun g _ => h g)

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

private theorem profile_coordinate (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice)
    (word : Occupation) :
    gradedProfile sharp f z word=(-(sourceTime 0:ℂ)/4)*(reciprocalVolume z:ℂ)*
      (exponent sharp (sourceLabel word):ℂ)*(reciprocal z:ℂ)^(exponent sharp (sourceLabel word)+2)*f z word := by
  change coordinate z word (gradedProfile sharp f)=_
  have hv (p : QuantumTest) : coordinate z word (inverseVolumeAction p)=
      (reciprocalVolume z:ℂ)*coordinate z word p := rfl
  simp only [gradedProfile,LinearMap.smul_apply,Module.End.mul_apply,map_smul,hv,
    LinearMap.sum_apply,map_sum]
  have he (g : Label) : coordinate z word ((inverseAction^(exponent sharp g+2)) (project g f))=
      (reciprocal z:ℂ)^(exponent sharp g+2)*(if sourceLabel word=g then f z word else 0) := by
    change ((inverseAction^(exponent sharp g+2)) (project g f)) z word=_
    rw [inverse_power_apply]
    change (reciprocal z:ℂ)^(exponent sharp g+2)*(project g f z word)=_
    rw [project_apply,fiberPiece_apply]
  simp_rw [he]
  simp only [smul_eq_mul,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  ring

private theorem euler_coordinate (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice)
    (word : Occupation) :
    radialEuler sharp f z word=(exponent sharp (sourceLabel word):ℂ)*
      ((reciprocal z:ℂ)^exponent sharp (sourceLabel word)*((reciprocal z:ℂ)^2-1))*f z word := by
  change coordinate z word (radialEuler sharp f)=_
  simp only [radialEuler,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul]
  have he (g : Label) : coordinate z word
      ((inverseAction^exponent sharp g) ((inverseAction^2-(1:End)) (project g f)))=
      ((reciprocal z:ℂ)^exponent sharp g*((reciprocal z:ℂ)^2-1))*
        (if sourceLabel word=g then f z word else 0) := by
    change ((inverseAction^exponent sharp g) ((inverseAction^2-(1:End)) (project g f))) z word=_
    rw [inverse_power_apply]
    change (reciprocal z:ℂ)^exponent sharp g*((inverseAction^2) (project g f) z word-project g f z word)=_
    rw [inverse_power_apply]
    change (reciprocal z:ℂ)^exponent sharp g*((reciprocal z:ℂ)^2*(project g f z word)-project g f z word)=_
    rw [project_apply,fiberPiece_apply]
    ring
  simp_rw [he]
  simp only [smul_eq_mul,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  ring

private def contactCoefficient (sharp : Bool) (z : SourceCoordinateSlice) (word : Occupation) : ℝ :=
  sourceTime 0/4*reciprocalVolume z*
    (exponent sharp (sourceLabel word)*exponent (!sharp) (sourceLabel word):ℝ)*
      (reciprocal z^58-reciprocal z^60)

private theorem contact_coordinate (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice)
    (word : Occupation) : gradedContact sharp f z word=(contactCoefficient sharp z word:ℂ)*f z word := by
  change coordinate z word (gradedContact sharp f)=_
  have hv (p : QuantumTest) : coordinate z word (inverseVolumeAction p)=
      (reciprocalVolume z:ℂ)*coordinate z word p := rfl
  simp only [gradedContact,LinearMap.smul_apply,Module.End.mul_apply,map_smul,hv,
    LinearMap.sum_apply,map_sum]
  have he (g : Label) : coordinate z word ((inverseAction^58-inverseAction^60) (project g f))=
      ((reciprocal z:ℂ)^58-(reciprocal z:ℂ)^60)*(if sourceLabel word=g then f z word else 0) := by
    change ((inverseAction^58) (project g f)) z word-((inverseAction^60) (project g f)) z word=_
    rw [inverse_power_apply,inverse_power_apply]
    change (reciprocal z:ℂ)^58*(project g f z word)-(reciprocal z:ℂ)^60*(project g f z word)=_
    rw [project_apply,fiberPiece_apply]
    ring
  simp_rw [he]
  simp only [smul_eq_mul,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  unfold contactCoefficient
  push_cast
  ring

private theorem complementary_exponents (sharp : Bool) (g : Label) :
    exponent sharp g+exponent (!sharp) g=56 := by
  have hg := g.2.isLt
  cases sharp <;> simp [exponent] <;> omega

private theorem profile_weight_commute (sharp other : Bool) : Commute (gradedProfile sharp) (radialWeightCore other) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change gradedProfile sharp (radialWeightCore other f) z word=
    radialWeightCore other (gradedProfile sharp f) z word
  rw [profile_coordinate,radial_coordinate,radial_coordinate,profile_coordinate]
  ring

private theorem profile_euler_commute (sharp other : Bool) : Commute (gradedProfile sharp) (radialEuler other) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change gradedProfile sharp (radialEuler other f) z word=radialEuler other (gradedProfile sharp f) z word
  rw [profile_coordinate,euler_coordinate,euler_coordinate,profile_coordinate]
  ring

private theorem profile_euler_contact (sharp : Bool) : gradedProfile sharp*radialEuler (!sharp)=gradedContact sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change gradedProfile sharp (radialEuler (!sharp) f) z word=gradedContact sharp f z word
  rw [profile_coordinate,euler_coordinate,contact_coordinate]
  have hp : (reciprocal z:ℂ)^(exponent sharp (sourceLabel word)+2)*
      (reciprocal z:ℂ)^exponent (!sharp) (sourceLabel word)*((reciprocal z:ℂ)^2-1)=
        (reciprocal z:ℂ)^60-(reciprocal z:ℂ)^58 := by
    rw [←pow_add]
    have he : exponent sharp (sourceLabel word)+2+exponent (!sharp) (sourceLabel word)=58 := by
      have h := complementary_exponents sharp (sourceLabel word)
      omega
    rw [he,mul_sub,mul_one,←pow_add]
  unfold contactCoefficient
  push_cast
  calc
    _=(-(sourceTime 0:ℂ)/4)*(reciprocalVolume z:ℂ)*
      ((exponent sharp (sourceLabel word):ℂ)*(exponent (!sharp) (sourceLabel word):ℂ))*
      ((reciprocal z:ℂ)^(exponent sharp (sourceLabel word)+2)*
        (reciprocal z:ℂ)^exponent (!sharp) (sourceLabel word)*((reciprocal z:ℂ)^2-1))*f z word := by ring
    _=_ := by rw [hp];ring

private theorem euler_form_bracket (E G T : End) (hc : Commute G T) :
    bracket ((1/2:ℂ) • (E*G+G*E+(61:ℂ) • G)) T=
      (1/2:ℂ) • (bracket E T*G+G*bracket E T) := by
  have hL := congrArg (fun A : End => E*A) hc.eq
  have hR := congrArg (fun A : End => A*E) hc.eq
  simp only [bracket,smul_mul_assoc,mul_smul_comm,mul_add,add_mul,mul_sub,sub_mul,smul_add,smul_sub,mul_assoc] at *
  linear_combination (norm := module) (1/2:ℂ) • hL+(1/2:ℂ) • hR+(61/2:ℂ) • hc.eq

/-- The true scalar70 Euler source and complementary actual grades generate the positive mixed contact. -/
theorem original_graded_mixed_contact (sharp : Bool) :
    bracket (gradedRadialCurrent sharp) (radialWeightCore (!sharp))=gradedContact sharp := by
  rw [original_graded_euler_current,euler_form_bracket _ _ _ (profile_weight_commute sharp (!sharp)),euler_weight]
  rw [(profile_euler_commute sharp (!sharp)).symm.eq,←two_smul ℂ,smul_smul]
  norm_num
  exact profile_euler_contact sharp

/-- The original finite compression keeps the whole mixed defect on this same source core. -/
theorem actual_graded_mixed_contact (sharp : Bool) (F : Index) :
    bracket (correctedGradedCurrent sharp F) (radialWeightCore (!sharp))=
      gradedContact sharp-bracket (bracket (defectAction F) (radialWeightCore sharp)) (radialWeightCore (!sharp)) := by
  have h := original_graded_mixed_contact sharp
  rw [correctedGradedCurrent]
  unfold bracket at *
  linear_combination (norm := noncomm_ring) h

private theorem reciprocal_bounds (z : SourceCoordinateSlice) : 0≤reciprocal z ∧ reciprocal z≤1 := by
  constructor
  · exact inv_nonneg.mpr (radius_pos z).le
  · exact inv_le_one_of_one_le₀ (one_le_radius z)

private theorem coefficient_nonnegative (sharp : Bool) (z : physicalChart) (word : Occupation) :
    0≤contactCoefficient sharp z.val word := by
  have hr := reciprocal_bounds z.val
  have hsq : reciprocal z.val^2≤1 := by nlinarith only [hr.1,hr.2]
  have hd : 0≤reciprocal z.val^58-reciprocal z.val^60 := by
    rw [show (60:ℕ)=58+2 from rfl,pow_add]
    nlinarith [pow_nonneg hr.1 58]
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hv : 0≤reciprocalVolume z.val := inv_nonneg.mpr (volume_pos z).le
  unfold contactCoefficient
  positivity

/-- The contact's sign is generated by the actual lapse, volume, radial band and full Number-weighted source pair. -/
theorem original_graded_contact_nonnegative (sharp : Bool) (q : QuantumTest) :
    0≤(sourcePair q (gradedContact sharp q)).re := by
  rw [sourcePair_integral]
  change 0≤RCLike.re (∫ z, densityPair q (gradedContact sharp q) z ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable q (gradedContact sharp q))]
  apply integral_nonneg
  intro z
  change 0≤(densityPair q (gradedContact sharp q) z).re
  rw [densityPair_sum,Complex.re_sum]
  apply Finset.sum_nonneg
  intro word _
  by_cases hz : z∈physicalChart
  · rw [contact_coordinate]
    have hd := GaussDensityCore.density_pos word.card ⟨z,hz⟩
    have hc := coefficient_nonnegative sharp ⟨z,hz⟩ word
    change 0≤((GaussDensityCore.density word.card z:ℂ)*star (q z word)*
      ((contactCoefficient sharp z word:ℂ)*q z word)).re
    have he : ((GaussDensityCore.density word.card z:ℂ)*star (q z word)*
      ((contactCoefficient sharp z word:ℂ)*q z word)).re=
        GaussDensityCore.density word.card z*contactCoefficient sharp z word*‖q z word‖^2 := by
      simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.star_def,Complex.conj_re,Complex.conj_im]
      rw [Complex.sq_norm,Complex.normSq_apply]
      ring
    rw [he]
    positivity
  · have hq : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    simp only [hq,PiLp.zero_apply,star_zero,mul_zero,zero_mul,Complex.zero_re,le_refl]

end LowEnergy.SourceClockYukawaGradedContact
