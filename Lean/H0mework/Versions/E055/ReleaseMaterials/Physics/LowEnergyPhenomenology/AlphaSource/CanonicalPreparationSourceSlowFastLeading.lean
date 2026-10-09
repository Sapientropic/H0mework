import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalHermitian

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumWholeOrigin
open PreparationVacuumFullOriginResponse CanonicalGradedSpatialSource
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

def slowFastFrameTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,0⟩,1⟩,⟨1,1,⟨0,0,0,0⟩,1⟩,⟨2,2,⟨0,0,0,0⟩,1⟩,
  ⟨3,2,⟨0,0,0,0⟩,1⟩,⟨2,3,⟨0,0,0,0⟩,1⟩,⟨3,3,⟨0,0,0,0⟩,-1⟩,⟨4,4,⟨0,0,0,0⟩,1⟩]
def slowFastInverseTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,0⟩,1⟩,⟨1,1,⟨0,0,0,0⟩,1⟩,⟨2,2,⟨0,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨3,2,⟨0,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,⟨2,3,⟨0,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨3,3,⟨0,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,⟨4,4,⟨0,0,0,0⟩,1⟩]
def slowFastFrame : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix slowFastFrameTerms 0
def slowFastInverse : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix slowFastInverseTerms 0

theorem slowFastFrame_constant (p : Fin 4→ℂ) : sourceMatrix slowFastFrameTerms p=slowFastFrame:=by
  norm_num [slowFastFrame,slowFastFrameTerms,sourceMatrix,SourceTerm.matrix,Powers.value]

theorem slowFastFrame_inverse : slowFastInverse*slowFastFrame=fiveProjection:=by
  have h:=normalization_equal (productTerms slowFastInverseTerms slowFastFrameTerms) fiveProjectionTerms (by decide +kernel) (0:Fin 4→ℂ)
  simpa only [productTerms_value,slowFastInverse,slowFastFrame,fiveProjection] using h

theorem slowFastFrame_inverse_right : slowFastFrame*slowFastInverse=fiveProjection:=by
  have h:=normalization_equal (productTerms slowFastFrameTerms slowFastInverseTerms) fiveProjectionTerms (by decide +kernel) (0:Fin 4→ℂ)
  simpa only [productTerms_value,slowFastInverse,slowFastFrame,fiveProjection] using h

def slowFastLeadingTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-25/54:ℚ)⟩⟩⟩,
  ⟨0,0,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-25/54:ℚ)⟩⟩⟩,
  ⟨0,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/54:ℚ)⟩⟩⟩,
  ⟨0,0,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/18:ℚ)⟩⟩⟩,
  ⟨1,1,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-12/335:ℚ)⟩⟩⟩,
  ⟨1,1,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-12/335:ℚ)⟩⟩⟩,
  ⟨1,1,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-12/335:ℚ)⟩⟩⟩,
  ⟨1,1,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(10/99:ℚ)⟩⟩⟩,
  ⟨2,2,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-8/15:ℚ)⟩⟩⟩,
  ⟨2,2,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-8/15:ℚ)⟩⟩⟩,
  ⟨2,2,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-8/15:ℚ)⟩⟩⟩,
  ⟨2,2,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(20/27:ℚ)⟩⟩⟩,
  ⟨2,3,⟨1,0,0,1⟩,⟨⟨(-40/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨2,3,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-20/27:ℚ)⟩⟩⟩,
  ⟨3,2,⟨1,0,0,1⟩,⟨⟨(-40/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨3,2,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-20/27:ℚ)⟩⟩⟩,
  ⟨3,3,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩⟩,
  ⟨3,3,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩⟩,
  ⟨3,3,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩⟩,
  ⟨3,3,⟨1,0,0,1⟩,⟨⟨(40/3:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨3,3,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(110/81:ℚ)⟩⟩⟩,
  ⟨3,4,⟨1,0,0,0⟩,⟨⟨0,-8⟩,⟨0,0⟩⟩⟩,
  ⟨4,3,⟨1,0,0,0⟩,⟨⟨0,8⟩,⟨0,0⟩⟩⟩,
  ⟨4,4,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩⟩,
  ⟨4,4,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩⟩,
  ⟨4,4,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩⟩,
  ⟨4,4,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(50/27:ℚ)⟩⟩⟩]

theorem slowFastLeading_generated (p : Fin 4→ℂ) :
    slowFastFrame.transpose*leadingTensor p*slowFastFrame=sourceMatrix slowFastLeadingTerms p:=by
  have h:=normalization_equal
    (productTerms (productTerms (reflectedTerms slowFastFrameTerms) fullLeadingTerms) slowFastFrameTerms)
    slowFastLeadingTerms (by decide +kernel) p
  simpa only [productTerms_value,reflectedTerms_value,slowFastFrame_constant,leadingTensor] using h

def fiveIndex (i : Fin 5) : Fin 289:=⟨i.val,by omega⟩
def slowFastLeadingFive (p : Fin 4→ℂ) : Matrix (Fin 5) (Fin 5) ℂ:=
  (slowFastFrame.transpose*leadingTensor p*slowFastFrame).submatrix fiveIndex fiveIndex

def spatialSquare (k : PhysicalMomentum) : ℝ:=(k 0)^2+(k 1)^2+(k 2)^2

def characteristicTensor (s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 5) (Fin 5) ℂ:=
  Matrix.diagonal ![
    rootTwo*rootFifteen*((25/18:ℂ)*(s:ℂ)^2+(25/54:ℂ)*(spatialSquare n:ℂ)),
    rootTwo*rootFifteen*(-(10/99:ℂ)*(s:ℂ)^2+(12/335:ℂ)*(spatialSquare n:ℂ)),
    rootTwo*rootFifteen*(-(20/27:ℂ)*(s:ℂ)^2+(8/15:ℂ)*(spatialSquare n:ℂ)),0,0]+
    Matrix.single 3 4 (8*Complex.I*rootTwo*(s:ℂ))+Matrix.single 4 3 (-8*Complex.I*rootTwo*(s:ℂ))

def characteristicMix (s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 5) (Fin 5) ℂ:=
  let c:=-(40/9:ℂ)*(s:ℂ)*(n 2:ℂ)+(20/27:ℂ)*rootTwo*rootFifteen*(s:ℂ)^2
  Matrix.single 2 3 c+Matrix.single 3 2 c

def characteristicFast (s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 5) (Fin 5) ℂ:=
  Matrix.single 3 3 (-(4/5:ℂ)*rootTwo*rootFifteen*(spatialSquare n:ℂ)+(40/3:ℂ)*(s:ℂ)*(n 2:ℂ)-
    (110/81:ℂ)*rootTwo*rootFifteen*(s:ℂ)^2)+
  Matrix.single 4 4 (-(4/5:ℂ)*rootTwo*rootFifteen*(spatialSquare n:ℂ)-(50/27:ℂ)*rootTwo*rootFifteen*(s:ℂ)^2)

def frequencyRay (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→ℂ:=
  physicalFrequencyMomentum (s*epsilon^2) (epsilon^2 • n)

private theorem ray_zero (e s : ℝ) (n : PhysicalMomentum) : frequencyRay e s n 0= -Complex.I*((s*e^2:ℝ):ℂ):=rfl
private theorem ray_one (e s : ℝ) (n : PhysicalMomentum) : frequencyRay e s n 1=Complex.I*((e^2*n 0:ℝ):ℂ):=rfl
private theorem ray_two (e s : ℝ) (n : PhysicalMomentum) : frequencyRay e s n 2=Complex.I*((e^2*n 1:ℝ):ℂ):=rfl
private theorem ray_three (e s : ℝ) (n : PhysicalMomentum) : frequencyRay e s n 3=Complex.I*((e^2*n 2:ℝ):ℂ):=rfl

def rayScaling (epsilon : ℝ) : Matrix (Fin 5) (Fin 5) ℂ:=
  Matrix.diagonal (fun i=>if i.val<3 then (epsilon:ℂ)⁻¹^2 else (epsilon:ℂ)⁻¹)

/-- Exact full tensor identity; the time-space mixing is retained at order epsilon. -/
theorem normalizedLeading_generated (epsilon s : ℝ) (n : PhysicalMomentum) (nonzero : epsilon≠0) :
    rayScaling epsilon*slowFastLeadingFive (frequencyRay epsilon s n)*rayScaling epsilon=
      characteristicTensor s n+(epsilon:ℂ) • characteristicMix s n+(epsilon:ℂ)^2 • characteristicFast s n:=by
  unfold slowFastLeadingFive
  rw [slowFastLeading_generated]
  have complexNonzero : (epsilon:ℂ)≠0:=Complex.ofReal_ne_zero.mpr nonzero
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rayScaling,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.submatrix_apply,fiveIndex,
      sourceMatrix,slowFastLeadingTerms,SourceTerm.matrix,Powers.value,coefficientValue,
      ray_zero,ray_one,ray_two,ray_three,characteristicTensor,characteristicMix,characteristicFast,
      spatialSquare,Matrix.single_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,
      Pi.smul_apply,smul_eq_mul,Fin.ext_iff,mul_pow,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,Complex.I_sq] <;>
    field_simp [complexNonzero] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem sparse_five_det (a b c d : ℂ) :
    (Matrix.diagonal (![a,b,c,0,0] : Fin 5→ℂ)+Matrix.single 3 4 d+Matrix.single 4 3 (-d)).det=a*b*c*d^2:=by
  let M : Matrix (Fin 5) (Fin 5) ℂ:=Matrix.diagonal ![a,b,c,0,0]+Matrix.single 3 4 d+Matrix.single 4 3 (-d)
  have diagonal : M.submatrix id (Equiv.swap (3:Fin 5) 4)=Matrix.diagonal ![a,b,c,d,-d]:=by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M,Matrix.submatrix_apply,Matrix.diagonal_apply,Matrix.single_apply,Matrix.add_apply,Equiv.swap_apply_def,Fin.ext_iff]
  have h:=Matrix.det_permute' (Equiv.swap (3:Fin 5) 4) M
  rw [diagonal,Matrix.det_diagonal] at h
  norm_num [Fin.prod_univ_succ,Fin.ext_iff] at h
  change M.det=a*b*c*d^2
  calc
    M.det=a*(b*(c*(d*d))):=h.symm
    _=a*b*c*d^2:=by ring

private theorem source_rootTwo_square : rootTwo^2=(2:ℂ):=by
  norm_num [rootTwo,←Complex.ofReal_pow,Real.sq_sqrt]

theorem characteristic_det_generated (s : ℝ) (n : PhysicalMomentum) :
    (characteristicTensor s n).det= -128*(s:ℂ)^2*
      (rootTwo*rootFifteen*((25/18:ℂ)*(s:ℂ)^2+(25/54:ℂ)*(spatialSquare n:ℂ)))*
      (rootTwo*rootFifteen*(-(10/99:ℂ)*(s:ℂ)^2+(12/335:ℂ)*(spatialSquare n:ℂ)))*
      (rootTwo*rootFifteen*(-(20/27:ℂ)*(s:ℂ)^2+(8/15:ℂ)*(spatialSquare n:ℂ))):=by
  unfold characteristicTensor
  simp only [neg_mul]
  rw [sparse_five_det]
  simp only [mul_pow,Complex.I_sq,source_rootTwo_square]
  ring

def sourceRoot : ℝ:=Real.sqrt 2*Real.sqrt 15

def characteristicDeterminant (s : ℝ) (n : PhysicalMomentum) : ℝ:=
  -128*s^2*(sourceRoot*((25/18:ℝ)*s^2+(25/54:ℝ)*spatialSquare n))*
    (sourceRoot*(-(10/99:ℝ)*s^2+(12/335:ℝ)*spatialSquare n))*
    (sourceRoot*(-(20/27:ℝ)*s^2+(8/15:ℝ)*spatialSquare n))

theorem characteristic_det_real (s : ℝ) (n : PhysicalMomentum) :
    (characteristicTensor s n).det=(characteristicDeterminant s n:ℂ):=by
  rw [characteristic_det_generated]
  unfold characteristicDeterminant sourceRoot rootTwo rootFifteen
  push_cast
  ring

theorem characteristic_endpoint_signs (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    characteristicDeterminant (1/2) n<0 ∧ 0<characteristicDeterminant (2/3) n ∧
      0<characteristicDeterminant (4/5) n ∧ characteristicDeterminant (9/10) n<0:=by
  have positive : 0<sourceRoot:=by unfold sourceRoot;positivity
  have cube:=pow_pos positive 3
  simp only [characteristicDeterminant,unit]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

def scaleDomain : Set ℝ:={e | 0<e ∧ e≤PreparationVacuumFullOriginResponse.sourceRadius}
def slopeDomain : Set ℝ:={s | |s|≤1}

theorem scale_le_one (e : scaleDomain) : e.val≤1:=
  e.property.2.trans PreparationVacuumFullOriginResponse.sourceRadius_le_one

theorem scale_square_cap (e : scaleDomain) : e.val^2≤PreparationVacuumFullOriginResponse.sourceRadius:=by
  calc
    _=e.val*e.val:=pow_two _
    _≤1*e.val:=mul_le_mul_of_nonneg_right (scale_le_one e) e.property.1.le
    _≤_:=by simpa only [one_mul] using e.property.2

theorem frequencyRay_bound (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    ∀i,‖frequencyRay e.val s.val n i‖≤e.val^2:=by
  apply physicalFrequencyMomentum_bound
  · rw [abs_mul,abs_of_nonneg (sq_nonneg e.val)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right s.property (sq_nonneg e.val)
  · intro i
    change |e.val^2*n i|≤e.val^2
    rw [abs_mul,abs_of_nonneg (sq_nonneg e.val)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (direction i) (sq_nonneg e.val)

def rayPoint (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    PreparationVacuumFullOriginResponse.complementRegular:=
  PreparationVacuumFullOriginResponse.controlledPoint (frequencyRay e.val s.val n)
    (fun i=>(frequencyRay_bound e s n direction i).trans (scale_square_cap e))

def rayEffective (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    Matrix (Fin 289) (Fin 289) ℂ:=PreparationVacuumFullOriginResponse.effectiveKernel (rayPoint e s n direction)

theorem rayEffective_leading_price (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    ‖rayEffective e s n direction-leadingTensor (frequencyRay e.val s.val n)‖≤effectiveErrorBudget*e.val^6:=by
  have h:=effectiveKernel_leading_price (frequencyRay e.val s.val n) (e.val^2)
    (sq_nonneg e.val) (scale_square_cap e) (frequencyRay_bound e s n direction)
  simpa only [rayEffective,rayPoint,←pow_mul] using h

def wideRayScaling (e : ℝ) : Matrix (Fin 289) (Fin 289) ℂ:=
  Matrix.diagonal (fun i=>if i.val<3 then (e:ℂ)⁻¹^2 else if i.val<5 then (e:ℂ)⁻¹ else 0)

theorem wideRayScaling_price (e : scaleDomain) : ‖wideRayScaling e.val‖≤e.val⁻¹^2:=by
  have positive:=e.property.1
  have inverse : 1≤e.val⁻¹:=by
    calc
      1=e.val*e.val⁻¹:=(mul_inv_cancel₀ positive.ne').symm
      _≤1*e.val⁻¹:=mul_le_mul_of_nonneg_right (scale_le_one e) (inv_nonneg.mpr positive.le)
      _=e.val⁻¹:=one_mul _
  have inverse_square : e.val⁻¹≤e.val⁻¹^2:=by nlinarith [sq_nonneg (e.val⁻¹-1)]
  rw [wideRayScaling,Matrix.linfty_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg e.val⁻¹)).mpr
  intro i
  split_ifs
  · simp only [norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive,le_refl]
  · simpa only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive] using inverse_square
  · simpa only [norm_zero] using sq_nonneg e.val⁻¹

def scaledErrorBudget : ℝ:=‖slowFastFrame.transpose‖*effectiveErrorBudget*‖slowFastFrame‖

theorem scaledErrorBudget_nonnegative : 0 ≤ scaledErrorBudget:=by
  unfold scaledErrorBudget
  exact mul_nonneg (mul_nonneg (norm_nonneg _) effectiveErrorBudget_nonneg) (norm_nonneg _)

/-- Complete complement self-energy remains in this source error, not in a pole-shell assumption. -/
theorem scaledEffective_remainder (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    ‖wideRayScaling e.val*(slowFastFrame.transpose*
      (rayEffective e s n direction-leadingTensor (frequencyRay e.val s.val n))*slowFastFrame)*wideRayScaling e.val‖≤
      scaledErrorBudget*e.val^2:=by
  have D:=wideRayScaling_price e
  have C:=effectiveErrorBudget_nonneg
  have remainder:=rayEffective_leading_price e s n direction
  have nonzero:=e.property.1.ne'
  calc
    _≤‖wideRayScaling e.val‖*(‖slowFastFrame.transpose‖*
        ‖rayEffective e s n direction-leadingTensor (frequencyRay e.val s.val n)‖*‖slowFastFrame‖)*‖wideRayScaling e.val‖:=by
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _≤e.val⁻¹^2*(‖slowFastFrame.transpose‖*(effectiveErrorBudget*e.val^6)*‖slowFastFrame‖)*e.val⁻¹^2:=by gcongr
    _=scaledErrorBudget*e.val^2:=by unfold scaledErrorBudget;field_simp [nonzero]

def scaleApproach : Filter scaleDomain:=Filter.comap Subtype.val (𝓝[>] (0:ℝ))

theorem scaleApproach_nonempty : scaleApproach.NeBot:=by
  apply Filter.NeBot.comap_of_range_mem (inferInstance : (𝓝[>] (0:ℝ)).NeBot)
  have near : ∀ᶠ e in 𝓝 (0:ℝ),e<PreparationVacuumFullOriginResponse.sourceRadius:=
    continuous_id.continuousAt.eventually_lt_const PreparationVacuumFullOriginResponse.sourceRadius_pos
  filter_upwards [self_mem_nhdsWithin,near.filter_mono nhdsWithin_le_nhds] with e positive small
  exact ⟨⟨e,positive,small.le⟩,rfl⟩

theorem scaleVal_tendsto : Filter.Tendsto (Subtype.val : scaleDomain→ℝ) scaleApproach (𝓝 0):=
  (Filter.tendsto_comap : Filter.Tendsto (Subtype.val : scaleDomain→ℝ) scaleApproach (𝓝[>] (0:ℝ))).mono_right nhdsWithin_le_nhds

def normalizedEffective (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    Matrix (Fin 5) (Fin 5) ℂ:=
  (wideRayScaling e.val*(slowFastFrame.transpose*rayEffective e s n direction*slowFastFrame)*wideRayScaling e.val).submatrix fiveIndex fiveIndex

private theorem scaling_submatrix (e : ℝ) (M : Matrix (Fin 289) (Fin 289) ℂ) :
    (wideRayScaling e*M*wideRayScaling e).submatrix fiveIndex fiveIndex=
      rayScaling e*M.submatrix fiveIndex fiveIndex*rayScaling e:=by
  ext i j
  simp only [wideRayScaling,rayScaling,Matrix.submatrix_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,fiveIndex]
  simp only [i.isLt,j.isLt,if_true]

private theorem source_entry_norm (M : Matrix (Fin 289) (Fin 289) ℂ) (i j : Fin 289) : ‖M i j‖≤‖M‖:=by
  have column:=Matrix.linfty_opNorm_mulVec M (Pi.single j (1:ℂ))
  simp only [Matrix.mulVec_single_one,Pi.norm_single,norm_one,mul_one] at column
  exact (norm_le_pi_norm (M.col j) i).trans column

theorem normalizedEffective_entry_error (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (i j : Fin 5) :
    ‖(normalizedEffective e s n direction-
      (characteristicTensor s.val n+(e.val:ℂ) • characteristicMix s.val n+(e.val:ℂ)^2 • characteristicFast s.val n)) i j‖≤
      scaledErrorBudget*e.val^2:=by
  rw [←normalizedLeading_generated e.val s.val n e.property.1.ne']
  unfold normalizedEffective slowFastLeadingFive
  rw [←scaling_submatrix]
  have difference :
      wideRayScaling e.val*(slowFastFrame.transpose*rayEffective e s n direction*slowFastFrame)*wideRayScaling e.val-
        wideRayScaling e.val*(slowFastFrame.transpose*leadingTensor (frequencyRay e.val s.val n)*slowFastFrame)*wideRayScaling e.val=
      wideRayScaling e.val*(slowFastFrame.transpose*(rayEffective e s n direction-leadingTensor (frequencyRay e.val s.val n))*slowFastFrame)*wideRayScaling e.val:=by
    simp only [mul_sub,sub_mul]
  calc
    _=‖(wideRayScaling e.val*(slowFastFrame.transpose*
        (rayEffective e s n direction-leadingTensor (frequencyRay e.val s.val n))*slowFastFrame)*wideRayScaling e.val) (fiveIndex i) (fiveIndex j)‖:=
      congrArg norm (congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M (fiveIndex i) (fiveIndex j)) difference)
    _≤_ :=(source_entry_norm _ (fiveIndex i) (fiveIndex j)).trans (scaledEffective_remainder e s n direction)

/-- The complete source effective tensor, rather than its quadratic truncation, has this generated scaled limit. -/
theorem normalizedEffective_tendsto (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    Filter.Tendsto (fun e : scaleDomain=>normalizedEffective e s n direction) scaleApproach (𝓝 (characteristicTensor s.val n)):=by
  have scalar : Filter.Tendsto (fun e : scaleDomain=>(e.val:ℂ)) scaleApproach (𝓝 (0:ℂ)):=by
    simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp scaleVal_tendsto
  have main := ((tendsto_const_nhds (x:=characteristicTensor s.val n)).add
    (scalar.smul (tendsto_const_nhds (x:=characteristicMix s.val n)))).add
      ((scalar.pow 2).smul (tendsto_const_nhds (x:=characteristicFast s.val n)))
  simp only [zero_smul,add_zero,zero_pow (by decide : 2≠0)] at main
  have upper : Filter.Tendsto (fun e : scaleDomain=>scaledErrorBudget*e.val^2) scaleApproach (𝓝 (0:ℝ)):=by
    simpa only [zero_pow (by decide : 2≠0),mul_zero] using tendsto_const_nhds.mul (scaleVal_tendsto.pow 2)
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have error : Filter.Tendsto (fun e : scaleDomain=>(normalizedEffective e s n direction-
      (characteristicTensor s.val n+(e.val:ℂ) • characteristicMix s.val n+(e.val:ℂ)^2 • characteristicFast s.val n)) i j)
      scaleApproach (𝓝 (0:ℂ)):=
    squeeze_zero_norm (fun e=>normalizedEffective_entry_error e s n direction i j) upper
  have component := (continuous_apply j).continuousAt.tendsto.comp ((continuous_apply i).continuousAt.tendsto.comp main)
  have combined:=error.add component
  simpa only [Function.comp_def,Matrix.sub_apply,sub_add_cancel,zero_add] using combined

private theorem slowFastFrame_adjoint : slowFastFrame.conjTranspose=slowFastFrame.transpose:=by
  have h:=sourceMatrix_adjoint slowFastFrameTerms (0:Fin 4→ℂ)
  have zero : (fun i : Fin 4=>star ((0:Fin 4→ℂ) i))=0:=by funext i;exact star_zero _
  simpa only [zero,slowFastFrame_constant] using h

private theorem wideRayScaling_hermitian (e : ℝ) : (wideRayScaling e).IsHermitian:=by
  simp [Matrix.IsHermitian,wideRayScaling]
  intro i
  split_ifs <;> simp

theorem rayEffective_hermitian (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    (rayEffective e s n direction).IsHermitian:=
  physicalEffective_hermitian (s.val*e.val^2) (e.val^2 • n) (rayPoint e s n direction).property

theorem normalizedEffective_hermitian (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    (normalizedEffective e s n direction).IsHermitian:=by
  have source:=Matrix.isHermitian_conjTranspose_mul_mul (slowFastFrame*wideRayScaling e.val)
    (rayEffective_hermitian e s n direction)
  have same : (wideRayScaling e.val*(slowFastFrame.transpose*rayEffective e s n direction*slowFastFrame)*wideRayScaling e.val).IsHermitian:=by
    simpa only [Matrix.conjTranspose_mul,(wideRayScaling_hermitian e.val).eq,slowFastFrame_adjoint,mul_assoc] using source
  exact same.submatrix fiveIndex

theorem normalizedEffective_det_real (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    (normalizedEffective e s n direction).det=((normalizedEffective e s n direction).det.re:ℂ):=by
  have h:=congrArg Matrix.det (normalizedEffective_hermitian e s n direction).eq
  rw [Matrix.det_conjTranspose] at h
  have imaginary:=congrArg Complex.im h
  simp only [Complex.star_def,Complex.conj_im] at imaginary
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

end LowEnergy.PreparationVacuumPhysicalCharacteristic
