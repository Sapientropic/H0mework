import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalPropagation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedControl
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCharacteristic CanonicalGradedSpatialSource
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

/-- Homogeneous components are selected from the original coefficient list. -/
def degreeTerms (terms : List SourceTerm) (d : ℕ) : List SourceTerm:=
  terms.filter (fun a=>decide (a.powers.total=d))

def degreeTensor (terms : List SourceTerm) (d : ℕ) (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  sourceMatrix (degreeTerms terms d) p

theorem degreeTensor_scaled (terms : List SourceTerm) (d : ℕ) (z : ℂ) (p : Fin 4→ℂ) :
    degreeTensor terms d (z • p)=z^d • degreeTensor terms d p:=by
  apply sourceMatrix_homogeneous
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp ha).2

private theorem sourceMatrix_twoDegrees (terms : List SourceTerm) (d₁ d₂ : ℕ) (different : d₁≠d₂)
    (degrees : ∀a∈terms,a.powers.total=d₁ ∨ a.powers.total=d₂) (p : Fin 4→ℂ) :
    sourceMatrix terms p=degreeTensor terms d₁ p+degreeTensor terms d₂ p:=by
  induction terms with
  | nil=>simp [sourceMatrix,degreeTensor,degreeTerms]
  | cons a rest ih=>
    have tail:=ih (fun b hb=>degrees b (by simp [hb]))
    rcases degrees a (by simp) with one|two
    · simp only [degreeTensor,degreeTerms,List.filter_cons,one,different,decide_true,ite_true,
        decide_false,Bool.false_eq_true,ite_false,sourceMatrix_cons] at tail ⊢
      rw [tail];abel
    · simp only [degreeTensor,degreeTerms,List.filter_cons,two,Ne.symm different,decide_true,ite_true,
        decide_false,Bool.false_eq_true,ite_false,sourceMatrix_cons] at tail ⊢
      rw [tail];abel

private theorem active_positive_degrees :
    ∀a∈positiveTerms activeTerms,a.powers.total=1 ∨ a.powers.total=2:=by
  have checked : (positiveTerms activeTerms).all (fun a=>decide (a.powers.total=1 ∨ a.powers.total=2))=true:=by decide +kernel
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp checked a ha)

/-- Exact source first and second variation, before any eigenmode selection. -/
def nativeVariation (z : ℂ) (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  degreeTensor (positiveTerms activeTerms) 1 p+z • degreeTensor (positiveTerms activeTerms) 2 p

theorem active_delta_scaled (z : ℂ) (p : Fin 4→ℂ) :
    activeKernel (z • p)-activeKernel 0=z • nativeVariation z p:=by
  change sourceMatrix activeTerms (z • p)-sourceMatrix activeTerms 0=_
  rw [sourceMatrix_delta,sourceMatrix_twoDegrees (positiveTerms activeTerms) 1 2 (by decide) active_positive_degrees,
    degreeTensor_scaled,degreeTensor_scaled]
  simp only [nativeVariation,smul_add,smul_smul,pow_one,pow_two]

def nativeHigher (z : ℂ) (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  degreeTensor fullHigherTerms 3 p+z • degreeTensor fullHigherTerms 4 p

theorem higher_scaled (z : ℂ) (p : Fin 4→ℂ) : higherTensor (z • p)=z^3 • nativeHigher z p:=by
  have degrees : ∀a∈fullHigherTerms,a.powers.total=3 ∨ a.powers.total=4:=by
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp higher_degrees a ha)
  rw [higherTensor,sourceMatrix_twoDegrees fullHigherTerms 3 4 (by decide) degrees,
    degreeTensor_scaled,degreeTensor_scaled]
  simp only [nativeHigher,smul_add,smul_smul,←pow_succ]

/-- Exact complete Schur remainder: the complementary Green remains the original source inverse. -/
def schurRemainder (z : ℂ) (p : Fin 4→ℂ) (G : Matrix (Fin 289) (Fin 289) ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  nativeHigher z p+fullKernelFrame.transpose*nativeVariation z p*G*nativeVariation z p*
    fullInverse*nativeVariation z p*fullKernelFrame

theorem effective_scaled_remainder (z : ℂ) (p : Fin 4→ℂ) (regular : z • p∈complementRegular) :
    effectiveKernel ⟨z • p,regular⟩=leadingTensor (z • p)+
      z^3 • schurRemainder z p (complementGreen ⟨z • p,regular⟩):=by
  rw [effectiveKernel_source_tensor,complementGreen_delta,active_delta_scaled,higher_scaled]
  simp only [mul_neg,neg_mul,mul_smul_comm,smul_mul_assoc,smul_smul,
    schurRemainder,smul_add,mul_assoc]
  module

theorem frequencyRay_scaled (epsilon s : ℝ) (n : PhysicalMomentum) :
    frequencyRay epsilon s n=(epsilon:ℂ)^2 • physicalFrequencyMomentum s n:=by
  funext i
  fin_cases i
  · change -Complex.I*((s*epsilon^2:ℝ):ℂ)=(epsilon:ℂ)^2*(-Complex.I*(s:ℂ))
    push_cast;ring
  · change Complex.I*((epsilon^2*n 0:ℝ):ℂ)=(epsilon:ℂ)^2*(Complex.I*(n 0:ℂ))
    push_cast;ring
  · change Complex.I*((epsilon^2*n 1:ℝ):ℂ)=(epsilon:ℂ)^2*(Complex.I*(n 1:ℂ))
    push_cast;ring
  · change Complex.I*((epsilon^2*n 2:ℝ):ℂ)=(epsilon:ℂ)^2*(Complex.I*(n 2:ℂ))
    push_cast;ring

/-- No division by the source scale appears in the complete sixth-order remainder. -/
theorem rayEffective_exact_remainder (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) :
    rayEffective e s n direction=leadingTensor (frequencyRay e.val s.val n)+
      (e.val:ℂ)^6 • schurRemainder ((e.val:ℂ)^2) (physicalFrequencyMomentum s.val n)
        (complementGreen (rayPoint e s n direction)):=by
  have h:=effective_scaled_remainder ((e.val:ℂ)^2) (physicalFrequencyMomentum s.val n)
    (by rw [←frequencyRay_scaled];exact (rayPoint e s n direction).property)
  simpa only [←frequencyRay_scaled,←pow_mul,show (2:ℕ)*3=6 from rfl,rayEffective,rayPoint,PreparationVacuumFullOriginResponse.controlledPoint] using h

/-- The same source matrix inverse, with its local legal domain proved separately. -/
def unrestrictedGreen (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullComplementProjection*(complementKernel p)⁻¹*fullComplementProjection

def rayRemainder (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ:=
  schurRemainder ((epsilon:ℂ)^2) (physicalFrequencyMomentum s n)
    (unrestrictedGreen (frequencyRay epsilon s n))

def regularScaling (epsilon : ℝ) : Matrix (Fin 5) (Fin 5) ℂ:=
  Matrix.diagonal (fun i=>if i.val<3 then 1 else (epsilon:ℂ))

def scaledRemainder (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 5) (Fin 5) ℂ:=
  regularScaling epsilon*(slowFastFrame.transpose*rayRemainder epsilon s n*slowFastFrame).submatrix fiveIndex fiveIndex*
    regularScaling epsilon

/-- The zero-scale continuation is defined by source coefficients and the original complementary inverse. -/
def extendedTensor (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 5) (Fin 5) ℂ:=
  characteristicTensor s n+(epsilon:ℂ) • characteristicMix s n+(epsilon:ℂ)^2 • characteristicFast s n+
    (epsilon:ℂ)^2 • scaledRemainder epsilon s n

theorem extendedTensor_origin (s : ℝ) (n : PhysicalMomentum) :
    extendedTensor 0 s n=characteristicTensor s n:=by
  simp only [extendedTensor,Complex.ofReal_zero,zero_smul,add_zero,zero_pow (by decide : 2≠0)]

private theorem scaling_submatrix (e : ℝ) (M : Matrix (Fin 289) (Fin 289) ℂ) :
    (wideRayScaling e*M*wideRayScaling e).submatrix fiveIndex fiveIndex=
      rayScaling e*M.submatrix fiveIndex fiveIndex*rayScaling e:=by
  ext i j
  simp only [wideRayScaling,rayScaling,Matrix.submatrix_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,fiveIndex]
  simp only [i.isLt,j.isLt,if_true]

private theorem regularScaling_identity (epsilon : ℝ) (nonzero : epsilon≠0) :
    rayScaling epsilon=(epsilon:ℂ)⁻¹^2 • regularScaling epsilon:=by
  have ne : (epsilon:ℂ)≠0:=Complex.ofReal_ne_zero.mpr nonzero
  ext i j
  simp only [rayScaling,regularScaling,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> field_simp
  simp only [zero_mul]

/-- The continued tensor is exactly the complete physical field tensor at every legal nonzero scale. -/
theorem extendedTensor_actual (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) : extendedTensor e.val s.val n=normalizedEffective e s n direction:=by
  have nonzero : e.val≠0:=e.property.1.ne'
  have ne : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr nonzero
  have exactR : rayEffective e s n direction=leadingTensor (frequencyRay e.val s.val n)+
      (e.val:ℂ)^6 • rayRemainder e.val s.val n:=rayEffective_exact_remainder e s n direction
  have split : (slowFastFrame.transpose*rayEffective e s n direction*slowFastFrame).submatrix fiveIndex fiveIndex=
      slowFastLeadingFive (frequencyRay e.val s.val n)+
        (e.val:ℂ)^6 • (slowFastFrame.transpose*rayRemainder e.val s.val n*slowFastFrame).submatrix fiveIndex fiveIndex:=by
    rw [exactR]
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,slowFastLeadingFive]
    rfl
  unfold PreparationVacuumPhysicalCharacteristic.normalizedEffective
  rw [scaling_submatrix,split,mul_add,add_mul,normalizedLeading_generated e.val s.val n nonzero]
  rw [regularScaling_identity e.val nonzero]
  simp only [mul_smul_comm,smul_mul_assoc,smul_smul]
  have factor : (e.val:ℂ)⁻¹^2*((e.val:ℂ)^6*(e.val:ℂ)⁻¹^2)=(e.val:ℂ)^2:=by field_simp
  simp only [←mul_assoc] at factor
  simp only [←mul_assoc]
  rw [factor]
  rfl

end LowEnergy.PreparationVacuumPhysicalPoleSheet
