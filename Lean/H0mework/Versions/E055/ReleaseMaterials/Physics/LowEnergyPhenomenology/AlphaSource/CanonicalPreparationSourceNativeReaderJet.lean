import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualCurrentResidues
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeSchurResponse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeSlowCoupling
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedControl
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open PreparationVacuumStaticPoleResponse CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel originalReadback originalChange fullKernelFrame fullInverse
  unrestrictedGreen rawEffectiveReader activeProjection fullComplementProjection complementKernel

/-- The complete source reader before the five-coordinate restriction. -/
def sourceNativeReader (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  rawEffectiveReader p*activeProjection*originalReadback p

def sourceReadbackTerms : List SourceTerm := reflectedTerms originalChangeTerms

def sourceLinearPart (terms : List SourceTerm) (v : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  degreeTensor (positiveTerms terms) 1 v

def sourceHigherTerms (terms : List SourceTerm) : List SourceTerm :=
  (positiveTerms terms).filter (fun a=> !(decide (a.powers.total=1)))

private theorem sourceMatrix_split (terms : List SourceTerm) (select : SourceTerm→Bool) (p : Fin 4→ℂ) :
    sourceMatrix terms p=sourceMatrix (terms.filter select) p+sourceMatrix (terms.filter (fun a=> !(select a))) p := by
  induction terms with
  | nil=>simp only [List.filter_nil,sourceMatrix,List.map_nil,List.sum_nil,add_zero]
  | cons a rest ih=>
    cases selected:select a <;>
      simp only [List.filter_cons,selected,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,
        sourceMatrix_cons] at ih ⊢
    all_goals rw [ih];abel

/-- Every coefficient is selected from the original source list; no derivative is supplied. -/
theorem sourceMatrix_first_return (terms : List SourceTerm) (z : ℂ) (v : Fin 4→ℂ) :
    sourceMatrix terms (z • v)-sourceMatrix terms 0-z • sourceLinearPart terms v=
      sourceMatrix (sourceHigherTerms terms) (z • v) := by
  rw [sourceMatrix_delta,sourceMatrix_split (positiveTerms terms) (fun a=>decide (a.powers.total=1))]
  change degreeTensor (positiveTerms terms) 1 (z • v)+sourceMatrix (sourceHigherTerms terms) (z • v)-
    z • sourceLinearPart terms v=_
  rw [degreeTensor_scaled,pow_one]
  unfold sourceLinearPart
  abel

private theorem minimum_degree_price (terms : List SourceTerm) (d : ℕ)
    (degrees : ∀a∈terms,d≤a.powers.total) (p : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (small : r≤1) (bound : ∀i,‖p i‖≤r) :
    ‖sourceMatrix terms p‖≤(termsPrice terms:ℝ)*r^d := by
  induction terms with
  | nil=>simp only [sourceMatrix,List.map_nil,List.sum_nil,norm_zero,termsPrice,Rat.cast_zero,zero_mul,le_refl]
  | cons a rest ih=>
    have power:r^a.powers.total≤r^d := pow_le_pow_of_le_one nonneg small (degrees a (by simp))
    have first:‖a.matrix p‖≤(coefficientPrice a.coefficient:ℝ)*r^d :=
      (sourceTerm_price a p r nonneg bound).trans
        (mul_le_mul_of_nonneg_left power (by exact_mod_cast coefficientPrice_nonneg a.coefficient))
    have tail:=ih (fun b hb=>degrees b (by simp [hb]))
    rw [sourceMatrix_cons]
    calc
      _≤‖a.matrix p‖+‖sourceMatrix rest p‖ := norm_add_le _ _
      _≤(coefficientPrice a.coefficient:ℝ)*r^d+(termsPrice rest:ℝ)*r^d := add_le_add first tail
      _=(termsPrice (a::rest):ℝ)*r^d := by
        change _=((coefficientPrice a.coefficient+termsPrice rest : ℚ):ℝ)*r^d
        push_cast
        ring

theorem sourceMatrix_higher_price (terms : List SourceTerm) (p : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (small : r≤1) (bound : ∀i,‖p i‖≤r) :
    ‖sourceMatrix (sourceHigherTerms terms) p‖≤(termsPrice (sourceHigherTerms terms):ℝ)*r^2 := by
  apply minimum_degree_price _ 2 _ p r nonneg small bound
  intro a member
  have positive:=of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp member).1).2
  have different : a.powers.total≠1 := by
    simpa only [Bool.not_eq_true',decide_eq_false_iff_not] using (List.mem_filter.mp member).2
  omega

theorem sourceMatrix_bounded (terms : List SourceTerm) (p : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (small : r≤1) (bound : ∀i,‖p i‖≤r) :
    ‖sourceMatrix terms p‖≤(termsPrice terms:ℝ) := by
  simpa only [pow_zero,mul_one] using minimum_degree_price terms 0 (fun a _=>Nat.zero_le _) p r nonneg small bound

theorem sourceReadback_generated (p : Fin 4→ℂ) : sourceMatrix sourceReadbackTerms p=originalReadback p := by
  unfold sourceReadbackTerms originalReadback originalChange
  exact reflectedTerms_value originalChangeTerms p

private theorem kernel_left_zero : fullKernelFrame.transpose*activeKernel 0=0 := by
  have source:=congrArg Matrix.transpose fullKernel_origin
  have reflected : (activeKernel 0).transpose=activeKernel 0 := by
    simpa only [neg_zero] using PreparationVacuumMixedEffective.activeKernel_reflect (0 : Fin 4→ℂ)
  simpa only [Matrix.transpose_mul,Matrix.transpose_zero,reflected] using source

private theorem kernel_left_active : fullKernelFrame.transpose*activeProjection=fullKernelFrame.transpose := by
  have source:=congrArg Matrix.transpose fullKernel_active
  simpa only [Matrix.transpose_mul,activeProjection,projectionMatrix,Matrix.diagonal_transpose] using source

theorem sourceNativeReader_origin : sourceNativeReader 0=fullNativeOrigin.transpose := by
  unfold sourceNativeReader rawEffectiveReader
  rw [kernel_left_zero,zero_mul,sub_zero,kernel_left_active]
  simp only [fullNativeOrigin,Matrix.transpose_mul,originalReadback,neg_zero]

def sourceNativeReaderFirst (v : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fullKernelFrame.transpose*activeProjection*sourceLinearPart sourceReadbackTerms v-
    fullKernelFrame.transpose*sourceLinearPart activeTerms v*fullInverse*activeProjection*originalReadback 0

def sourceNativeRemainder (z : ℂ) (v : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fullKernelFrame.transpose*activeProjection*sourceMatrix (sourceHigherTerms sourceReadbackTerms) (z • v)-
    fullKernelFrame.transpose*sourceMatrix (sourceHigherTerms activeTerms) (z • v)*unrestrictedGreen (z • v)*
      activeProjection*originalReadback (z • v)-
    z • (fullKernelFrame.transpose*sourceLinearPart activeTerms v*(unrestrictedGreen (z • v)-fullInverse)*
      activeProjection*originalReadback (z • v))-
    z • (fullKernelFrame.transpose*sourceLinearPart activeTerms v*fullInverse*activeProjection*
      (originalReadback (z • v)-originalReadback 0))

private theorem reader_taylor {R : Type*} [Ring R] [Algebra ℂ R]
    (N P K K0 K1 G B V V0 V1 : R) (z : ℂ) (zero : N*K0=0) :
    ((N-N*K*G)*P*V-N*P*V0)-z • (N*P*V1-N*K1*B*P*V0)=
      N*P*(V-V0-z • V1)-N*(K-K0-z • K1)*G*P*V-
        z • (N*K1*(G-B)*P*V)-z • (N*K1*B*P*(V-V0)) := by
  have killed : N*(K0*(G*(P*V)))=0 := by rw [←mul_assoc,zero,zero_mul]
  have delta : (N-N*K*G)*P*V-N*P*V0=N*P*(V-V0)-N*(K-K0)*G*P*V := by
    simp only [sub_mul,mul_sub,mul_assoc,killed]
    abel
  rw [delta]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,smul_sub,mul_assoc]
  module

/-- Exact full source Taylor remainder, including the complete complementary return. -/
theorem sourceNativeReader_first_return (z : ℂ) (v : Fin 4→ℂ) :
    sourceNativeReader (z • v)-fullNativeOrigin.transpose-z • sourceNativeReaderFirst v=
      sourceNativeRemainder z v := by
  have generated:=reader_taylor fullKernelFrame.transpose activeProjection (activeKernel (z • v)) (activeKernel 0)
    (sourceLinearPart activeTerms v) (unrestrictedGreen (z • v)) fullInverse (originalReadback (z • v))
    (originalReadback 0) (sourceLinearPart sourceReadbackTerms v) z kernel_left_zero
  have readRemainder:=sourceMatrix_first_return sourceReadbackTerms z v
  rw [sourceReadback_generated,sourceReadback_generated] at readRemainder
  have kernelRemainder : activeKernel (z • v)-activeKernel 0-z • sourceLinearPart activeTerms v=
      sourceMatrix (sourceHigherTerms activeTerms) (z • v) := by
    simpa only [activeKernel] using sourceMatrix_first_return activeTerms z v
  rw [readRemainder,kernelRemainder] at generated
  have origin : fullNativeOrigin.transpose=fullKernelFrame.transpose*activeProjection*originalReadback 0 := by
    rw [←sourceNativeReader_origin,sourceNativeReader,rawEffectiveReader,kernel_left_zero,zero_mul,sub_zero]
  simpa only [sourceNativeReader,rawEffectiveReader,origin,sourceNativeReaderFirst,sourceNativeRemainder] using generated


def sourceReaderRadius (v : Fin 4→ℂ) : ℝ :=
  PreparationVacuumFullOriginResponse.sourceRadius/(1+‖v‖)

def sourceReaderScale (z : ℂ) (v : Fin 4→ℂ) : ℝ := ‖z‖*(1+‖v‖)

def sourceReaderBudget : ℝ :=
  ‖fullKernelFrame.transpose‖*‖activeProjection‖*
    ((termsPrice (sourceHigherTerms sourceReadbackTerms):ℝ)+
      (termsPrice (sourceHigherTerms activeTerms):ℝ)*(2*PreparationVacuumFullOriginResponse.inverseBudget)*
        (termsPrice sourceReadbackTerms:ℝ)+
      (termsPrice (degreeTerms (positiveTerms activeTerms) 1):ℝ)*
        (2*PreparationVacuumFullOriginResponse.inverseBudget^2*variationBudget)*(termsPrice sourceReadbackTerms:ℝ)+
      (termsPrice (degreeTerms (positiveTerms activeTerms) 1):ℝ)*‖fullInverse‖*
        (termsPrice (positiveTerms sourceReadbackTerms):ℝ))

def sourceReaderErrorBudget (v : Fin 4→ℂ) : ℝ := sourceReaderBudget*(1+‖v‖)^2

theorem sourceReaderRadius_positive (v : Fin 4→ℂ) : 0<sourceReaderRadius v :=
  div_pos PreparationVacuumFullOriginResponse.sourceRadius_pos (by positivity)

theorem sourceReaderScale_bound (z : ℂ) (v : Fin 4→ℂ) (small : ‖z‖ ≤ sourceReaderRadius v) :
    sourceReaderScale z v≤PreparationVacuumFullOriginResponse.sourceRadius := by
  exact (le_div_iff₀ (show 0<1+‖v‖ by positivity)).mp small

theorem sourceReader_point_bound (z : ℂ) (v : Fin 4→ℂ) (i : Fin 4) :
    ‖(z • v) i‖ ≤ sourceReaderScale z v := by
  simp only [Pi.smul_apply,norm_smul,sourceReaderScale]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm v i).trans (by linarith)) (norm_nonneg z)

private theorem linear_price (terms : List SourceTerm) (z : ℂ) (v : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (bound : ∀i,‖(z • v) i‖≤r) :
    ‖z • sourceLinearPart terms v‖≤(termsPrice (degreeTerms (positiveTerms terms) 1):ℝ)*r := by
  have scaled : sourceMatrix (degreeTerms (positiveTerms terms) 1) (z • v)=z • sourceLinearPart terms v := by
    simpa only [degreeTensor,pow_one,sourceLinearPart] using degreeTensor_scaled (positiveTerms terms) 1 z v
  rw [←scaled]
  have homogeneous : ∀a∈degreeTerms (positiveTerms terms) 1,a.powers.total=1 := by
    intro a member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  simpa only [pow_one] using sourceMatrix_homogeneous_price _ 1 homogeneous (z • v) r nonneg bound

private theorem norm_product3 {R : Type*} [NormedRing R] (A B C : R) (c : ℝ) (bound : ‖C‖≤c) :
    ‖A*B*C‖≤‖A‖*‖B‖*c :=
  (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le A B) bound (norm_nonneg C)
    (mul_nonneg (norm_nonneg A) (norm_nonneg B)))

private theorem norm_product5 {R : Type*} [NormedRing R] (A B C D E : R) (b c e : ℝ)
    (boundB : ‖B‖≤b) (boundC : ‖C‖≤c) (boundE : ‖E‖≤e) :
    ‖A*B*C*D*E‖≤‖A‖*b*c*‖D‖*e := by
  have bpos : 0≤b := (norm_nonneg B).trans boundB
  have cpos : 0≤c := (norm_nonneg C).trans boundC
  have epos : 0≤e := (norm_nonneg E).trans boundE
  calc
    _≤‖A*B*C*D‖*‖E‖ := norm_mul_le _ _
    _≤(‖A*B*C‖*‖D‖)*‖E‖ := by gcongr;exact norm_mul_le _ _
    _≤((‖A*B‖*‖C‖)*‖D‖)*‖E‖ := by gcongr;exact norm_mul_le _ _
    _≤(((‖A‖*‖B‖)*‖C‖)*‖D‖)*‖E‖ := by gcongr;exact norm_mul_le _ _
    _≤_ := by gcongr

private theorem norm_sub4 {R : Type*} [SeminormedAddCommGroup R] (A B C D : R) :
    ‖A-B-C-D‖≤‖A‖+‖B‖+‖C‖+‖D‖ := by
  calc
    _≤‖A-B-C‖+‖D‖ := norm_sub_le _ _
    _≤(‖A-B‖+‖C‖)+‖D‖ := add_le_add (norm_sub_le _ _) le_rfl
    _≤_ := add_le_add (add_le_add (norm_sub_le A B) le_rfl) le_rfl

/-- The source complementary inverse and original coefficients price the full quadratic remainder. -/
theorem sourceNativeReader_remainder_price (z : ℂ) (v : Fin 4→ℂ)
    (small : ‖z‖ ≤ sourceReaderRadius v) :
    ‖sourceNativeRemainder z v‖ ≤ sourceReaderErrorBudget v*‖z‖^2 := by
  let r:=sourceReaderScale z v
  have nonneg : 0≤r := by unfold r sourceReaderScale;positivity
  have cap : r≤PreparationVacuumFullOriginResponse.sourceRadius := sourceReaderScale_bound z v small
  have smallR : r≤1 := cap.trans PreparationVacuumFullOriginResponse.sourceRadius_le_one
  have point : ∀i,‖(z • v) i‖≤r := sourceReader_point_bound z v
  have global : ∀i,‖(z • v) i‖≤PreparationVacuumFullOriginResponse.sourceRadius := fun i=>(point i).trans cap
  have green : ‖unrestrictedGreen (z • v)‖≤2*PreparationVacuumFullOriginResponse.inverseBudget :=
    by simpa only [unrestrictedGreen,complementGreen,PreparationVacuumFullOriginResponse.controlledPoint] using complementGreen_price (z • v) global
  have greenDelta : ‖unrestrictedGreen (z • v)-fullInverse‖≤
      2*PreparationVacuumFullOriginResponse.inverseBudget^2*variationBudget*r :=
    by simpa only [unrestrictedGreen,complementGreen,PreparationVacuumFullOriginResponse.controlledPoint] using complementGreen_delta_price (z • v) r nonneg cap point
  have highK:=sourceMatrix_higher_price activeTerms (z • v) r nonneg smallR point
  have highR:=sourceMatrix_higher_price sourceReadbackTerms (z • v) r nonneg smallR point
  have lowK:=linear_price activeTerms z v r nonneg point
  have read : ‖originalReadback (z • v)‖≤(termsPrice sourceReadbackTerms:ℝ) := by
    rw [←sourceReadback_generated]
    exact sourceMatrix_bounded sourceReadbackTerms (z • v) r nonneg smallR point
  have readDelta : ‖originalReadback (z • v)-originalReadback 0‖≤
      (termsPrice (positiveTerms sourceReadbackTerms):ℝ)*r := by
    rw [←sourceReadback_generated,←sourceReadback_generated,sourceMatrix_delta]
    exact sourceMatrix_positive_price sourceReadbackTerms (z • v) r nonneg smallR point
  have first:=norm_product3 fullKernelFrame.transpose activeProjection
    (sourceMatrix (sourceHigherTerms sourceReadbackTerms) (z • v)) _ highR
  have second:=norm_product5 fullKernelFrame.transpose
    (sourceMatrix (sourceHigherTerms activeTerms) (z • v)) (unrestrictedGreen (z • v)) activeProjection
    (originalReadback (z • v)) _ _ _ highK green read
  have third:=norm_product5 fullKernelFrame.transpose (z • sourceLinearPart activeTerms v)
    (unrestrictedGreen (z • v)-fullInverse) activeProjection (originalReadback (z • v)) _ _ _ lowK greenDelta read
  have fourth:=norm_product5 fullKernelFrame.transpose (z • sourceLinearPart activeTerms v)
    fullInverse activeProjection (originalReadback (z • v)-originalReadback 0) _ _ _ lowK le_rfl readDelta
  have expression : sourceNativeRemainder z v=
      fullKernelFrame.transpose*activeProjection*sourceMatrix (sourceHigherTerms sourceReadbackTerms) (z • v)-
      fullKernelFrame.transpose*sourceMatrix (sourceHigherTerms activeTerms) (z • v)*unrestrictedGreen (z • v)*
        activeProjection*originalReadback (z • v)-
      fullKernelFrame.transpose*(z • sourceLinearPart activeTerms v)*(unrestrictedGreen (z • v)-fullInverse)*
        activeProjection*originalReadback (z • v)-
      fullKernelFrame.transpose*(z • sourceLinearPart activeTerms v)*fullInverse*activeProjection*
        (originalReadback (z • v)-originalReadback 0) := by
    simp only [sourceNativeRemainder,mul_smul_comm,smul_mul_assoc]
  rw [expression]
  calc
    _≤‖fullKernelFrame.transpose*activeProjection*sourceMatrix (sourceHigherTerms sourceReadbackTerms) (z • v)‖+
      ‖fullKernelFrame.transpose*sourceMatrix (sourceHigherTerms activeTerms) (z • v)*unrestrictedGreen (z • v)*activeProjection*originalReadback (z • v)‖+
      ‖fullKernelFrame.transpose*(z • sourceLinearPart activeTerms v)*(unrestrictedGreen (z • v)-fullInverse)*activeProjection*originalReadback (z • v)‖+
      ‖fullKernelFrame.transpose*(z • sourceLinearPart activeTerms v)*fullInverse*activeProjection*(originalReadback (z • v)-originalReadback 0)‖ := norm_sub4 _ _ _ _
    _≤‖fullKernelFrame.transpose‖*‖activeProjection‖*((termsPrice (sourceHigherTerms sourceReadbackTerms):ℝ)*r^2)+
      ‖fullKernelFrame.transpose‖*((termsPrice (sourceHigherTerms activeTerms):ℝ)*r^2)*(2*PreparationVacuumFullOriginResponse.inverseBudget)*‖activeProjection‖*(termsPrice sourceReadbackTerms:ℝ)+
      ‖fullKernelFrame.transpose‖*((termsPrice (degreeTerms (positiveTerms activeTerms) 1):ℝ)*r)*(2*PreparationVacuumFullOriginResponse.inverseBudget^2*variationBudget*r)*‖activeProjection‖*(termsPrice sourceReadbackTerms:ℝ)+
      ‖fullKernelFrame.transpose‖*((termsPrice (degreeTerms (positiveTerms activeTerms) 1):ℝ)*r)*‖fullInverse‖*‖activeProjection‖*((termsPrice (positiveTerms sourceReadbackTerms):ℝ)*r) :=
      add_le_add (add_le_add (add_le_add first second) third) fourth
    _=sourceReaderErrorBudget v*‖z‖^2 := by unfold sourceReaderErrorBudget sourceReaderBudget r sourceReaderScale;ring

theorem sourceNativeReader_error (z : ℂ) (v : Fin 4→ℂ) (small : ‖z‖ ≤ sourceReaderRadius v) :
    ‖sourceNativeReader (z • v)-fullNativeOrigin.transpose-z • sourceNativeReaderFirst v‖≤
      sourceReaderErrorBudget v*‖z‖^2 := by
  rw [sourceNativeReader_first_return]
  exact sourceNativeReader_remainder_price z v small

private theorem slope_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f a d : E) (z : ℂ) (C : ℝ) (nonzero : z≠0)
    (bound : ‖f-a-z • d‖≤C*‖z‖^2) : ‖z⁻¹ • (f-a)-d‖≤C*‖z‖ := by
  have identity : z⁻¹ • (f-a)-d=z⁻¹ • (f-a-z • d) := by
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  rw [identity,norm_smul,norm_inv]
  calc
    _≤‖z‖⁻¹*(C*‖z‖^2) := mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (norm_nonneg z))
    _=C*‖z‖ := by have nz:=norm_ne_zero_iff.mpr nonzero;field_simp

/-- The first source jet is the actual punctured derivative, on a generated nonempty domain. -/
theorem sourceNativeReader_slope (v : Fin 4→ℂ) :
    Tendsto (fun z : ℂ=>z⁻¹ • (sourceNativeReader (z • v)-fullNativeOrigin.transpose))
      (𝓝[≠] 0) (𝓝 (sourceNativeReaderFirst v)) := by
  have near : ∀ᶠ z : ℂ in 𝓝[≠] 0,‖z‖<sourceReaderRadius v :=
    (continuous_norm.continuousAt.eventually_lt_const
      (by simpa only [norm_zero] using sourceReaderRadius_positive v)).filter_mono nhdsWithin_le_nhds
  have nonzero : ∀ᶠ z : ℂ in 𝓝[≠] 0,z≠0 := by
    exact self_mem_nhdsWithin
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun z=>norm_nonneg
    (z⁻¹ • (sourceNativeReader (z • v)-fullNativeOrigin.transpose)-sourceNativeReaderFirst v)))
  · exact (near.and nonzero).mono (fun z hz=>slope_error _ _ _ z _ hz.2 (sourceNativeReader_error z v hz.1.le))
  · simpa only [norm_zero,mul_zero] using
      (tendsto_const_nhds.mul (continuous_norm.tendsto (0 : ℂ))).mono_left nhdsWithin_le_nhds

theorem sourceNativeReader_derivative (v : Fin 4→ℂ) :
    HasDerivAt (fun z : ℂ=>sourceNativeReader (z • v)) (sourceNativeReaderFirst v) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add,zero_smul,sourceNativeReader_origin] using sourceNativeReader_slope v

end LowEnergy.PreparationVacuumNativeSlowCoupling
