import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticTable
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelRadialResponse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumStaticSpatialSource PreparationPhysicalChannelGreen
open PreparationPhysicalChannelRadialJet PreparationPhysicalCommonSpatialGreen
open PreparationVacuumChargedSpatialResponse PreparationVacuumChargedLongRangeRead
open CanonicalGradedSpatialSource MeasureTheory Filter Set
open scoped Matrix BigOperators Topology SchwartzMap

/-- The existing source Gaussian fundamental kernel before its channel coefficient. -/
def emRegulatedNewton : ℂ→ℝ→PhysicalMomentum→ℂ := paidRadialGreen% greenKernel

def emNewtonMultiplier (kappa : ℂ) (d : ℝ) (frequency : PhysicalMomentum) : ℂ :=
  ((spatialSquare (sourceSpatialMomentum frequency):ℂ)+(d:ℂ)^2*kappa^2)⁻¹

/-- Exact normalization of the original source kernel, retaining its own complex mass and regulator. -/
theorem em_newton_source_kernel (branch : Fin 2) (negative : Bool) (eta : ℝ) (channel : Fin 3)
    (d : ℝ) (x : PhysicalMomentum) :
    emRegulatedNewton (sourceChannelMass branch negative eta channel) d x=
      (sourceChargedSpatialCoefficient channel:ℂ)*sourceChannelFundamentalKernel branch negative eta channel d x := by
  have nonzero : (sourceChargedSpatialCoefficient channel:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (sourceChargedSpatialCoefficient_positive channel).ne'
  simp only [sourceChannelFundamentalKernel,←mul_assoc,mul_inv_cancel₀ nonzero,one_mul,emRegulatedNewton]

/-- The original radial return fixes the Newton 4pi coefficient, without selecting an EM scalar coupling. -/
theorem em_newton_source_radial (branch : Fin 2) (negative : Bool) (eta : ℝ) (positive : 0<eta)
    (channel : Fin 3) (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    Tendsto (fun d : ℝ=>emRegulatedNewton (sourceChannelMass branch negative eta channel) d x)
      (𝓝[>] 0) (𝓝 ((4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹)) := by
  have generated:=(sourceChannelFundamentalKernel_radial branch negative eta positive channel x spatial).const_mul
    (sourceChargedSpatialCoefficient channel:ℂ)
  have nonzero : (sourceChargedSpatialCoefficient channel:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (sourceChargedSpatialCoefficient_positive channel).ne'
  have value : (sourceChargedSpatialCoefficient channel:ℂ)*
      (4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient channel:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹=
      (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹ := by
    rw [show 4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient channel:ℂ)*(Real.sqrt (spatialSquare x):ℂ)=
      (sourceChargedSpatialCoefficient channel:ℂ)*(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare x):ℂ)) by ring,mul_inv_rev]
    field_simp [nonzero]
  simpa only [←em_newton_source_kernel,value] using generated

private theorem em_newton_integrable (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d) :
    Integrable (emRegulatedNewton kappa d) :=
  (paidRadialGreen% greenKernel_integrable) kappa positive d radial

private theorem em_newton_fourier (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (frequency : PhysicalMomentum) :
    (∫x : PhysicalMomentum,sourceSpatialPhase (-frequency) x*emRegulatedNewton kappa d x)=
      emNewtonMultiplier kappa d frequency :=
  (paidRadialGreen% greenKernel_fourier) kappa positive d radial frequency

private theorem em_phase_norm (frequency x : PhysicalMomentum) : ‖sourceSpatialPhase frequency x‖=1 := by
  simp [sourceSpatialPhase,Complex.norm_exp]

private theorem em_newton_bound (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (frequency : PhysicalMomentum) :
    ‖emNewtonMultiplier kappa d frequency‖≤∫x : PhysicalMomentum,‖emRegulatedNewton kappa d x‖ := by
  rw [←em_newton_fourier kappa positive d radial frequency]
  have generated:=norm_integral_le_integral_norm (μ:=volume)
    (fun x : PhysicalMomentum=>sourceSpatialPhase (-frequency) x*emRegulatedNewton kappa d x)
  simpa only [norm_mul,em_phase_norm,one_mul] using generated

private theorem em_newton_denominator_nonzero (kappa : ℂ) (positive : 0<kappa.re)
    (d : ℝ) (radial : 0<d) (frequency : PhysicalMomentum) :
    (spatialSquare (sourceSpatialMomentum frequency):ℂ)+(d:ℂ)^2*kappa^2≠0 := by
  have rate:=(paidRadialGreen% kernel_rate_positive) kappa positive d radial (sourceSpatialMomentum frequency)
  have nonzero : kappa≠0 := by
    intro zero
    rw [zero,Complex.zero_re] at positive
    exact lt_irrefl _ positive
  intro zero
  have identity : ((spatialSquare (sourceSpatialMomentum frequency):ℂ)+(d:ℂ)^2*kappa^2)/kappa=
      (spatialSquare (sourceSpatialMomentum frequency):ℂ)/kappa+(d:ℂ)^2*kappa := by field_simp
  rw [←identity,zero,zero_div,Complex.zero_re] at rate
  exact lt_irrefl _ rate

private theorem em_newton_continuous (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d) :
    Continuous (emNewtonMultiplier kappa d) := by
  unfold emNewtonMultiplier
  apply Continuous.inv₀
  · unfold sourceSpatialMomentum spatialSquare
    fun_prop
  · exact em_newton_denominator_nonzero kappa positive d radial

private def emWord (word : List (Fin 3)) (frequency : PhysicalMomentum) : ℂ :=
  (word.map (fun j=>Complex.I*(sourceSpatialMomentum frequency j:ℂ))).prod

def emFourierMoment (H : PhysicalMomentum→ℂ) (word : List (Fin 3))
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,emWord word frequency*sourceSpatialPhase frequency x*test frequency*H frequency

private theorem em_word_continuous (word : List (Fin 3)) : Continuous (emWord word) := by
  apply continuous_list_prod
  intro j _
  unfold sourceSpatialMomentum
  fun_prop

private theorem em_coordinate_bound (frequency : PhysicalMomentum) (j : Fin 3) :
    ‖Complex.I*(sourceSpatialMomentum frequency j:ℂ)‖≤(2*Real.pi)*‖frequency‖ := by
  rw [norm_mul,Complex.norm_I,one_mul]
  simp only [sourceSpatialMomentum,Pi.smul_apply,smul_eq_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm frequency j) (by positivity)

private theorem em_word_bound (word : List (Fin 3)) (frequency : PhysicalMomentum) :
    ‖emWord word frequency‖≤(2*Real.pi)^word.length*‖frequency‖^word.length := by
  induction word with
  | nil=>simp [emWord]
  | cons j word ih=>
    change ‖(Complex.I*(sourceSpatialMomentum frequency j:ℂ))*emWord word frequency‖≤_
    rw [norm_mul,List.length_cons]
    calc
      _≤((2*Real.pi)*‖frequency‖)*((2*Real.pi)^word.length*‖frequency‖^word.length) :=
        mul_le_mul (em_coordinate_bound frequency j) ih (norm_nonneg _) (by positivity)
      _=_ := by ring

private theorem em_moment_bound (H : PhysicalMomentum→ℂ) (bound : ℝ) (bounded : ∀frequency,‖H frequency‖≤bound)
    (word : List (Fin 3)) (test : 𝓢(PhysicalMomentum,ℂ)) (x frequency : PhysicalMomentum) :
    ‖emWord word frequency*sourceSpatialPhase frequency x*test frequency*H frequency‖≤
      ((2*Real.pi)^word.length*bound)*(‖frequency‖^word.length*‖test frequency‖) := by
  simp only [norm_mul,em_phase_norm,mul_one]
  calc
    _≤(((2*Real.pi)^word.length*‖frequency‖^word.length)*‖test frequency‖)*bound :=
      mul_le_mul (mul_le_mul_of_nonneg_right (em_word_bound word frequency) (norm_nonneg _))
        (bounded frequency) (norm_nonneg _) (by positivity)
    _=_ := by ring

private theorem em_moment_integrable (H : PhysicalMomentum→ℂ) (continuous : Continuous H)
    (bound : ℝ) (bounded : ∀frequency,‖H frequency‖≤bound)
    (word : List (Fin 3)) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency=>emWord word frequency*sourceSpatialPhase frequency x*test frequency*H frequency) := by
  have phase : Continuous (fun frequency=>sourceSpatialPhase frequency x) := by
    unfold sourceSpatialPhase sourceSpatialMomentum
    fun_prop
  exact ((test.integrable_pow_mul volume word.length).const_mul _).mono'
    ((((em_word_continuous word).mul phase).mul test.continuous).mul continuous).aestronglyMeasurable
    (Eventually.of_forall (em_moment_bound H bound bounded word test x))

private theorem em_phase_shift (frequency x : PhysicalMomentum) (j : Fin 3) (t : ℝ) :
    sourceSpatialPhase frequency (x+t • (Pi.single j 1:PhysicalMomentum))=
      sourceSpatialPhase frequency x*Complex.exp (Complex.I*(sourceSpatialMomentum frequency j:ℂ)*(t:ℂ)) := by
  have dot : (∑k : Fin 3,sourceSpatialMomentum frequency k*(x+t • (Pi.single j 1:PhysicalMomentum)) k)=
      (∑k : Fin 3,sourceSpatialMomentum frequency k*x k)+sourceSpatialMomentum frequency j*t := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same,mul_one]
    · intro k _ different
      rw [Pi.single_eq_of_ne different,mul_zero,mul_zero]
    · simp
  simp only [sourceSpatialPhase,dot,Complex.ofReal_add,Complex.ofReal_mul,mul_add,Complex.exp_add,mul_assoc]

private theorem em_phase_derivative (frequency x : PhysicalMomentum) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ=>sourceSpatialPhase frequency (x+s • (Pi.single j 1 : PhysicalMomentum)))
      (Complex.I*(sourceSpatialMomentum frequency j:ℂ)*sourceSpatialPhase frequency (x+t • (Pi.single j 1 : PhysicalMomentum))) t := by
  simp_rw [em_phase_shift]
  have h:=(((Complex.ofRealCLM.hasFDerivAt (x:=t)).hasDerivAt.const_mul
    (Complex.I*(sourceSpatialMomentum frequency j:ℂ))).cexp).const_mul (sourceSpatialPhase frequency x)
  convert! h using 1
  simp [Complex.ofRealCLM]
  ring

private theorem em_moment_derivative (H : PhysicalMomentum→ℂ) (continuous : Continuous H)
    (bound : ℝ) (bounded : ∀frequency,‖H frequency‖≤bound)
    (word : List (Fin 3)) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ=>emFourierMoment H word test (x+s • (Pi.single j 1:PhysicalMomentum)))
      (emFourierMoment H (j::word) test (x+t • (Pi.single j 1:PhysicalMomentum))) t := by
  have generated:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀:=t) (μ:=volume) (s:=Set.univ) (Filter.univ_mem)
    (F:=fun s frequency=>emWord word frequency*sourceSpatialPhase frequency (x+s • (Pi.single j 1:PhysicalMomentum))*test frequency*H frequency)
    (F':=fun s frequency=>emWord (j::word) frequency*sourceSpatialPhase frequency (x+s • (Pi.single j 1:PhysicalMomentum))*test frequency*H frequency)
    (bound:=fun frequency=>((2*Real.pi)^(j::word).length*bound)*(‖frequency‖^(j::word).length*‖test frequency‖))
    (Eventually.of_forall (fun s=>(em_moment_integrable H continuous bound bounded word test _).aestronglyMeasurable))
    (em_moment_integrable H continuous bound bounded word test _)
    (em_moment_integrable H continuous bound bounded (j::word) test _).aestronglyMeasurable
    (Eventually.of_forall (fun frequency s _=>em_moment_bound H bound bounded (j::word) test _ frequency))
    ((test.integrable_pow_mul volume (j::word).length).const_mul _)
    (Eventually.of_forall (fun frequency s _=>by
      have h:=((em_phase_derivative frequency x j s).const_mul (emWord word frequency)).mul_const (test frequency) |>.mul_const (H frequency)
      simpa only [emWord,List.map_cons,List.prod_cons,mul_assoc,mul_comm,mul_left_comm] using h))
  exact generated.2

/-- Original source-regulated Newton potential tested by a Schwartz packet. -/
def emNewtonPacket (kappa : ℂ) (d : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  emFourierMoment (emNewtonMultiplier kappa d) [] test x

def emPacket (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceSpatialPhase frequency x*test frequency

/-- Genuine source-kernel convolution, retaining the original physical Fourier phase. -/
theorem em_newton_packet_convolution (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emNewtonPacket kappa d test x=∫y : PhysicalMomentum,emRegulatedNewton kappa d y*emPacket test (x-y) := by
  have generated:=(paidRadialGreen% kernel_convolution) kappa positive d radial test test.integrable x
  simp only [emNewtonPacket,emFourierMoment,emWord,List.map_nil,List.prod_nil,one_mul,emPacket,emRegulatedNewton]
  rw [generated]
  congr 1
  funext frequency
  unfold emNewtonMultiplier
  ring

/-- Coordinate derivatives are genuine spatial derivatives of the same regulated Newton convolution. -/
theorem em_newton_packet_hessian (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (i j : Fin 3) :
    deriv (fun t : ℝ=>deriv (fun u : ℝ=>emNewtonPacket kappa d test
      (x+t • (Pi.single i 1:PhysicalMomentum)+u • (Pi.single j 1:PhysicalMomentum))) 0) 0=
      emFourierMoment (emNewtonMultiplier kappa d) [i,j] test x := by
  have first (t : ℝ) : deriv (fun u : ℝ=>emNewtonPacket kappa d test
      (x+t • (Pi.single i 1:PhysicalMomentum)+u • (Pi.single j 1:PhysicalMomentum))) 0=
      emFourierMoment (emNewtonMultiplier kappa d) [j] test (x+t • (Pi.single i 1:PhysicalMomentum)) := by
    have h:=(em_moment_derivative _ (em_newton_continuous kappa positive d radial) _
      (em_newton_bound kappa positive d radial) [] test (x+t • (Pi.single i 1:PhysicalMomentum)) j 0).deriv
    simpa only [emNewtonPacket,zero_smul,add_zero] using h
  simp_rw [first]
  have h:=(em_moment_derivative _ (em_newton_continuous kappa positive d radial) _
    (em_newton_bound kappa positive d radial) [j] test x i 0).deriv
  simpa only [zero_smul,add_zero] using h


/-- Coefficients of the source-generated angular tensor; each unordered monomial occurs once. -/
def emAngularCoefficient (i j : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  let R:=rootTwo*rootFifteen
  if i=0 ∧ j=0 then Matrix.single 1 1 (R*(605677/1206000)) else
  if i=1 ∧ j=1 then Matrix.single 2 2 (R*(605677/1206000)) else
  if i=0 ∧ j=1 then Matrix.single 1 2 (R*(605677/1206000))+Matrix.single 2 1 (R*(605677/1206000)) else
  if i=0 ∧ j=2 then Matrix.single 0 1 (3/80)+Matrix.single 1 0 (3/80)+
    Matrix.single 1 3 (R*(287177/603000))+Matrix.single 3 1 (R*(287177/603000)) else
  if i=1 ∧ j=2 then Matrix.single 0 2 (3/80)+Matrix.single 2 0 (3/80)+
    Matrix.single 2 3 (R*(287177/603000))+Matrix.single 3 2 (R*(287177/603000)) else
  if i=2 ∧ j=2 then Matrix.single 0 0 (R/96)+Matrix.single 0 3 (3/40)+Matrix.single 3 0 (3/40)+
    Matrix.single 3 3 (R*(137677/301500)) else 0

def emRieszSymbol (kappa : ℂ) (d : ℝ) (k : PhysicalMomentum) (i j : Fin 3) : ℂ :=
  (k i:ℂ)*(k j:ℂ)*((spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2)⁻¹

/-- Original finite leading tensor, with the source Gaussian radial regulator on its angular denominator. -/
def emLeadingSymbol (kappa : ℂ) (d : ℝ) (k : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu=>emStaticRegularOrigin mu nu+
    ∑i : Fin 3,∑j : Fin 3,emAngularCoefficient i j mu nu*emRieszSymbol kappa d k i j

set_option maxHeartbeats 2400000 in
/-- At zero regulator the leading symbol is the already computed original full static tensor on every unit direction. -/
theorem em_static_leading_symbol (kappa : ℂ) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    emLeadingSymbol kappa 0 n=emStaticLimitTensor n := by
  rw [em_static_limit_explicit]
  ext mu nu
  simp only [emLeadingSymbol,emRieszSymbol,unit,Complex.ofReal_zero,Complex.ofReal_one,
    zero_pow (by decide : 2≠0),zero_mul,add_zero,inv_one,mul_one,Fin.sum_univ_three,
    em_static_regular_explicit]
  fin_cases mu <;> fin_cases nu <;>
    norm_num [emAngularCoefficient,emStaticExplicit,Matrix.single_apply,Matrix.diagonal_apply,Matrix.cons_val,Fin.ext_iff] <;> ring

/-- Physical inverse Fourier packet of the complete leading EM symbol. -/
def emLeadingPacket (kappa : ℂ) (d : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ := fun mu nu=>
  ∫frequency,sourceSpatialPhase frequency x*test frequency*emLeadingSymbol kappa d (sourceSpatialMomentum frequency) mu nu

def emNewtonHessian (kappa : ℂ) (d : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (i j : Fin 3) : ℂ :=
  deriv (fun t : ℝ=>deriv (fun u : ℝ=>emNewtonPacket kappa d test
    (x+t • (Pi.single i 1:PhysicalMomentum)+u • (Pi.single j 1:PhysicalMomentum))) 0) 0

private theorem em_riesz_integrable (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (i j : Fin 3) :
    Integrable (fun frequency=>sourceSpatialPhase frequency x*test frequency*
      emRieszSymbol kappa d (sourceSpatialMomentum frequency) i j) := by
  have generated:=(em_moment_integrable _ (em_newton_continuous kappa positive d radial) _
    (em_newton_bound kappa positive d radial) [i,j] test x).neg
  convert generated using 1
  funext frequency
  simp only [Pi.neg_apply,emWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    emRieszSymbol,emNewtonMultiplier]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem em_packet_integrable (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency=>sourceSpatialPhase frequency x*test frequency) := by
  have phase : Continuous (fun frequency=>sourceSpatialPhase frequency x) := by
    unfold sourceSpatialPhase sourceSpatialMomentum
    fun_prop
  exact test.integrable.norm.mono' (phase.mul test.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun frequency=>by simp only [norm_mul,em_phase_norm,one_mul];exact le_rfl))

/-- The angular multiplier is the negative Hessian of the original regulated Newton convolution. -/
theorem em_riesz_newton_hessian (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (i j : Fin 3) :
    (∫frequency,sourceSpatialPhase frequency x*test frequency*emRieszSymbol kappa d (sourceSpatialMomentum frequency) i j)=
      -emNewtonHessian kappa d test x i j := by
  rw [emNewtonHessian,em_newton_packet_hessian kappa positive d radial,emFourierMoment,←integral_neg]
  apply integral_congr_ae
  filter_upwards with frequency
  simp only [emWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    emRieszSymbol,emNewtonMultiplier]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Full leading EM inverse Fourier response: explicit local packet plus all source angular Newton Hessians. -/
theorem em_leading_packet_return (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (mu nu : Fin 4) :
    emLeadingPacket kappa d test x mu nu=emStaticRegularOrigin mu nu*emPacket test x-
      ∑i : Fin 3,∑j : Fin 3,emAngularCoefficient i j mu nu*emNewtonHessian kappa d test x i j := by
  have constant:=(em_packet_integrable test x).const_mul (emStaticRegularOrigin mu nu)
  have angular (i j : Fin 3):= (em_riesz_integrable kappa positive d radial test x i j).const_mul
    (emAngularCoefficient i j mu nu)
  have point (frequency : PhysicalMomentum) :
      sourceSpatialPhase frequency x*test frequency*emLeadingSymbol kappa d (sourceSpatialMomentum frequency) mu nu=
      emStaticRegularOrigin mu nu*(sourceSpatialPhase frequency x*test frequency)+
        ∑i : Fin 3,∑j : Fin 3,emAngularCoefficient i j mu nu*
          (sourceSpatialPhase frequency x*test frequency*emRieszSymbol kappa d (sourceSpatialMomentum frequency) i j) := by
    simp only [emLeadingSymbol,mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  unfold emLeadingPacket
  simp_rw [point]
  rw [integral_add constant (integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>angular i j))),
    integral_const_mul,integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>angular i j))]
  simp_rw [integral_finsetSum _ (fun j _=>angular _ j),integral_const_mul,
    em_riesz_newton_hessian kappa positive d radial]
  simp only [mul_neg,Finset.sum_neg_distrib,emPacket,sub_eq_add_neg]


private theorem em_coordinate_square_le (k : PhysicalMomentum) (i : Fin 3) : (k i)^2≤ spatialSquare k := by
  fin_cases i
  · change (k 0)^2≤(k 0)^2+(k 1)^2+(k 2)^2
    nlinarith [sq_nonneg (k 1),sq_nonneg (k 2)]
  · change (k 1)^2≤(k 0)^2+(k 1)^2+(k 2)^2
    nlinarith [sq_nonneg (k 0),sq_nonneg (k 2)]
  · change (k 2)^2≤(k 0)^2+(k 1)^2+(k 2)^2
    nlinarith [sq_nonneg (k 0),sq_nonneg (k 1)]

private theorem em_coordinate_product_le (k : PhysicalMomentum) (i j : Fin 3) :
    |k i| * |k j|≤ spatialSquare k := by
  have hi:=em_coordinate_square_le k i
  have hj:=em_coordinate_square_le k j
  nlinarith [sq_nonneg (|k i|-|k j|),sq_abs (k i),sq_abs (k j)]

private theorem em_denominator_price (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (k : PhysicalMomentum) :
    spatialSquare k*kappa.re≤‖(spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2‖*‖kappa‖ := by
  have knz : kappa≠0 := by
    intro zero
    rw [zero,Complex.zero_re] at positive
    exact lt_irrefl _ positive
  have kp : 0<‖kappa‖:=norm_pos_iff.mpr knz
  have quotient : ((spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2)/kappa=
      (spatialSquare k:ℂ)/kappa+(d:ℂ)^2*kappa := by field_simp
  have real : (((spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2)/kappa).re=
      spatialSquare k*kappa.re/‖kappa‖^2+d^2*kappa.re := by
    rw [quotient]
    simp only [Complex.add_re,Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,zero_div,add_zero,←Complex.ofReal_pow,Complex.mul_re,sub_zero,Complex.normSq_eq_norm_sq]
  have lower : spatialSquare k*kappa.re/‖kappa‖^2≤
      ‖(spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2‖/‖kappa‖ := by
    calc
      _≤(((spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2)/kappa).re := by
        rw [real]
        nlinarith [mul_nonneg (sq_nonneg d) positive.le]
      _≤‖((spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2)/kappa‖ := Complex.re_le_norm _
      _=_ := norm_div _ _
  have generated:=(div_le_iff₀ (sq_pos_of_pos kp)).mp lower
  calc
    _≤(‖(spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2‖/‖kappa‖)*‖kappa‖^2 := generated
    _=_ := by field_simp [kp.ne']

/-- Momentum- and regulator-uniform bound for every angular component, paid by the same source complex mass. -/
theorem em_riesz_uniform_bound (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (k : PhysicalMomentum) (i j : Fin 3) :
    ‖emRieszSymbol kappa d k i j‖≤‖kappa‖/kappa.re := by
  by_cases zero : (spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2=0
  · simp only [emRieszSymbol,zero,inv_zero,mul_zero,norm_zero]
    exact div_nonneg (norm_nonneg _) positive.le
  have dp : 0<‖(spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2‖:=norm_pos_iff.mpr zero
  unfold emRieszSymbol
  rw [norm_mul,norm_mul,norm_inv]
  simp only [Complex.norm_real,Real.norm_eq_abs,←div_eq_mul_inv]
  calc
    _≤ spatialSquare k/‖(spatialSquare k:ℂ)+(d:ℂ)^2*kappa^2‖ :=
      div_le_div_of_nonneg_right (em_coordinate_product_le k i j) dp.le
    _≤‖kappa‖/kappa.re := (div_le_div_iff₀ dp positive).mpr (by nlinarith [em_denominator_price kappa positive d k])

private theorem em_riesz_radial_limit (kappa : ℂ) (k : PhysicalMomentum) (i j : Fin 3) :
    Tendsto (fun d : ℝ=>emRieszSymbol kappa d k i j) (𝓝[>] 0) (𝓝 (emRieszSymbol kappa 0 k i j)) := by
  by_cases origin : spatialSquare k=0
  · have ki : k i=0 := by
      have h:=em_coordinate_square_le k i
      rw [origin] at h
      nlinarith [sq_nonneg (k i)]
    simp only [emRieszSymbol,ki,Complex.ofReal_zero,zero_mul]
    exact tendsto_const_nhds
  · have continuous : ContinuousAt (fun d : ℝ=>emRieszSymbol kappa d k i j) 0 := by
      unfold emRieszSymbol
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.inv₀
      · fun_prop
      · simpa only [Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_mul,add_zero] using
          (Complex.ofReal_ne_zero.mpr origin)
    exact continuous.tendsto.mono_left nhdsWithin_le_nhds

/-- Removal of the original radial regulator is paid inside each actual Schwartz Fourier observation. -/
theorem em_riesz_packet_radial (kappa : ℂ) (positive : 0<kappa.re)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (i j : Fin 3) :
    Tendsto (fun d : ℝ=>∫frequency,sourceSpatialPhase frequency x*test frequency*
      emRieszSymbol kappa d (sourceSpatialMomentum frequency) i j) (𝓝[>] 0)
      (𝓝 (∫frequency,sourceSpatialPhase frequency x*test frequency*
        emRieszSymbol kappa 0 (sourceSpatialMomentum frequency) i j)) := by
  apply tendsto_integral_filter_of_dominated_convergence (μ:=volume)
    (fun frequency=>(‖kappa‖/kappa.re)*‖test frequency‖)
  · filter_upwards [self_mem_nhdsWithin] with d dp
    exact (em_riesz_integrable kappa positive d dp test x i j).aestronglyMeasurable
  · exact Eventually.of_forall (fun d=>Eventually.of_forall (fun frequency=>by
      simp only [norm_mul,em_phase_norm,one_mul]
      calc
        _≤‖test frequency‖*(‖kappa‖/kappa.re) :=
          mul_le_mul_of_nonneg_left (em_riesz_uniform_bound kappa positive d _ i j) (norm_nonneg _)
        _=_ := by ring))
  · exact test.integrable.norm.const_mul _
  · exact Eventually.of_forall (fun frequency=>
      (tendsto_const_nhds (x:=sourceSpatialPhase frequency x*test frequency)).mul
        (em_riesz_radial_limit kappa (sourceSpatialMomentum frequency) i j))


private def emLeadingPrice (kappa : ℂ) (mu nu : Fin 4) : ℝ :=
  ‖emStaticRegularOrigin mu nu‖+∑i : Fin 3,∑j : Fin 3,‖emAngularCoefficient i j mu nu‖*(‖kappa‖/kappa.re)

private theorem em_leading_bound (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (k : PhysicalMomentum) (mu nu : Fin 4) :
    ‖emLeadingSymbol kappa d k mu nu‖≤emLeadingPrice kappa mu nu := by
  unfold emLeadingSymbol emLeadingPrice
  calc
    _≤‖emStaticRegularOrigin mu nu‖+‖∑i : Fin 3,∑j : Fin 3,emAngularCoefficient i j mu nu*emRieszSymbol kappa d k i j‖ := norm_add_le _ _
    _≤‖emStaticRegularOrigin mu nu‖+∑i : Fin 3,‖∑j : Fin 3,emAngularCoefficient i j mu nu*emRieszSymbol kappa d k i j‖ :=
      add_le_add le_rfl (norm_sum_le _ _)
    _≤‖emStaticRegularOrigin mu nu‖+∑i : Fin 3,∑j : Fin 3,‖emAngularCoefficient i j mu nu*emRieszSymbol kappa d k i j‖ := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _≤_ := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (em_riesz_uniform_bound kappa positive d k i j) (norm_nonneg _)

private theorem em_leading_measurable (kappa : ℂ) (d : ℝ) (test : 𝓢(PhysicalMomentum,ℂ))
    (x : PhysicalMomentum) (mu nu : Fin 4) :
    Measurable (fun frequency=>sourceSpatialPhase frequency x*test frequency*
      emLeadingSymbol kappa d (sourceSpatialMomentum frequency) mu nu) := by
  unfold emLeadingSymbol emRieszSymbol sourceSpatialPhase sourceSpatialMomentum spatialSquare
  fun_prop

/-- The complete sixteen-entry leading Fourier observation has an actual dominated radial limit. -/
theorem em_leading_packet_radial (kappa : ℂ) (positive : 0<kappa.re)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (mu nu : Fin 4) :
    Tendsto (fun d : ℝ=>emLeadingPacket kappa d test x mu nu) (𝓝[>] 0)
      (𝓝 (emLeadingPacket kappa 0 test x mu nu)) := by
  unfold emLeadingPacket
  apply tendsto_integral_filter_of_dominated_convergence (μ:=volume)
    (fun frequency=>emLeadingPrice kappa mu nu*‖test frequency‖)
  · exact Eventually.of_forall (fun d=>(em_leading_measurable kappa d test x mu nu).aestronglyMeasurable)
  · exact Eventually.of_forall (fun d=>Eventually.of_forall (fun frequency=>by
      simp only [norm_mul,em_phase_norm,one_mul]
      calc
        _≤‖test frequency‖*emLeadingPrice kappa mu nu :=
          mul_le_mul_of_nonneg_left (em_leading_bound kappa positive d _ mu nu) (norm_nonneg _)
        _=_ := by ring))
  · exact test.integrable.norm.const_mul _
  · apply Eventually.of_forall
    intro frequency
    apply Tendsto.mul tendsto_const_nhds
    unfold emLeadingSymbol
    apply Tendsto.add tendsto_const_nhds
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (em_riesz_radial_limit kappa (sourceSpatialMomentum frequency) i j).const_mul _


/-- The zero-regulator symbol uses the original physical radial momentum, while retaining its complete unit-direction tensor. -/
theorem em_leading_physical_ray (kappa : ℂ) (r : ℝ) (nonzero : r≠0)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    emLeadingSymbol kappa 0 (r • n)=emStaticLimitTensor n := by
  have square : spatialSquare (r • n)=r^2 := by
    calc
      _=r^2*spatialSquare n := by simp only [spatialSquare,Pi.smul_apply,smul_eq_mul];ring
      _=_ := by rw [unit,mul_one]
  have same (i j : Fin 3) : emRieszSymbol kappa 0 (r • n) i j=emRieszSymbol kappa 0 n i j := by
    simp only [emRieszSymbol,Pi.smul_apply,smul_eq_mul,square,unit,Complex.ofReal_zero,Complex.ofReal_one,
      zero_pow (by decide : 2≠0),zero_mul,add_zero,inv_one,mul_one,Complex.ofReal_pow,Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr nonzero]
  rw [←em_static_leading_symbol kappa n unit]
  ext mu nu
  simp only [emLeadingSymbol,same]

end LowEnergy.GaussComposite.ActualEMCarrierOwn
