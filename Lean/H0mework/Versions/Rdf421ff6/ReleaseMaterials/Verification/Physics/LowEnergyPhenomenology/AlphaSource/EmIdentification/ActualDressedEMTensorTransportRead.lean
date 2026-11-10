import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMPhysicalTransportJet
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularCoulombCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMSourceTransport
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open PreparationVacuumPhysicalCharacteristic ActualDressedEMTensorClock ActualDressedZeroDamping
open PreparationVacuumPhysicalPoleSheet
open ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion ActualDressedEMZeroClockColumns
open ActualDressedAngularSpherePrice ActualEMCarrierOwn
open ActualDressedAngularSectorFourier ActualDressedNoetherCoulombUnit
open ActualDressedOrderedStatic
open ActualCompositeFieldCurrent
open LowEnergy.ActualDressedVisiblePole Filter Set
open scoped Matrix BigOperators Topology

def sourceTangentSpatialReadJet (P : TangentFrequency) (s : ℂ) : ℂ :=
  (sourceTangentSpatialPolynomial P s).derivative.eval 0

def sourceTangentClockReadJet (P : TangentFrequency) (s : ℂ) : ℂ :=
  (tangentFrequencySpecialize 0 P).derivative.eval s

/-- Both partial derivatives come from the same original polynomial, before selecting a branch. -/
theorem actual_source_tangent_curve_derivative (P : TangentFrequency) (beta : ℝ→ℂ) (s v : ℂ)
    (point : beta 0=s) (derivative : HasDerivAt beta v 0) :
    HasDerivAt (fun t : ℝ => sourceTangentRead P t (beta t))
      (sourceTangentSpatialReadJet P s+v*sourceTangentClockReadJet P s) 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have generated := hP.fun_add hQ
    simpa only [sourceTangentRead,sourceTangentSpatialReadJet,sourceTangentClockReadJet,
      sourceTangentSpatialPolynomial,tangentFrequencySpecialize,map_add,eval_add,derivative_add,mul_add,
      add_assoc,add_left_comm,add_comm] using generated
  | monomial m c =>
    have coefficient := (c.hasDerivAt (0 : ℂ)).comp_ofReal
    have generated := coefficient.fun_mul (derivative.fun_pow m)
    have factor : c.derivative.eval 0*s^m+c.eval 0*((m : ℂ)*s^(m-1)*v)=
        (c*C s^m).derivative.eval 0+v*((monomial m (c.eval 0) : ℂ[X]).derivative.eval s) := by
      simp only [←C_pow,derivative_mul,derivative_C,eval_mul,eval_C,mul_zero,add_zero,
        derivative_monomial,eval_monomial]
      ring
    simp only [point,Complex.ofReal_zero] at generated
    rw [factor] at generated
    simpa only [sourceTangentRead,sourceTangentSpatialReadJet,sourceTangentClockReadJet,
      sourceTangentSpatialPolynomial,tangentFrequencySpecialize,Polynomial.coe_mapRingHom,map_monomial,
      eval_monomial,coe_evalRingHom,Complex.ofReal_zero] using generated

private theorem real_polynomial_zero (P : ℂ[X]) (zero : ∀t : ℝ,P.eval (t : ℂ)=0) : P=0 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro z ⟨t,rfl⟩
  change P.eval (t : ℂ)=(0 : ℂ[X]).eval (t : ℂ)
  simpa only [eval_zero] using zero t

private theorem source_bivariate_zero (P : TangentFrequency)
    (zero : ∀t s : ℝ,sourceTangentRead P t (s : ℂ)=0) : P=0 := by
  have every : ∀t : ℝ,tangentFrequencySpecialize t P=0 :=
    fun t => real_polynomial_zero _ (zero t)
  apply Polynomial.ext
  intro j
  change P.coeff j=0
  apply real_polynomial_zero
  intro t
  have paid := congrArg (fun Q : ℂ[X] => Q.coeff j) (every t)
  simpa only [tangentFrequencySpecialize,Polynomial.coe_mapRingHom,coeff_map,coe_evalRingHom,coeff_zero] using paid

/-- The original positive-damping source denominator makes the tangent carrier nonzero. -/
theorem actual_source_tangent_clearing_nonzero (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) :
    sourceTangentClearing event eps n delta≠0 := by
  intro vanish
  have oldZero : fullClockClearing event eps n=0 := by
    have paid := actual_tangent_full_clearing event eps 0 n delta
    rw [vanish,map_zero] at paid
    simp only [sourceTangentMomentum,zero_smul,add_zero] at paid
    exact paid.symm
  have value : MvPolynomial.eval (ActualDressedUniformMaterialCoefficients.irValues eps 1 0)
      (ActualDressedUniformMaterialCoefficients.commonDenominator event n)=0 := by
    have paid := congrArg (fun P : (ℂ[X])[X] => (ActualDressedOrderedStatic.clockSpecialize 0 P).eval (1 : ℂ)) oldZero
    rw [←frequency_damping_eval eps 0 1 (ActualDressedUniformMaterialCoefficients.commonDenominator event n)]
    simpa only [fullClockClearing,frequency_clock_specialize,map_zero,eval_zero,Complex.ofReal_one] using paid
  exact ActualDressedUniformClockNonzero.actual_common_ir_denominator_nonzero event n eps 1 0 (by norm_num) value

/-- A real nonempty derivative chart is generated from the original source, before any root branch is selected. -/
theorem actual_source_tangent_chart_exists (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) :
    ∃t s : ℝ,sourceTangentRead (sourceTangentThresholdClearing event eps n delta) t (s : ℂ)≠0 := by
  have lead : sourceTangentThresholdClearing event eps n delta≠0 := by
    simpa only [sourceTangentThresholdClearing,sourceTangentOrder] using
      (coeff_natTrailingDegree_ne_zero.mpr (actual_source_tangent_clearing_nonzero event eps n delta))
  by_contra h
  push Not at h
  exact lead (source_bivariate_zero _ h)

/-- The full threshold determinant retains every mode and every constraint. -/
def sourceTangentDispersion (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) : TangentFrequency :=
  (sourceTangentThresholdPencil event eps n delta).det

theorem actual_source_tangent_dispersion (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum)
    (regular : tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)≠0) :
    tangentFrequencySpecialize t (sourceTangentDispersion event eps n delta)=
      (zeroClockPencil event eps (sourceTangentMomentum n delta t)).det := by
  rw [sourceTangentDispersion,(tangentFrequencySpecialize t).map_det]
  exact congrArg Matrix.det (actual_tangent_threshold_pencil event eps t n delta regular)

/-- Each actual visible EM pole is a root of this same spatial/frequency source determinant. -/
theorem actual_em_source_tangent_dispersion_root (event : DressedEvent) (eps t s : ℝ) (n delta : PhysicalMomentum)
    (mu nu : Fin 4)
    (regular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) t (s : ℂ)≠0)
    (balanced : PencilClockBalanced event eps (sourceTangentMomentum n delta t))
    (finite : EMColumnsClockFinite event eps (sourceTangentMomentum n delta t))
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps (sourceTangentMomentum n delta t) mu nu)) :
    sourceTangentRead (sourceTangentDispersion event eps n delta) t (s : ℂ)=0 := by
  have polyRegular : tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)≠0 := by
    intro h
    exact regular (by simp [sourceTangentRead,h])
  have clearing := actual_tangent_threshold_clearing event eps t n delta polyRegular
  have oldRegular : (zeroClockClearing event eps (sourceTangentMomentum n delta t)).eval (s : ℂ)≠0 := by
    rw [←clearing]
    exact regular
  have mode := actual_zero_clock_em_full_mode event eps (sourceTangentMomentum n delta t) mu nu (s : ℂ) balanced finite root
  have kernel := actual_zero_clock_em_threshold_kernel event eps s (sourceTangentMomentum n delta t) mu nu balanced finite oldRegular root
  let v := actualEMZeroClockMode event eps (sourceTangentMomentum n delta t) nu (s : ℂ)
  have nonzero : v≠0 := mode.1
  have some : ∃i,v i≠0 := by
    by_contra h
    push Not at h
    exact nonzero (funext h)
  obtain ⟨i,hi⟩ := some
  have clearedKernel : ((zeroClockPencil event eps (sourceTangentMomentum n delta t)).map (eval (s : ℂ)))*ᵥv=0 := by
    have identity : (zeroClockPencil event eps (sourceTangentMomentum n delta t)).map (eval (s : ℂ))=
        (zeroClockClearing event eps (sourceTangentMomentum n delta t)).eval (s : ℂ) •
          zeroClockThresholdPencil event eps s (sourceTangentMomentum n delta t) := by
      funext i j
      simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,zeroClockThresholdPencil]
      field_simp [oldRegular]
    rw [identity,Matrix.smul_mulVec,kernel,smul_zero]
  have det := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors clearedKernel
    (mem_nonZeroDivisors_of_ne_zero hi)
  rw [sourceTangentRead,actual_source_tangent_dispersion event eps t n delta polyRegular]
  have mapped := (evalRingHom (s : ℂ)).map_det (zeroClockPencil event eps (sourceTangentMomentum n delta t))
  exact mapped.trans det

/-- An actual differentiable real pole branch pays its directional group-dispersion equation.
    No phase-speed, isotropy or simple-pole premise enters this source derivative. -/
theorem actual_em_source_group_dispersion (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum)
    (mu nu : Fin 4) (beta : ℝ→ℝ) (v : ℂ)
    (derivative : HasDerivAt (fun t : ℝ => (beta t : ℂ)) v 0)
    (regular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) 0 (beta 0 : ℂ)≠0)
    (sourceChart : ∀ᶠt in 𝓝 (0 : ℝ),
        PencilClockBalanced event eps (sourceTangentMomentum n delta t) ∧
        EMColumnsClockFinite event eps (sourceTangentMomentum n delta t) ∧
        (beta t : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps (sourceTangentMomentum n delta t) mu nu)) :
    sourceTangentSpatialReadJet (sourceTangentDispersion event eps n delta) (beta 0 : ℂ)+
      v*sourceTangentClockReadJet (sourceTangentDispersion event eps n delta) (beta 0 : ℂ)=0 := by
  have generated := actual_source_tangent_curve_derivative (sourceTangentDispersion event eps n delta)
    (fun t : ℝ => (beta t : ℂ)) (beta 0 : ℂ) v rfl derivative
  have clearing := actual_source_tangent_curve_derivative (sourceTangentThresholdClearing event eps n delta)
    (fun t : ℝ => (beta t : ℂ)) (beta 0 : ℂ) v rfl derivative
  have regularChart := clearing.continuousAt.eventually_ne regular
  have zero : (fun t : ℝ => sourceTangentRead (sourceTangentDispersion event eps n delta) t (beta t : ℂ))
      =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
    filter_upwards [sourceChart,regularChart] with t chart ht
    exact actual_em_source_tangent_dispersion_root event eps t (beta t) n delta mu nu
      ht chart.1 chart.2.1 chart.2.2
  exact (generated.congr_of_eventuallyEq zero.symm).unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

/-- Nondegenerate clock charts solve the actual branch derivative; degenerate charts keep the spatial constraint. -/
theorem actual_em_source_group_price (P : TangentFrequency) (s v : ℂ)
    (source : sourceTangentSpatialReadJet P s+v*sourceTangentClockReadJet P s=0) :
    (sourceTangentClockReadJet P s≠0 → v= -sourceTangentSpatialReadJet P s/sourceTangentClockReadJet P s) ∧
      (sourceTangentClockReadJet P s=0 → sourceTangentSpatialReadJet P s=0) := by
  constructor
  · intro clock
    apply (eq_div_iff clock).2
    linear_combination source
  · intro clock
    simpa only [clock,mul_zero,add_zero] using source

/-- Original omega=eps²*s and k=eps²*n transform both tangent derivatives together. -/
theorem actual_source_physical_branch_tangent (eps : ℝ) (n delta : PhysicalMomentum) (beta : ℝ→ℝ) (v : ℂ)
    (derivative : HasDerivAt (fun t : ℝ => (beta t : ℂ)) v 0) :
    HasDerivAt (fun t : ℝ => (sourceFrequency eps (beta t) : ℂ)) ((eps^2 : ℂ)*v) 0 ∧
      HasDerivAt (fun t : ℝ => (eps^2 : ℝ) • sourceTangentMomentum n delta t) ((eps^2 : ℝ) • delta) 0 := by
  constructor
  · simpa only [sourceFrequency,Complex.ofReal_mul,Complex.ofReal_pow] using derivative.const_mul (eps^2 : ℂ)
  · apply hasDerivAt_pi.2
    intro j
    simpa only [sourceTangentMomentum,Pi.add_apply,Pi.smul_apply,smul_eq_mul,id_eq,one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (delta j)).const_add (n j)).const_mul (eps^2)

def directionTangentPolynomial (n delta : PhysicalMomentum) : DirectionParameters→+*ℂ[X] :=
  MvPolynomial.eval₂Hom C (fun j => C (n j : ℂ)+X*C (delta j : ℂ))

theorem actual_direction_tangent_polynomial (P : DirectionParameters) (n delta : PhysicalMomentum) (t : ℝ) :
    (directionTangentPolynomial n delta P).eval (t : ℂ)=
      MvPolynomial.eval (directionValues (sourceTangentMomentum n delta t)) P := by
  have hom : (evalRingHom (t : ℂ)).comp (directionTangentPolynomial n delta)=
      MvPolynomial.eval (directionValues (sourceTangentMomentum n delta t)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [directionTangentPolynomial]
    · intro j
      simp [directionTangentPolynomial,directionValues,sourceTangentMomentum,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      exact mul_comm _ _
  exact congrArg (fun f : DirectionParameters→+*ℂ => f P) hom

def directionSquarePolynomial (n delta : PhysicalMomentum) : ℂ[X] :=
  ∑j : Fin 3,(C (n j : ℂ)+X*C (delta j : ℂ))^2

theorem actual_direction_square_polynomial (n delta : PhysicalMomentum) (t : ℝ) :
    (directionSquarePolynomial n delta).eval (t : ℂ)=(spatialSquare (sourceTangentMomentum n delta t) : ℂ) := by
  simp only [directionSquarePolynomial,eval_pow,eval_add,eval_C,eval_mul,eval_X,
    spatialSquare,sourceTangentMomentum,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Fin.sum_univ_three,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]

/-- The whole four-tensor has one original Noether vertex square and one physical 4π read.
    The minus and q remove precisely the ordered spatial normalization; no directional average enters. -/
def actualSourceCoulombTensor (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-(spatialSquare n : ℂ)*(noetherPairScale : ℂ)^2/(4*(Real.pi : ℂ))) • directionEMCoefficient event n

def sourceCoulombTangentNumerator (event : DressedEvent) (n delta : PhysicalMomentum) (mu nu : Fin 4) : ℂ[X] :=
  directionSquarePolynomial n delta*
    directionTangentPolynomial n delta ((directionScaledNumerator event (directionZeroClockEM event mu nu)).coeff 0)*
      C ((noetherPairScale : ℂ)^2/(4*(Real.pi : ℂ)))

def sourceCoulombTangentDenominator (event : DressedEvent) (n delta : PhysicalMomentum) : ℂ[X] :=
  directionTangentPolynomial n delta (directionLeadingDenominator event)

attribute [local irreducible] sourceCoulombTangentNumerator sourceCoulombTangentDenominator
  directionLeadingDenominator directionLeadingRead directionScaledNumerator directionZeroClockEM

theorem actual_source_coulomb_tangent_denominator (event : DressedEvent) (n delta : PhysicalMomentum) (t : ℝ) :
    (sourceCoulombTangentDenominator event n delta).eval (t : ℂ)=
      directionLeadingRead event (sourceTangentMomentum n delta t) := by
  simpa only [sourceCoulombTangentDenominator,directionLeadingRead] using
    actual_direction_tangent_polynomial (directionLeadingDenominator event) n delta t

def sourceCoulombTensorSpatialJet (event : DressedEvent) (n delta : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu =>
    let A := sourceCoulombTangentNumerator event n delta mu nu
    let d := sourceCoulombTangentDenominator event n delta
    (A.derivative.eval 0*d.eval 0-A.eval 0*d.derivative.eval 0)/(d.eval 0)^2

theorem actual_source_coulomb_tensor_fraction (event : DressedEvent) (n delta : PhysicalMomentum) (t : ℝ) (mu nu : Fin 4) :
    actualSourceCoulombTensor event (sourceTangentMomentum n delta t) mu nu=
      (sourceCoulombTangentNumerator event n delta mu nu).eval (t : ℂ)/
        (sourceCoulombTangentDenominator event n delta).eval (t : ℂ) := by
  simp only [actualSourceCoulombTensor,Matrix.smul_apply,smul_eq_mul,directionEMCoefficient,directionCoulombCoefficient,
    sourceCoulombTangentNumerator,sourceCoulombTangentDenominator,eval_mul,eval_C,
    actual_direction_square_polynomial,actual_direction_tangent_polynomial,directionLeadingRead]
  ring

/-- The source angular feedback generates the entire Coulomb-tensor derivative, including its denominator derivative. -/
theorem actual_source_coulomb_tensor_spatial_derivative (event : DressedEvent) (n delta : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) :
    HasDerivAt (fun t : ℝ => actualSourceCoulombTensor event (sourceTangentMomentum n delta t))
      (sourceCoulombTensorSpatialJet event n delta) 0 := by
  have denominator : (sourceCoulombTangentDenominator event n delta).eval 0≠0 := by
    have point := actual_source_coulomb_tangent_denominator event n delta 0
    simp only [Complex.ofReal_zero,sourceTangentMomentum,zero_smul,add_zero] at point
    rw [point]
    exact regular
  apply hasDerivAt_pi.2
  intro mu
  apply hasDerivAt_pi.2
  intro nu
  have generated := ((sourceCoulombTangentNumerator event n delta mu nu).hasDerivAt (0 : ℂ)).div
    ((sourceCoulombTangentDenominator event n delta).hasDerivAt (0 : ℂ)) denominator
  simpa only [actual_source_coulomb_tensor_fraction,sourceCoulombTensorSpatialJet,Complex.ofReal_zero,
    Pi.div_apply] using generated.comp_ofReal

/-- Each coordinate requested to be direction independent has this exact source condition.
    The full tensor remains available for the actual constrained physical read. -/
theorem actual_source_coulomb_tensor_constant_condition (event : DressedEvent) (n delta : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) (mu nu : Fin 4) :
    sourceCoulombTensorSpatialJet event n delta mu nu=0 ↔
      (sourceCoulombTangentNumerator event n delta mu nu).derivative.eval 0*
        (sourceCoulombTangentDenominator event n delta).eval 0=
      (sourceCoulombTangentNumerator event n delta mu nu).eval 0*
        (sourceCoulombTangentDenominator event n delta).derivative.eval 0 := by
  have denominator : (sourceCoulombTangentDenominator event n delta).eval 0≠0 := by
    have point := actual_source_coulomb_tangent_denominator event n delta 0
    simp only [Complex.ofReal_zero,sourceTangentMomentum,zero_smul,add_zero] at point
    rw [point]
    exact regular
  simp only [sourceCoulombTensorSpatialJet,div_eq_zero_iff,pow_ne_zero 2 denominator,or_false,sub_eq_zero]

/-- The source tensor is the actual complete EM ordered response in the original Noether/Fourier units. -/
theorem actual_source_coulomb_tensor_ordered_return (event : DressedEvent) (pd ps n : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (regular : directionLeadingRead event n≠0)
    (clock : DirectionClockFinite event pd ps dL dR sL sR)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    (∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n))) ∧
    Tendsto (fun eps : ℝ => (-(spatialSquare n : ℂ)*noetherPairScale^2/(4*(Real.pi : ℂ))) •
      (-(eps : ℂ)^4 • zeroClockEMRead event eps n))
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (actualSourceCoulombTensor event n)) := by
  have finite := actual_direction_clock_finite event n pd ps dL dR sL sR regular clock
  constructor
  · filter_upwards [actual_direction_original_chart event n regular] with eps chart
    apply tendsto_pi_nhds.2
    intro mu
    apply tendsto_pi_nhds.2
    intro nu
    exact actual_zero_clock_em_entry event eps n chart.1 mu nu (finite.1 mu nu)
  · simpa only [actualSourceCoulombTensor] using
      (actual_direction_coulomb_coefficient event pd ps dL dR sL sR n regular spatial).1.const_smul
        (-(spatialSquare n : ℂ)*noetherPairScale^2/(4*(Real.pi : ℂ)))

end LowEnergy.GaussComposite.ActualDressedEMSourceTransport
