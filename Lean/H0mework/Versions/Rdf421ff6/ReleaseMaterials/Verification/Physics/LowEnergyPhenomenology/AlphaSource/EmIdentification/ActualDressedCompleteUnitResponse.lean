import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourceActionUnitPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMWholeUnitCovariance
open SaturationMonoid.PhysicsCore CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open SourcePropagationNativeActionHessian GaussCoreHilbert PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumNoetherChart
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedFrequencyHalf
open ActualDressedEMTensorClock ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMCarrierOwn ActualEMResponseSplit PreparationVacuumCurrentSignalOperator ActualCompositeFieldCurrent
open PreparationVacuumCurrentNativeLaplaceBridge
open ActualDressedFieldCovariance ActualElectronWholeNoetherObserver
open PreparationVacuumGaugeSourceInjection PreparationVacuumPhysicalHalfAxis
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := ActualElectronWholeNoetherObserver.realOperators
local instance : NormedAlgebra ℚ (H→L[ℂ]H) := ActualElectronWholeNoetherObserver.rationalOperators
attribute [local irreducible] dressedNoetherKernel actualFullNoetherVariation actualPhysicalEulerObserver
  unitWindowResponse unitWindowPencil dressedNativeWindowPencil emInsertion frequencyResponsePencil
  correctedGreen correctedDet frequencyHalfPolarization frequencyInputNormalizer
  jointGenerator jointResolvent physicalTime noetherReader

def sourceUnitFieldMatrix (u : SourceUnits) : Matrix (Fin 289) (Fin 289) ℝ := u.field • 1

private theorem field_matrix_value (u : SourceUnits) :
    sourceUnitMatrix (sourceUnitFieldMatrix u)=(u.field : ℂ) • (1 : Matrix (Fin 289) (Fin 289) ℂ) := by
  funext i j
  by_cases same : i=j
  · subst j
    simp [sourceUnitMatrix,sourceUnitFieldMatrix,Matrix.map_apply,Matrix.smul_apply]
  · simp [sourceUnitMatrix,sourceUnitFieldMatrix,Matrix.map_apply,Matrix.smul_apply,same]

def sourceUnitResponseFactor (u : SourceUnits) : ℂ :=
  (sourceDensityUnit u : ℂ)*(u.field : ℂ)^2

theorem source_unit_response_factor_nonzero (u : SourceUnits) : sourceUnitResponseFactor u≠0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
    (div_ne_zero (pow_ne_zero _ u.length_positive.ne') u.energy_positive.ne'))
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr u.field_nonzero))

private theorem inverse_real_smul {A : Type*} [Ring A] [Algebra ℝ A]
    (c : ℝ) (nonzero : c≠0) (a : A) : Ring.inverse (c • a)=c⁻¹ • Ring.inverse a := by
  let unit : Aˣ := {
    val := c • 1
    inv := c⁻¹ • 1
    val_inv := by simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,
      one_mul,inv_mul_cancel₀ nonzero,one_smul]
    inv_val := by simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,
      one_mul,mul_inv_cancel₀ nonzero,one_smul] }
  have same : c • a=(unit : A)*a := by
    change c • a=(c • (1:A))*a
    rw [Algebra.smul_mul_assoc,one_mul]
  rw [same,Ring.inverse_mul (Or.inl unit.isUnit),Ring.inverse_unit]
  change Ring.inverse a*(c⁻¹ • (1:A))=c⁻¹ • Ring.inverse a
  rw [Algebra.mul_smul_comm,mul_one]

private theorem clock_scalar {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (c t : ℝ) (a : V) :
    t • ((-Complex.I) • (c • a))=(c*t) • ((-Complex.I) • a) := by
  rw [smul_comm (-Complex.I) c,smul_smul,mul_comm t c]

private theorem clock_five_product {A : Type*} [Ring A] [Algebra ℝ A]
    (c : ℝ) (nonzero : c≠0) (a b j d e : A) :
    c • (a*(c⁻¹ • b)*(c • j)*(c⁻¹ • d)*e)=a*b*j*d*e := by
  simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
  have scalar : c*(c⁻¹*(c*(c⁻¹)))=1 := by
    field_simp [nonzero]
  rw [scalar,one_smul]

def sourceUnitOccurrenceGenerator (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (f : Field289) : H→L[ℂ]H :=
  sourceUnitGenerator u (u.length • p) F ((u.time : ℂ)*z) f

theorem source_unit_occurrence_generator (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (f : Field289) :
    sourceUnitOccurrenceGenerator u p F z f=u.time • jointGenerator p F z (u.field • f) := by
  have clock : ((u.time : ℂ)*z)/(u.time : ℂ)=z := by
    exact mul_div_cancel_left₀ z (Complex.ofReal_ne_zero.mpr u.time_positive.ne')
  simp only [sourceUnitOccurrenceGenerator,sourceUnitGenerator,smul_smul,
    inv_mul_cancel₀ u.length_positive.ne',one_smul,clock]

def sourceUnitCircuitTime (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (age : ℝ) (f : Field289) : H→L[ℂ]H :=
  SourceFiniteUnitary.time (sourceUnitOccurrenceGenerator u p F 0 f) age

theorem source_unit_circuit_time (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (age : ℝ) (f : Field289) :
    sourceUnitCircuitTime u p F age f=physicalTime p F (u.time*age) (u.field • f) := by
  rw [sourceUnitCircuitTime,source_unit_occurrence_generator,physicalTime,SourceFiniteUnitary.time]
  exact congrArg (NormedSpace.exp : (H→L[ℂ]H)→(H→L[ℂ]H))
    (clock_scalar (V:=H→L[ℂ]H) u.time age (jointGenerator p F 0 (u.field • f)))

def sourceUnitCircuitResolvent (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (f : Field289) : H→L[ℂ]H :=
  Ring.inverse (sourceUnitOccurrenceGenerator u p F z f)

theorem source_unit_circuit_inverse (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (f : Field289) :
    sourceUnitCircuitResolvent u p F z f=u.time⁻¹ • jointResolvent p F z (u.field • f) := by
  unfold sourceUnitCircuitResolvent jointResolvent
  exact (congrArg Ring.inverse (source_unit_occurrence_generator u p F z f)).trans
    (inverse_real_smul u.time u.time_positive.ne' _)

def sourceUnitCircuitNoetherReader (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (reader f : Field289) : H→L[ℂ]H :=
  u.time • noetherReader (u.field • reader) p F (u.field • f)

def sourceUnitRawNoetherKernel (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (f : Field289) : H→L[ℂ]H :=
  let p := event.momentum-u.length⁻¹ • transfer
  sourceUnitCircuitTime u p event.frame (-age) f*
    sourceUnitCircuitResolvent u p event.frame event.energy f*
    sourceUnitCircuitNoetherReader u event.momentum event.frame reader f*
    sourceUnitCircuitResolvent u event.momentum event.frame event.energy f*
    sourceUnitCircuitTime u event.momentum event.frame age f

/-- The canonical action reader pays the clock conversion on the actual five-factor frequency circuit. -/
def sourceUnitNoetherKernel (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (f : Field289) : H→L[ℂ]H :=
  u.time • sourceUnitRawNoetherKernel u event transfer reader age f

theorem source_unit_complete_circuit (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (f : Field289) :
    sourceUnitNoetherKernel u event transfer reader age f=
      dressedNoetherKernel event (u.length⁻¹ • transfer) (u.field • reader) (u.time*age) (u.field • f) := by
  simp only [sourceUnitNoetherKernel,sourceUnitRawNoetherKernel,sourceUnitCircuitNoetherReader,
    source_unit_circuit_time,source_unit_circuit_inverse,mul_neg,dressedNoetherKernel]
  exact clock_five_product u.time u.time_positive.ne' _ _ _ _ _

def sourceUnitNoetherVariation (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (age : ℝ) : H→L[ℂ]H :=
  deriv (fun r : ℝ => sourceUnitNoetherKernel u event transfer reader age (r • force)) 0

attribute [local irreducible] sourceUnitNoetherKernel sourceUnitNoetherVariation

/-- All five original factors, both time slopes, both inverse slopes and the complete Noether contact survive. -/
theorem source_unit_noether_five_generated (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (age : ℝ) :
    sourceUnitNoetherVariation u event transfer reader force age=
      actualFullNoetherVariation event (u.length⁻¹ • transfer) (u.field • reader) (u.field • force) (u.time*age) := by
  have original := actual_full_noether_kernel_field_generated event (u.length⁻¹ • transfer)
    (u.field • reader) (u.field • force) (u.time*age)
  have same : (fun r : ℝ => sourceUnitNoetherKernel u event transfer reader age (r • force))=
      (fun r : ℝ => dressedNoetherKernel event (u.length⁻¹ • transfer)
        (u.field • reader) (u.time*age) (r • (u.field • force))) := by
    funext r
    rw [source_unit_complete_circuit]
    exact congrArg (dressedNoetherKernel event (u.length⁻¹ • transfer)
      (u.field • reader) (u.time*age)) (smul_comm u.field r force)
  unfold sourceUnitNoetherVariation
  exact (congrArg (fun f : ℝ→(H→L[ℂ]H) => deriv f 0) same).trans original.deriv

/-- Density and clock conversion are applied to the actual whole-H observer, retaining its physical state and background. -/
def sourceUnitPhysicalNoetherObserver (u : SourceUnits) (event : DressedEvent) (leg : CompositeLeg) :
    (H→L[ℂ]H)→L[ℂ]ℂ :=
  (sourceDensityUnit u : ℂ) • actualPhysicalEulerObserver event leg

theorem source_unit_actual_noether_observation (u : SourceUnits) (event : DressedEvent) (leg : CompositeLeg)
    (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    sourceUnitPhysicalNoetherObserver u event leg (sourceUnitNoetherVariation u event transfer reader force age)=
      (sourceDensityUnit u : ℂ)*actualPhysicalEulerObserver event leg
        (actualFullNoetherVariation event (u.length⁻¹ • transfer) (u.field • reader) (u.field • force) (u.time*age)) := by
  simp only [sourceUnitPhysicalNoetherObserver,smul_apply,smul_eq_mul]
  exact congrArg (fun A : H→L[ℂ]H => (sourceDensityUnit u : ℂ)*actualPhysicalEulerObserver event leg A)
    (source_unit_noether_five_generated u event transfer reader force age)

/-- The input is the original actual nonlinear Euler/window consumer in changed field units. -/
def sourceUnitActualWindowResponse (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (a : Fin 289→ℂ) : Fin 289→ℂ :=
  ((sourceDensityUnit u : ℂ)/(u.time : ℂ)) •
    unitWindowResponse event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p)
      (sourceUnitFieldMatrix u) (lambda/(u.time : ℂ)) (u.time*T) a

def sourceUnitWindowPencil (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  ((sourceDensityUnit u : ℂ)/(u.time : ℂ)) •
    unitWindowPencil event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p)
      (sourceUnitFieldMatrix u) (lambda/(u.time : ℂ)) (u.time*T)

theorem source_unit_actual_window_generated (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (future : 0≤T) (a : Fin 289→ℂ)
    (inside : u.time*T<sourceUnitDuration event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p)
      (sourceUnitFieldMatrix u) a) :
    sourceUnitActualWindowResponse u event transfer p lambda T a=sourceUnitWindowPencil u event transfer p lambda T*ᵥa := by
  rw [sourceUnitActualWindowResponse,unit_window_generated event (u.length⁻¹ • transfer)
    (sourceUnitFourierMomentum u p) (sourceUnitFieldMatrix u) (lambda/(u.time : ℂ))
    (u.time*T) (mul_nonneg u.time_positive.le future) a inside,sourceUnitWindowPencil,Matrix.smul_mulVec]

theorem source_unit_window_complete_covariance (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) :
    sourceUnitWindowPencil u event transfer p lambda T=(sourceUnitResponseFactor u/(u.time : ℂ)) •
      dressedNativeWindowPencil event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p)
        (lambda/(u.time : ℂ)) (u.time*T) := by
  rw [sourceUnitWindowPencil,unitWindowPencil,field_matrix_value,Matrix.transpose_smul,Matrix.transpose_one,
    Matrix.smul_mul,Matrix.one_mul,Matrix.mul_smul,Matrix.mul_one,smul_smul,smul_smul]
  apply congrArg (fun c : ℂ => c • _)
  unfold sourceUnitResponseFactor
  ring

def sourceUnitInputScalar (u : SourceUnits) (p : Fin 4→ℂ) (lambda : ℂ) : ℂ :=
  ∫t in Ioi (0:ℝ),Complex.exp
    (((sourceUnitFourierMomentum u p) 0-lambda/(u.time : ℂ))*((u.time*t : ℝ) : ℂ))

theorem source_unit_input_scalar_generated (u : SourceUnits) (p : Fin 4→ℂ) (lambda : ℂ) :
    sourceUnitInputScalar u p lambda=(u.time : ℂ)⁻¹*
      sourcePlaneHalfScalar ((sourceUnitFourierMomentum u p) 0) (lambda/(u.time : ℂ)) := by
  have generated := integral_comp_mul_left_Ioi
    (fun t : ℝ => Complex.exp (((sourceUnitFourierMomentum u p) 0-lambda/(u.time : ℂ))*(t : ℂ))) 0 u.time_positive
  change _=(u.time : ℂ)⁻¹*(∫t in Ioi (0:ℝ),Complex.exp
    (((sourceUnitFourierMomentum u p) 0-lambda/(u.time : ℂ))*(t : ℂ)))
  rw [mul_zero] at generated
  refine generated.trans ?_
  change ((u.time⁻¹ : ℝ) : ℂ)*_=(u.time : ℂ)⁻¹*_
  rw [Complex.ofReal_inv]

def sourceUnitInputNormalizer (u : SourceUnits) (p : Fin 4→ℂ) (lambda : ℂ) : ℂ :=
  (sourceUnitInputScalar u p lambda)⁻¹

theorem source_unit_input_normalizer_generated (u : SourceUnits) (p : Fin 4→ℂ) (lambda : ℂ) :
    sourceUnitInputNormalizer u p lambda=(u.time : ℂ)*
      frequencyInputNormalizer (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ)) := by
  rw [sourceUnitInputNormalizer,source_unit_input_scalar_generated,mul_inv_rev,inv_inv,frequencyInputNormalizer]
  ring

/-- Each entry is the original source quantum derivative on the changed field amplitude and reader. -/
def sourceUnitQuantumMatrix (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => (sourceDensityUnit u : ℂ)*((sourceUnitMatrix (sourceUnitFieldMatrix u)).transpose*ᵥ
    dressedSignalQuadrature event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (u.time*t)
      (sourceUnitMatrix (sourceUnitFieldMatrix u)*ᵥPi.single j 1)) i

theorem source_unit_actual_quantum_matrix (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) :
    sourceUnitQuantumMatrix u event transfer p t=sourceUnitResponseFactor u •
      dressedSignalMatrix event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (u.time*t) := by
  have source : sourceUnitQuantumMatrix u event transfer p t=(sourceDensityUnit u : ℂ) •
      ((sourceUnitMatrix (sourceUnitFieldMatrix u)).transpose*
        dressedSignalMatrix event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (u.time*t)*
          sourceUnitMatrix (sourceUnitFieldMatrix u)) := by
    funext i j
    rw [sourceUnitQuantumMatrix,dressed_signal_matrix_actual,Matrix.smul_apply,smul_eq_mul]
    simp only [Matrix.mulVec_mulVec,Matrix.mulVec_single_one]
    rfl
  rw [source,field_matrix_value,Matrix.transpose_smul,Matrix.transpose_one,Matrix.smul_mul,
    Matrix.one_mul,Matrix.mul_smul,Matrix.mul_one,smul_smul,smul_smul,sourceUnitResponseFactor,pow_two]
  rw [mul_assoc]

def sourceUnitHalfQuantum (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => ∫t in Ioi (0:ℝ),laplaceWeight lambda t*sourceUnitQuantumMatrix u event transfer p t i j

theorem source_unit_half_quantum_generated (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth (sourceUnitFourierMomentum u p)<(lambda/(u.time : ℂ)).re) :
    sourceUnitHalfQuantum u event transfer p lambda=(sourceUnitResponseFactor u/(u.time : ℂ)) •
      frequencyHalfPolarization event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ)) := by
  have wave (t : ℝ) : laplaceWeight lambda t=laplaceWeight (lambda/(u.time : ℂ)) (u.time*t) := by
    unfold laplaceWeight
    apply congrArg Complex.exp
    have nonzero : (u.time : ℂ)≠0 := Complex.ofReal_ne_zero.mpr u.time_positive.ne'
    push_cast
    field_simp [nonzero]
  funext i j
  have generated := integral_comp_mul_left_Ioi (fun t : ℝ =>
    laplaceWeight (lambda/(u.time : ℂ)) t*
      dressedSignalMatrix event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) t i j) 0 u.time_positive
  have input : sourceUnitHalfQuantum u event transfer p lambda i j=sourceUnitResponseFactor u*
      (∫t in Ioi (0:ℝ),laplaceWeight (lambda/(u.time : ℂ)) (u.time*t)*
        dressedSignalMatrix event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (u.time*t) i j) := by
    rw [sourceUnitHalfQuantum,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [wave,source_unit_actual_quantum_matrix,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [input,generated,mul_zero,←frequency_half_polarization_integral _ _ _ _ off]
  change sourceUnitResponseFactor u*(((u.time⁻¹ : ℝ) : ℂ)*
      frequencyHalfPolarization event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ)) i j)=
    (sourceUnitResponseFactor u/(u.time : ℂ))*
      frequencyHalfPolarization event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ)) i j
  rw [Complex.ofReal_inv]
  exact (mul_assoc (sourceUnitResponseFactor u) (u.time : ℂ)⁻¹
    (frequencyHalfPolarization event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ)) i j)).symm

def sourceUnitResponsePencil (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  sourceUnitActionJacobi u p-sourceUnitInputNormalizer u p lambda • sourceUnitHalfQuantum u event transfer p lambda

theorem source_unit_response_complete_covariance (u : SourceUnits) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth (sourceUnitFourierMomentum u p)<(lambda/(u.time : ℂ)).re) :
    sourceUnitResponsePencil u event transfer p lambda=sourceUnitResponseFactor u •
      frequencyResponsePencil event (u.length⁻¹ • transfer) (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ)) := by
  rw [sourceUnitResponsePencil,source_unit_whole_action_jacobi,source_unit_input_normalizer_generated,
    source_unit_half_quantum_generated u event transfer p lambda off,
    smul_smul,frequencyResponsePencil,frequencyQuantumCorrection,smul_sub,smul_smul]
  have time_ne : (u.time : ℂ)≠0 := Complex.ofReal_ne_zero.mpr u.time_positive.ne'
  have scalar : (u.time : ℂ)*frequencyInputNormalizer (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ))*
      (sourceUnitResponseFactor u/(u.time : ℂ))=sourceUnitResponseFactor u*
        frequencyInputNormalizer (sourceUnitFourierMomentum u p) (lambda/(u.time : ℂ)) := by
    field_simp [time_ne]
  rw [scalar,sourceUnitResponseFactor]

/-- The original actual corrected chart generates the whole inverse in the new density and field coordinates. -/
def sourceUnitCorrectedGreen (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  (sourceUnitResponseFactor u)⁻¹ • correctedGreen event eps s sigma n

def sourceUnitForwardFourier (u : SourceUnits) (p : Fin 4→ℂ) : Fin 4→ℂ :=
  fun mu => (sourceAxisUnit u mu : ℂ)*p mu

theorem source_unit_forward_fourier (u : SourceUnits) (p : Fin 4→ℂ) :
    sourceUnitFourierMomentum u (sourceUnitForwardFourier u p)=p := by
  funext mu
  have nonzero : sourceAxisUnit u mu≠0 := by
    unfold sourceAxisUnit
    split
    · exact u.time_positive.ne'
    · exact u.length_positive.ne'
  exact mul_div_cancel_left₀ (p mu) (Complex.ofReal_ne_zero.mpr nonzero)

def sourceUnitCorrectedPencil (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  sourceUnitResponsePencil u event (u.length • ((eps^2 : ℝ) • n))
    (sourceUnitForwardFourier u (frequencyRay eps s n))
    ((u.time : ℂ)*dampedFourierClock (sourceFrequency eps s) sigma)

/-- The actual new unit chart is generated from the action and quantum halfline before inversion. -/
theorem source_unit_corrected_pencil_generated (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) :
    sourceUnitCorrectedPencil u event eps s sigma n=sourceUnitResponseFactor u •
      frequencyResponsePencil event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma) := by
  have clock : ((u.time : ℂ)*dampedFourierClock (sourceFrequency eps s) sigma)/(u.time : ℂ)=
      dampedFourierClock (sourceFrequency eps s) sigma :=
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr u.time_positive.ne')
  have off : sourceClockGrowth (frequencyRay eps s n)<
      (dampedFourierClock (sourceFrequency eps s) sigma).re := by
    have same : sourceFrequency eps s=s*eps^2 := by unfold sourceFrequency;ring
    simpa only [frequencyRay,same] using
      damped_fourier_source_domain (sourceFrequency eps s) sigma ((eps^2 : ℝ) • n) positive
  have converted : sourceClockGrowth (sourceUnitFourierMomentum u (sourceUnitForwardFourier u (frequencyRay eps s n)))<
      (((u.time : ℂ)*dampedFourierClock (sourceFrequency eps s) sigma)/(u.time : ℂ)).re := by
    simpa only [source_unit_forward_fourier,clock] using off
  simpa only [sourceUnitCorrectedPencil,source_unit_forward_fourier,clock,smul_smul,←mul_assoc,
    inv_mul_cancel₀ u.length_positive.ne',one_mul,one_smul] using
    source_unit_response_complete_covariance u event (u.length • ((eps^2 : ℝ) • n))
      (sourceUnitForwardFourier u (frequencyRay eps s n))
      ((u.time : ℂ)*dampedFourierClock (sourceFrequency eps s) sigma) converted

theorem source_unit_actual_green_inverse (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (regular : correctedDet event eps s sigma n≠0) :
    sourceUnitCorrectedPencil u event eps s sigma n*sourceUnitCorrectedGreen u event eps s sigma n=1 ∧
      sourceUnitCorrectedGreen u event eps s sigma n*sourceUnitCorrectedPencil u event eps s sigma n=1 := by
  have actual := actual_corrected_green_inverse event eps s sigma n positive regular
  have nonzero := source_unit_response_factor_nonzero u
  constructor
  · rw [source_unit_corrected_pencil_generated u event eps s sigma n positive,sourceUnitCorrectedGreen,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,mul_inv_cancel₀ nonzero,one_smul]
    exact actual.1
  · rw [source_unit_corrected_pencil_generated u event eps s sigma n positive,sourceUnitCorrectedGreen,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,inv_mul_cancel₀ nonzero,one_smul]
    exact actual.2

def sourceUnitEMInsertion (u : SourceUnits) : Matrix (Fin 289) (Fin 4) ℂ :=
  ((u.field : ℂ)*(u.generator : ℂ)) • emInsertion

def sourceUnitFullEMTensor (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (sourceUnitEMInsertion u).transpose*sourceUnitCorrectedGreen u event eps s sigma n*sourceUnitEMInsertion u

theorem source_unit_all_sixteen_tensor (u : SourceUnits) (event : DressedEvent) (eps s sigma : ℝ) (n : PhysicalMomentum) :
    sourceUnitFullEMTensor u event eps s sigma n=((u.generator : ℂ)^2/(sourceDensityUnit u : ℂ)) •
      correctedEMTensor event eps s sigma n := by
  simp only [sourceUnitFullEMTensor,sourceUnitEMInsertion,sourceUnitCorrectedGreen,Matrix.transpose_smul,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,smul_smul,
    correctedEMTensor,emResponseTensor]
  apply congrArg (fun c : ℂ => c • (emInsertion.transpose*correctedGreen event eps s sigma n*emInsertion))
  have field_ne : (u.field : ℂ)≠0 := Complex.ofReal_ne_zero.mpr u.field_nonzero
  have density_ne : (sourceDensityUnit u : ℂ)≠0 := by
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (pow_ne_zero _ u.length_positive.ne') u.energy_positive.ne')
  unfold sourceUnitResponseFactor
  field_simp [density_ne,field_ne]

end LowEnergy.GaussComposite.ActualDressedEMWholeUnitCovariance
