import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherSylvester
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSylvester
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationNoetherTime SourcePropagationResolvent
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix Interval
attribute [local irreducible] dressedEulerObserver dressedSignalQuadrature dressedNoetherJet
  sourceHistoryOperator noetherHistoryOperatorJet dressedSignalHalfOperator
  noetherStaticHalf noetherStaticInitial noetherStaticContact dressedKinematicPoint
  fieldUnit laplaceWeight dressedSignalWeighted dressedSignalWindow dressedWindowPolarization

private theorem static_native_signal (p : Fin 4→ℂ) (static : p 0=0) (a : SignalAmplitude) :
    nativeTimeSignal (sourceRealSignal p a)=(fun _=>⟨fun i=>(a i).re,0,0⟩) := by
  funext t
  rw [sourceTimeSignal_actual]
  simp only [sourceTimeHistory_actual,static,mul_zero,Complex.exp_zero,one_mul,
    zero_mul,Complex.zero_re]
  rfl

private theorem static_quadrature_signal (p : Fin 4→ℂ) (static : p 0=0) (a : SignalAmplitude) :
    nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))=(fun _=>⟨fun i=>(a i).im,0,0⟩) := by
  rw [static_native_signal p static]
  ext i
  simp [sourceQuadrature]

private theorem static_noether_zero (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader (fun _=>⟨0,0,0⟩) t).value=0 := by
  have signal:=static_native_signal (fun _ : Fin 4=>(0:ℂ)) rfl (0:SignalAmplitude)
  change nativeTimeSignal (sourceRealSignal (fun _=>(0:ℂ)) (0:SignalAmplitude))=
    (fun _=>⟨0,0,0⟩) at signal
  rw [←signal,←sourceHistoryOperator_actual]
  exact map_zero _

private theorem static_half_zero (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ) :
    noetherStaticHalf q reader 0 lambda=0 := by
  unfold noetherStaticHalf
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun t=>by
    change laplaceWeight lambda t •
      (noetherHistoryOperatorJet q reader (fun _=>⟨0,0,0⟩) t).value=(0:ResponseOp)
    rw [static_noether_zero]
    apply ContinuousLinearMap.ext
    intro x
    simp only [smul_apply,zero_apply,smul_zero])

/-- The complete current at zero input clock keeps both genuine real quadratures. -/
theorem dressed_static_current (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (a : SignalAmplitude) (t : ℝ) (i : Fin 289) :
    dressedSignalQuadrature event transfer p t a i=
      dressedEulerObserver event
        (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
          (fun _=>⟨fun j=>(a j).re,0,0⟩) t).value+
      Complex.I*dressedEulerObserver event
        (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
          (fun _=>⟨fun j=>(a j).im,0,0⟩) t).value := by
  let observe : (ℝ→SourceJet Field289)→ℂ := fun signal=>
    dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i) signal t).value
  have realpart:=congrArg observe (static_native_signal p static a)
  have imaginarypart:=congrArg observe (static_quadrature_signal p static a)
  have actual:=congrFun (dressed_signal_quadrature_actual event transfer p t a) i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,dressed_noether_jet_original] at actual
  exact actual.trans (congrArg₂ (fun x y : ℂ=>x+Complex.I*y) realpart imaginarypart)

private theorem observed_half_integrable (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    IntegrableOn (fun t=>laplaceWeight lambda t*dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) reader
        (fun _=>⟨force,0,0⟩) t).value) (Ioi (0:ℝ)) := by
  simpa only [IntegrableOn,map_smul,smul_eq_mul] using!
    (dressedEulerObserver event).integrable_comp
      (noether_static_half_integrable (dressedKinematicPoint event transfer) reader force lambda positive)

private theorem observed_half (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    (∫t in Ioi (0:ℝ),laplaceWeight lambda t*dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) reader
        (fun _=>⟨force,0,0⟩) t).value)=
      dressedEulerObserver event (noetherStaticHalf (dressedKinematicPoint event transfer) reader force lambda) := by
  simpa only [noetherStaticHalf,map_smul,smul_eq_mul] using!
    (dressedEulerObserver event).integral_comp_comm
      (noether_static_half_integrable (dressedKinematicPoint event transfer) reader force lambda positive)

private theorem half_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re)
    (a : SignalAmplitude) (i : Fin 289) :
    dressedSignalHalfOperator event transfer p lambda a i=
      ∫t in Ioi (0:ℝ),laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a i := by
  have integrable:=dressed_signal_weighted_integrable event transfer p lambda off
  have applied:=(ContinuousLinearMap.apply ℝ (Fin 289→ℂ) a).integrable_comp integrable
  have coordinate:=(ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ]ℂ).integral_comp_comm applied
  simp only [ContinuousLinearMap.proj_apply,ContinuousLinearMap.apply_apply] at coordinate
  have first : dressedSignalHalfOperator event transfer p lambda a i=
      (∫t in Ioi (0:ℝ),dressedSignalWeighted event transfer p lambda t a) i := by
    unfold dressedSignalHalfOperator
    exact congrFun (ContinuousLinearMap.integral_apply integrable a) i
  have last : (∫t in Ioi (0:ℝ),dressedSignalWeighted event transfer p lambda t a) i=
      ∫t in Ioi (0:ℝ),laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a i := by
    simpa only [dressedSignalWeighted,smul_apply,Pi.smul_apply,smul_eq_mul] using! coordinate.symm
  exact first.trans last

theorem dressed_static_half_current (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (a : SignalAmplitude) (lambda : ℂ)
    (positive : 0<lambda.re) (i : Fin 289) :
    dressedSignalHalfOperator event transfer p lambda a i=
      dressedEulerObserver event (noetherStaticHalf (dressedKinematicPoint event transfer)
        (fieldUnit i) (fun j=>(a j).re) lambda)+
      Complex.I*dressedEulerObserver event (noetherStaticHalf (dressedKinematicPoint event transfer)
        (fieldUnit i) (fun j=>(a j).im) lambda) := by
  have off : sourceClockGrowth p<lambda.re := by
    simpa only [sourceClockGrowth,static,Complex.zero_re,max_self] using positive
  let realRead : ℝ→ℂ := fun t=>dressedEulerObserver event
    (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
      (fun _=>⟨fun j=>(a j).re,0,0⟩) t).value
  let imaginaryRead : ℝ→ℂ := fun t=>dressedEulerObserver event
    (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
      (fun _=>⟨fun j=>(a j).im,0,0⟩) t).value
  have realIntegral:=observed_half_integrable event transfer (fieldUnit i) (fun j=>(a j).re) lambda positive
  have imaginaryIntegral:=observed_half_integrable event transfer (fieldUnit i) (fun j=>(a j).im) lambda positive
  calc
    _=∫t in Ioi (0:ℝ),laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a i :=
      half_actual event transfer p lambda off a i
    _=∫t in Ioi (0:ℝ),laplaceWeight lambda t*realRead t+
        Complex.I*(laplaceWeight lambda t*imaginaryRead t) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t=>by
        have generated:=congrArg (fun z : ℂ=>laplaceWeight lambda t*z)
          (dressed_static_current event transfer p static a t i)
        exact generated.trans (by dsimp only [realRead,imaginaryRead];ring))
    _=(∫t in Ioi (0:ℝ),laplaceWeight lambda t*realRead t)+
        Complex.I*(∫t in Ioi (0:ℝ),laplaceWeight lambda t*imaginaryRead t) := by
      rw [integral_add realIntegral (imaginaryIntegral.const_mul Complex.I),integral_const_mul]
    _=_ := congrArg₂ (fun x y : ℂ=>x+Complex.I*y)
      (observed_half event transfer (fieldUnit i) (fun j=>(a j).re) lambda positive)
      (observed_half event transfer (fieldUnit i) (fun j=>(a j).im) lambda positive)

/-- Every entry comes from the actual normalized creation-minus-background and full joint inverse. -/
def dressedStaticPolarization (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>dressedEulerObserver event
    (noetherStaticHalf (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j) lambda)

attribute [local irreducible] dressedStaticPolarization

theorem dressed_static_polarization_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    dressedSignalHalfOperator event transfer p lambda (Pi.single j 1) i=
      dressedStaticPolarization event transfer lambda i j := by
  have realpart : (fun k=>((Pi.single j 1 : SignalAmplitude) k).re)=fieldUnit j := by
    ext k
    by_cases same : k=j <;> simp [fieldUnit,same]
  have imaginarypart : (fun k=>((Pi.single j 1 : SignalAmplitude) k).im)=0 := by
    ext k
    by_cases same : k=j <;> simp [same]
  let read : Field289→ℂ := fun force=>dressedEulerObserver event
    (noetherStaticHalf (dressedKinematicPoint event transfer) (fieldUnit i) force lambda)
  have realRead:=congrArg read realpart
  have zeroRead : read (fun k=>((Pi.single j 1 : SignalAmplitude) k).im)=0 :=
    (congrArg read imaginarypart).trans
      ((congrArg (dressedEulerObserver event)
        (static_half_zero (dressedKinematicPoint event transfer) (fieldUnit i) lambda)).trans
          (dressedEulerObserver event).map_zero)
  have actual:=dressed_static_half_current event transfer p static (Pi.single j 1) lambda positive i
  simpa only [mul_zero,add_zero,read,dressedStaticPolarization] using
    actual.trans (congrArg₂ (fun x y : ℂ=>x+Complex.I*y) realRead zeroRead)

theorem dressed_static_polarization_inverse (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    dressedStaticPolarization event transfer lambda i j=
      dressedEulerObserver event (sourceInverse (dressedKinematicPoint event transfer) lambda
        (noetherStaticInitial (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j)-
          leftCurrent (dressedKinematicPoint event transfer) (fieldUnit j)*
            sourceInverse (dressedKinematicPoint event transfer) lambda
              (rawInitial (dressedKinematicPoint event transfer) (fieldUnit i))+
          sourceInverse (dressedKinematicPoint event transfer) lambda
              (rawInitial (dressedKinematicPoint event transfer) (fieldUnit i))*
            rightCurrent (dressedKinematicPoint event transfer) (fieldUnit j))) := by
  unfold dressedStaticPolarization
  rw [noether_static_half_inverse _ _ _ lambda positive]

/-- The original operator tail controls each entry of this same full static-clock response. -/
theorem dressed_static_polarization_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer lambda i j-
      dressedWindowPolarization event transfer p lambda T i j‖ ≤
        dressedSignalTailPrice event transfer p lambda T := by
  have off : sourceClockGrowth p<lambda.re := by
    simpa only [sourceClockGrowth,static,Complex.zero_re,max_self] using positive
  have window:=congrFun
    (dressed_window_polarization_actual event transfer p lambda T (Pi.single j 1)) i
  simp only [Matrix.mulVec_single_one,Matrix.col_apply] at window
  let A:=dressedSignalHalfOperator event transfer p lambda-dressedSignalWindow event transfer p lambda T
  have difference : dressedStaticPolarization event transfer lambda i j-
      dressedWindowPolarization event transfer p lambda T i j=(A (Pi.single j 1)) i :=
    congrArg₂ (fun x y : ℂ=>x-y)
      (dressed_static_polarization_actual event transfer p static lambda positive i j).symm window.symm
  refine (congrArg norm difference).le.trans ((norm_le_pi_norm (A (Pi.single j 1)) i).trans ?_)
  have applied : ‖A (Pi.single j 1)‖≤‖A‖ := by
    simpa only [Pi.norm_single,norm_one,mul_one] using A.le_opNorm (Pi.single j 1)
  exact applied.trans (dressed_signal_half_operator_tail event transfer p lambda off T future)

end LowEnergy.GaussComposite.ActualDressedSylvester
