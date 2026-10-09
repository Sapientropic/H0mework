import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseRiesz
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderContactBasis
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhaseWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumPropagationPencil PreparationVacuumPhysicalModeContact
open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSourcePreparation
open ActualDressedLockedWard ActualDressedConstraintRead ActualDressedSignal
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationMotherResidualDirections SourcePropagationNativeEulerHistory Stage9C.Material.SpinPair ActualDressedPencil
open MeasureTheory Set
open scoped Interval
open Filter
open scoped Matrix BigOperators InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] dressedEulerObserver jointResolvent noetherReader rawReader rawReaderContact
  physicalTime timeSlope jointCurrent noetherReaderContact phaseReader phaseReaderContact noetherHistoryOperatorJet

private theorem history_contact_algebra {A : Type*} [Ring A]
    (dl dr l r tl tr cl cr j old next : A) :
    (dl*(l*j*r)*tr+tl*((-cl)*j*r+l*old*r+l*j*(-cr))*tr+tl*(l*j*r)*dr)+
      tl*l*(next-old)*r*tr=
    dl*(l*j*r)*tr+tl*((-cl)*j*r+l*next*r+l*j*(-cr))*tr+tl*(l*j*r)*dr := by
  simp only [mul_sub,sub_mul,mul_add,add_mul,mul_assoc]
  abel

private theorem original_history_contact (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader signal t).value=
      nativeWardHistory q (noetherReader reader q.p q.F 0)
        (fun force=>noetherReaderContact reader force q.p q.F) (fun s=>(signal s).value) t := by
  rw [noetherHistoryOperatorJet_value]
  simp only [historyOperator,historyMiddle,rawInitial,nativeWardHistory,noetherReader_source]
  exact history_contact_algebra _ _ _ _ _ _ _ _ _ _ _

private def historyLinear (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) :
    (Operator×(Field289→Operator))→ₗ[ℂ]Operator where
  toFun x:=nativeWardHistory q x.1 x.2 history t
  map_add' a b:=by
    simp only [nativeWardHistory,Prod.fst_add,Prod.snd_add,Pi.add_apply,mul_add,add_mul]
    noncomm_ring
  map_smul' c a:=by
    simp only [nativeWardHistory,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,
      mul_smul_comm,smul_mul_assoc,smul_add,mul_add,add_mul,RingHom.id_apply]

private theorem history_three (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) (c : ℂ)
    (N W S D : Operator) (CN CW CS CD : Field289→Operator)
    (reader : c • N=W-S-D) (contact : c • CN=CW-CS-CD) :
    c • nativeWardHistory q N CN history t=
      nativeWardHistory q W CW history t-nativeWardHistory q S CS history t-nativeWardHistory q D CD history t := by
  have same : c • (N,CN)=(W,CW)-(S,CS)-(D,CD):=Prod.ext reader contact
  have generated:=congrArg (historyLinear q history t) same
  simpa only [map_smul,map_sub,historyLinear,LinearMap.coe_mk,AddHom.coe_mk] using generated

/-- Each term uses the original two ordered time legs, both actual uncut resolvents, and its own generated contact. -/
def phaseHistory (part : PhasePart) (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (t : ℝ) : Operator :=
  nativeWardHistory (dressedKinematicPoint event transfer)
    (phaseReader part event.momentum event.frame 0)
    (fun force=>phaseReaderContact part force event.momentum event.frame)
    (fun s=>(signal s).value) t

/-- The held full phase Ward reaches the actual N2 creation-minus-background causal response, preserving scalar and preparation/configuration terms. -/
theorem phase_actual_history (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    ((gaugeScale/2:ℝ):ℂ)*dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) sourceModeField signal t).value=
    dressedEulerObserver event (phaseHistory .ward event transfer signal t)-
      dressedEulerObserver event (phaseHistory .scalar event transfer signal t)-
      dressedEulerObserver event (phaseHistory .deviation event transfer signal t) := by
  have reader : ((gaugeScale/2:ℝ):ℂ) • noetherReader sourceModeField event.momentum event.frame 0=
      phaseReader .ward event.momentum event.frame 0-phaseReader .scalar event.momentum event.frame 0-
        phaseReader .deviation event.momentum event.frame 0 := by
    calc
      _=(gaugeScale/2:ℝ) • noetherReader sourceModeField event.momentum event.frame 0 := by
        apply ContinuousLinearMap.ext
        intro v
        exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (gaugeScale/2) _).symm
      _=_ := phase_reader_initial event.momentum event.frame
  have contact : ((gaugeScale/2:ℝ):ℂ) • (fun force=>noetherReaderContact sourceModeField force event.momentum event.frame)=
      (fun force=>phaseReaderContact .ward force event.momentum event.frame)-
        (fun force=>phaseReaderContact .scalar force event.momentum event.frame)-
        (fun force=>phaseReaderContact .deviation force event.momentum event.frame) := by
    funext force
    change ((gaugeScale/2:ℝ):ℂ) • noetherReaderContact sourceModeField force event.momentum event.frame=_
    calc
      _=(gaugeScale/2:ℝ) • noetherReaderContact sourceModeField force event.momentum event.frame := by
        apply ContinuousLinearMap.ext
        intro v
        exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (gaugeScale/2) _).symm
      _=_ := phase_reader_contact force event.momentum event.frame
  have split:=history_three (dressedKinematicPoint event transfer) (fun s=>(signal s).value) t
    ((gaugeScale/2:ℝ):ℂ) _ _ _ _ _ _ _ _ reader contact
  have original:=original_history_contact (dressedKinematicPoint event transfer) sourceModeField signal t
  have generated:=congrArg (dressedEulerObserver event)
    ((congrArg (fun A : Operator=>((gaugeScale/2:ℝ):ℂ) • A) original).trans split)
  simpa only [map_smul,map_sub,smul_eq_mul,phaseHistory] using generated

/-- All289 existing actual Noether rows consume the same fixed source spatial mode. -/
theorem phase_actual_current (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    ((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*(dressedNoetherJet event transfer signal t j).value)=
    dressedEulerObserver event (phaseHistory .ward event transfer signal t)-
      dressedEulerObserver event (phaseHistory .scalar event transfer signal t)-
      dressedEulerObserver event (phaseHistory .deviation event transfer signal t) := by
  exact (congrArg (fun z : ℂ=>((gaugeScale/2:ℝ):ℂ)*z)
    (actual_noether_reader_contraction event transfer sourceModeField signal t).symm).trans
      (phase_actual_history event transfer signal t)

/-- Both original real Fourier quadratures are kept independently in each actual action branch. -/
def phaseSignalRead (part : PhasePart) (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) : ℂ :=
  dressedEulerObserver event (phaseHistory part event transfer (nativeTimeSignal (sourceRealSignal p a)) t)+
    Complex.I*dressedEulerObserver event
      (phaseHistory part event transfer (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t)

private theorem row_quadrature {n : ℕ} (f a b : Fin n→ℂ) :
    (∑j,f j*(a+Complex.I • b) j)=(∑j,f j*a j)+Complex.I*(∑j,f j*b j) := by
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The genuine dressed response tensor now consumes the held phase Ward, including the nonzero scalar countervariation and full emitted-configuration deviation. -/
theorem phase_signal_matrix_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) :
    ((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*
      (dressedSignalMatrix event transfer p t*ᵥa) j)=
      phaseSignalRead .ward event transfer p a t-phaseSignalRead .scalar event transfer p a t-
        phaseSignalRead .deviation event transfer p a t := by
  have tensor:=(dressed_signal_matrix_actual event transfer p t a).symm.trans
    (dressed_signal_quadrature_actual event transfer p t a)
  have row:=(congrArg (fun v : Fin 289→ℂ=>∑j,(sourceModeField j:ℂ)*v j) tensor).trans
    (row_quadrature (fun j=>(sourceModeField j:ℂ)) _ _)
  have realPaid:=phase_actual_current event transfer (nativeTimeSignal (sourceRealSignal p a)) t
  have imaginaryPaid:=phase_actual_current event transfer
    (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t
  rw [row]
  have distribute (c x y : ℂ) : c*(x+Complex.I*y)=c*x+Complex.I*(c*y):=by ring
  rw [distribute,realPaid,imaginaryPaid]
  unfold phaseSignalRead
  ring

/-- The same finite quantum polarization consumes the complete held phase return inside its original window. -/
theorem phase_window_polarization_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (lambda : ℂ) (T : ℝ) :
    ((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*
      (dressedWindowPolarization event transfer p lambda T*ᵥa) j)=
    ∫t in (0:ℝ)..T,laplaceWeight lambda t*
      (phaseSignalRead .ward event transfer p a t-phaseSignalRead .scalar event transfer p a t-
        phaseSignalRead .deviation event transfer p a t) := by
  have continuousWeight : Continuous (laplaceWeight lambda) := by
    unfold laplaceWeight
    fun_prop
  have continuousRow (j : Fin 289) :
      Continuous (fun t=>dressedSignalQuadrature event transfer p t a j) :=
    (continuous_apply j).comp ((dressed_signal_quadrature_continuous event transfer p).clm_apply continuous_const)
  have integrable (j : Fin 289) : IntervalIntegrable
      (fun t=>((gaugeScale/2:ℝ):ℂ)*(sourceModeField j:ℂ)*
        (laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a j)) volume 0 T :=
    ((continuousWeight.mul (continuousRow j)).const_mul _).intervalIntegrable 0 T
  have tensor:=(dressed_window_polarization_actual event transfer p lambda T a).symm.trans
    (dressed_signal_window_actual event transfer p lambda T a)
  have row:=congrArg (fun v : Fin 289→ℂ=>((gaugeScale/2:ℝ):ℂ)*∑j : Fin 289,(sourceModeField j:ℂ)*v j) tensor
  calc
    _=((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*
        ∫t in (0:ℝ)..T,laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a j) := row
    _=∫t in (0:ℝ)..T,∑j : Fin 289,((gaugeScale/2:ℝ):ℂ)*(sourceModeField j:ℂ)*
        (laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a j) := by
      calc
        _=∑j : Fin 289,∫t in (0:ℝ)..T,((gaugeScale/2:ℝ):ℂ)*(sourceModeField j:ℂ)*
            (laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [intervalIntegral.integral_const_mul]
          ring
        _=_ := (intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume) (fun j _=>integrable j)).symm
    _=_ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      have point:=phase_signal_matrix_return event transfer p a t
      rw [←dressed_signal_matrix_actual event transfer p t a] at point
      rw [←point]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end LowEnergy.GaussComposite.ActualDressedPhaseWard
