import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorReader

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open FullQuantum.StateGreen PreparationVacuumFixedMomentumActionReturn PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization SourceQuantumFockGauge PreparationVacuumNonlinearFieldCurve
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumLowerClassical PreparationVacuumTemporalCharge PreparationVacuumGaugeSourceInjection
open PreparationVacuumNoetherChart PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open SourcePropagationNativeActionHessian GaussNativeMatter GaussCoreHilbert
open ActualDressedNativeConstraint ActualDressedNullNative ActualDressedLockedWard ActualDressedConstraintRead
open ActualDressedTemporalCurrent PreparationVacuumWeightedChargeActionWard
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] nativeSourceColumn noetherReader nativeReader nativeReaderContact

open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumNonlinearFieldCurve PreparationVacuumHalfDensityFiber
open MeasureTheory Set
open scoped InnerProductSpace
private abbrev NativeOp:=H→L[ℂ]H
local instance : NormedAlgebra ℝ NativeOp:=NormedAlgebra.restrictScalars ℝ ℂ _

open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime PreparationVacuumPropagationPencil
open PreparationVacuumFieldConstraintResponse GaussFockPair PreparationVacuumElectricConstraint PreparationPhysicalActionUnits PreparationVacuumSourceChargeWard
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumFullElectricWard CanonicalGradedCharge
open ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation
attribute [local irreducible] nativeWardHistory dressedEulerObserver jointResolvent physicalTime jointCurrent sourceHamiltonian

private theorem history_contact_algebra {A : Type*} [Ring A]
    (dl dr l r tl tr cl cr j old next : A) :
    (dl*(l*j*r)*tr+tl*((-cl)*j*r+l*old*r+l*j*(-cr))*tr+tl*(l*j*r)*dr)+
      tl*l*(next-old)*r*tr=
    dl*(l*j*r)*tr+tl*((-cl)*j*r+l*next*r+l*j*(-cr))*tr+tl*(l*j*r)*dr :=by
  simp only [mul_sub,sub_mul,mul_add,add_mul,mul_assoc]
  abel

private theorem history_layout (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader signal t).value=
      nativeWardHistory q (noetherReader reader q.p q.F 0)
        (fun force=>noetherReaderContact reader force q.p q.F) (fun s=>(signal s).value) t :=by
  rw [noetherHistoryOperatorJet_value]
  simp only [historyOperator,historyMiddle,rawInitial,nativeWardHistory,noetherReader_source]
  exact history_contact_algebra _ _ _ _ _ _ _ _ _ _ _

private theorem history_sum (q : PhysicalResponsePoint) (coefficient : Fin 12×Fin 4→ℂ)
    (A : Fin 12×Fin 4→NativeOp) (C : Fin 12×Fin 4→Field289→NativeOp)
    (history : ℝ→Field289) (t : ℝ) :
    nativeWardHistory q (∑b,coefficient b • A b) (fun f=>∑b,coefficient b • C b f) history t=
      ∑b,coefficient b • nativeWardHistory q (A b) (C b) history t :=by
  simp only [nativeWardHistory,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    Finset.sum_add_distrib,smul_add,mul_add,add_mul]

/-- The complete gradient response keeps the original initial/material, contact and two ordered histories. -/
theorem native_color_gradient_history (q : PhysicalResponsePoint) (g : Fin 3) (gradient : Fin 4→ℝ)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    nativeWardHistory q (nativeReader (Fin.castAdd 6 g) 0 gradient q.p q.F 0)
      (fun f=>nativeReaderContact (Fin.castAdd 6 g) 0 gradient f q.p q.F) (fun s=>(signal s).value) t=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        (noetherHistoryOperatorJet q (gaugeField b.2 b.1) signal t).value :=by
  have contact : (fun f=>nativeReaderContact (Fin.castAdd 6 g) 0 gradient f q.p q.F)=
      fun f=>∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        noetherReaderContact (gaugeField b.2 b.1) f q.p q.F:=
    funext (fun f=>native_color_gradient_contact g gradient f q.p q.F)
  have read:=congrArg₂ (fun A C=>nativeWardHistory q A C (fun s=>(signal s).value) t)
    (native_color_gradient_reader g gradient q.p q.F) contact
  exact read.trans ((history_sum q _ _ _ _ t).trans (Finset.sum_congr rfl (fun b _=>
    congrArg (fun A : NativeOp=>((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) • A)
      (history_layout q (gaugeField b.2 b.1) signal t).symm)))

/-- This is the unchanged actual creation-minus-background observer, on the same physical transfer. -/
theorem native_color_gradient_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (g : Fin 3) (gradient : Fin 4→ℝ) (signal : ℝ→SourceJet Field289) (t : ℝ) :
    dressedEulerObserver event
      (nativeWardHistory (dressedKinematicPoint event transfer)
        (nativeReader (Fin.castAdd 6 g) 0 gradient event.momentum event.frame 0)
        (fun f=>nativeReaderContact (Fin.castAdd 6 g) 0 gradient f event.momentum event.frame)
        (fun s=>(signal s).value) t)=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ)*dressedEulerObserver event
        (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (gaugeField b.2 b.1) signal t).value :=by
  have actual:=congrArg (dressedEulerObserver event)
    (native_color_gradient_history (dressedKinematicPoint event transfer) g gradient signal t)
  have hp : (dressedKinematicPoint event transfer).p=event.momentum:=rfl
  have hF : (dressedKinematicPoint event transfer).F=event.frame:=rfl
  simpa only [map_sum,map_smul,smul_eq_mul,hp,hF] using actual

private theorem temporal_reader (g : Fin 3) (r : ℝ) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    nativeReader (Fin.castAdd 6 g) 0 (Pi.single 0 r) p F 0=
      ∑a : Fin 12,((-r*gaugeColorRaw g a : ℝ):ℂ) • noetherReader (temporalField a) p F 0 :=by
  rw [native_color_gradient_reader,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (0 : Fin 4)]
  · rw [Pi.single_eq_same]
    rfl
  · intro mu _ other
    simp [other]
    exact zero_smul ℂ (noetherReader (gaugeField mu a) p F 0)
  · simp

/-- The time component is the original weighted Gauss orbit and the normal-order pair, not a bare charge scalar. -/
theorem native_color_temporal_gauss (g : Fin 3) (r : ℝ) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (nativeReader (Fin.castAdd 6 g) 0 (Pi.single 0 r) p F 0 y)=
      ∑a : Fin 12,((r*gaugeColorRaw g a : ℝ):ℂ)*
        (sourcePair (sourceTestApprox F x)
          (sourceTimeWeightCore (orbitAction (originalUnit a) (sourceTestApprox F y)))+
         sourcePair (sourceTestApprox F x) (normalChargeCore a (sourceTestApprox F y))) :=by
  rw [temporal_reader]
  simp only [sum_apply,smul_apply,inner_sum,inner_smul_right]
  apply Finset.sum_congr rfl
  intro a _
  rw [temporal_noether_reader_return,temporal_core,original_gauss_constraint]
  simp only [LinearMap.neg_apply,map_neg,sourcePair,inner_neg_right,Complex.ofReal_neg,neg_mul]
  ring

/-- The original physical-time insertion is formed on the same two source generators. -/
def nativeColorTemporalInsertion (q : PhysicalResponsePoint) (g : Fin 3) (r : ℝ) : NativeOp:=
  sourceHamiltonian (q.p+q.k) q.F*nativeReader (Fin.castAdd 6 g) 0 (Pi.single 0 r) q.p q.F 0-
    nativeReader (Fin.castAdd 6 g) 0 (Pi.single 0 r) q.p q.F 0*sourceHamiltonian q.p q.F

/-- Arbitrary actual right legs consume all four original compression/uncut defects, before taking the actual observer. -/
theorem native_color_prepared_insertion (q : PhysicalResponsePoint) (g : Fin 3) (r : ℝ) (y : H) :
    nativeColorTemporalInsertion q g r y=
      ∑a : Fin 12,((-r*gaugeColorRaw g a : ℝ):ℂ) •
        (sourceApprox q.F (embed (weightedWardCore q.p q.k a (sourceTestApprox q.F y)))+
         leftCompressionDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F y))+
         leftUncutDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F y))-
         sourceApprox q.F (embed (rawChargeCore a
           (rightCompressionDefect q.p q.F y+rightUncutDefect q.p q.F y)))) :=by
  simp only [nativeColorTemporalInsertion,temporal_reader,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,←Finset.sum_sub_distrib,sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [noetherTimeInsertion,sub_apply,smul_sub,smul_apply] using
    (congrArg (fun z : H=>((-r*gaugeColorRaw g a : ℝ):ℂ) • z)
      (temporalInsertion_action_return q a y))

end LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
