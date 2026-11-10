import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeAdaptivePhysicalSoftReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualQuantumBinaryReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft
open ActualDressedFullCoulomb ActualDressedNoether PreparationVacuumSourcePreparedResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open SourcePropagationCommonMomentum SourcePropagationTimeDependentFeedback PreparationVacuumActionFieldLift
open PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard PreparationVacuumMixedFieldReturn
open SourceFamilyHilbert SourceFamilyOperator Filter
open ActualQuantitativePreparedFrameOwn GaussComposite.SourceGraph
open scoped Topology InnerProductSpace
local instance realOperators : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance rationalOperators : NormedAlgebra ℚ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] physicalTime jointGenerator jointResolvent dressedNoetherKernel noetherReader

/-- The original physical observer time uses the complete uncut source Hamiltonian. -/
theorem actual_noether_physical_time_momentum_continuous (F : GaussUnitaryHistory.Index) (age : ℝ) :
    Continuous (fun p : PhysicalMomentum=>physicalTime p F age 0) := by
  unfold physicalTime SourceFiniteUnitary.time
  exact NormedSpace.exp_continuous.comp
    (((jointGenerator_base_continuous F 0).const_smul (-Complex.I)).const_smul age)

/-- The observer's actual event frame is fixed; both physical inverse/time legs vary with the actual transfer. -/
theorem actual_full_noether_transfer_continuous (event : DressedEvent) (reader : Field289) (age : ℝ) :
    Continuous (fun k : PhysicalMomentum=>dressedNoetherKernel event (-k) reader age 0) := by
  have momentum : Continuous (fun k : PhysicalMomentum=>event.momentum+k):=
    (continuous_const (y:=event.momentum)).add continuous_id
  have tl :=(actual_noether_physical_time_momentum_continuous event.frame (-age)).comp momentum
  have rl :=(actual_electron_physical_resolvent_continuous event.frame event.energy event.nonreal).comp momentum
  have actual :=(((tl.mul rl).mul_const (noetherReader reader event.momentum event.frame 0)).mul_const
    (jointResolvent event.momentum event.frame event.energy 0)).mul_const (physicalTime event.momentum event.frame age 0)
  simpa only [dressedNoetherKernel,sub_neg_eq_add,Function.comp_def,Pi.mul_apply] using actual

private theorem constant_reader_bound {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (A : E→L[ℂ]E) :‖SourceFamilyOperator.lift u (SourceFamilyOperator.constant A)‖≤‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit u (SourceFamilyOperator.constant A) ‖A‖
    (norm_nonneg A) (fun _ y=>A.le_opNorm y) x

private def constant_reader_map {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) : (E→L[ℂ]E)→L[ℂ](SourceFamilyHilbert.Hilbert E u→L[ℂ]SourceFamilyHilbert.Hilbert E u) :=
  (show (E→L[ℂ]E)→ₗ[ℂ](SourceFamilyHilbert.Hilbert E u→L[ℂ]SourceFamilyHilbert.Hilbert E u) from
    {toFun:=fun A=>SourceFamilyOperator.lift u (SourceFamilyOperator.constant A)
     map_add':=fun A B=>SourceFamilyOperator.constant_add u A B
     map_smul':=fun c A=>SourceFamilyOperator.constant_smul u c A}).mkContinuous 1
      (fun A=>by
        change ‖SourceFamilyOperator.lift u (SourceFamilyOperator.constant A)‖≤1*‖A‖
        rw [one_mul]
        exact constant_reader_bound u A)

/-- This is the original whole-H reader, with its source-generated operator-norm bound. -/
def actualHistoryReader : (H→L[ℂ]H)→L[ℂ](ElectronHistory→L[ℂ]ElectronHistory) :=
  constant_reader_map GaussUnitaryHistory.sourceFilter

def actualNoetherBackground (event : DressedEvent) : ElectronHistory:=
  GaussUnitaryHistory.inclusion (prepared (sourceProfile event.epsilon event.precision))

theorem actual_noether_background_norm (event : DressedEvent) :‖actualNoetherBackground event‖=1 := by
  rw [actualNoetherBackground,GaussUnitaryHistory.inclusion.norm_map]
  simpa only [actualPrepared] using actualPrepared_norm event.epsilon event.precision

/-- The same actual physical N3 state and the original background are read through the original whole-H operator consumer. -/
def actualPhysicalEulerObserver (event : DressedEvent) (leg : CompositeLeg) : (H→L[ℂ]H)→L[ℂ]ℂ :=
  -((innerSL ℂ (actualElectronPhysicalState event.momentum event.energy event.nonreal leg)).comp
      ((ContinuousLinearMap.apply ℂ ElectronHistory (actualElectronPhysicalState event.momentum event.energy event.nonreal leg)).comp actualHistoryReader)-
    (innerSL ℂ (actualNoetherBackground event)).comp
      ((ContinuousLinearMap.apply ℂ ElectronHistory (actualNoetherBackground event)).comp actualHistoryReader))

theorem actual_physical_euler_observer_value (event : DressedEvent) (leg : CompositeLeg) (A : H→L[ℂ]H) :
    actualPhysicalEulerObserver event leg A=
      -inner ℂ (actualElectronPhysicalState event.momentum event.energy event.nonreal leg)
        (GaussUnitaryHistory.reader A (actualElectronPhysicalState event.momentum event.energy event.nonreal leg))+
      inner ℂ (actualNoetherBackground event) (GaussUnitaryHistory.reader A (actualNoetherBackground event)) := by
  simp only [actualPhysicalEulerObserver,sub_apply,neg_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply,actualHistoryReader,constant_reader_map,LinearMap.mkContinuous_apply,GaussUnitaryHistory.reader]
  abel

/-- Every original product derivative is retained, including the complete Noether contact. -/
def actualFullNoetherVariation (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (age : ℝ) : H→L[ℂ]H :=
  let p:=event.momentum-transfer
  let TL:=physicalTime p event.frame (-age) 0
  let L:=jointResolvent p event.frame event.energy 0
  let J:=noetherReader reader event.momentum event.frame 0
  let R:=jointResolvent event.momentum event.frame event.energy 0
  let TR:=physicalTime event.momentum event.frame age 0
  let dTL:=timeSlope force p event.frame (-age)
  let dL:=-(L*jointCurrent p event.frame event.energy 0 force*L)
  let dJ:=noetherReaderContact reader force event.momentum event.frame
  let dR:=-(R*jointCurrent event.momentum event.frame event.energy 0 force*R)
  let dTR:=timeSlope force event.momentum event.frame age
  (((dTL*L+TL*dL)*J+(TL*L)*dJ)*R+((TL*L)*J)*dR)*TR+(((TL*L)*J)*R)*dTR

theorem actual_full_noether_kernel_field_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>dressedNoetherKernel event transfer reader age (r • force))
      (actualFullNoetherVariation event transfer reader force age) 0 := by
  have tl:=physicalTime_direction force (event.momentum-transfer) event.frame (-age)
  have rl:=inverse_direction (event.momentum-transfer) event.frame event.energy event.nonreal force
  have j:=noetherReader_generated reader force event.momentum event.frame
  have rr:=inverse_direction event.momentum event.frame event.energy event.nonreal force
  have tr:=physicalTime_direction force event.momentum event.frame age
  simpa only [dressedNoetherKernel,actualFullNoetherVariation,Pi.mul_apply,zero_smul] using!
    (((tl.mul rl).mul j).mul rr).mul tr

/-- Preparation is fixed by its actual event; this derivative varies the complete interaction kernel and all its contact terms. -/
theorem actual_whole_physical_noether_response_generated (event : DressedEvent) (leg : CompositeLeg)
    (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>actualPhysicalEulerObserver event leg
      (dressedNoetherKernel event transfer reader age (r • force)))
      (actualPhysicalEulerObserver event leg (actualFullNoetherVariation event transfer reader force age)) 0 :=
  ((actualPhysicalEulerObserver event leg).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (actual_full_noether_kernel_field_generated event transfer reader force age)

end LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver
