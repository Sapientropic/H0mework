import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyObservation
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyInitialSource
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInfrared

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin PreparationVacuumMixedPrincipal
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumMixedFieldReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumNativeSlowCoupling
open PreparationVacuumNativePoleTensor PreparationVacuumFullSlowFieldResponse
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedControl
open PreparationPhysicalCurvatureSheetLimit CanonicalGradedSpatialSource ActualEMCarrierOwn
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceNativeFrame sourceChargedNativeFrameJet sourceChargedNativeFrameResidual
  fullNativeOrigin fullKernelFrame fullInverse originalChange originalReadback
  sourceWholePhotonFrequencyResidue sourceNativeFrequencyPolarization

namespace VoltageJetTable
private def readerTerms : List SourceTerm :=
  [⟨0,20,⟨0,0,0,0⟩,1⟩,⟨1,32,⟨0,0,0,0⟩,1⟩,
   ⟨2,44,⟨0,0,0,0⟩,1⟩,⟨3,56,⟨0,0,0,0⟩,1⟩]
private def change0 := fastNormalizeTerms (productTerms readerTerms (originTerms originalChangeTerms))
private def change1 := fastNormalizeTerms (productTerms readerTerms (degreeTerms (positiveTerms originalChangeTerms) 1))
private def response := fastNormalizeTerms (productTerms change0 fullInverseTerms)
private def force := fastNormalizeTerms (productTerms (degreeTerms (positiveTerms activeTerms) 1) fullKernelTerms)
private def jet := fastNormalizeTerms (productTerms change1 fullKernelTerms ++ negativeTerms (productTerms response force))
private def jetTerms : List SourceTerm :=
  [⟨0,1,⟨1,0,0,0⟩,⟨⟨5/11,0⟩,⟨0,0⟩⟩⟩,
   ⟨1,1,⟨0,1,0,0⟩,⟨⟨25/67,0⟩,⟨0,0⟩⟩⟩,
   ⟨2,1,⟨0,0,1,0⟩,⟨⟨25/67,0⟩,⟨0,0⟩⟩⟩,
   ⟨3,1,⟨0,0,0,1⟩,⟨⟨25/67,0⟩,⟨0,0⟩⟩⟩]
private theorem jet_certificate : jet=jetTerms := by decide +kernel
private theorem origin_certificate : fastNormalizeTerms (productTerms readerTerms fullNativeOriginTerms)=[] := by decide +kernel
private theorem slowFast_certificate : fastNormalizeTerms
    (productTerms jetTerms slowFastFrameTerms++negativeTerms jetTerms)=[] := by decide +kernel

private theorem origin_value (ts : List SourceTerm) (v : Fin 4→ℂ) :
    sourceMatrix (originTerms ts) v=sourceMatrix ts 0 := by
  calc
    _=sourceMatrix (originTerms ts) 0 := by
      simpa only [degreeTensor,degreeTerms,originTerms,zero_smul,pow_zero,one_smul] using
        (degreeTensor_scaled ts 0 (0:ℂ) v).symm
    _=sourceMatrix ts 0 := originTerms_generated ts
private def index (mu : Fin 4) : Fin 289 := ⟨mu.val,by omega⟩
private def reader : Matrix (Fin 289) (Fin 289) ℂ := sourceMatrix readerTerms 0
private theorem reader_constant (v : Fin 4→ℂ) : sourceMatrix readerTerms v=reader := by
  norm_num [reader,readerTerms,sourceMatrix,SourceTerm.matrix,Powers.value]
private theorem reader_entry (mu : Fin 4) (j : Fin 289) :
    reader (index mu) j=if j=gaugeSlot mu 11 then 1 else 0 := by
  fin_cases mu <;> norm_num [reader,readerTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    index,gaugeSlot,coefficientValue,Powers.value,eq_comm,Fin.ext_iff,
    QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
private theorem reader_mul (M : Matrix (Fin 289) (Fin 289) ℂ) (mu : Fin 4) (j : Fin 289) :
    (reader*M) (index mu) j=M (gaugeSlot mu 11) j := by
  simp only [Matrix.mul_apply,reader_entry,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
private theorem change0_value (v : Fin 4→ℂ) : sourceMatrix change0 v=reader*originalChange 0 := by
  simp only [change0,fastNormalizeTerms_value,productTerms_value,origin_value,reader_constant,originalChange]
private theorem jet_value (v : Fin 4→ℂ) : sourceMatrix jetTerms v=
    reader*(sourceLinearPart originalChangeTerms v*fullKernelFrame-
      originalChange 0*fullInverse*sourceLinearPart activeTerms v*fullKernelFrame) := by
  rw [←jet_certificate]
  simp only [jet,change1,response,force,fastNormalizeTerms_value,sourceMatrix_append,negativeTerms_value,
    productTerms_value,change0_value,reader_constant,fullInverse_generated,fullKernel_generated,
    sourceLinearPart,degreeTensor]
  noncomm_ring

/-- The actual four Y rows have zero origin, before any choice of pole column. -/
theorem voltage_y_origin (mu : Fin 4) (j : Fin 289) : fullNativeOrigin (gaugeSlot mu 11) j=0 := by
  have zero : reader*fullNativeOrigin=0 := by
    rw [fullNativeOrigin_generated,←reader_constant 0,←productTerms_value,←fastNormalizeTerms_value,
      origin_certificate]
    rfl
  have row:=congrFun (congrFun zero (index mu)) j
  rwa [reader_mul] at row

/-- Every slow and fast column is computed from the original full complementary inverse. -/
theorem voltage_y_frame_jet (v : Fin 4→ℂ) (mu : Fin 4) (j : Fin 289) :
    sourceChargedNativeFrameJet v (gaugeSlot mu 11) j=
      (Pi.single 1 ((if mu=0 then (5/11:ℂ) else 25/67)*v mu) : Fin 289→ℂ) j := by
  have paid:=normalization_equal (productTerms jetTerms slowFastFrameTerms) jetTerms slowFast_certificate v
  rw [productTerms_value,slowFastFrame_constant] at paid
  nth_rw 1 [jet_value] at paid
  have row:=congrFun (congrFun paid (index mu)) j
  rw [Matrix.mul_assoc,reader_mul] at row
  rw [sourceChargedNativeFrameJet,row]
  fin_cases mu <;> norm_num [jetTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,index,
    coefficientValue,Powers.value,Pi.single_apply,eq_comm,Fin.ext_iff]
  all_goals split_ifs <;> try ring
  all_goals congr 1
end VoltageJetTable

/-- The native Y output of the actual pole keeps the complete cofactor and full remainder. -/
theorem voltage_y_frequency_field (branch : Fin 2) (e s : ℝ) (n : PhysicalMomentum)
    (nonzero : e≠0) (mu : Fin 4) :
    sourceNativeFrequencyPolarization branch e s n (gaugeSlot mu 11)=
      (e:ℂ)^2*((if mu=0 then (5/11:ℂ) else 25/67)*physicalFrequencyMomentum s n mu*
        sourcePoleCoordinates branch e s n 1)+sourcePoleFrameResidual branch e s n (gaugeSlot mu 11) := by
  have paid:=congrFun (sourceNativeFrequencyPolarization_firstReturn branch e s n nonzero) (gaugeSlot mu 11)
  have origin : sourcePoleOriginField branch e s n (gaugeSlot mu 11)=0 := by
    unfold sourcePoleOriginField
    rw [←Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec,dotProduct,VoltageJetTable.voltage_y_origin,zero_mul,Finset.sum_const_zero]
  have jet : sourcePoleJetField branch e s n (gaugeSlot mu 11)=
      (if mu=0 then (5/11:ℂ) else 25/67)*physicalFrequencyMomentum s n mu*sourcePoleCoordinates branch e s n 1 := by
    simp only [sourcePoleJetField,Matrix.mulVec,dotProduct,VoltageJetTable.voltage_y_frame_jet]
    exact single_dotProduct _ _ _

  change sourceNativeFrequencyPolarization branch e s n (gaugeSlot mu 11)-
    sourcePoleOriginField branch e s n (gaugeSlot mu 11)-(e:ℂ)^2*sourcePoleJetField branch e s n (gaugeSlot mu 11)=_ at paid
  rw [origin,jet] at paid
  linear_combination paid

/-- The ordinary Y electric curvature, with the original physical clock sign. -/
def voltageYElectric (p : Fin 4→ℂ) (field : Fin 289→ℂ) (i : Fin 3) : ℂ :=
  p 0*field (gaugeSlot i.succ 11)-p i.succ*field (gaugeSlot 0 11)

set_option backward.isDefEq.respectTransparency true in
/-- The electric output is an actual row of the original 36-curvature reader. -/
theorem voltage_y_electric_read (p : Fin 4→ℂ) (field : Fin 289→ℂ) (i : Fin 3) :
    (originalReader36 p *ᵥ field) ⟨24+i.val,by omega⟩=voltageYElectric p field i := by
  have row : originalReader36 p ⟨24+i.val,by omega⟩=
      Pi.single (gaugeSlot i.succ 11) (p 0)-Pi.single (gaugeSlot 0 11) (p i.succ) := by
    fin_cases i <;> ext j
    all_goals fin_cases j
    all_goals first
      | (change (0:ℂ)=0-0; exact (sub_self 0).symm)
      | (change p 0=p 0-0; exact (sub_zero (p 0)).symm)
      | (change -p 1=0-p 1; exact (zero_sub (p 1)).symm)
      | (change -p 2=0-p 2; exact (zero_sub (p 2)).symm)
      | (change -p 3=0-p 3; exact (zero_sub (p 3)).symm)
  change dotProduct (originalReader36 p ⟨24+i.val,by omega⟩) field=_
  rw [row,sub_dotProduct,single_dotProduct,single_dotProduct]
  rfl

/-- The original complete mode generates a nonzero electric second jet; all fast channels were included in the computation. -/
theorem voltage_y_frequency_electric (branch : Fin 2) (e s : ℝ) (n : PhysicalMomentum)
    (nonzero : e≠0) (i : Fin 3) :
    voltageYElectric (frequencyRay e s n) (sourceNativeFrequencyPolarization branch e s n) i=
      (e:ℂ)^4*((-60/737:ℂ)*(s:ℂ)*(n i:ℂ)*sourcePoleCoordinates branch e s n 1)+
      (e:ℂ)^2*voltageYElectric (physicalFrequencyMomentum s n) (sourcePoleFrameResidual branch e s n) i := by
  unfold voltageYElectric
  rw [voltage_y_frequency_field branch e s n nonzero i.succ,
    voltage_y_frequency_field branch e s n nonzero 0,frequencyRay_scaled]
  have diff : i.succ≠(0:Fin 4):=Fin.succ_ne_zero i
  simp only [if_neg diff,ite_true,Pi.smul_apply,smul_eq_mul,physicalFrequencyMomentum,
    Fin.cases_zero,Fin.cases_succ]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Longitudinal leading Y potential has zero magnetic second jet, while its full remainder is retained. -/
theorem voltage_y_frequency_magnetic (branch : Fin 2) (e s : ℝ) (n : PhysicalMomentum)
    (nonzero : e≠0) (i j : Fin 3) :
    (frequencyRay e s n) i.succ*sourceNativeFrequencyPolarization branch e s n (gaugeSlot j.succ 11)-
      (frequencyRay e s n) j.succ*sourceNativeFrequencyPolarization branch e s n (gaugeSlot i.succ 11)=
    (e:ℂ)^2*(physicalFrequencyMomentum s n i.succ*sourcePoleFrameResidual branch e s n (gaugeSlot j.succ 11)-
      physicalFrequencyMomentum s n j.succ*sourcePoleFrameResidual branch e s n (gaugeSlot i.succ 11)) := by
  rw [voltage_y_frequency_field branch e s n nonzero i.succ,
    voltage_y_frequency_field branch e s n nonzero j.succ,frequencyRay_scaled]
  simp only [if_neg (Fin.succ_ne_zero _),Pi.smul_apply,smul_eq_mul,physicalFrequencyMomentum,Fin.cases_succ]
  ring

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
