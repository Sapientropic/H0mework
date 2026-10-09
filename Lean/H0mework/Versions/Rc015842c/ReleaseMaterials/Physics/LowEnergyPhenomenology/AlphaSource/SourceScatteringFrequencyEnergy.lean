import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyPreparedWard
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargedScatteringReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalScatteringFrequencyWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance scatteringFrequencyQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe PreparationVacuumWholeOrigin

/-- The original scattering frequency leg is the complete already normalized field-energy jet. -/
theorem sourceScatteringHamiltonianCoefficients (f : Field289) (k : Fin 4) :
    fieldHamiltonianCoefficients (sourceField f) k=
      sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection f) k := by
  rw [←sourceNormalizedEnergyJet_matrix _ _ (sourceState_valid sourcePoint),
    sourceNormalizedEnergyJet_fullField _ (sourceState_valid sourcePoint)]
  have reader : statePhase sourceVoltageActualState*densityVariation f sourceVoltageActualState k=readerCoefficient f k := by
    change familyReader f sourcePoint.val k=_
    exact familyReader_event_native f k
  rw [reader,reader_coefficient_forcing,neg_neg]

theorem sourceScatteringFrequency_real (f : Field289) (k : Fin 4) :
    frequencyCoefficients (sourceField f) k=sourceEnergyCoefficients (fieldDirection f) k := by
  rw [frequencyCoefficients,sourceScatteringHamiltonianCoefficients]
  rfl

private theorem field_coordinates (f : Field289) : f=∑j : Fin 289,f j • fieldUnit j := by
  funext j
  simp [fieldUnit,Finset.sum_apply,Pi.single_apply]

/-- Complexification occurs after all original real source directions; each of the 289 field coordinates is retained. -/
theorem sourceScatteringFrequency_complex (V : Fin 289→ℂ) (k : Fin 4) :
    complexFrequencyCoefficients (originalComplexDirection V) k=
      ∑j : Fin 289,V j • sourceEnergyCoefficients (fieldDirection (fieldUnit j)) k := by
  have real (f : Field289) : realFrequencyCoefficients k f=
      ∑j : Fin 289,(f j:ℂ) • sourceEnergyCoefficients (fieldDirection (fieldUnit j)) k := by
    conv_lhs => rw [field_coordinates f]
    simp only [map_sum,map_smul,realFrequencyCoefficients_source,
      sourceScatteringFrequency_real]
    apply Finset.sum_congr rfl
    intro j _
    exact RCLike.real_smul_eq_coe_smul (K:=ℂ) (f j)
      (sourceEnergyCoefficients (fieldDirection (fieldUnit j)) k)
  change realFrequencyCoefficients k (fun j=>(V j).re)+
    Complex.I • realFrequencyCoefficients k (fun j=>(V j).im)=_
  rw [real,real,Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  have scalar : ((V j).re:ℂ)+Complex.I*((V j).im:ℂ)=V j := by
    rw [mul_comm Complex.I,Complex.re_add_im]
  exact (add_smul ((V j).re:ℂ) (Complex.I*((V j).im:ℂ))
    (sourceEnergyCoefficients (fieldDirection (fieldUnit j)) k)).symm.trans
      (congrArg (fun z : ℂ=>z • sourceEnergyCoefficients (fieldDirection (fieldUnit j)) k) scalar)

private theorem affine_field_sum (p : PhysicalMomentum) (V : Fin 289→ℂ)
    (C : Fin 289→Fin 4→FiberOperators) :
    affine (fun k=>∑j : Fin 289,V j • C j k) p=
      ∑j : Fin 289,V j • affine (C j) p := by
  simp only [affine,smul_add,Finset.smul_sum,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul,smul_smul,mul_comm]

/-- The existing scattering leg evaluates the same full Hamiltonian matrix used by the physical field-energy reader. -/
theorem sourceScatteringFrequency_affine (p : PhysicalMomentum) (V : Fin 289→ℂ) :
    affine (complexFrequencyCoefficients (originalComplexDirection V)) p=
      sourceEnergyMatrixRead (∑j : Fin 289,V j •
        affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (fieldUnit j))) p) := by
  have coefficients : complexFrequencyCoefficients (originalComplexDirection V)=
      fun k=>∑j : Fin 289,V j • sourceEnergyCoefficients (fieldDirection (fieldUnit j)) k := by
    funext k
    exact sourceScatteringFrequency_complex V k
  rw [coefficients,affine_field_sum]
  simp only [sourceEnergyCoefficients_affine,map_sum,map_smul]

/-- Every native propagation column feeds the original scattering frequency leg with its actual energy weight. -/
theorem sourceScatteringFrequency_channel (p n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3) :
    affine (complexFrequencyCoefficients (originalComplexDirection (sourceChargedChannel n zeta i))) p=
      sourceEnergyMatrixRead (sourcePhysicalPrimalWeight p (fixedMomentum n zeta) i) := by
  rw [sourceScatteringFrequency_affine,sourcePhysicalPrimalWeight_source]
  apply congrArg sourceEnergyMatrixRead
  apply Finset.sum_congr rfl
  intro j _
  have field : sourceChargedChannel n zeta i j=
      sourceMatrix sourceEnergyChannelTerms (fixedMomentum n zeta) j ⟨i.val,by omega⟩ := by
    rw [sourceEnergyChannelMatrix_entry]
    unfold sourceChargedChannel
    have unit : fiveVector (Pi.single (⟨i.val,by omega⟩:Fin 5) (1:ℂ))=Pi.single (⟨i.val,by omega⟩:Fin 289) (1:ℂ) := by
      funext row
      by_cases inside : row.val<5
      · simp [fiveVector,inside,Pi.single_apply,Fin.ext_iff]
      · have different : i.val≠row.val:=by omega
        simp [fiveVector,inside,Fin.ext_iff,different]
    rw [unit,Matrix.mulVec_single_one]
    rfl
  rw [field]

/-- The actual channel-two insertion is the original Clifford energy operator in the unchanged scattering kernel. -/
theorem sourceScatteringFrequency_two (p n : PhysicalMomentum) (zeta : ℂ) :
    affine (complexFrequencyCoefficients (originalComplexDirection (sourceChargedChannel n zeta 2))) p=
      sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n zeta)) := by
  rw [sourceScatteringFrequency_channel,sourcePhysicalPrimalWeight_two]
  rfl

end LowEnergy.PreparationPhysicalScatteringFrequencyWard
