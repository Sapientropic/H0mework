import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyChannelFrame
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNormalizedEnergyJet
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelTwoSpinPort
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedPropagatingRead
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.BosonCausal.Metric
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Lapse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNormalizedFullField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse PreparationVacuumMixedControl
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumChargedLongRangeRead
open PreparationVacuumNativeSlowCoupling PreparationVacuumSourceFieldFamily
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalQuantumLockedCharge PreparationPhysicalActionUnits
open PreparationVacuumCausalPoleResponse PreparationVacuumActualFieldQuantization
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedSpatialResponse
open PreparationVacuumFullSlowFieldResponse PreparationVacuumChargedPacketGreen
open PreparationVacuumQuantumSlowResidue
open PreparationVacuumGaugeSourceInjection GaussQuantumMultiplier GaussFockLift
open GaussCoreHilbert SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open CanonicalGradedCharge GaussHistoryHilbert PreparationVacuumMovingPoleGaussReturn
open FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open Stage10.CanonicalMatter PreparationVacuumElectromagneticIdentity
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance fieldEnergyAxesQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
local instance fieldEnergyAxesMode : DecidableEq Mode:=Classical.decEq _

def sourceEnergyAxisField (i : Fin 3) (k : Fin 4) : Field289 :=
  fun row=>(sourceMatrix sourceEnergyChannelTerms (Pi.single k 1) row ⟨i.val,by omega⟩).re

private theorem sourceTerm_real (t : SourceTerm) (v : Fin 4→ℝ) (row column : Fin 289) :
    (t.matrix (fun k=>(v k:ℂ)) row column).im=0 := by
  simp only [SourceTerm.matrix,Matrix.single_apply]
  split_ifs
  · simp [coefficientValue,Powers.value,rootTwo,rootFifteen,←Complex.ofReal_pow]
  · rfl

private theorem sourceMatrix_real (terms : List SourceTerm) (v : Fin 4→ℝ)
    (row column : Fin 289) :
    (sourceMatrix terms (fun k=>(v k:ℂ)) row column).im=0 := by
  induction terms with
  | nil=>rfl
  | cons t rest ih=>
    rw [sourceMatrix_cons,Matrix.add_apply,Complex.add_im,sourceTerm_real,ih,zero_add]

theorem sourceEnergyAxisField_cast (i : Fin 3) (k : Fin 4) :
    (fun row=>(sourceEnergyAxisField i k row:ℂ))=
      (fun row=>sourceMatrix sourceEnergyChannelTerms (Pi.single k 1) row ⟨i.val,by omega⟩) := by
  have values : (fun j=>(((Pi.single k (1:ℝ):Fin 4→ℝ)) j:ℂ))=(Pi.single k (1:ℂ):Fin 4→ℂ) := by
    funext j
    simp only [Pi.single_apply]
    split_ifs <;> rfl
  funext row
  change ((sourceMatrix sourceEnergyChannelTerms (Pi.single k 1) row ⟨i.val,by omega⟩).re:ℂ)=_
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    rw [←values,sourceMatrix_real]

private theorem sourceEnergyAxisField_two_low (k : Fin 4) (row : Fin 289) (low : row.val<73) :
    sourceEnergyAxisField 2 k row=0 := by
  simp (disch := omega) [sourceEnergyAxisField,sourceEnergyChannelTerms,sourceMatrix,
    SourceTerm.matrix]

/-- Vanishing coframe/scalar/gauge is calculated only for this actual channel; its other full-field rows remain in the native frame. -/
theorem sourceEnergyAxisField_two_bosonic (k : Fin 4) :
    fieldCoframe (sourceEnergyAxisField 2 k)=0 ∧
    (∀mu,fieldGauge (sourceEnergyAxisField 2 k) mu=0) ∧
    fieldScalar (sourceEnergyAxisField 2 k)=0 := by
  constructor
  · ext a mu
    exact sourceEnergyAxisField_two_low k _ (by simp only [coframeSlot];omega)
  constructor
  · intro mu
    unfold fieldGauge
    apply Finset.sum_eq_zero
    intro a _
    rw [sourceEnergyAxisField_two_low k _ (by simp only [gaugeSlot];omega),zero_smul]
  · unfold fieldScalar
    apply Finset.sum_eq_zero
    intro a _
    rw [sourceEnergyAxisField_two_low k _ (by simp only [scalarSlot];omega),zero_smul]

theorem sourceEnergyAxisField_two_lorentz (k : Fin 4) :
    fieldLorentz (sourceEnergyAxisField 2 k)=sourceChannelTwoLorentz (Pi.single k 1) := by
  ext mu a
  change (sourceMatrix sourceEnergyChannelTerms (Pi.single k 1)
    (lorentzSlot mu a) (2:Fin 289)).re=_
  rw [←rowTerms_entry sourceEnergyChannelTerms (Pi.single k 1) (lorentzSlot mu a) (2:Fin 289)]
  fin_cases mu <;> fin_cases a <;>
    norm_num [rowTerms,sourceEnergyChannelTerms,lorentzSlot,sourceChannelTwoLorentz,
      Matrix.of_apply,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals fin_cases k <;>
    norm_num [sourceMatrix,SourceTerm.matrix,Matrix.single_apply,coefficientValue,
      Powers.value,rootTwo,rootFifteen,Pi.single_apply,Fin.ext_iff]
  all_goals ring

theorem sourceEnergyAxisField_two_state (k : Fin 4) :
    fieldDirection (sourceEnergyAxisField 2 k)=
      (0,(fun mu=>spinLinear mu (sourceChannelTwoLorentz (Pi.single k 1))),0) := by
  rw [←stateDirection_source]
  change (fieldCoframe (sourceEnergyAxisField 2 k),
    (fun mu=>spinLinear mu (fieldLorentz (sourceEnergyAxisField 2 k))+
      GaussNativeMatter.nativePrimal (fieldGauge (sourceEnergyAxisField 2 k) mu)),
      scalarLinear (fieldScalar (sourceEnergyAxisField 2 k)))=_
  rw [(sourceEnergyAxisField_two_bosonic k).1,sourceEnergyAxisField_two_lorentz,
    (sourceEnergyAxisField_two_bosonic k).2.2]
  simp only [(sourceEnergyAxisField_two_bosonic k).2.1,map_zero,add_zero]

private theorem sourceChannelTwoSpin_generated (v : Fin 4→ℝ) (mu : Fin 4) :
    spinLinear mu (sourceChannelTwoLorentz v)=
      spinCoordinates (sourceChannelTwoSpinConnection (fun k=>(v k:ℂ)) mu) :=
  congrArg spinCoordinates (sourceChannelTwoDiracConnection_generated v mu)

/-- The original energy jet of the complete third-channel source axis has the full Clifford matrix normal form. -/
theorem sourceChannelTwoAxisEnergy (p : PhysicalMomentum) (k : Fin 4) :
    sourceNormalizedEnergySymbol p (sourceState sourcePoint.val)
      (fieldDirection (sourceEnergyAxisField 2 k))=
      SourceRealScalarFock.branches (spinCoordinates
        ((Complex.I*((Pi.single k (1:ℝ):Fin 4→ℝ) 0:ℂ)) • (1:DiracMatrix)-
          (Complex.I*(Real.sqrt 30:ℂ)/5) •
            (∑j : Fin 3,((Pi.single k (1:ℝ):Fin 4→ℝ) j.succ:ℂ) •
              (diracGammaZero*diracGamma j.succ)))) := by
  rw [sourceEnergyAxisField_two_state,
    sourceNormalizedEnergySymbol_connection p _
      (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint)]
  simp only [sourceChannelTwoSpin_generated,sourceState_event]
  rw [sourceSpinConnectionHamiltonian_original,sourceChannelTwoSpin_normal]

end LowEnergy.PreparationPhysicalNormalizedFullField
