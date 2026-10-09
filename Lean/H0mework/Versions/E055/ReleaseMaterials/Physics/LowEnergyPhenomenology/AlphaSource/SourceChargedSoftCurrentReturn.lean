import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedJointScattering
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualSoftSelection

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedSoftScatteringReturn
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
local instance chargedSoftCurrentQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

/-- A fixed-rest charged source, with its original material resolvents and time window. -/
structure SourceChargedSoftLeg where
  q : PhysicalResponsePoint
  sideL : Fin 2
  edgeL : Fin 2
  sideR : Fin 2
  edgeR : Fin 2
  window : ℝ

private def physicalResidueLinear (epsilon s : ℝ) (n : PhysicalMomentum) :
    (Fin 289→ℂ)→ₗ[ℂ](Fin 289→ℂ) where
  toFun f:=(epsilon:ℂ)^2 • nativeInsertion epsilon s n
    (sourceResidue epsilon s n*ᵥnativeModeForcing epsilon s n f)
  map_add' f g:=by
    have forcing : nativeModeForcing epsilon s n (f+g)=
        nativeModeForcing epsilon s n f+nativeModeForcing epsilon s n g := by
      funext i
      simp only [nativeModeForcing,activeForcing,Matrix.mulVec_add,Pi.add_apply]
    have insertion (v w : Fin 5→ℂ) : nativeInsertion epsilon s n (v+w)=
        nativeInsertion epsilon s n v+nativeInsertion epsilon s n w := by
      have lift : fiveVector (v+w)=fiveVector v+fiveVector w := by
        funext i
        simp only [fiveVector,Pi.add_apply]
        split_ifs <;> simp
      simp only [nativeInsertion,lift,Matrix.mulVec_add]
    rw [forcing,Matrix.mulVec_add,insertion,smul_add]
  map_smul' c f:=by
    have forcing : nativeModeForcing epsilon s n (c • f)=c • nativeModeForcing epsilon s n f := by
      funext i
      simp only [nativeModeForcing,activeForcing,Matrix.mulVec_smul,Pi.smul_apply]
    rw [forcing,Matrix.mulVec_smul,nativeInsertion_smul,smul_comm]
    rfl

def sourceChargedSoftCurrent (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : Fin 289→ℂ :=
  actualSoftCurrent leg.q branch n unit (sourceChargedRestIndex leg.sideL leg.edgeL)
    (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window e

/-- All eight moving source states contribute to the same fixed charged maker; the conjugate right overlap is retained. -/
theorem sourceChargedSoftCurrent_commonCarrier (leg : SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) :
    sourceChargedSoftCurrent leg branch n unit e=
      ∑b : RestStateIndex,∑a : RestStateIndex,
        (movingOverlap (sheetLeft e.val n 0) (sourceChargedRestIndex leg.sideL leg.edgeL) a*
          star (movingOverlap 0 (sourceChargedRestIndex leg.sideR leg.edgeR) b)) •
        sheetCurrent leg.q e.val (sourceSheet branch n unit e.val) n 0 a b leg.window := by
  funext i
  rw [sourceChargedSoftCurrent,actualSoftCurrent_same_carrier]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual physical-frequency residue of the fixed charged source is the full overlap combination of original moving-source residues. -/
theorem sourceChargedSoftResidue_commonCarrier (leg : SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) :
    actualSoftResidue leg.q branch n unit (sourceChargedRestIndex leg.sideL leg.edgeL)
      (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window e=
      ∑b : RestStateIndex,∑a : RestStateIndex,
        (movingOverlap (sheetLeft e.val n 0) (sourceChargedRestIndex leg.sideL leg.edgeL) a*
          star (movingOverlap 0 (sourceChargedRestIndex leg.sideR leg.edgeR) b)) •
        actualFrequencyResidue leg.q e.val (sourceSheet branch n unit e.val) n 0 a b leg.window := by
  change physicalResidueLinear e.val (sourceSheet branch n unit e.val) n
    (sourceChargedSoftCurrent leg branch n unit e)=_
  rw [sourceChargedSoftCurrent_commonCarrier]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (e.val:ℂ)^2 • (_ : Fin 289→ℂ)=((e.val^2:ℝ):ℂ) • (_ : Fin 289→ℂ)
  rw [Complex.ofReal_pow,actualSheetResidue]

/-- The source frequency conversion is applied to the physical residue, with its original factor 2ω. -/
def sourceChargedSoftField (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : Fin 289→ℂ :=
  (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) •
    actualSoftResidue leg.q branch n unit (sourceChargedRestIndex leg.sideL leg.edgeL)
      (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window e

def sourceChargedSoftFieldLimit (leg : SourceChargedSoftLeg) (branch : Fin 2) : Fin 289→ℂ :=
  if branch=0 then
    ((softCoefficient branch:ℂ)*actualGaussWeight leg.q (sourceChargedRestIndex leg.sideL leg.edgeL)
      (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window) • nativeBranchVector branch else 0

/-- The complete Gauss weight retains the charge derivative, color contact and actual source deviation. -/
theorem sourceChargedSoftField_tendsto (leg : SourceChargedSoftLeg) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (nonrealL : leg.q.z.im≠0) (nonrealR : leg.q.w.im≠0) :
    Tendsto (sourceChargedSoftField leg branch n unit) scaleApproach (𝓝 (sourceChargedSoftFieldLimit leg branch)) :=
  actualSoftResidue_source_selection leg.q branch n unit _ _ leg.window nonrealL nonrealR

end LowEnergy.PreparationPhysicalChargedSoftScatteringReturn
