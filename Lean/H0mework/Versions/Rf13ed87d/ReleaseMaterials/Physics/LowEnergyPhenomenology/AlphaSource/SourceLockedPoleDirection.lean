import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceBackgroundLockedDirection
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPolarizationRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalElectromagneticDirectionReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalElectromagneticDirection PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open CanonicalGradedSpatialSource PreparationVacuumWholeOrigin
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair StageNineHolonomicField YangMills.FullPairing
open PreparationVacuumPhysicalModeChargeRead
open PreparationPhysicalNativePhotonScatteringSheetReturn Filter
open scoped BigOperators Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] sourceChargedNativeFrameJet sourcePoleCoordinates
  sourceNativeFrequencyPolarization sourcePoleFastJet sourcePoleFrameResidual

/-- All four current coefficients are calculated from the original literal 200 terms; the middle slow column is retained as a computed zero in this particular read. -/
def sourceDirectionLiteralMatrix (v : Fin 4→ℂ) : Matrix (Fin 4) (Fin 3) ℂ :=
  !![(25/108:ℂ)*rootTwo*rootFifteen*v 3,0,0;
     0,0,(-10/9:ℂ)*v 2;
     0,0,(10/9:ℂ)*v 1;
     (-25/108:ℂ)*rootTwo*rootFifteen*v 0,0,0]

private def literalRow (v : Fin 4→ℂ) : Fin 4→(Fin 289→ℂ) :=
  ![Pi.single 0 ((25/108:ℂ)*rootTwo*rootFifteen*v 3),
    Pi.single 2 ((-10/9:ℂ)*v 2),
    Pi.single 2 ((10/9:ℂ)*v 1),
    Pi.single 0 ((-25/108:ℂ)*rootTwo*rootFifteen*v 0)]

private theorem literal_row (v : Fin 4→ℂ) (mu : Fin 4) (j : Fin 289) :
    sourceMatrix sourceEnergyChannelTerms v (lorentzSlot mu (sourceSpinSlot 2)) j=literalRow v mu j := by
  rw [←rowTerms_entry sourceEnergyChannelTerms v (lorentzSlot mu (sourceSpinSlot 2)) j]
  fin_cases mu <;>
    norm_num [rowTerms,sourceEnergyChannelTerms,lorentzSlot,sourceSpinSlot,literalRow,
      Matrix.of_apply,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals simp [sourceMatrix,SourceTerm.matrix,Matrix.single_apply,coefficientValue,
    Powers.value,Pi.single_apply,eq_comm]

/-- This is an entry of the original native frame derivative, proved from its already generated full inverse and all 200 literal terms. -/
theorem sourceDirectionLiteral_generated (v : Fin 4→ℂ) (mu : Fin 4) (channel : Fin 3) :
    sourceChargedNativeFrameJet v (lorentzSlot mu (sourceSpinSlot 2)) ⟨channel.val,by omega⟩=
      sourceDirectionLiteralMatrix v mu channel := by
  rw [←sourceEnergyChannelMatrix_entry,literal_row]
  fin_cases mu <;> fin_cases channel <;> simp [literalRow,sourceDirectionLiteralMatrix]

def sourceDirectionLiteralRead (v : Fin 4→ℂ) (w : Fin 289→ℂ) : Fin 4→ℂ :=
  ![(25/108:ℂ)*rootTwo*rootFifteen*v 3*w 0,
    (-10/9:ℂ)*v 2*w 2,
    (10/9:ℂ)*v 1*w 2,
    (-25/108:ℂ)*rootTwo*rootFifteen*v 0*w 0]

theorem sourceDirectionLiteralRead_generated (v : Fin 4→ℂ) (w : Fin 289→ℂ) (mu : Fin 4) :
    sourceChargedCoefficient (sourceMatrix sourceEnergyChannelTerms v*ᵥw) mu=
      sourceDirectionLiteralRead v w mu := by
  simp only [sourceChargedCoefficient,Matrix.mulVec_apply,dotProduct,Matrix.row,literal_row]
  fin_cases mu <;> simp [literalRow,sourceDirectionLiteralRead,Pi.single_apply,
    ite_mul,Finset.sum_ite_eq']

/-- The same actual pole column, fast coordinates, and exact native-frame residual determine the observed direction. -/
def sourceDirectionPoleCoefficient (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (mu : Fin 4) : ℂ :=
  (epsilon:ℂ)^2*(sourceDirectionLiteralRead (physicalFrequencyMomentum s n)
    (sourcePoleCoordinates branch epsilon s n) mu+
      sourceChargedCoefficient (sourcePoleFastJet branch epsilon s n) mu)+
    sourceChargedCoefficient (sourcePoleFrameResidual branch epsilon s n) mu

theorem sourceDirectionPoleCoefficient_generated (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (nonzero : epsilon≠0) (mu : Fin 4) :
    sourceChargedCoefficient (sourceNativeFrequencyPolarization branch epsilon s n) mu=
      sourceDirectionPoleCoefficient branch epsilon s n mu := by
  rw [sourceNativeFrequencyPolarization_charge branch epsilon s n nonzero,sourcePoleJetField_literal]
  change (epsilon:ℂ)^2*(sourceChargedCoefficient (sourcePoleLiteralJet branch epsilon s n) mu+
    sourceChargedCoefficient (sourcePoleFastJet branch epsilon s n) mu)+_= _
  rw [sourcePoleLiteralJet,sourceDirectionLiteralRead_generated]
  rfl

private theorem background_axis : sourceBackgroundMatterAction (Pi.single 2 (1:ℝ))=sourceLockedAction 2 := by
  simp [sourceBackgroundMatterAction,Pi.single_apply,apply_ite,ite_smul]

/-- The direction selected in the pole decomposition is the same source-background locked action. All other physical background variation is still in the full remainder. -/
theorem sourceDirectionPole_backgroundMatter (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (mu : Fin 4) (point : BasePoint) :
    sourceModeMother (sourceNativeFrequencyPolarization branch epsilon s n) mu (actual.matter point)=
      sourceModeMother (sourceChargedFieldRemainder
        (sourceNativeFrequencyPolarization branch epsilon s n)) mu (actual.matter point) := by
  have zero:=sourceBackgroundMatter_source (Pi.single 2 (1:ℝ)) point
  rw [background_axis] at zero
  rw [sourceChargedMother_generated]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,zero,smul_zero,zero_add]

/-- The actual independent dual is handled by its original composition action, without an adjoint replacement. -/
theorem sourceDirectionPole_backgroundDual (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (mu : Fin 4) (point : BasePoint) :
    (actual.conjugateMatter point).comp (sourceModeMother (sourceNativeFrequencyPolarization branch epsilon s n) mu)=
      (actual.conjugateMatter point).comp (sourceModeMother (sourceChargedFieldRemainder
        (sourceNativeFrequencyPolarization branch epsilon s n)) mu) := by
  have zero:=sourceBackgroundDual_source (Pi.single 2 (1:ℝ)) point
  rw [background_axis] at zero
  rw [sourceChargedMother_generated,LinearMap.comp_add,LinearMap.comp_smul,zero,smul_zero,zero_add]

/-- Both physical sheets retain their independent full current emitter and frequency-flux normalization. -/
theorem sourceDirectionFrequencyResidue (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀leg : SourcePhotonLeg,∀mu : Fin 4,
      sourceChargedCoefficient (sourcePhotonFrequencyResidue leg e.val (sourceSheet branch n unit e.val) n) mu=
        sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*
          sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n mu := by
  filter_upwards [sourcePhotonFrequencyResidue_fluxFactor branch n unit] with e factor
  intro leg mu
  rw [factor leg]
  change sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*
    sourceChargedCoefficient (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) mu=_
  rw [sourceDirectionPoleCoefficient_generated branch e.val _ n e.property.1.ne']

end LowEnergy.PreparationPhysicalElectromagneticDirectionReturn
