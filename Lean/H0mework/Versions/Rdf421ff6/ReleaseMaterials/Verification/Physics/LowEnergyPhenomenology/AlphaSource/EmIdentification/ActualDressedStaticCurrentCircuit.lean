import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticFeedback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticFeedback
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumStaticPoleResponse ActualDressedFullCoulomb ActualDressedFrequencyHalf
open ActualDressedCorrectedGreen ActualDressedCorrectedElectronRead ActualDressedOrderedStatic
open ActualEMDressedConstraint ActualEMDressedSchur ActualCompositeFieldCurrent ActualWholeStatic
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] correctedResponse sourceGreen ActualCompositeFieldCurrent.compositeCurrent

/-- Both actual independent full/sharp endpoints enter the native field before observation. -/
def nativeCurrentRead (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain)
    (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
    (sourceSpatialStaticNativeField n unit kappa (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))

def feedbackCurrentRead (event : DressedEvent) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (kappa : staticDomain) (sigma : ℝ) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
    (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa)*ᵥ
      (frequencyQuantumCorrection event (kappa.val • n) (sourceStaticSpatialMomentum n kappa.val)
        (dampedFourierClock 0 sigma)*ᵥcorrectedResponse event (Real.sqrt kappa.val) 0 sigma n
          (ActualCompositeFieldCurrent.compositeCurrent ps sL sR)))

def nullCurrentRead (event : DressedEvent) (n : PhysicalMomentum) (kappa : staticDomain)
    (sigma : ℝ) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
    (sourceNullLift (sourceStaticSpatialMomentum n kappa.val)
      (sourceNullCoordinates (sourceStaticSpatialMomentum n kappa.val)
        (correctedResponse event (Real.sqrt kappa.val) 0 sigma n
          (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))))

theorem actual_static_current_circuit (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (kappa : staticDomain) (sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event (Real.sqrt kappa.val) 0 sigma n≠0)
    (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    correctedProbeRead event (Real.sqrt kappa.val) 0 sigma n pd ps dL dR sL sR=
      nativeCurrentRead n unit kappa pd ps dL dR sL sR+
        feedbackCurrentRead event n unit kappa sigma pd ps dL dR sL sR+
        nullCurrentRead event n kappa sigma pd ps dL dR sL sR := by
  rw [corrected_probe_read_original,actual_corrected_static_feedback event n unit kappa sigma positive regular]
  simp only [dotProduct_add,nativeCurrentRead,feedbackCurrentRead,nullCurrentRead,
    sourceSpatialStaticNativeField,PreparationVacuumOriginalGreenFeedback.sourceField]

def nativeCurrentCoefficient (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
    (staticResidue (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))

/-- The scalar coefficient belongs to the original full native residue on these actual endpoints, independently of direction. -/
theorem actual_native_current_spatial_return (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    Tendsto (fun kappa : staticDomain => -(kappa.val : ℂ)^2*nativeCurrentRead n unit kappa pd ps dL dR sL sR)
      staticApproach (𝓝 (nativeCurrentCoefficient pd ps dL dR sL sR)) := by
  have observer : Continuous (fun a : Fin 289→ℂ => dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR) a) := by
    unfold dotProduct
    fun_prop
  have paid:=observer.continuousAt.tendsto.comp
    (sourceSpatialStaticNativeFieldResidue n unit (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))
  simpa only [Function.comp_def,dotProduct_smul,smul_eq_mul,nativeCurrentRead,nativeCurrentCoefficient] using paid

def nativeMatrixReader (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : WholeMatrix→L[ℝ] ℂ :=
  ({toFun := fun M => dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
      (M*ᵥActualCompositeFieldCurrent.compositeCurrent ps sL sR)
    map_add' := fun M N => by simp only [Matrix.add_mulVec,dotProduct_add]
    map_smul' := fun r M => by simp only [Matrix.smul_mulVec,dotProduct_smul,RingHom.id_apply]} :
      WholeMatrix→ₗ[ℝ] ℂ).toContinuousLinearMap

def nativeCurrentPrice (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℝ :=
  ‖nativeMatrixReader pd ps dL dR sL sR‖*wholeStaticBudget

/-- The old full-field uniform radius is consumed by the new actual unnormalized current, without a speed or detector insertion. -/
theorem actual_native_current_uniform_price (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    ∃radius : ℝ,0<radius ∧ ∀kappa : staticDomain,kappa.val<radius →
      ∀n : PhysicalMomentum,∀unit : spatialSquare n=1,
        ‖(kappa.val : ℂ)^2*nativeCurrentRead n unit kappa pd ps dL dR sL sR‖≤
          nativeCurrentPrice pd ps dL dR sL sR := by
  obtain ⟨radius,positive,paid⟩:=whole_static_green_domination
  refine ⟨radius,positive,?_⟩
  intro kappa small n unit
  have bound:=(nativeMatrixReader pd ps dL dR sL sR).le_opNorm
    ((kappa.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit kappa))
  have total:=bound.trans (mul_le_mul_of_nonneg_left (paid kappa small n unit) (norm_nonneg _))
  change ‖dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
    (((kappa.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit kappa))*ᵥ
      ActualCompositeFieldCurrent.compositeCurrent ps sL sR)‖≤nativeCurrentPrice pd ps dL dR sL sR at total
  simpa only [Matrix.smul_mulVec,dotProduct_smul,Complex.real_smul,Complex.ofReal_pow,smul_eq_mul,
    nativeCurrentRead,sourceSpatialStaticNativeField,PreparationVacuumOriginalGreenFeedback.sourceField] using total

end LowEnergy.GaussComposite.ActualDressedStaticFeedback
