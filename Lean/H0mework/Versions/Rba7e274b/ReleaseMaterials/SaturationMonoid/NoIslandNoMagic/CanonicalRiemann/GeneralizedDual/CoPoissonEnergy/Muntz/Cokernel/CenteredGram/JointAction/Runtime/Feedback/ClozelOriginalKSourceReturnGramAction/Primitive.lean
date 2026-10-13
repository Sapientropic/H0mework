import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReturnGramAction.Ward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceScaledMaximalResponse
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
open OriginalRieszSource
local instance primitiveAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def literalFiniteAction (h : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
 pairedMellinTranslationCharacter (star observation.coordinate) h • ContinuousLinearMap.id ℂ BurnolL2-
 pairedBurnolMultiplicativeDilation h

private theorem actual_paired_R_action (h : ℝ) (material : BurnolL2) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (pairedBurnolMultiplicativeDilation h material)=
 pairedBurnolMultiplicativeDilation h (OriginalKFullSourceRResponse.Op.R observation nontrivial half material) := by
 unfold pairedBurnolMultiplicativeDilation
 simp only [smul_apply,add_apply,map_smul,map_add]
 simp only [OriginalKCombCofinalRAction.original_R_direct]
 exact congrArg (fun value : BurnolL2=>(1/2:ℂ) • value)
   (congrArg₂ (fun left right : BurnolL2=>left+right)
     (burnolDirectRightResolvent_dilation (observation.coordinate/2) h material)
     (burnolDirectRightResolvent_dilation (observation.coordinate/2) (-h) material))

private theorem actual_finite_R_action (h : ℝ) (material : BurnolL2) :
 literalFiniteAction observation h (OriginalKFullSourceRResponse.Op.R observation nontrivial half material)=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (literalFiniteAction observation h material) := by
 unfold literalFiniteAction
 simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,map_sub,map_smul,actual_paired_R_action]

def contactFiniteInventory (h : ℝ) : BurnolL2 :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half;
 -(OriginalRieszSource.Kernel.A coordinate/2) •
   (OriginalRieszFiniteSource.edgeIntegral coordinate h+OriginalRieszFiniteSource.edgeIntegral coordinate (-h))+
 (OriginalRieszSource.Kernel.beta coordinate/2) •
   ((2*(star coordinate.value-1/2)) •
     (OriginalRieszFiniteSource.nativeIntegral (star coordinate.value-1/2) (OriginalRieszFiniteSource.fourierPrimitive coordinate) h+
      OriginalRieszFiniteSource.nativeIntegral (star coordinate.value-1/2) (OriginalRieszFiniteSource.fourierPrimitive coordinate) (-h))-
     (OriginalRieszFiniteSource.fourierEdgeIntegral coordinate h+OriginalRieszFiniteSource.fourierEdgeIntegral coordinate (-h)))

private theorem actual_edge_finite (h : ℝ) :
 literalFiniteAction observation h
   (OriginalRieszFiniteSource.edgePrimitive (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))=
 -(1/2:ℂ) •
   (OriginalRieszFiniteSource.edgeIntegral (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h+
    OriginalRieszFiniteSource.edgeIntegral (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (-h)) := by
 unfold literalFiniteAction pairedBurnolMultiplicativeDilation OriginalRieszFiniteSource.edgeIntegral
 simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,add_apply,
   ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
 simp only [pairedMellinTranslationCharacter,OriginalKCombCofinalTwoDirection.coordinate_value,
   reciprocalMellinTranslationCharacter_eq_negativeShift]
 module

private theorem actual_fourier_edge_finite (h : ℝ) :
 literalFiniteAction observation h
   (OriginalRieszFiniteSource.fourierPrimitive (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))=
 -(1/2:ℂ) •
   ((2*(star observation.coordinate-1/2)) •
     (OriginalRieszFiniteSource.nativeIntegral (star observation.coordinate-1/2)
       (OriginalRieszFiniteSource.fourierPrimitive (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)) h+
      OriginalRieszFiniteSource.nativeIntegral (star observation.coordinate-1/2)
       (OriginalRieszFiniteSource.fourierPrimitive (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)) (-h))-
    (OriginalRieszFiniteSource.fourierEdgeIntegral (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h+
     OriginalRieszFiniteSource.fourierEdgeIntegral (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (-h))) := by
 unfold literalFiniteAction pairedBurnolMultiplicativeDilation OriginalRieszFiniteSource.fourierEdgeIntegral
 simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,add_apply,
   ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
 simp only [pairedMellinTranslationCharacter,OriginalKCombCofinalTwoDirection.coordinate_value,
   reciprocalMellinTranslationCharacter_eq_negativeShift]
 module

/-- The original quarter-edge and Fourier-quarter-edge actions generate the complete contact action. -/
theorem actual_contact_finite_inventory (h : ℝ) :
 literalFiniteAction observation h
   (OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))=
 contactFiniteInventory observation nontrivial half h := by
 unfold OriginalKSourceBalance.contactCorrection
 rw [map_sub,map_smul,map_smul,actual_edge_finite,actual_fourier_edge_finite]
 unfold contactFiniteInventory
 simp only [OriginalKCombCofinalTwoDirection.coordinate_value]
 module

/-- The literal returned primitive acts through its actual contact and regular-source inventories. -/
theorem actual_primitive_finite_inventory (h : ℝ) :
 primitiveFiniteAction observation nontrivial half h=
 contactFiniteInventory observation nontrivial half h-
 Return.sourceA observation • OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (contactFiniteInventory observation nontrivial half h)+
 (1/2:ℂ) • OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (literalFiniteAction observation h
     (OriginalKSourceBalance.regularSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))) := by
 change literalFiniteAction observation h (Return.primitiveSource observation nontrivial half)=_
 unfold _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux.primitiveSource
 rw [map_add,map_sub,map_smul,map_smul,actual_finite_R_action,actual_finite_R_action,
   actual_contact_finite_inventory]

def actualPrimitiveProjectionInventory (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolL2 :=
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) •
  (contactFiniteInventory observation nontrivial half h-
   Return.sourceA observation • OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (contactFiniteInventory observation nontrivial half h)+
   (1/2:ℂ) • OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (literalFiniteAction observation h
     (OriginalKSourceBalance.regularSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))))+
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • (Return.sourceA observation • Paid.actualMovedOutsideRStock observation nontrivial half h)+
 Return.sourceA observation • Paid.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
 Return.sourceA observation • Paid.actualOutsideRResponseStock observation nontrivial half h

/-- The character-price consumer reads the actual returned contact action, regular action and projection inventory together. -/
theorem actual_original_character_source_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 Return.sourceA observation*Paid.originalKernelCross observation nontrivial half h=
 characterPrice*star a*star (originalKForcingWard observation nontrivial half h+originalFKForcingWard observation nontrivial half h)-
 star characterPrice*a*(originalKForcingWard observation nontrivial half h-originalFKForcingWard observation nontrivial half h)-
 characterPrice*Paid.originalPairKernelRead observation nontrivial half (actualPrimitiveProjectionInventory observation nontrivial half h nonnegative bounded)+
 star characterPrice*Paid.originalSiblingKernelRead observation nontrivial half (actualPrimitiveProjectionInventory observation nontrivial half h nonnegative bounded) := by
 dsimp only
 rw [actual_scaled_kernel_cross_ward]
 unfold primitiveProjectionStock actualPrimitiveProjectionInventory
 rw [actual_primitive_finite_inventory]

/-- The paid corrected-source Euler action generates its entire finite regular response. -/
theorem actual_corrected_regular_finite (endpoint : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 burnolMultiplicativeDilation endpoint (OriginalKSourceBalance.correctedField coordinate)=
 fullMellinTranslationCharacter (star observation.coordinate) endpoint • OriginalKSourceBalance.correctedField coordinate+
 OriginalRieszFiniteSource.nativeIntegral (star observation.coordinate-1/2)
   (OriginalKSourceBalance.regularSource coordinate) endpoint := by
 dsimp only
 have source:=OriginalKSourceBalance.corrected_source_euler
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 unfold OriginalKSourceBalance.correctedVelocity at source
 change GapEuler.euler _=
   Lp.toTemperedDistributionCLM ℂ volume 2
    (-(star (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value-1/2) •
      OriginalKSourceBalance.correctedField (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)+
     OriginalKSourceBalance.regularSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)) at source
 simp only [map_add,map_smul,Lp.toTemperedDistributionCLM_apply,
   OriginalKCombCofinalTwoDirection.coordinate_value] at source
 have native : GapEuler.euler
    (OriginalKSourceBalance.correctedField (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : TemperedDistribution ℝ ℂ)+
    (star (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value-1/2) •
     (OriginalKSourceBalance.correctedField (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : TemperedDistribution ℝ ℂ)=
    (OriginalKSourceBalance.regularSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : TemperedDistribution ℝ ℂ) := by
  rw [source,OriginalKCombCofinalTwoDirection.coordinate_value]
  module
 have generated:=OriginalRieszFinitePairing.ColumnIntegral.action_of_euler
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) _ _ native endpoint
 simpa only [OriginalKCombCofinalTwoDirection.coordinate_value] using generated

def regularFiniteIntegral (h : ℝ) : BurnolL2 :=
 OriginalRieszFiniteSource.nativeIntegral (star observation.coordinate-1/2)
   (OriginalKSourceBalance.regularSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)) h+
 OriginalRieszFiniteSource.nativeIntegral (star observation.coordinate-1/2)
   (OriginalKSourceBalance.regularSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)) (-h)

/-- The same corrected-source finite evolution generates its regular integral and its full contact inventory together. -/
theorem actual_regular_finite_integral_inventory (h : ℝ) :
 regularFiniteIntegral observation nontrivial half h=
 originalForcingPair observation nontrivial half h-
 (2:ℂ) • contactFiniteInventory observation nontrivial half h := by
 have plus:=actual_corrected_regular_finite observation nontrivial half h
 have minus:=actual_corrected_regular_finite observation nontrivial half (-h)
 dsimp only at plus minus
 have paired : pairedBurnolMultiplicativeDilation h
   (OriginalKSourceBalance.correctedField (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))=
   pairedMellinTranslationCharacter (star observation.coordinate) h •
   OriginalKSourceBalance.correctedField (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)+
   (1/2:ℂ) • regularFiniteIntegral observation nontrivial half h := by
  unfold pairedBurnolMultiplicativeDilation pairedMellinTranslationCharacter regularFiniteIntegral
  simp only [smul_apply,add_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,reciprocalMellinTranslationCharacter_eq_negativeShift]
  rw [plus,minus]
  module
 unfold OriginalKSourceBalance.correctedField at paired
 rw [map_add,actual_original_K_finite_pair] at paired
 have contact:=actual_contact_finite_inventory observation nontrivial half h
 unfold literalFiniteAction at contact
 simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply] at contact
 have moved : pairedBurnolMultiplicativeDilation h
   (OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))=
   pairedMellinTranslationCharacter (star observation.coordinate) h •
    OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)-
   contactFiniteInventory observation nontrivial half h := by
  rw [←contact]
  abel
 rw [moved] at paired
 have generated:=congrArg (fun material : BurnolL2=>(2:ℂ) • material) paired
 have simplified : originalForcingPair observation nontrivial half h-
   (2:ℂ) • contactFiniteInventory observation nontrivial half h=
   regularFiniteIntegral observation nontrivial half h := by
  calc
   _ = (2:ℂ) • (pairedMellinTranslationCharacter (star observation.coordinate) h •
     (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)+
     (1/2:ℂ) • originalForcingPair observation nontrivial half h+
     (pairedMellinTranslationCharacter (star observation.coordinate) h •
      OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)-
      contactFiniteInventory observation nontrivial half h))-
     (2:ℂ) • (pairedMellinTranslationCharacter (star observation.coordinate) h •
      ((burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)+
       OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))) := by module
   _ = _ := by rw [generated];module
 exact simplified.symm


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceScaledMaximalResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
