import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteForcingQSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFiniteSource OriginalRieszFiniteColumns OriginalRieszFinitePairing OriginalPaPhysicalGreen
local instance stockInsideDebtAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
namespace Full
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint.FullStock
 (meanDebt actual_inside_mean_debt)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint
 (upperSeedFactor upperSourceWave upperSourceField upperSourceCorrection actual_upper_common_seed)
end Full
namespace Prior
export OriginalKFiniteForcingQSource (actualFinitePaStock actualFiniteOutsideStock actual_finite_source_character_price)
export OriginalKSourceScaledMaximalResponse (originalForcingPair)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualInsidePosition (h : ℝ) : BurnolL2 :=
 positionColumn (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h+
 originalPhysicalCutoff (1/4:ℝ) (positionColumn (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (-h))

def actualInsideFourier (h : ℝ) : BurnolL2 :=
 fourierColumn (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (-h)+
 originalPhysicalCutoff (1/4:ℝ) (fourierColumn (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)

def actualInsideDebt (h : ℝ) : BurnolL2 :=
 actualInsidePosition observation nontrivial half h+fourierL2 (actualInsideFourier observation nontrivial half h)+
 (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)

private theorem physical_Fourier_read (material : BurnolL2) :
 P (fourierL2 material)=Fphysical (P material) := by
 apply Subtype.ext
 exact (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius material).symm

/-- Both actual inside restrictions and their own two seed means generate the physical zero read; the inventory is retained. -/
theorem actual_inside_debt_physical_zero (h : ℝ) (nonnegative : 0≤h) :
 P (actualInsideDebt observation nontrivial half h)=0 := by
 have source:=Full.actual_inside_mean_debt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative
 unfold actualInsideDebt actualInsidePosition actualInsideFourier
 rw [map_add,map_add,physical_Fourier_read]
 have debt:P (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)=
   Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h := by
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 rw [debt,source,neg_add_cancel]

/-- Full raw source columns and the actual upper seed create the inside inventory before any projection or R action. -/
theorem actual_full_inside_source (h : ℝ) (nonnegative : 0≤h) :
 OriginalKFullSourceRResponse.completeSource observation nontrivial half h+
 Full.upperSeedFactor h • Prior.originalForcingPair observation nontrivial half h=
 Full.upperSourceWave (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h+
 Full.upperSeedFactor h • actualInsideDebt observation nontrivial half h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have columns : Prior.originalForcingPair observation nontrivial half h=
   (OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h+
     fourierL2 (OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h))+
   actualInsidePosition observation nontrivial half h+
   fourierL2 (actualInsideFourier observation nontrivial half h) := by
  unfold OriginalKSourceScaledMaximalResponse.originalForcingPair actualInsidePosition actualInsideFourier
  rw [OriginalRieszFinitePairing.CoPoisson.positionSeed_eq_exterior coordinate h nonnegative,
    OriginalRieszFinitePairing.CoPoisson.fourierSeed_eq_exterior coordinate h nonnegative,
    forcingIntegral_columns,forcingIntegral_columns,map_sub,map_add]
  module
 unfold OriginalKFullSourceRResponse.completeSource Full.upperSourceCorrection actualInsideDebt
 rw [Full.actual_upper_common_seed coordinate h nonnegative,columns]
 module

/-- The original outside stock is this literal inside-column/two-mean inventory, not an erased source value. -/
theorem actual_original_outside_inside_stock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Prior.actualFiniteOutsideStock observation nontrivial half h=
 Full.upperSeedFactor h • actualInsideDebt observation nontrivial half h := by
 have source:=actual_full_inside_source observation nontrivial half h nonnegative
 have acted:=congrArg OriginalKPairedResponseGramAction.originalOutside source
 unfold OriginalKFiniteForcingQSource.actualFiniteOutsideStock
 simp only [map_add,map_smul] at acted
 have wave : OriginalKPairedResponseGramAction.originalOutside (Full.upperSourceWave
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)=0 := by
  have admitted : Full.upperSourceWave (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h ∈
   evenBurnolClosedFace burnolUnscaledCommonGapRadius :=
   (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded).property
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.le_orthogonal_orthogonal admitted
 have stock : OriginalKPairedResponseGramAction.originalOutside (actualInsideDebt observation nontrivial half h)=
   actualInsideDebt observation nontrivial half h := by
  have split:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal
    (actualInsideDebt observation nontrivial half h)
  change (P (actualInsideDebt observation nontrivial half h) : BurnolL2)+
    OriginalKPairedResponseGramAction.originalOutside (actualInsideDebt observation nontrivial half h)=_ at split
  rw [actual_inside_debt_physical_zero observation nontrivial half h nonnegative,Submodule.coe_zero,zero_add] at split
  exact split
 rw [wave,stock,zero_add] at acted
 exact acted

/-- The same source Pa inventory realizes the actual generated wave; both mean debts remain in the outside inventory. -/
theorem actual_original_Pa_wave_stock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Prior.actualFinitePaStock observation nontrivial half h=
 OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded := by
 have source:=actual_full_inside_source observation nontrivial half h nonnegative
 have acted:=congrArg OriginalKCombCofinalPaAction.E source
 simp only [map_add,map_smul] at acted
 have debt : OriginalKCombCofinalPaAction.E (actualInsideDebt observation nontrivial half h)=0 := by
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (P (actualInsideDebt observation nontrivial half h))=0
  rw [actual_inside_debt_physical_zero observation nontrivial half h nonnegative,map_zero]
 have wave : OriginalKCombCofinalPaAction.E (Full.upperSourceWave
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)=
   OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded := by
  let value:=OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded
  have physical : P (value : BurnolL2)=value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (P (value : BurnolL2))=value
  rw [physical]
  exact Submodule.starProjection_eq_self_iff.mpr
   (OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa _ h nonnegative bounded)
 unfold OriginalKFiniteForcingQSource.actualFinitePaStock
 rw [debt,wave,smul_zero,add_zero] at acted
 exact acted

/-- Original R acts on this explicit full inside/two-mean inventory, without preserving its zero P-read for free. -/
theorem actual_original_R_inside_stock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (Prior.actualFiniteOutsideStock observation nontrivial half h)=
 Full.upperSeedFactor h • OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (actualInsideDebt observation nontrivial half h) := by
 rw [actual_original_outside_inside_stock observation nontrivial half h nonnegative bounded,map_smul]

/-- The actual source R effect retains both original inside columns and the two source means. -/
theorem actual_original_R_inside_effect (h : ℝ) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualInsideDebt observation nontrivial half h)=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualInsidePosition observation nontrivial half h)+
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (fourierL2 (actualInsideFourier observation nontrivial half h))+
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
  (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2) := by
 unfold actualInsideDebt
 rw [map_add,map_add]

def insideDebtREffect (h : ℝ) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualInsidePosition observation nontrivial half h)+
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (fourierL2 (actualInsideFourier observation nontrivial half h))+
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
