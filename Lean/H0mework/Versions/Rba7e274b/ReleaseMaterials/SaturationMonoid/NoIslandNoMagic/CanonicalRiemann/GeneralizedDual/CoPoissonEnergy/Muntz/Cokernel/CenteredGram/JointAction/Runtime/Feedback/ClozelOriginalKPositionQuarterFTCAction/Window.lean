import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapMeanRSourceAction.Price
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPositionQuarterFTCAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- Own compact support controls the whole moving mean window before the R equation is differentiated. -/
theorem actual_compact_positive_mean (material : BurnolL2)
 (supported : originalPhysicalCutoff q material=material) (shift : ℝ) (positive : 0≤shift) :
 Paid.actualMean (burnolMultiplicativeDilation shift material)=
 (Real.exp (-shift/2):ℂ)*Paid.actualMean material := by
 have read:=originalPhysicalCutoff_coeFn q material
 rw [supported] at read
 have inventory : (∫ x : ℝ in symmetricInterval (q*Real.exp shift),material x)=
   (∫ x : ℝ in symmetricInterval q,material x) := by
  rw [←integral_indicator (measurableSet_symmetricInterval (q*Real.exp shift)),
    ←integral_indicator (measurableSet_symmetricInterval q)]
  apply integral_congr_ae
  filter_upwards [read] with x source
  by_cases inside : x∈symmetricInterval q
  · have moved : x∈symmetricInterval (q*Real.exp shift) := by
     have scale:=Real.one_le_exp_iff.mpr positive
     have bound:=abs_le.mpr inside
     apply abs_le.mp
     nlinarith
    rw [Set.indicator_of_mem inside,Set.indicator_of_mem moved]
  · have zero : material x=0 := by rw [source,Set.indicator_of_notMem inside]
    rw [Set.indicator_of_notMem inside]
    by_cases moved : x∈symmetricInterval (q*Real.exp shift)
    · rw [Set.indicator_of_mem moved,zero]
    · rw [Set.indicator_of_notMem moved]
 rw [Paid.actual_mean_dilation_source,inventory,Paid.actual_mean_source_integral]
 ring

/-- The actual source R orbit generates its derivative mean through the existing read map. -/
theorem actual_R_mean_orbit (z : ℂ) (right : 1/4<z.re) (material : BurnolL2) :
 HasDerivAt (fun time : ℝ=>Paid.actualMean
   (burnolMultiplicativeDilation (-time/2) (burnolDirectRightResolvent z material)))
 ((z-1/4)*Paid.actualMean (burnolDirectRightResolvent z material)+Paid.actualMean material) 0 := by
 have source:=burnolDirectRightResolventOrbit_hasDerivAt z right material
 have generated:=(Paid.actualMean.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 source
 change HasDerivAt (fun time : ℝ=>Paid.actualMean
   (burnolMultiplicativeDilation (-time/2) (burnolDirectRightResolvent z material)))
   (Paid.actualMean ((z-1/4) • burnolDirectRightResolvent z material+material)) 0 at generated
 simpa only [map_add,map_smul,smul_eq_mul] using generated


private theorem actual_mean_reflection (material : BurnolL2) :
 Paid.actualMean (reflectL2 material)=Paid.actualMean material := by
 change (‖intervalConstant q‖^2:ℂ)⁻¹*inner ℂ (intervalConstant q)
   (restrictToInterval q (reflectL2 material))=_
 rw [restrictToInterval_reflectL2]
 have paired:=(reflectRestricted q).inner_map_map (intervalConstant q) (burnolRadiusRestriction q material)
 rw [reflectRestricted_intervalConstant] at paired
 exact congrArg (fun price : ℂ=>(‖intervalConstant q‖^2:ℂ)⁻¹*price) paired

/-- The literal normalized source tail generates the moving quarter integral with both reflected halves. -/
theorem actual_tail_quarter_mean (coordinate : BurnolCompletedMellinCoordinate)
 (radius : ℝ) (positive : 0<radius) (bounded : radius≤q) :
 Paid.actualMean (burnolRadiusNormalizedUnitTail coordinate radius positive)=
 -(4:ℂ)*(∫ x : ℝ in radius..q,(x:ℂ)^(-coordinate.value)) := by
 let tail:=burnolRadiusMellinTailKernelL2 radius positive (star coordinate.value)
   (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf)
 have integralRead : (∫ x : ℝ in symmetricInterval q,tail x)=
   (∫ x : ℝ in Ioc radius q,(x:ℂ)^(-coordinate.value)) := by
  rw [←integral_indicator (measurableSet_symmetricInterval q),←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (burnolRadiusMellinTailKernelRaw_memLp positive (star coordinate.value)
    (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf))] with x raw
  change tail x=burnolRadiusMellinTailKernelRaw radius (star coordinate.value) x at raw
  unfold burnolRadiusMellinTailKernelRaw at raw
  simp only [star_star,mem_Ioi] at raw
  by_cases after : radius<x
  · have lower : -q≤x := by linarith
    by_cases upper : x≤q
    · rw [Set.indicator_of_mem (show x∈symmetricInterval q from ⟨lower,upper⟩),
      Set.indicator_of_mem (show x∈Ioc radius q from ⟨after,upper⟩),raw,if_pos after]
    · rw [Set.indicator_of_notMem (show x∉symmetricInterval q from fun member=>upper member.2),
      Set.indicator_of_notMem (show x∉Ioc radius q from fun member=>upper member.2)]
  · rw [Set.indicator_of_notMem (show x∉Ioc radius q from fun member=>after member.1)]
    by_cases inside : x∈symmetricInterval q
    · rw [Set.indicator_of_mem inside,raw,if_neg after]
    · rw [Set.indicator_of_notMem inside]
 have mean : Paid.actualMean tail=(2:ℂ)*(∫ x : ℝ in radius..q,(x:ℂ)^(-coordinate.value)) := by
  rw [Paid.actual_mean_source_integral,integralRead,←intervalIntegral.integral_of_le bounded]
 change Paid.actualMean (-(tail+reflectL2 tail))=_
 rw [map_neg,map_add,actual_mean_reflection,mean]
 ring



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPositionQuarterFTCAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
