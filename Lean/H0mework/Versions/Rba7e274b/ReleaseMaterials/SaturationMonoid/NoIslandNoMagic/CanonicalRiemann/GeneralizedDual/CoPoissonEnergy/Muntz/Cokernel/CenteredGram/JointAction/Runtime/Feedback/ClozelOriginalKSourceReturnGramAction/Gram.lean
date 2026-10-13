import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReturnGramAction.Primitive
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Gram
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
local instance gramAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The actual source return consumes the original resolvent Gram law without dividing by sourceA. -/
theorem actual_original_return_gram :
 star (Return.sourceA observation)*
   inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
     (closedKernelSource observation nontrivial half)+
 Return.sourceA observation*star
   (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
     (closedKernelSource observation nontrivial half))=
 -(observation.coordinate/2+star (observation.coordinate/2)-1/2)*
   inner ℂ (closedKernelSource observation nontrivial half) (closedKernelSource observation nontrivial half) := by
 have source:=burnolDirectRightResolvent_gram (observation.coordinate/2) (observation.coordinate/2)
   (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)
   (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
 rw [←OriginalKCombCofinalRAction.original_R_direct observation nontrivial half] at source
 change inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (Paid.originalKernelRResponse observation nontrivial half)+
   star (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
    (Paid.originalKernelRResponse observation nontrivial half))=
   -(observation.coordinate/2+star (observation.coordinate/2)-1/2)*
   inner ℂ (Paid.originalKernelRResponse observation nontrivial half) (Paid.originalKernelRResponse observation nontrivial half) at source
 have generated:=congrArg (fun price : ℂ=>star (Return.sourceA observation)*Return.sourceA observation*price) source
 rw [←actual_original_K_return]
 simp only [inner_smul_left,inner_smul_right,starRingEnd_apply,star_mul]
 calc
  _ = star (Return.sourceA observation)*Return.sourceA observation*
      (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
       (Paid.originalKernelRResponse observation nontrivial half)+
       star (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
       (Paid.originalKernelRResponse observation nontrivial half))) := by ring
  _ = _ := by rw [generated];ring

/-- Its norm/imaginary price is generated from the literal original primitive, including the zero-A branch. -/
theorem actual_original_primitive_gram :
 -Return.sourceA observation*
   inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
     (Return.primitiveSource observation nontrivial half)+
 Return.sourceA observation*star
   (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
     (Return.primitiveSource observation nontrivial half))=
 -(observation.coordinate/2+star (observation.coordinate/2)-1/2)*
   ((‖closedKernelSource observation nontrivial half‖:ℝ):ℂ)^2 := by
 have generated:=actual_original_return_gram observation nontrivial half
 have self : star (inner ℂ
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))=
   inner ℂ
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2) := by
  simpa only [starRingEnd_apply] using (inner_conj_symm (𝕜:=ℂ)
    (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
    (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
 rw [inner_self_eq_norm_sq_to_K] at generated
 unfold closedKernelSource at generated ⊢
 rw [actual_sourceA_star,inner_add_right,star_add,self] at generated
 linear_combination generated

/-- The primitive imaginary price is computed from the original return Gram, rather than supplied as a zero premise. -/
theorem actual_original_primitive_imaginary_price :
 (2:ℝ)*observation.coordinate.im*
   (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
     (Return.primitiveSource observation nontrivial half)).im=
 (observation.coordinate.re-1/2)*‖closedKernelSource observation nontrivial half‖^2 := by
 have source:=congrArg Complex.re (actual_original_primitive_gram observation nontrivial half)
 unfold _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux.sourceA at source
 have normRead : (((‖closedKernelSource observation nontrivial half‖:ℝ):ℂ)^2).re=
   ‖closedKernelSource observation nontrivial half‖^2 := by norm_cast
 have normImag : (((‖closedKernelSource observation nontrivial half‖:ℝ):ℂ)^2).im=0 := by
   rw [←Complex.ofReal_pow];rfl
 have flip : (inner ℂ (Return.primitiveSource observation nontrivial half)
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)).im=
   -(inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
     (Return.primitiveSource observation nontrivial half)).im := by
  rw [←inner_conj_symm]
  rfl
 norm_num [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
   Complex.star_def,normRead,normImag] at source
 rw [flip] at source
 nlinarith [source]

private theorem actual_two_source_R_gram (left right : BurnolL2) :
 inner ℂ left (OriginalKFullSourceRResponse.Op.R observation nontrivial half right)+
 inner ℂ (OriginalKFullSourceRResponse.Op.R observation nontrivial half left) right=
 -((observation.coordinate+star observation.coordinate-1)/2)*
 inner ℂ (OriginalKFullSourceRResponse.Op.R observation nontrivial half left)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half right) := by
 have leftSource:=OriginalKSourceBalance.source_R_ordinary_strong observation nontrivial half left
 have rightSource:=OriginalKSourceBalance.source_R_ordinary_strong observation nontrivial half right
 have generated:=leftSource.inner ℂ rightSource
 simp only [burnolMultiplicativeDilation_zero] at generated
 have constant : (fun shift : ℝ=>inner ℂ
   (burnolMultiplicativeDilation shift (OriginalKFullSourceRResponse.Op.R observation nontrivial half left))
   (burnolMultiplicativeDilation shift (OriginalKFullSourceRResponse.Op.R observation nontrivial half right)))=
   fun _ : ℝ=>inner ℂ (OriginalKFullSourceRResponse.Op.R observation nontrivial half left)
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half right) := by
  funext shift
  exact (burnolMultiplicativeDilation shift).inner_map_map _ _
 change HasDerivAt (fun shift : ℝ=>inner ℂ
   (burnolMultiplicativeDilation shift (OriginalKFullSourceRResponse.Op.R observation nontrivial half left))
   (burnolMultiplicativeDilation shift (OriginalKFullSourceRResponse.Op.R observation nontrivial half right)))
   (inner ℂ (OriginalKFullSourceRResponse.Op.R observation nontrivial half left)
    (-(observation.coordinate-1/2) • OriginalKFullSourceRResponse.Op.R observation nontrivial half right-(2:ℂ) • right)+
    inner ℂ (-(observation.coordinate-1/2) • OriginalKFullSourceRResponse.Op.R observation nontrivial half left-(2:ℂ) • left)
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half right)) 0 at generated
 rw [constant] at generated
 have source:=generated.unique (hasDerivAt_const (0:ℝ)
   (inner ℂ (OriginalKFullSourceRResponse.Op.R observation nontrivial half left)
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half right)))
 simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
   starRingEnd_apply,star_neg,star_sub,star_div₀,star_ofNat,star_one] at source
 linear_combination -(1/2:ℂ)*source

/-- Two genuine original R source actions couple the returned K primitive to the full C-and-mean source. -/
theorem actual_return_complete_source_coupling (h : ℝ) :
 Return.sourceA observation*
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h))=
 inner ℂ (closedKernelSource observation nontrivial half) (Src.completeSource observation nontrivial half h)+
 ((observation.coordinate+star observation.coordinate-1)/2)*
 inner ℂ (closedKernelSource observation nontrivial half)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h)) := by
 have source:=actual_two_source_R_gram observation nontrivial half
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (Src.completeSource observation nontrivial half h)
 change inner ℂ _ (OriginalKFullSourceRResponse.Op.R observation nontrivial half _)+
   inner ℂ (Paid.originalKernelRResponse observation nontrivial half) _=
   -((observation.coordinate+star observation.coordinate-1)/2)*
   inner ℂ (Paid.originalKernelRResponse observation nontrivial half)
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half _) at source
 have priced:=congrArg (fun price : ℂ=>star (Return.sourceA observation)*price) source
 rw [←actual_original_K_return]
 simp only [inner_smul_left,starRingEnd_apply]
 rw [actual_sourceA_star] at priced ⊢
 linear_combination -priced
private theorem actual_Fourier_R_source_strong :
 HasDerivAt (fun shift : ℝ=>burnolMultiplicativeDilation shift
   (fourierL2 (Paid.originalKernelRResponse observation nontrivial half)))
   ((observation.coordinate-1/2) • fourierL2 (Paid.originalKernelRResponse observation nontrivial half)+
    (2:ℂ) • fourierL2
     (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)) 0 := by
 let k := (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
 have original:=burnolDirectRightResolventOrbit_hasDerivAt (observation.coordinate/2)
   (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) k
 rw [←OriginalKCombCofinalRAction.original_R_direct observation nontrivial half] at original
 have dual:=burnolFourierOrbit_hasDerivAt _ _ original
 have scalar : HasDerivAt (fun shift : ℝ=>-2*shift) (-2:ℝ) 0 := by
  simpa only [id_eq,mul_one] using (hasDerivAt_id (0:ℝ)).const_mul (-2)
 have generated:=HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) dual.hasFDerivAt scalar (by norm_num)
 convert! generated using 1
 · funext shift
   change burnolMultiplicativeDilation shift _=burnolMultiplicativeDilation (-(-2*shift)/2) _
   rw [show -(-2*shift)/2=shift by ring]
   rfl
 · change _=(-2:ℝ) • (-fourierL2 ((observation.coordinate/2-1/4) • Paid.originalKernelRResponse observation nontrivial half+k))
   rw [←algebraMap_smul ℂ (-2:ℝ)]
   simp only [map_neg,map_ofNat,map_add,map_smul]
   module

/-- The true Fourier-return action supplies the second original kernel foot without identifying Fourier with the identity. -/
theorem actual_Fourier_return_complete_source_coupling (h : ℝ) :
 Return.sourceA observation*
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h))=
 Return.sourceA observation*inner ℂ (fourierL2 (closedKernelSource observation nontrivial half))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h))-
 inner ℂ (fourierL2 (closedKernelSource observation nontrivial half)) (Src.completeSource observation nontrivial half h) := by
 have leftSource:=actual_Fourier_R_source_strong observation nontrivial half
 have rightSource:=OriginalKSourceBalance.source_R_ordinary_strong observation nontrivial half
   (Src.completeSource observation nontrivial half h)
 have generated:=leftSource.inner ℂ rightSource
 simp only [burnolMultiplicativeDilation_zero] at generated
 have constant : (fun shift : ℝ=>inner ℂ
   (burnolMultiplicativeDilation shift (fourierL2 (Paid.originalKernelRResponse observation nontrivial half)))
   (burnolMultiplicativeDilation shift (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (Src.completeSource observation nontrivial half h))))=
   fun _ : ℝ=>inner ℂ (fourierL2 (Paid.originalKernelRResponse observation nontrivial half))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h)) := by
  funext shift
  exact (burnolMultiplicativeDilation shift).inner_map_map _ _
 rw [constant] at generated
 have source:=generated.unique (hasDerivAt_const (0:ℝ)
   (inner ℂ (fourierL2 (Paid.originalKernelRResponse observation nontrivial half))
    (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h))))
 simp only [inner_add_left,inner_sub_right,inner_smul_left,inner_smul_right,
   starRingEnd_apply,star_sub,star_div₀,star_ofNat,star_one] at source
 have returned:=congrArg fourierL2 (actual_original_K_return observation nontrivial half)
 rw [map_smul] at returned
 rw [←returned]
 simp only [inner_smul_left,starRingEnd_apply]
 have priced:=congrArg (fun price : ℂ=>star (Return.sourceA observation)*price) source
 rw [actual_sourceA_star] at priced ⊢
 unfold _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux.sourceA at priced ⊢
 linear_combination -(1/2:ℂ)*priced
def returnedOriginalKPrice (h : ℝ) : ℂ :=
 inner ℂ (closedKernelSource observation nontrivial half) (Src.completeSource observation nontrivial half h)+
 ((observation.coordinate+star observation.coordinate-1)/2)*
 inner ℂ (closedKernelSource observation nontrivial half)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h))

def returnedOriginalFKPrice (h : ℝ) : ℂ :=
 Return.sourceA observation*inner ℂ (fourierL2 (closedKernelSource observation nontrivial half))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (Src.completeSource observation nontrivial half h))-
 inner ℂ (fourierL2 (closedKernelSource observation nontrivial half)) (Src.completeSource observation nontrivial half h)

/-- Both original K/FK response prices are generated by the actual source-return actions before the character consumer reads them. -/
theorem actual_return_generated_character_price (h : ℝ) :
 let characterPrice:=2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
   (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 Return.sourceA observation*Paid.originalKernelCross observation nontrivial half h=
 -characterPrice*star (returnedOriginalKPrice observation nontrivial half h+returnedOriginalFKPrice observation nontrivial half h)+
 star characterPrice*(returnedOriginalKPrice observation nontrivial half h-returnedOriginalFKPrice observation nontrivial half h) := by
 dsimp only
 have originalKSource:=actual_return_complete_source_coupling observation nontrivial half h
 have originalFKSource:=actual_Fourier_return_complete_source_coupling observation nontrivial half h
 change Return.sourceA observation*inner ℂ _ _=returnedOriginalKPrice observation nontrivial half h at originalKSource
 change Return.sourceA observation*inner ℂ _ _=returnedOriginalFKPrice observation nontrivial half h at originalFKSource
 have starKSource:=congrArg star originalKSource
 have starFKSource:=congrArg star originalFKSource
 simp only [star_mul,actual_sourceA_star] at starKSource starFKSource
 rw [actual_kernel_cross_response_read,
   OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
   OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
 simp only [star_add]
 linear_combination
  -(2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
    (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*starKSource-
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
    (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*starFKSource+
  star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
    (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*originalKSource-
  star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
    (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*originalFKSource

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceScaledMaximalResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
