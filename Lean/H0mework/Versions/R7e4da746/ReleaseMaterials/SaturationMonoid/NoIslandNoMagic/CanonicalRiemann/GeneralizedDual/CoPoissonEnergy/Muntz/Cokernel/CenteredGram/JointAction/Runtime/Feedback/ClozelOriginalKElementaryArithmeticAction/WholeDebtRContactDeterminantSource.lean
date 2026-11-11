import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRContactDeterminantSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalKPairedBEulerJunctionSource OriginalCommonInverseForcing.SourceJoint
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace Topology

open private face physicalRaw physical_raw_read physical_raw_gap rRaw r_read r_continuous
  kernelRaw kernelInner kernelOuter kernel_read kernel_inner kernel_outer kernel_outer_continuous kernel_jump
  vRaw vInner vOuter v_read v_piece v_piece_continuous v_jump continuous_junction
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource
open private source_norm_strict observation_kernel_source_nonzero
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource

local notation "q" => (1/4 : ℝ)
local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector
local notation "gK" => OriginalKSourceResolventReconstruction.generatedK
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "h0" => junctionShift
local notation "u" => upperSeedFactor h0
local notation "PD" => OriginalWholeDebtRProjectionSource.projectedDebt
local notation "Z" => OriginalWholeDebtRProjectionSource.kernelRBoundary
local notation "alpha" => OriginalWholeDebtRProjectionSource.powerReturnPrice
local notation "beta" => OriginalWholeDebtRProjectionSource.fourierDebtPrice
local notation "Delta" => OriginalWholeDebtRContactSource.contactDeterminant
local notation "a" => OriginalWholeDebtRContactSource.boundaryTrace
local notation "t" => OriginalWholeDebtRContactSource.returnTrace

def sourceMass (c : BurnolCompletedMellinCoordinate) : ℂ := ((‖(K c : BurnolL2)‖^2 : ℝ) : ℂ)
def sourceDamping (c : BurnolCompletedMellinCoordinate) : ℂ :=
  (OriginalKCrossParameterRAdjointSource.CayleyEnergySource.sourceDamping c : ℂ)
private def coefficient (c : BurnolCompletedMellinCoordinate) : ℂ :=
  OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.sourceForwardRatio c/sourceDamping c
private def flip (i : Fin 2) : Fin 2 := ![(1 : Fin 2),0] i

private def fourierKernel (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  evenFaceFourierEquiv q (K c)

private theorem flipped_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (face i (F (K c : BurnolL2)) : ℝ → ℂ)=ᵐ[volume] kernelRaw c (flip i) := by
  fin_cases i
  · exact kernel_read c 1
  · change (F (F (K c : BurnolL2)) : ℝ → ℂ)=ᵐ[volume] kernelRaw c 0
    rw [fourierL2_fourierL2,mem_evenL2ClosedFace_iff.mp (K c).property.2]
    exact kernel_read c 0

private def sourceRaw (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  coefficient c*kernelRaw (barC c) i x-(sourceDamping c)⁻¹*kernelRaw c (flip i) x-
    (2*sourceMass c)*vRaw c i x
private def sourceInner (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  coefficient c*kernelInner (barC c) i-(sourceDamping c)⁻¹*kernelInner c (flip i)-
    (2*sourceMass c)*vInner c i x
private def sourceOuter (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  coefficient c*kernelOuter (barC c) i x-(sourceDamping c)⁻¹*kernelOuter c (flip i) x-
    (2*sourceMass c)*vOuter c i x

private theorem source_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    rRaw c (fourierKernel c) (physicalRaw (fourierKernel c)) i=ᵐ[volume] sourceRaw c i := by
  have whole : R c (F (K c : BurnolL2))=
      coefficient c • (K (barC c) : BurnolL2)-(sourceDamping c)⁻¹ • F (K c : BurnolL2)-
        (2*sourceMass c) • physicalOutsideColumn c := by
    unfold coefficient sourceDamping sourceMass
    change burnolDirectRightResolvent (c.value/2) (F (K c : BurnolL2))=_
    simpa only [OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.sourceFKAction,
      OriginalKSourceResolventReconstruction.generatedK_eq_original] using
        OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.original_R_FK_generated c
  have actual : face i (R c (F (K c : BurnolL2)))=
      coefficient c • face i (K (barC c) : BurnolL2)-
        (sourceDamping c)⁻¹ • face i (F (K c : BurnolL2))-
        (2*sourceMass c) • face i (physicalOutsideColumn c) := by
    fin_cases i
    · exact whole
    · change F (R c (F (K c : BurnolL2)))=
        coefficient c • F (K (barC c) : BurnolL2)-
          (sourceDamping c)⁻¹ • F (F (K c : BurnolL2))-
          (2*sourceMass c) • F (physicalOutsideColumn c)
      simpa only [map_sub,map_smul] using congrArg F whole
  have combined :
      ((coefficient c • face i (K (barC c) : BurnolL2)-
        (sourceDamping c)⁻¹ • face i (F (K c : BurnolL2))-
        (2*sourceMass c) • face i (physicalOutsideColumn c) : BurnolL2) : ℝ → ℂ)
        =ᵐ[volume] sourceRaw c i := by
    filter_upwards [Lp.coeFn_sub
      (coefficient c • face i (K (barC c) : BurnolL2)-
        (sourceDamping c)⁻¹ • face i (F (K c : BurnolL2)))
      ((2*sourceMass c) • face i (physicalOutsideColumn c)),
      Lp.coeFn_sub (coefficient c • face i (K (barC c) : BurnolL2))
        ((sourceDamping c)⁻¹ • face i (F (K c : BurnolL2))),
      Lp.coeFn_smul (coefficient c) (face i (K (barC c) : BurnolL2)),
      Lp.coeFn_smul ((sourceDamping c)⁻¹) (face i (F (K c : BurnolL2))),
      Lp.coeFn_smul (2*sourceMass c) (face i (physicalOutsideColumn c)),
      kernel_read (barC c) i,flipped_read c i,v_read c i]
      with x sub0 sub1 scale0 scale1 scale2 raw0 raw1 raw2
    simp only [sub0,sub1,Pi.sub_apply,scale0,scale1,scale2,Pi.smul_apply,smul_eq_mul,
      raw0,raw1,raw2,sourceRaw]
  exact (r_read c _ _ (physical_raw_read _) (physical_raw_gap _) i).symm.trans
    (by change (face i (R c (F (K c : BurnolL2))) : ℝ → ℂ)=ᵐ[volume] _;rw [actual];exact combined)

/-- The complete original R(FK) action generates both contact equations before any determinant read. -/
theorem actual_FK_contact_source (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    ![coefficient c*Kernel.A (barC c)+(sourceDamping c)⁻¹*Kernel.beta c+2*sourceMass c*t c 0,
      coefficient c*Kernel.beta (barC c)+(sourceDamping c)⁻¹*Kernel.A c+2*sourceMass c*t c 1] i=0 := by
  have limits := continuous_junction
    (inside := sourceInner c i) (outside := sourceOuter c i) (source_read c i)
    (fun x positive small => by
      unfold sourceRaw sourceInner
      rw [kernel_inner (barC c) i positive small.le,kernel_inner c (flip i) positive small.le,
        (v_piece c i positive).1 small.le])
    (fun x large => by
      unfold sourceRaw sourceOuter
      rw [kernel_outer (barC c) i large,kernel_outer c (flip i) large,
        (v_piece c i (by linarith)).2 large])
    (fun x positive => (r_continuous c _ _ (physical_raw_read _) (physical_raw_gap _) i positive.ne').continuousWithinAt)
    (fun x positive => by
      unfold sourceInner
      exact ((continuousAt_const.sub continuousAt_const).sub
        (continuousAt_const.mul (v_piece_continuous c i positive).1)).continuousWithinAt)
    (fun x positive => by
      unfold sourceOuter
      exact (((continuousAt_const.mul (kernel_outer_continuous (barC c) i positive)).sub
        (continuousAt_const.mul (kernel_outer_continuous c (flip i) positive))).sub
        (continuousAt_const.mul (v_piece_continuous c i positive).2)).continuousWithinAt)
  have barJump := kernel_jump (barC c) i
  have currentJump := kernel_jump c (flip i)
  have returned := v_jump c i
  unfold sourceOuter sourceInner at limits
  fin_cases i
  · change coefficient c*Kernel.A (barC c)+(sourceDamping c)⁻¹*Kernel.beta c+2*sourceMass c*t c 0=0
    simp only [Fin.mk_zero] at barJump returned
    simp only [Fin.mk_zero,flip,Matrix.cons_val_zero] at limits
    change kernelOuter (barC c) 0 q-kernelInner (barC c) 0= -Kernel.A (barC c) at barJump
    change kernelOuter c 1 q-kernelInner c 1=Kernel.beta c at currentJump
    change vOuter c 0 q-vInner c 0 q=t c 0 at returned
    linear_combination -limits+coefficient c*barJump-(sourceDamping c)⁻¹*currentJump-(2*sourceMass c)*returned
  · change coefficient c*Kernel.beta (barC c)+(sourceDamping c)⁻¹*Kernel.A c+2*sourceMass c*t c 1=0
    simp only [Fin.mk_one] at barJump returned
    simp only [Fin.mk_one,flip,Matrix.cons_val_one,Matrix.cons_val_zero] at limits
    change kernelOuter (barC c) 1 q-kernelInner (barC c) 1=Kernel.beta (barC c) at barJump
    change kernelOuter c 0 q-kernelInner c 0= -Kernel.A c at currentJump
    change vOuter c 1 q-vInner c 1 q= -t c 1 at returned
    linear_combination limits-coefficient c*barJump+(sourceDamping c)⁻¹*currentJump+(2*sourceMass c)*returned

/-- N remains the full original Riesz mass in this source-generated determinant law. -/
theorem actual_determinant_source (c : BurnolCompletedMellinCoordinate) :
    2*sourceDamping c*sourceMass c*Delta c=
      Kernel.beta (barC c)*Kernel.beta c-Kernel.A (barC c)*Kernel.A c := by
  have first := actual_FK_contact_source c 0
  have second := actual_FK_contact_source c 1
  change coefficient c*Kernel.A (barC c)+(sourceDamping c)⁻¹*Kernel.beta c+2*sourceMass c*t c 0=0 at first
  change coefficient c*Kernel.beta (barC c)+(sourceDamping c)⁻¹*Kernel.A c+2*sourceMass c*t c 1=0 at second
  have combined : 2*sourceMass c*Delta c=(sourceDamping c)⁻¹*
      (Kernel.beta (barC c)*Kernel.beta c-Kernel.A (barC c)*Kernel.A c) := by
    unfold OriginalWholeDebtRContactSource.contactDeterminant
    linear_combination Kernel.A (barC c)*second-Kernel.beta (barC c)*first
  have damping : sourceDamping c≠0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (OriginalKCrossParameterRAdjointSource.CayleyEnergySource.sourceDamping_pos c))
  have weighted := congrArg (fun z : ℂ => sourceDamping c*z) combined
  rw [←mul_assoc (sourceDamping c) ((sourceDamping c)⁻¹),mul_inv_cancel₀ damping,one_mul] at weighted
  linear_combination weighted

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

private theorem original_source_product_ne_zero :
    Kernel.beta (barC c)*Kernel.beta c-Kernel.A (barC c)*Kernel.A c≠0 := by
  have rightNative := observation_kernel_source_nonzero observation nontrivial half.down
  let reflected := conjugateZeroObservation observation
  have reflectedHalf : 1/2<reflected.coordinate.re := by
    change 1/2<(starRingEnd ℂ observation.coordinate).re
    simpa only [Complex.conj_re] using half.down
  have leftNative := observation_kernel_source_nonzero reflected
    (observation.conjugate_nontrivial nontrivial) reflectedHalf
  have same : burnolDivisionZeroCompletedMellinCoordinate reflected reflectedHalf=barC c := by rfl
  rw [same] at leftNative
  have left := source_norm_strict (barC c) leftNative
  have right := source_norm_strict c rightNative
  intro zero
  have normRead := congrArg norm (sub_eq_zero.mp zero)
  rw [norm_mul,norm_mul] at normRead
  have first := mul_le_mul_of_nonneg_left right.le (norm_nonneg (Kernel.beta (barC c)))
  have second := mul_lt_mul_of_pos_right left (lt_of_le_of_lt (norm_nonneg (Kernel.beta c)) right)
  exact (ne_of_lt (first.trans_lt second)) normRead

/-- The determinant is nonzero because the actual RFK source law has a nonzero native K source. -/
theorem original_contactDeterminant_ne_zero : Delta c≠0 := by
  intro zero
  have source := actual_determinant_source c
  rw [zero,mul_zero] at source
  exact original_source_product_ne_zero observation nontrivial half source.symm

/-- Both original return prices are generated from the two actual RK endpoint traces. -/
theorem original_return_prices :
    alpha c=(t c 1*a c 0+t c 0*a c 1)/(2*Delta c) ∧
      beta c=(u*(Kernel.beta (barC c)*a c 0+Kernel.A (barC c)*a c 1))/Delta c := by
  have det := original_contactDeterminant_ne_zero observation nontrivial half
  have first := (OriginalWholeDebtRContactSource.original_return_settlement observation nontrivial half).1
  have second := (OriginalWholeDebtRContactSource.original_return_settlement observation nontrivial half).2
  have unit : u≠0 := by
    unfold upperSeedFactor
    exact div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))) (by norm_num)
  constructor
  · apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ)≠0) det)).mpr
    apply mul_left_cancel₀ unit
    linear_combination first
  · exact (eq_div_iff det).mpr second

def unweightedField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  R coordinate (upperSourceWave coordinate h0)-(2*u) • (P (Z coordinate) : BurnolL2)-
    ((2*u*(t coordinate 1*a coordinate 0+t coordinate 0*a coordinate 1))/Delta coordinate) • gK (barC coordinate)-
    ((2*u*(Kernel.beta (barC coordinate)*a coordinate 0+Kernel.A (barC coordinate)*a coordinate 1))/Delta coordinate) •
      physicalOutsideColumn coordinate

/-- The same complete R(PD) action now has no determinant weight or uncomputed alpha/beta coefficient. -/
theorem original_unweighted_source_action :
    R c (PD c : BurnolL2)=unweightedField c := by
  have det := original_contactDeterminant_ne_zero observation nontrivial half
  have prices := original_return_prices observation nontrivial half
  have first : 4*u*alpha c=(2*u*(t c 1*a c 0+t c 0*a c 1))/Delta c := by
    rw [prices.1]
    field_simp [det];ring
  have second : 2*beta c=(2*u*(Kernel.beta (barC c)*a c 0+Kernel.A (barC c)*a c 1))/Delta c := by
    rw [prices.2]
    ring
  rw [OriginalWholeDebtRProjectionSource.original_source_action observation nontrivial half]
  unfold OriginalWholeDebtRProjectionSource.sourceField unweightedField
  rw [first,second]

end OriginalWholeDebtRContactDeterminantSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
