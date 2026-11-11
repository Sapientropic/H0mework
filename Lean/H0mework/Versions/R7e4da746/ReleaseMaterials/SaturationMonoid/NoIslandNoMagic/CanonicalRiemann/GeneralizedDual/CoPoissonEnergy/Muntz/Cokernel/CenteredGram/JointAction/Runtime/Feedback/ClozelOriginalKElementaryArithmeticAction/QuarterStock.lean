import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RieszEulerDomain
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.FullUnit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.QuarterStock
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKSourceFiniteUpdate.OriginalBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalPaPhysicalGreen
open scoped Topology InnerProductSpace
open private centered_even fourier_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
open private dual_boundary from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.Source
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local notation "D"=>burnolMultiplicativeDilation
local notation "J"=>burnolTateReciprocalL2
local notation "S"=>burnolMeanZeroTruncatedFourier

theorem position_input (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    E (compactPosition c h:Hq)=finiteBoundaryAction c h (E (sourceSB c:Hq))+
      (1/2:ℂ) • FullUnit.fullSource c h 1 := by
  have outward:=outward_full_source_inventory h (sourceSB c)
  rw [compactPosition,sourceFirstSB_actual c h nn,sourceSecondB_actual c h nn]
  simp only [Submodule.coe_sub,Submodule.coe_add,Submodule.coe_smul,map_sub,map_smul,map_add]
  rw [inward_extension h nn]
  change _=finiteBoundaryAction c h (E (sourceSB c:Hq))+(1/2:ℂ) • fullWindowLoss h (sourceSB c)
  unfold finiteBoundaryAction
  linear_combination (norm:=module) (1/2:ℂ) • outward

theorem fourier_input (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    E (compactFourier c h:Hq)=-(finiteBoundaryAction c h (E (sourceB c:Hq)))-
      (1/2:ℂ) • FullUnit.fullSource c h 0 := by
  have outward:=outward_full_source_inventory h (sourceB c)
  rw [compactFourier,sourceSecondSB_actual c h nn,sourceFirstB_actual c h nn]
  simp only [Submodule.coe_add,Submodule.coe_smul,map_add,map_smul]
  rw [inward_extension h nn]
  change _=-(finiteBoundaryAction c h (E (sourceB c:Hq)))-(1/2:ℂ) • fullWindowLoss h (sourceB c)
  unfold finiteBoundaryAction
  linear_combination (norm:=module) -(1/2:ℂ) • outward

private theorem dilation_even (h:ℝ) (value:M) (even:reflectRestricted q (value:Hq)=value) :
    reflectRestricted q (meanZeroDilation h value:Hq)=meanZeroDilation h value := by
  change reflectRestricted q (Constructor.zeroMean (Rq (D h (E (value:Hq)))):Hq)=_
  apply centered_even
  change reflectRestricted q (restrictToInterval q (D h (E (value:Hq))))=_
  rw [←restrictToInterval_reflectL2,reflectL2_burnolMultiplicativeDilation]
  have original : reflectL2 (E (value:Hq))=E (value:Hq) := by
    change reflectL2 (burnolRadiusZeroExtension q (value:Hq))=_
    rw [burnolRadiusZeroExtension_reflect,even]
    rfl
  rw [original]
  rfl

private theorem b_even (c:BurnolCompletedMellinCoordinate) : reflectRestricted q (sourceB c:Hq)=sourceB c :=
  burnolRieszSingleFourierSource_reflection_fixed c
private theorem r_even (c:BurnolCompletedMellinCoordinate) : reflectRestricted q (sourceSB c:Hq)=sourceSB c :=
  fourier_even (sourceB c) (b_even c)
private theorem position_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    reflectRestricted q (compactPosition c h:Hq)=compactPosition c h := by
  rw [compactPosition,sourceFirstSB_actual c h nn,sourceSecondB_actual c h nn]
  simp only [Submodule.coe_sub,Submodule.coe_smul,Submodule.coe_add,map_sub,map_smul,map_add]
  rw [r_even,dilation_even h _ (r_even c),dilation_even (-h) _ (r_even c)]
private theorem fourier_even_input (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    reflectRestricted q (compactFourier c h:Hq)=compactFourier c h := by
  rw [compactFourier,sourceSecondSB_actual c h nn,sourceFirstB_actual c h nn]
  simp only [Submodule.coe_add,Submodule.coe_smul,map_add,map_smul]
  rw [b_even,dilation_even (-h) _ (b_even c),dilation_even h _ (b_even c)]

/-- Each value is generated by the original B/SB finite response and its complete reverse sequence. -/
def positionValue (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (ReturnCounting.value c)+(1/2:ℂ) • FullUnit.fullReverse c h 1
def fourierValue (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
  -(finiteBoundaryAction c h (CountingDual.value c))-(1/2:ℂ) • FullUnit.fullReverse c h 0

private theorem boundary_continuous (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    Continuous (finiteBoundaryAction c h) := by
  unfold finiteBoundaryAction
  fun_prop

theorem position_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (compactPosition c h:Hq))) atTop (𝓝 (positionValue c h)) := by
  have direct:=((boundary_continuous c h).tendsto _).comp (ReturnCounting.finite_tendsto c)
  have actual:=direct.add ((FullUnit.full_reverse_tendsto c h nn 1).const_smul (1/2:ℂ))
  apply actual.congr'
  filter_upwards with N
  symm
  rw [position_input c h nn,CountingDual.dual_eq_adjoint,map_add,map_smul,
    ←CountingDual.dual_eq_adjoint,←CountingDual.dual_eq_adjoint,dual_boundary]
  rfl

theorem fourier_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (compactFourier c h:Hq))) atTop (𝓝 (fourierValue c h)) := by
  have direct:=((boundary_continuous c h).tendsto _).comp (CountingDual.original_dual_tendsto c)
  have actual:=direct.neg.sub ((FullUnit.full_reverse_tendsto c h nn 0).const_smul (1/2:ℂ))
  apply actual.congr'
  filter_upwards with N
  symm
  rw [fourier_input c h nn,CountingDual.dual_eq_adjoint,map_sub,map_neg,map_smul,
    ←CountingDual.dual_eq_adjoint,←CountingDual.dual_eq_adjoint,dual_boundary]
  rfl

private theorem support_limit (state:M) (even:reflectRestricted q (state:Hq)=state) (value:BurnolL2)
    (source:Tendsto (fun N:ℕ=>DualSource.source N (E (state:Hq))) atTop (𝓝 value)) :
    originalPhysicalCutoff q value=value := by
  have cut:=(burnolQuarterZeroExtension.continuous.tendsto _).comp
    ((burnolQuarterRestriction.continuous.tendsto _).comp source)
  have read:=cut.congr' (show _ =ᶠ[atTop] (fun N:ℕ=>DualSource.source N (E (state:Hq))) from by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N positive
    exact (CenteredCountingDualSupport.source_support state even N positive).symm)
  exact tendsto_nhds_unique read source

theorem position_support (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    originalPhysicalCutoff q (positionValue c h)=positionValue c h :=
  support_limit _ (position_even c h nn) _ (position_tendsto c h nn)
theorem fourier_support (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    originalPhysicalCutoff q (fourierValue c h)=fourierValue c h :=
  support_limit _ (fourier_even_input c h nn) _ (fourier_tendsto c h nn)

/-- Quarter versus reciprocal-quarter orthogonality is paid by actual support, not Pa membership. -/
theorem quarter_tate_zero (left right:BurnolL2)
    (leftSource:originalPhysicalCutoff q left=left) (rightSource:originalPhysicalCutoff q right=right) :
    inner ℂ left (J right)=0 := by
  have lread:=originalPhysicalCutoff_coeFn q left
  have rread:=originalPhysicalCutoff_coeFn q right
  rw [leftSource] at lread
  rw [rightSource] at rread
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp right)
    ((Lp.memLp right).ae_eq rread) rread
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [lread,burnolTateReciprocalL2_coeFn right,pulled,volume.ae_ne (0:ℝ)] with x leftAt tateAt pulledAt nonzero
  change inner ℂ (left x) (J right x)=0
  by_cases inside:x∈symmetricInterval q
  · have outside : x⁻¹∉symmetricInterval q := by
      intro member
      have first:=abs_le.mpr inside
      have second:=abs_le.mpr member
      rw [abs_inv] at second
      have product : |x| *|x|⁻¹=1 := mul_inv_cancel₀ (abs_ne_zero.mpr nonzero)
      nlinarith [abs_nonneg x,inv_nonneg.mpr (abs_nonneg x)]
    rw [tateAt,pulledAt]
    unfold burnolTateReciprocalRaw
    rw [indicator_of_notMem outside,mul_zero,inner_zero_right]
  · rw [leftAt,indicator_of_notMem inside,inner_zero_left]

def leftVelocity (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) : BurnolL2 :=
  (star c.value-1/2) • PositionCounting.value c zero-Kernel.A c • ResponseCounting.value true+
    Kernel.beta c • ResponseCounting.value false
def rightVelocity (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (star c.value-1/2) • CountingDual.value c+Kernel.A c • ResponseCounting.value false-
    Kernel.beta c • ResponseCounting.value true

private theorem left_support (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    originalPhysicalCutoff q (leftVelocity c zero)=leftVelocity c zero := by
  unfold originalPhysicalCutoff leftVelocity
  simp only [map_add,map_sub,map_smul]
  change (star c.value-1/2) • originalPhysicalCutoff q (PositionCounting.value c zero)-
    Kernel.A c • originalPhysicalCutoff q (ResponseCounting.value true)+
      Kernel.beta c • originalPhysicalCutoff q (ResponseCounting.value false)=_
  rw [PositionCounting.value_support,ResponseCounting.value_support,ResponseCounting.value_support]
private theorem right_support (c:BurnolCompletedMellinCoordinate) :
    originalPhysicalCutoff q (rightVelocity c)=rightVelocity c := by
  have original : originalPhysicalCutoff q (CountingDual.value c)=CountingDual.value c :=
    (DualLanding.original_support c).symm
  unfold originalPhysicalCutoff rightVelocity
  simp only [map_add,map_sub,map_smul]
  change (star c.value-1/2) • originalPhysicalCutoff q (CountingDual.value c)+
    Kernel.A c • originalPhysicalCutoff q (ResponseCounting.value false)-
      Kernel.beta c • originalPhysicalCutoff q (ResponseCounting.value true)=_
  rw [original,ResponseCounting.value_support,ResponseCounting.value_support]

/-- These are the two actual non-unit cross feet of the whole counted velocity/stock pairing. -/
theorem source_cross_feet (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) (nn:0≤h) :
    inner ℂ (leftVelocity c zero) (J (fourierValue c h))=0 ∧
      inner ℂ (J (rightVelocity c)) (positionValue c h)=0 := by
  constructor
  · exact quarter_tate_zero _ _ (left_support c zero) (fourier_support c h nn)
  · exact inner_eq_zero_symm.mp (quarter_tate_zero _ _ (position_support c h nn) (right_support c))

end OriginalKElementaryArithmeticAction.QuarterStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
