import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.CompletedSourceRConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedWeakWardSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace Topology BigOperators
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "J" => burnolMeanZeroBlockInverse
local notation "Tq" => burnolTruncatedFourier
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "μq" => volume.restrict (symmetricInterval q)
local instance : CompleteSpace M :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def epsilon (odd:Bool) : ℂ := if odd then -1 else 1
def radius (h:ℝ) : ℝ := q*Real.exp (-h)
def nativeField (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : BurnolL2 :=
 if odd then (1/2:ℂ) • (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector c:BurnolL2)-
   burnolMultiplicativeDilation (-h) (burnolCompletedMellinRieszVector c:BurnolL2))
 else pairedBurnolMultiplicativeDilation h (burnolCompletedMellinRieszVector c:BurnolL2)
def face (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : BurnolL2 :=
 ![nativeField c odd h,fourierL2 (nativeField c odd h)] i
def drive (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : M :=
 ![burnolAmbientMeanZeroPosition (nativeField c odd h),
   burnolAmbientMeanZeroFourier (nativeField c odd h)] i
def first (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : M :=
 burnolAmbientMeanZeroFirstCorrection (nativeField c odd h)
def second (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : M :=
 burnolAmbientMeanZeroSecondCorrection (nativeField c odd h)
def solution (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : M :=
 ![first c odd h,second c odd h] i
def sourceMean (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : ℂ :=
 burnolQuarterMeanCoefficient (Rq (burnolAmbientEvenPart (face c odd h i)))
def returnedMean (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : ℂ :=
 burnolQuarterMeanCoefficient (Tq (solution c odd h i:Hq))
def nativeB0 (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : ℂ :=
 sourceMean c odd h 0-returnedMean c odd h 1

def outwardWeight (odd:Bool) (i:Fin 2) (h:ℝ) : ℂ :=
 ((Real.exp (h/2):ℂ)/2)*(if i=0 then 1 else epsilon odd)
def inwardWeight (odd:Bool) (i:Fin 2) (h:ℝ) : ℂ :=
 ((Real.exp (-h/2):ℂ)/2)*(if i=0 then epsilon odd else 1)
def driverInner (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : ℂ :=
 (outwardWeight odd i h+inwardWeight odd i h)*originalGap c i-sourceMean c odd h i
def driverOuter (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) (x:ℝ) : ℂ :=
 outwardWeight odd i h*originalOuter c i (Real.exp h*x)+
 inwardWeight odd i h*originalGap c i-sourceMean c odd h i
def driverRaw (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) (x:ℝ) : ℂ :=
 if |x|≤radius h then driverInner c odd h i else driverOuter c odd h i |x|
def jump (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : ℂ :=
 outwardWeight odd i h*originalCharge c i
def outerTrace (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : ℂ :=
 driverOuter c odd h i q-burnolMeanZeroFourierRaw (solution c odd h (![1,0] i)) q

def correction (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : BurnolL2 :=
 Eq (first c odd h:Hq)+fourierL2 (Eq (second c odd h:Hq))
def lambda (c:BurnolCompletedMellinCoordinate) : ℂ := star c.value-1/2
def sigma (c:BurnolCompletedMellinCoordinate) : ℂ := OriginalWholeDebtRAdjointContactSource.sigma c c
def effect (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : BurnolL2 :=
 sigma c • (burnolDirectRightResolventCLM c).adjoint (correction c odd h)+
  (2:ℂ) • correction c odd h

def power (c:BurnolCompletedMellinCoordinate) : M :=
 SingularCounting.centeredPower (OriginalPrimitiveRankBalance.conjugateCoordinate c)
def powerResponse (c:BurnolCompletedMellinCoordinate) : M := J (power c)
def test (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
 ![-S (powerResponse c),powerResponse c] i
def centeredPowerRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
 SingularCounting.powerRaw (OriginalPrimitiveRankBalance.conjugateCoordinate c) x-
 burnolQuarterMeanCoefficient (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c))
def testRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
 ![-burnolMeanZeroFourierRaw (powerResponse c) x,
   centeredPowerRaw c x+burnolMeanZeroFourierRaw (S (powerResponse c)) x] i

/-- The forcing contains the original Psi/Muntz drive and the actual moving jump. -/
def annulusForcing (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : ℂ :=
 2*outwardWeight odd i h*
  ∫x:ℝ in (radius h)..q,star (testRaw c i x)*
   (PsiDrive.psiCoupling c i (Real.exp h*x)-
    (1/2+PsiDrive.sourceRate c i)*originalGap c i)
def jumpForcing (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) (i:Fin 2) : ℂ :=
 2*(radius h:ℂ)*star (testRaw c i (radius h))*jump c odd h i
def forcing (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : ℂ :=
 (-2*sigma c)*∑i:Fin 2,(annulusForcing c odd h i+jumpForcing c odd h i)

def eigenBill (c:BurnolCompletedMellinCoordinate) (anti:Bool) (h:ℝ) : ℂ :=
 ∫s:ℝ in 0..h,Complex.exp ((if anti then lambda c else -lambda c)*(h-s:ℂ))*
  (forcing c false s+(if anti then -1 else 1)*forcing c true s)
/-- The output is generated from the two literal source bills, with no Gamma input. -/
def sourceCharge (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : ℂ :=
 (1/2:ℂ)*(eigenBill c false h+epsilon odd*eigenBill c true h)
def nativeCharge (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) : ℂ :=
 (-2*sigma c)*inner ℂ (power c) (second c odd h)

theorem fixed_B_first (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) :
 first c odd h+S (second c odd h)=drive c odd h 0 :=
 burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs (nativeField c odd h))
theorem fixed_B_second (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) :
 S (first c odd h)+second c odd h=drive c odd h 1 :=
 burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs (nativeField c odd h))

theorem original_even_field (c:BurnolCompletedMellinCoordinate) :
 nativeField c false junctionShift=sourceAction c := rfl
theorem original_even_columns (c:BurnolCompletedMellinCoordinate) :
 first c false junctionShift=sourceFirst c ∧ second c false junctionShift=sourceSecond c := ⟨rfl,rfl⟩
theorem original_even_charge (c:BurnolCompletedMellinCoordinate) :
 nativeCharge c false junctionShift=OriginalWholeDebtRJointMobiusContactPsiPriceSource.nativeGamma c c := by
 rw [OriginalWholeDebtRJointMobiusContactPsiPriceSource.actual_native_gamma]
 rfl

theorem source_charge_initial (c:BurnolCompletedMellinCoordinate) (odd:Bool) : sourceCharge c odd 0=0 := by
 simp only [sourceCharge,eigenBill,intervalIntegral.integral_same,mul_zero,add_zero]

/-- The complete source calculation retains the means and B(0), not a renormalized charge. -/
def calculation (c:BurnolCompletedMellinCoordinate) (odd:Bool) (h:ℝ) :=
 (nativeField c odd h,fun i=>face c odd h i,fun i=>drive c odd h i,
  fun i=>solution c odd h i,fun i=>sourceMean c odd h i,fun i=>returnedMean c odd h i,
  nativeB0 c odd h,radius h,fun i=>jump c odd h i,fun i=>outerTrace c odd h i,
  powerResponse c,fun i=>test c i,fun i=>testRaw c i,
  fun i=>annulusForcing c odd h i,fun i=>jumpForcing c odd h i,
  forcing c odd h,sourceCharge c odd h,effect c odd h)

end OriginalKPairedWeakWardSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
