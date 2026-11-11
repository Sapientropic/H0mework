import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointQuarter

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward InverseAction
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionHead OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PowerHead
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointQuarter OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open scoped Topology InnerProductSpace
open private seed_quarter_balance original_correction_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open private original_fourier_split from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "Cq" => intervalConstant q
local notation "box" => burnolRadiusTruncatedFourierRaw q Cq

def dualFourierRaw (c:BurnolCompletedMellinCoordinate):ℝ→ℂ:=
  Constructor.fourierRaw (dualRaw c.value c.belowOne)

def dualReciprocalMean (c:BurnolCompletedMellinCoordinate):ℂ:=
  ∫x:ℝ in Ioi (0:ℝ),(x:ℂ)⁻¹*dualFourierRaw c x

/-- A single genuine L2 source removes the homogeneous power before any action is requested. -/
def jointSource (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  quarterWave c-ForcingWhole.whole c+fourierL2 (E (correction c.value c.belowOne:Hq))

def jointSourceRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  quarterRaw c x-ForcingWhole.raw c x+Constructor.fourierRaw (correction c.value c.belowOne:Hq) x

def jointReciprocalMean (c:BurnolCompletedMellinCoordinate):ℂ:=
  ∫x:ℝ in Ioi (0:ℝ),(x:ℂ)⁻¹*jointSourceRaw c x

theorem actual_joint_source_raw (c:BurnolCompletedMellinCoordinate):
    (jointSource c:ℝ→ℂ)=ᵐ[volume]jointSourceRaw c:=by
  filter_upwards [Lp.coeFn_add (quarterWave c-ForcingWhole.whole c)
      (fourierL2 (E (correction c.value c.belowOne:Hq))),
    Lp.coeFn_sub (quarterWave c) (ForcingWhole.whole c),actual_quarter_raw c,ForcingWhole.whole_read c,
    burnolRadiusFourierL2_zeroExtension_ae_eq_raw (correction c.value c.belowOne:Hq)]
    with x added difference source forcing returned
  change (fourierL2 (E (correction c.value c.belowOne:Hq)):BurnolL2) x=
    Constructor.fourierRaw (correction c.value c.belowOne:Hq) x at returned
  change (quarterWave c-ForcingWhole.whole c+fourierL2 (E (correction c.value c.belowOne:Hq)):BurnolL2) x=_
  rw [added,Pi.add_apply,difference,Pi.sub_apply,source,forcing,returned]
  rfl

/-- The full homogeneous subtraction is an actual global source identity, including both outer tails. -/
theorem actual_joint_homogeneous_raw (c:BurnolCompletedMellinCoordinate):
    (jointSource c:ℝ→ℂ)=ᵐ[volume]fun x:ℝ=>
      quarterRaw c x+dualFourierRaw c x-
        ForcingPrimitive.leadingCoefficient c*((|x|:ℝ):ℂ)^(star c.value-1):=by
  filter_upwards [actual_joint_source_raw c,volume.ae_ne (0:ℝ)] with x source nonzero
  rw [source,jointSourceRaw,dualFourierRaw]
  have split:=congrFun (original_fourier_split c) x
  simp only [Pi.add_apply] at split
  have seed:=actual_seed_fourier_balance_abs c x nonzero
  linear_combination -seed-split

def nativeQuarterRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  aliasRaw c x-resolvedRaw c 0-jumpCoefficient c*box x+
    ForcingPrimitive.leadingCoefficient c*Constructor.fourierRaw (S (logBFirst c 0):Hq) x-
      Constructor.fourierRaw (S (burnolRieszSingleFourierSource c):Hq) x

theorem actual_joint_native_quarter_raw (c:BurnolCompletedMellinCoordinate):
    (Rq (jointSource c):ℝ→ℂ)=ᵐ[μq]nativeQuarterRaw c:=by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (jointSource c),
    ae_restrict_of_ae (actual_joint_source_raw c),ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x restricted raw inside
  change Rq (jointSource c) x=jointSource c x at restricted
  rw [restricted,raw,jointSourceRaw,quarterRaw,indicator_of_mem inside,periodicRaw,resolvedFourierRaw,
    original_correction_fourier]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,nativeQuarterRaw]
  ring

private def dualFourierQuarter (c:BurnolCompletedMellinCoordinate):Hq:=
  Constructor.compact (dualFourierRaw c) (actual_fourier_continuous _ (actual_dual_integrable c.value c.belowOne))

private theorem dual_quarter_split (c:BurnolCompletedMellinCoordinate):
    dualFourierQuarter c=Constructor.compact (Constructor.fourierRaw (seedRaw c.value))
        (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne))+
      Rq (fourierL2 (E (correction c.value c.belowOne:Hq))):=by
  apply Lp.ext
  filter_upwards [Constructor.compact_read (dualFourierRaw c)
      (actual_fourier_continuous _ (actual_dual_integrable c.value c.belowOne)),
    Lp.coeFn_add (Constructor.compact (Constructor.fourierRaw (seedRaw c.value))
      (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne)))
        (Rq (fourierL2 (E (correction c.value c.belowOne:Hq)))),
    Constructor.compact_read (Constructor.fourierRaw (seedRaw c.value))
      (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne)),
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (fourierL2 (E (correction c.value c.belowOne:Hq))),
    ae_restrict_of_ae (burnolRadiusFourierL2_zeroExtension_ae_eq_raw (correction c.value c.belowOne:Hq))]
    with x input added seed restricted returned
  change dualFourierQuarter c x=dualFourierRaw c x at input
  change Rq (fourierL2 (E (correction c.value c.belowOne:Hq))) x=
    (fourierL2 (E (correction c.value c.belowOne:Hq)):BurnolL2) x at restricted
  change (fourierL2 (E (correction c.value c.belowOne:Hq)):BurnolL2) x=
    Constructor.fourierRaw (correction c.value c.belowOne:Hq) x at returned
  rw [input,added,Pi.add_apply,seed,restricted,returned]
  exact congrFun (original_fourier_split c) x

theorem actual_joint_quarter_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Rq (jointSource c)=dualFourierQuarter c+regularQuarter c zero:=by
  have source:=congrArg Rq (actual_source_split c zero)
  rw [map_add,map_smul,powerSource,burnolQuarterRestriction_zeroExtension] at source
  change Rq (quarterWave c)=ForcingPrimitive.leadingCoefficient c • SingularCounting.powerL2 c+
    regularQuarter c zero at source
  rw [jointSource,map_add,map_sub,source,←seed_quarter_balance,dual_quarter_split]
  module

private theorem term_window (c:BurnolCompletedMellinCoordinate) (n:ℕ):
    quarterTerm c n=countingWindow ((n+1:ℕ):ℝ) (dualFourierQuarter c):=by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  have large:(1:ℝ)≤(n+1:ℕ):=by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  apply Lp.ext
  have value:=countingWindow_raw ((n+1:ℕ):ℝ) positive (dualFourierQuarter c) (dualFourierRaw c)
    (Constructor.compact_read _ _)
  filter_upwards [actual_quarter_term_raw c n,value,ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x actual counted inside
  have moved:x/((n+1:ℕ):ℝ)∈symmetricInterval q:=by
    apply abs_le.mp
    rw [abs_div,abs_of_pos positive]
    exact (div_le_self (abs_nonneg x) large).trans (abs_le.mpr inside)
  rw [actual,counted,countingRaw,indicator_of_mem moved]
  simp only [Complex.ofReal_natCast,dualFourierRaw]

theorem actual_joint_native_term (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (n:ℕ):
    jointTerm c zero n=countingWindow ((n+1:ℕ):ℝ) (Rq (jointSource c)):=by
  have additive (a b:Hq):countingWindow ((n+1:ℕ):ℝ) (a+b)=
      countingWindow ((n+1:ℕ):ℝ) a+countingWindow ((n+1:ℕ):ℝ) b:=by
    simp only [countingWindow,map_add,smul_add]
  rw [actual_joint_quarter_source,additive,←term_window]
  rfl

/-- The original integer programme of the same full L2 source generates the actual joint quarter. -/
theorem actual_joint_native_programme (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    HasSum (fun n:ℕ=>countingWindow ((n+1:ℕ):ℝ) (Rq (jointSource c)))
      (Rq (wholeValue c zero h positive+fourierL2 (fullFloorValue c zero))+
        (wholeReciprocalFinitePart c-2*deriv (poleFreeSource c) 1/(1-star c.value)) • Cq):=by
  have source:=actual_joint_quarter_hasSum c zero h positive
  exact source.congr_fun (fun n=>(actual_joint_native_term c zero n).symm)

theorem actual_joint_native_inverse (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    HasSum (fun n:ℕ=>BI (Constructor.zeroMean (countingWindow ((n+1:ℕ):ℝ) (Rq (jointSource c)))))
      (BI (Constructor.zeroMean (Rq (wholeValue c zero h positive+fourierL2 (fullFloorValue c zero))))):=by
  have source:=actual_joint_position_inverse_hasSum c zero h positive
  exact source.congr_fun (fun n=>by rw [actual_joint_native_term])

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
