import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterShell

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalPaPhysicalGreen
open OriginalKCompactAdjointRSource
open scoped InnerProductSpace Topology
open private tateTail_read from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.DyadicSource
local notation "q" => (1/4 : ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Cut" => originalPhysicalCutoff q
local notation "R" => burnolDirectRightResolventCLM
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The exact compact power covector is the even Tate image of the original tail kernel. -/
theorem actual_power_tail_covector (coordinate : BurnolCompletedMellinCoordinate) :
    E (SingularCounting.powerL2 coordinate)=
      -T (burnolRadiusNormalizedUnitTail (barC coordinate) 4 (by norm_num)) := by
  have inside : ∀ᵐ x ∂volume, x∈symmetricInterval q →
      SingularCounting.powerL2 coordinate x=SingularCounting.powerRaw coordinate x :=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (SingularCounting.power_coeFn coordinate)
  have tail := tateTail_read (barC coordinate) 4 (by norm_num)
  norm_num only [show (4 : ℝ)⁻¹=q by norm_num] at tail
  apply Lp.ext
  filter_upwards [burnolQuarterZeroExtension_coe (SingularCounting.powerL2 coordinate),inside,
    Lp.coeFn_neg (T (burnolRadiusNormalizedUnitTail (barC coordinate) 4 (by norm_num))),tail,
    volume.ae_ne q,volume.ae_ne (-q)] with x source raw negative tate notPlus notMinus
  rw [source,negative,Pi.neg_apply,tate]
  have notBoundary : |x|≠q := by
    intro same
    rcases eq_or_eq_neg_of_abs_eq same with atPlus|atMinus
    · exact notPlus atPlus
    · exact notMinus (by linarith)
  by_cases member : |x|<q
  · rw [indicator_of_mem (show x∈symmetricInterval q from abs_le.mp member.le),if_pos member,
      raw (abs_le.mp member.le)]
    simp only [SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,neg_neg]
  · have outside : x∉symmetricInterval q := fun inside =>
      member (lt_of_le_of_ne (abs_le.mpr inside) notBoundary)
    rw [indicator_of_notMem outside,if_neg member,neg_zero]

/-- Two positive-axis Mellin tails equal the full even quarter power moment, with no missing factor two. -/
theorem actual_compact_tail_coefficient (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    actualCompactTailCoefficient coordinate value=
      inner ℂ (SingularCounting.powerL2 coordinate) (Rq value) := by
  have tateEven : reflectL2 (T value)=T value := by rw [←burnolTateReciprocal_reflect,even]
  let kernel := burnolRadiusMellinTailKernelL2 4 (by norm_num) coordinate.value coordinate.rightHalf
  have reflected : inner ℂ (reflectL2 kernel) (T value)=inner ℂ kernel (T value) := by
    calc
      _=inner ℂ (reflectL2 kernel) (reflectL2 (T value)) := by rw [tateEven]
      _=_ := reflectL2.inner_map_map _ _
  let tateIsometry : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
    { toLinearMap := burnolTateReciprocalL2.toLinearMap, norm_map' := burnolTateReciprocalValue_norm }
  have paired := tateIsometry.inner_map_map
    (burnolRadiusNormalizedUnitTail (barC coordinate) 4 (by norm_num)) (T value)
  change inner ℂ (T (burnolRadiusNormalizedUnitTail (barC coordinate) 4 (by norm_num))) (T (T value))=_ at paired
  rw [burnolTateReciprocalL2_involutive] at paired
  have power := congrArg (fun covector : BurnolL2 => inner ℂ covector value) (actual_power_tail_covector coordinate)
  rw [inner_neg_left,paired] at power
  dsimp only [burnolRadiusNormalizedUnitTail,OriginalPrimitiveRankBalance.conjugateCoordinate] at power
  simp only [star_star] at power
  change inner ℂ (E (SingularCounting.powerL2 coordinate)) value=
    -inner ℂ (-(kernel+reflectL2 kernel)) (T value) at power
  rw [inner_neg_left,inner_add_left,reflected] at power
  have extension := ContinuousLinearMap.adjoint_inner_right Rq value (SingularCounting.powerL2 coordinate)
  change inner ℂ value (E (SingularCounting.powerL2 coordinate))=
    inner ℂ (Rq value) (SingularCounting.powerL2 coordinate) at extension
  have restricted := congrArg (starRingEnd ℂ) extension
  simp only [inner_conj_symm] at restricted
  rw [restricted] at power
  change 2*inner ℂ kernel (T value)=_
  linear_combination -power

/-- This whole source law is the generic compact R-to-Mellin bridge used before taking parameter jets. -/
theorem actual_compact_R_mellin_source (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (supported : Cut value=value) (even : reflectL2 value=value) :
    R coordinate value=Cut (R coordinate value)+
      inner ℂ (SingularCounting.powerL2 coordinate) (Rq value) •
        burnolRadiusNormalizedUnitTail coordinate q (by norm_num) := by
  have source := actual_compact_R_rank_source coordinate value supported even
  change R coordinate value=Cut (R coordinate value)+actualCompactTailCoefficient coordinate value • _ at source
  rw [actual_compact_tail_coefficient coordinate value even] at source
  exact source

theorem actual_compact_R_support (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (supported : Cut value=value) (even : reflectL2 value=value)
    (moment : inner ℂ (SingularCounting.powerL2 coordinate) (Rq value)=0) :
    Cut (R coordinate value)=R coordinate value := by
  have source := actual_compact_R_mellin_source coordinate value supported even
  rw [moment,zero_smul,add_zero] at source
  exact source.symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
