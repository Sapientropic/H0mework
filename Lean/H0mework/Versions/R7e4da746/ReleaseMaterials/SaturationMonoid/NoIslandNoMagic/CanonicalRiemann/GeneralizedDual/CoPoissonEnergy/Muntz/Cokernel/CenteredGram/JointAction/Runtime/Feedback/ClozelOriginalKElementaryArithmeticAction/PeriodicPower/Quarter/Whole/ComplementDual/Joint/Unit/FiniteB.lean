import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OutsideContact

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FiniteB
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace Topology
open private unit_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRColumnForwardSource
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "Rq" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The original B-power field is read through both actual finite quarter faces. -/
def finiteBRead (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  inner ℂ (Rq value) (hPowerBColumn c : Hq)+
    inner ℂ (Rq (fourierL2.symm value)) (hPowerBSecond c : Hq)

theorem actual_finite_B_read (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ value (hPowerPhysicalCorrection c) = finiteBRead c value := by
  rw [unit_source,inner_add_right]
  have extension (state : Hq) (input : BurnolL2) :
      inner ℂ input (E state) = inner ℂ (Rq input) state :=
    ContinuousLinearMap.adjoint_inner_right Rq _ _
  have fourier := fourierL2.inner_map_map (fourierL2.symm value) (E (hPowerBSecond c : Hq))
  rw [fourierL2.apply_symm_apply] at fourier
  rw [fourier,extension,extension]
  rfl

/-- The finite time orientation and conjugate first-slot weight are retained for arbitrary signed h. -/
def nativeFiniteBPrice (c : BurnolCompletedMellinCoordinate) (lambda : ℂ)
    (material : BurnolL2) (h : ℝ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..h,
    star (Complex.exp (-lambda*((h : ℂ)-(t : ℂ))))*finiteBRead c (D t material)

theorem actual_native_finite_B_price (c : BurnolCompletedMellinCoordinate) (lambda : ℂ)
    (material : BurnolL2) (h : ℝ) :
    inner ℂ (nativeIntegral lambda material h) (hPowerPhysicalCorrection c) =
      nativeFiniteBPrice c lambda material h := by
  have commute := (innerSL ℂ (hPowerPhysicalCorrection c)).intervalIntegral_comp_comm
    (nativeIntegrand_integrable lambda material h)
  change (∫ t : ℝ in (0 : ℝ)..h,
    inner ℂ (hPowerPhysicalCorrection c) (nativeIntegrand lambda material h t)) =
      inner ℂ (hPowerPhysicalCorrection c) (nativeIntegral lambda material h) at commute
  calc
    _ = star (inner ℂ (hPowerPhysicalCorrection c) (nativeIntegral lambda material h)) :=
      (inner_conj_symm _ _).symm
    _ = star (∫ t : ℝ in (0 : ℝ)..h,
        inner ℂ (hPowerPhysicalCorrection c) (nativeIntegrand lambda material h t)) := by rw [commute]
    _ = ∫ t : ℝ in (0 : ℝ)..h,
        star (inner ℂ (hPowerPhysicalCorrection c) (nativeIntegrand lambda material h t)) :=
      intervalIntegral.intervalIntegral_conj.symm
    _ = _ := by
      unfold nativeFiniteBPrice
      apply intervalIntegral.integral_congr
      intro t _
      change (starRingEnd ℂ) (inner ℂ (hPowerPhysicalCorrection c) (nativeIntegrand lambda material h t)) = _
      rw [inner_conj_symm]
      simp only [nativeIntegrand,inner_smul_left,starRingEnd_apply,actual_finite_B_read]

/-- The edge's actual gap/tail primitive keeps its complete coefficient (-star d * gapMean q d)^-1. -/
def edgeEndpointPrice (c d : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  finiteBRead c (D h (edgePrimitive d))-
    star (fullMellinTranslationCharacter (star d.value) h)*finiteBRead c (edgePrimitive d)

/-- The Fourier edge retains its distinct native 2-lambda source and both primitive endpoints. -/
def fourierEdgePrice (c d : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  star (2*(star d.value-1/2))*nativeFiniteBPrice c (star d.value-1/2) (fourierPrimitive d) h-
    (finiteBRead c (D h (fourierPrimitive d))-
      star (fullMellinTranslationCharacter (star d.value) h)*finiteBRead c (fourierPrimitive d))

def profileFiniteBPrice (c d : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  nativeFiniteBPrice c (star d.value-1/2) (F Response.wholeU-Response.wholeV) h-
    edgeEndpointPrice c d h

def fourierProfileFiniteBPrice (c d : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  nativeFiniteBPrice c (star d.value-1/2) (Response.wholeU-F Response.wholeV) h-
    fourierEdgePrice c d h

/-- L2 source/domain and actual Bochner commutation pay the complete Psi and edge program, without a Schwartz cotest premise. -/
theorem actual_profile_finite_B_price (c d : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (profileIntegral d h) (hPowerPhysicalCorrection c) = profileFiniteBPrice c d h := by
  rw [profileIntegral,inner_sub_left,actual_native_finite_B_price,edgeIntegral,
    inner_sub_left,inner_smul_left,actual_finite_B_read,actual_finite_B_read]
  rfl

theorem actual_fourier_profile_finite_B_price (c d : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (fourierProfileIntegral d h) (hPowerPhysicalCorrection c) = fourierProfileFiniteBPrice c d h := by
  rw [fourierProfileIntegral,inner_sub_left,actual_native_finite_B_price,fourierEdgeIntegral,
    inner_sub_left,inner_smul_left,actual_native_finite_B_price,inner_sub_left,
    inner_smul_left,actual_finite_B_read,actual_finite_B_read]
  rfl

/-- The full two-source price contains both signed finite integrals and the independent Fourier edge correction. -/
def pairedFiniteBPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (1/2 : ℂ)*(
    star (OriginalWholeDebtRPowerWaveDilationSource.coupling1 c)*
      (profileFiniteBPrice c (barC c) (-h)+profileFiniteBPrice c (barC c) h)+
    star (OriginalWholeDebtRPowerWaveDilationSource.coupling0 c)*
      (fourierProfileFiniteBPrice c (barC c) (-h)+fourierProfileFiniteBPrice c (barC c) h))

/-- This first original contact is generated directly from Psi/B/edge, with no reverse use of the powerWave action equation. -/
theorem actual_paired_source_finite_B_price (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (OriginalWholeDebtRPowerWaveDilationSource.pairedSource c h) (physicalOutsideColumn (barC c)) =
      pairedFiniteBPrice c h := by
  have twice : barC (barC c) = c := by
    cases c
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  have column : physicalOutsideColumn (barC c) = F (hPowerPhysicalCorrection c) := by
    unfold physicalOutsideColumn
    rw [twice]
    apply fourierL2.injective
    rw [fourierL2.apply_symm_apply,fourierL2_fourierL2]
    exact (burnolAmbientEvenPart_even _).symm
  rw [column,OriginalWholeDebtRPowerWaveDilationSource.pairedSource,
    OriginalWholeDebtRPowerWaveDilationSource.singleSource,OriginalWholeDebtRPowerWaveDilationSource.singleSource]
  simp only [inner_smul_left,inner_add_left,fourierL2.inner_map_map,
    actual_profile_finite_B_price,actual_fourier_profile_finite_B_price,starRingEnd_apply]
  unfold pairedFiniteBPrice
  norm_num only [star_div₀,star_one,star_ofNat]
  ring

open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OutsideContact
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

/-- The original reflected Unit consumer receives the complete finite Psi/B/edge price directly. -/
theorem actual_reflected_unit_paired_finite_contact (h : ℝ) :
    inner ℂ (OriginalKCombPhysicalAction.physicalRemainder
      (OriginalWholeDebtRPowerWaveDilationSource.pairedSource (barC c) h)) (unitOnePower c m) =
        -2*e*pairedFiniteBPrice (barC c) h := by
  rw [actual_unit_one_outside_price observation nontrivial half]
  have source := actual_paired_source_finite_B_price (barC c) h
  have twice : barC (barC c) = c := by
    cases c
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  rw [twice] at source
  rw [source]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FiniteB
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
