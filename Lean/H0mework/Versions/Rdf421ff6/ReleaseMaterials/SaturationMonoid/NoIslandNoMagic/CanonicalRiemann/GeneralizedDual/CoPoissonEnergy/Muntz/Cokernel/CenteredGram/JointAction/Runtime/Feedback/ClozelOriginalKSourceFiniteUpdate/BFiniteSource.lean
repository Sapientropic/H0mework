import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
import H0mework.Versions.V2.Arithmetic.RieszColumns.Window

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate.OriginalBFiniteAction

open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private def windowDilation (h : ℝ) : Hq →L[ℂ] Hq :=
  burnolQuarterRestriction.comp
    ((burnolMultiplicativeDilation h).toContinuousLinearEquiv.toContinuousLinearMap.comp
      burnolQuarterZeroExtension)

/-- Both signs use the same full dilation, cutoff and original mean projection. -/
def meanZeroDilation (h : ℝ) : M →L[ℂ] M :=
  Constructor.zeroMean.comp ((windowDilation h).comp
    (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

private theorem window_pair (h : ℝ) (left right : Hq) :
    inner ℂ (windowDilation h left) right =
      inner ℂ left (windowDilation (-h) right) := by
  have first : inner ℂ (windowDilation h left) right = inner ℂ
      (burnolMultiplicativeDilation h (burnolQuarterZeroExtension left))
        (burnolQuarterZeroExtension right) :=
    (ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _).symm
  have second := (burnolMultiplicativeDilation h).inner_map_eq_flip
    (burnolQuarterZeroExtension left) (burnolQuarterZeroExtension right)
  rw [← burnolMultiplicativeDilation_neg_eq_symm] at second
  rw [first, second]
  exact ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _

private theorem inward_support (h : ℝ) (nonnegative : 0 ≤ h) (value : Hq) :
    burnolQuarterZeroExtension (windowDilation h value) =
      burnolMultiplicativeDilation h (burnolQuarterZeroExtension value) := by
  apply OriginalRieszFiniteColumns.intervalDilation_cutoff_self
  exact mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ q)
    (Real.exp_le_one_iff.mpr (by linarith))

private theorem outward_constant (h : ℝ) (nonnegative : 0 ≤ h) :
    windowDilation (-h) (intervalConstant q) =
      (Real.exp (-h / 2) : ℂ) • intervalConstant q := by
  have gap : burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) =
      (1 : ℂ) • intervalConstant q := by
    rw [burnolQuarterRestriction_zeroExtension, one_smul]
  change burnolQuarterRestriction
    (burnolMultiplicativeDilation (-h) (burnolQuarterZeroExtension (intervalConstant q))) = _
  simpa only [mul_one] using
    OriginalKForcingGapAction.quarter_dilation_constant
      (burnolQuarterZeroExtension (intervalConstant q)) 1 gap (-h) (by linarith)

private theorem inward_mean (h : ℝ) (nonnegative : 0 ≤ h) (value : M) :
    burnolQuarterMeanCoefficient (windowDilation h (value : Hq)) = 0 := by
  have zero : inner ℂ (intervalConstant q) (value : Hq) = 0 :=
    (Submodule.mem_orthogonal _ _).mp value.property _ (Submodule.mem_span_singleton_self _)
  have paired := window_pair (-h) (intervalConstant q) (value : Hq)
  rw [neg_neg, outward_constant h nonnegative, inner_smul_left, zero, mul_zero] at paired
  unfold burnolQuarterMeanCoefficient
  rw [← paired, zero_div]

theorem inward_read (h : ℝ) (nonnegative : 0 ≤ h) (value : M) :
    (meanZeroDilation h value : Hq) = windowDilation h (value : Hq) := by
  change (Constructor.zeroMean (windowDilation h (value : Hq)) : Hq) = _
  rw [Constructor.zeroMean_read, inward_mean h nonnegative, zero_smul, sub_zero]

theorem inward_extension (h : ℝ) (nonnegative : 0 ≤ h) (value : M) :
    burnolQuarterZeroExtension (meanZeroDilation h value : Hq) =
      burnolMultiplicativeDilation h (burnolQuarterZeroExtension (value : Hq)) := by
  rw [inward_read h nonnegative]
  exact inward_support h nonnegative _

private theorem outward_local (h : ℝ) (nonnegative : 0 ≤ h) (value : BurnolL2) :
    burnolQuarterRestriction (burnolMultiplicativeDilation (-h) value) =
      windowDilation (-h) (burnolQuarterRestriction value) := by
  apply ext_inner_left ℂ
  intro test
  calc
    inner ℂ test (burnolQuarterRestriction (burnolMultiplicativeDilation (-h) value)) =
        inner ℂ (burnolQuarterZeroExtension test) (burnolMultiplicativeDilation (-h) value) :=
      (ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _).symm
    _ = inner ℂ (burnolMultiplicativeDilation h (burnolQuarterZeroExtension test)) value := by
      simpa only [← burnolMultiplicativeDilation_neg_eq_symm] using
        ((burnolMultiplicativeDilation h).inner_map_eq_flip
          (burnolQuarterZeroExtension test) value).symm
    _ = inner ℂ (burnolQuarterZeroExtension (windowDilation h test)) value := by
      rw [inward_support h nonnegative]
    _ = inner ℂ (windowDilation h test) (burnolQuarterRestriction value) :=
      ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _
    _ = inner ℂ test (windowDilation (-h) (burnolQuarterRestriction value)) :=
      window_pair h _ _

/-- The reverse mean is removed only after the actual outward constant read. -/
theorem finite_fourier_intertwining (h : ℝ) (nonnegative : 0 ≤ h) (value : M) :
    S (meanZeroDilation h value) = meanZeroDilation (-h) (S value) := by
  have first : S (meanZeroDilation h value) =
      Constructor.zeroMean (windowDilation (-h) (burnolTruncatedFourier (value : Hq))) := by
    change Constructor.zeroMean (burnolQuarterRestriction (fourierL2
      (burnolQuarterZeroExtension (meanZeroDilation h value : Hq)))) = _
    rw [inward_extension h nonnegative, fourierL2_burnolMultiplicativeDilation,
      outward_local h nonnegative]
    rfl
  rw [first]
  change Constructor.zeroMean (windowDilation (-h) (burnolTruncatedFourier (value : Hq))) =
    Constructor.zeroMean (windowDilation (-h) (S value : Hq))
  have centered : (S value : Hq) = burnolTruncatedFourier (value : Hq) -
      burnolQuarterMeanCoefficient (burnolTruncatedFourier (value : Hq)) • intervalConstant q :=
    Constructor.zeroMean_read _
  rw [centered, map_sub, map_smul, map_sub, map_smul, outward_constant h nonnegative,
    map_smul, Constructor.zeroMean_constant, smul_zero, smul_zero, sub_zero]

/-- The source commutator is generated from the two independently cut off S-orbits. -/
def sourceCommutator (h : ℝ) : M →L[ℂ] M :=
  (meanZeroDilation h - meanZeroDilation (-h)).comp S

theorem sourceCommutator_action (h : ℝ) (nonnegative : 0 ≤ h) (value : M) :
    sourceCommutator h value =
      meanZeroDilation h (S value) - S (meanZeroDilation h value) := by
  change meanZeroDilation h (S value) - meanZeroDilation (-h) (S value) = _
  rw [finite_fourier_intertwining h nonnegative]

def sourceDrive (h : ℝ) : M :=
  meanZeroDilation h Response.eta + sourceCommutator h Response.v +
    S (sourceCommutator h Response.u)

def sourceFirst (h : ℝ) : M := burnolMeanZeroBlockInverse (sourceDrive h)
def sourceSecond (h : ℝ) : M := S (sourceFirst h)

private theorem finite_B_balance (h : ℝ) (nonnegative : 0 ≤ h) (value : M) :
    burnolMeanZeroOneMinusSquare (meanZeroDilation h value) =
      meanZeroDilation h (burnolMeanZeroOneMinusSquare value) +
        sourceCommutator h (S value) + S (sourceCommutator h value) := by
  change meanZeroDilation h value - S (S (meanZeroDilation h value)) =
    meanZeroDilation h (value - S (S value)) +
      sourceCommutator h (S value) + S (sourceCommutator h value)
  rw [map_sub, sourceCommutator_action h nonnegative, sourceCommutator_action h nonnegative, map_sub]
  module

theorem original_B_finite_action (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMeanZeroOneMinusSquare (meanZeroDilation h Response.u) = sourceDrive h := by
  rw [finite_B_balance h nonnegative, Response.u_equation]
  rfl

theorem sourceFirst_actual (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceFirst h = meanZeroDilation h Response.u := by
  have inverseLeft : burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare = 1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  have read := congrArg burnolMeanZeroBlockInverse (original_B_finite_action h nonnegative)
  change (burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare)
    (meanZeroDilation h Response.u) = sourceFirst h at read
  rw [inverseLeft] at read
  exact read.symm

theorem sourceSecond_actual (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceSecond h = meanZeroDilation (-h) Response.v := by
  rw [sourceSecond, sourceFirst_actual h nonnegative, finite_fourier_intertwining h nonnegative]
  rfl

/-- Exterior stock and the original centering mean are separate full L2 source feet. -/
def outwardExterior (h : ℝ) (value : M) : BurnolL2 :=
  burnolMultiplicativeDilation (-h) (burnolQuarterZeroExtension (value : Hq)) -
    burnolQuarterZeroExtension
      (windowDilation (-h) (value : Hq))

def outwardMean (h : ℝ) (value : M) : ℂ :=
  burnolQuarterMeanCoefficient (windowDilation (-h) (value : Hq))

def fullWindowLoss (h : ℝ) (value : M) : BurnolL2 :=
  outwardExterior h value + outwardMean h value • ConstantDual.seed

theorem outward_full_source_inventory (h : ℝ) (value : M) :
    burnolMultiplicativeDilation (-h) (burnolQuarterZeroExtension (value : Hq)) =
      burnolQuarterZeroExtension (meanZeroDilation (-h) value : Hq) + fullWindowLoss h value := by
  change _ = burnolQuarterZeroExtension (Constructor.zeroMean (windowDilation (-h) (value : Hq)) : Hq) + _
  rw [Constructor.zeroMean_read, map_sub, map_smul]
  change _ = _ - outwardMean h value • ConstantDual.seed +
    ((burnolMultiplicativeDilation (-h) (burnolQuarterZeroExtension (value : Hq)) -
      burnolQuarterZeroExtension (windowDilation (-h) (value : Hq))) +
      outwardMean h value • ConstantDual.seed)
  module

theorem first_response_finite_source (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMultiplicativeDilation (-h) (fourierL2 Response.wholeU - Response.wholeV) =
      fourierL2 (burnolQuarterZeroExtension (sourceFirst h : Hq)) -
        burnolQuarterZeroExtension (sourceSecond h : Hq) - fullWindowLoss h Response.v := by
  rw [map_sub, ← fourierL2_burnolMultiplicativeDilation,
    sourceFirst_actual h nonnegative, inward_extension h nonnegative]
  rw [show Response.wholeV = burnolQuarterZeroExtension (Response.v : Hq) from rfl,
    outward_full_source_inventory, sourceSecond_actual h nonnegative]
  change fourierL2 (burnolMultiplicativeDilation h
    (burnolQuarterZeroExtension (Response.u : Hq))) -
      (burnolQuarterZeroExtension (meanZeroDilation (-h) Response.v : Hq) +
        fullWindowLoss h Response.v) =
    fourierL2 (burnolMultiplicativeDilation h
      (burnolQuarterZeroExtension (Response.u : Hq))) -
      burnolQuarterZeroExtension (meanZeroDilation (-h) Response.v : Hq) -
        fullWindowLoss h Response.v
  module

def sourceDriveV (h : ℝ) : M :=
  meanZeroDilation h (S Response.eta) +
    sourceCommutator h (Response.u - Response.eta) + S (sourceCommutator h Response.v)

def sourceVFirst (h : ℝ) : M := burnolMeanZeroBlockInverse (sourceDriveV h)
def sourceVSecond (h : ℝ) : M := S (sourceVFirst h)

private theorem original_v_equation : burnolMeanZeroOneMinusSquare Response.v = S Response.eta := by
  have pair := congrArg S Response.u_equation
  change S (Response.u - S (S Response.u)) = S Response.eta at pair
  rw [map_sub] at pair
  exact pair

theorem original_B_finite_v_action (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMeanZeroOneMinusSquare (meanZeroDilation h Response.v) = sourceDriveV h := by
  rw [finite_B_balance h nonnegative, original_v_equation]
  have pair : S Response.v = Response.u - Response.eta := by
    have paid := Response.source_pair_equation
    change Response.u - S Response.v = Response.eta at paid
    linear_combination (norm := module) -paid
  rw [pair]
  rfl

theorem sourceVFirst_actual (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceVFirst h = meanZeroDilation h Response.v := by
  have inverseLeft : burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare = 1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  have read := congrArg burnolMeanZeroBlockInverse (original_B_finite_v_action h nonnegative)
  change (burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare)
    (meanZeroDilation h Response.v) = sourceVFirst h at read
  rw [inverseLeft] at read
  exact read.symm

theorem sourceVSecond_actual (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceVSecond h + meanZeroDilation (-h) Response.eta = meanZeroDilation (-h) Response.u := by
  rw [sourceVSecond, sourceVFirst_actual h nonnegative, finite_fourier_intertwining h nonnegative]
  have pair := congrArg (meanZeroDilation (-h)) Response.source_pair_equation
  rw [map_sub] at pair
  change meanZeroDilation (-h) Response.u - meanZeroDilation (-h) (S Response.v) =
    meanZeroDilation (-h) Response.eta at pair
  linear_combination (norm := module) -pair

theorem first_response_forward_source (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMultiplicativeDilation h (fourierL2 Response.wholeU - Response.wholeV) =
      fourierL2 (burnolQuarterZeroExtension
        (sourceVSecond h + meanZeroDilation (-h) Response.eta : Hq)) -
        burnolQuarterZeroExtension (sourceVFirst h : Hq) + fourierL2 (fullWindowLoss h Response.u) := by
  have reverse : burnolMultiplicativeDilation h (fourierL2 Response.wholeU) =
      fourierL2 (burnolMultiplicativeDilation (-h) Response.wholeU) := by
    simpa only [neg_neg] using (fourierL2_burnolMultiplicativeDilation (-h) Response.wholeU).symm
  rw [map_sub, reverse]
  have sourceRead : (sourceVSecond h : Hq) +
      (meanZeroDilation (-h) Response.eta : Hq) = (meanZeroDilation (-h) Response.u : Hq) :=
    congrArg (fun value : M => (value : Hq)) (sourceVSecond_actual h nonnegative)
  rw [show Response.wholeU = burnolQuarterZeroExtension (Response.u : Hq) from rfl,
    outward_full_source_inventory, sourceVFirst_actual h nonnegative, sourceRead,
    inward_extension h nonnegative, map_add]
  change fourierL2 (burnolQuarterZeroExtension (meanZeroDilation (-h) Response.u : Hq)) +
    fourierL2 (fullWindowLoss h Response.u) -
    burnolMultiplicativeDilation h (burnolQuarterZeroExtension (Response.v : Hq)) =
    fourierL2 (burnolQuarterZeroExtension (meanZeroDilation (-h) Response.u : Hq)) -
      burnolMultiplicativeDilation h (burnolQuarterZeroExtension (Response.v : Hq)) +
      fourierL2 (fullWindowLoss h Response.u)
  module

/-- Source constructors read the B drives and contacts, not shifted f0. -/
def f0MinusSource (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  fourierL2 (burnolQuarterZeroExtension (sourceFirst h : Hq)) -
    burnolQuarterZeroExtension (sourceSecond h : Hq) - fullWindowLoss h Response.v +
      (1/2 - OriginalKSourceResolventReconstruction.sourceRate coordinate) •
        burnolMultiplicativeDilation (-h) ConstantDual.seed

def f0PlusSource (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  fourierL2 (burnolQuarterZeroExtension
    (sourceVSecond h + meanZeroDilation (-h) Response.eta : Hq)) -
    burnolQuarterZeroExtension (sourceVFirst h : Hq) + fourierL2 (fullWindowLoss h Response.u) +
      (1/2 - OriginalKSourceResolventReconstruction.sourceRate coordinate) •
        burnolMultiplicativeDilation h ConstantDual.seed

theorem forcing0_backward_source (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMultiplicativeDilation (-h) (OriginalKSourceGramAction.regularForcing coordinate 0) =
      f0MinusSource coordinate h := by
  change burnolMultiplicativeDilation (-h)
    (fourierL2 Response.wholeU - Response.wholeV +
      (1/2 - OriginalKSourceResolventReconstruction.sourceRate coordinate) • ConstantDual.seed) = _
  rw [map_add, map_smul, first_response_finite_source h nonnegative]
  rfl

theorem forcing0_forward_source (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMultiplicativeDilation h (OriginalKSourceGramAction.regularForcing coordinate 0) =
      f0PlusSource coordinate h := by
  change burnolMultiplicativeDilation h
    (fourierL2 Response.wholeU - Response.wholeV +
      (1/2 - OriginalKSourceResolventReconstruction.sourceRate coordinate) • ConstantDual.seed) = _
  rw [map_add, map_smul, first_response_forward_source h nonnegative]
  rfl

end
end OriginalKSourceFiniteUpdate.OriginalBFiniteAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
