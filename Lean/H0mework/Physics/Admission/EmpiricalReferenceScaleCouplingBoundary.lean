import H0mework.Physics.Constitutive.ConstitutiveOperator
import H0mework.Physics.Lorentz.RawLorentzianMetricHodgeRecovery

/-!
# Empirical reference-scale coupling boundary

Measured couplings at a chosen renormalization scale are external boundary
data.  This dependency-light module makes that boundary type-level:

* three positive coupling squares and their scale enter through a separate
  `EmpiricalReferenceScaleCouplings` input;
* only that external input is used to build the Standard-Model gauge
  constitutive block;
* a concrete two-boundary witness proves that distinct inputs produce distinct
  constitutive blocks.

No beta coefficient is squared, absolutized, or inverted to manufacture a
reference-scale coupling.  The comparison with the conditional reference-SM
running table lives in `ReferenceSMRunningReceipt`, so importing this module
does not import P459/P508/P523.
-/

namespace SaturationMonoid.PhysicsCore.EmpiricalReferenceScaleCouplingBoundary

noncomputable section

def lorentzianCoframeHodgeEquiv :
    LorentzianTwoForm ≃ₗ[ℝ] LorentzianTwoForm where
  toFun := lorentzianCoframeHodge
  invFun := fun form => -lorentzianCoframeHodge form
  map_add' := lorentzianCoframeHodge.map_add
  map_smul' := lorentzianCoframeHodge.map_smul
  left_inv := by
    intro form
    have hsquare := congrArg
      (fun operator : LorentzianTwoFormHodgeOperator => operator form)
      lorentzianCoframeHodge_square
    simpa using congrArg Neg.neg hsquare
  right_inv := by
    intro form
    have hsquare := congrArg
      (fun operator : LorentzianTwoFormHodgeOperator => operator form)
      lorentzianCoframeHodge_square
    simpa using congrArg Neg.neg hsquare

/-- External empirical boundary condition.  It is deliberately not a field of
the proof-free physical source and is not computed from beta coefficients. -/
structure EmpiricalReferenceScaleCouplings where
  renormalizationScale : ℝ
  scale_pos : 0 < renormalizationScale
  strongCouplingSquared : ℝˣ
  weakCouplingSquared : ℝˣ
  hyperchargeCouplingSquared : ℝˣ
  strong_pos : 0 < (strongCouplingSquared : ℝ)
  weak_pos : 0 < (weakCouplingSquared : ℝ)
  hypercharge_pos : 0 < (hyperchargeCouplingSquared : ℝ)

def gaugeConstitutiveBlock
    (boundary : EmpiricalReferenceScaleCouplings) :
    StandardModelGaugeConstitutiveBlock ℝ LorentzianTwoForm where
  spacetimeHodge := lorentzianCoframeHodgeEquiv
  strongCouplingSquared := boundary.strongCouplingSquared
  weakCouplingSquared := boundary.weakCouplingSquared
  hyperchargeCouplingSquared := boundary.hyperchargeCouplingSquared

def positiveUnit (value : ℝ) (hpositive : 0 < value) : ℝˣ :=
  Units.mk0 value (ne_of_gt hpositive)

def unitBoundary : EmpiricalReferenceScaleCouplings where
  renormalizationScale := 1
  scale_pos := by norm_num
  strongCouplingSquared := 1
  weakCouplingSquared := 1
  hyperchargeCouplingSquared := 1
  strong_pos := by norm_num
  weak_pos := by norm_num
  hypercharge_pos := by norm_num

def doubleBoundary : EmpiricalReferenceScaleCouplings where
  renormalizationScale := 1
  scale_pos := by norm_num
  strongCouplingSquared := positiveUnit 2 (by norm_num)
  weakCouplingSquared := 1
  hyperchargeCouplingSquared := 1
  strong_pos := by norm_num [positiveUnit]
  weak_pos := by norm_num
  hypercharge_pos := by norm_num

theorem unitBoundary_ne_doubleBoundary : unitBoundary ≠ doubleBoundary := by
  intro hequal
  have hstrong := congrArg EmpiricalReferenceScaleCouplings.strongCouplingSquared
    hequal
  have hvalue := congrArg (fun unit : ℝˣ => (unit : ℝ)) hstrong
  norm_num [unitBoundary, doubleBoundary, positiveUnit] at hvalue

theorem gaugeBlocks_distinct :
    gaugeConstitutiveBlock unitBoundary ≠
      gaugeConstitutiveBlock doubleBoundary := by
  intro hequal
  have hstrong := congrArg
    (StandardModelGaugeConstitutiveBlock.strongCouplingSquared) hequal
  have hvalue := congrArg (fun unit : ℝˣ => (unit : ℝ)) hstrong
  norm_num [gaugeConstitutiveBlock, unitBoundary, doubleBoundary,
    positiveUnit] at hvalue

end
end SaturationMonoid.PhysicsCore.EmpiricalReferenceScaleCouplingBoundary
