import H0mework.Physics.Admission.EmpiricalReferenceScaleCouplingBoundary
import H0mework.Physics.Source.SourceRelativePhysicalStationaryFamily

/-!
# One finite physical Plebanski / Standard-Model gauge master action

This module closes the Stage-4 common-action boundary at an explicitly finite,
jet-local strength.  One scalar action is the sum of

* the source-relative physical Plebanski density; and
* three constrained first-order gauge-sector densities using the empirical
  strong, weak, and hypercharge constitutive operators.

Each gauge sector contains the usual finite BF/YM quadratic density together
with an independent constitutive multiplier.  The multiplier's actual
Fréchet variation is the six-component defect `F-KB`; it vanishes exactly at
`B=K⁻¹F`.  Thus auxiliary elimination is derived from one action and is not a
stored field equation.

Boundary: gauge curvature is a finite two-form coordinate here.  This module
does not claim a full smooth Standard-Model connection, integration by parts,
matter current, or continuum Einstein/Yang--Mills recovery.
-/

namespace SaturationMonoid.PhysicsCore.UnifiedPhysicalMasterAction

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open SourceRelativePhysicalStationaryFamily
open JetLocalPhysicalPlebanskiAction
open PhysicalIIPlusFrechetVariation

noncomputable section

abbrev GaugeTwoFormVector := LorentzianTwoForm
abbrev GaugeCovector := GaugeTwoFormVector →L[ℝ] ℝ

abbrev gaugeHodgeVectorEquiv :
    GaugeTwoFormVector ≃ₗ[ℝ] GaugeTwoFormVector :=
  lorentzianCoframeHodgeEquiv

def gaugeConstitutiveOperatorVector (couplingSquared : ℝˣ) :
    GaugeTwoFormVector ≃ₗ[ℝ] GaugeTwoFormVector :=
  hodgeConstitutiveOperator lorentzianCoframeHodgeEquiv couplingSquared

@[simp] theorem gaugeConstitutiveOperatorVector_apply
    (couplingSquared : ℝˣ) (bivector : GaugeTwoFormVector) :
    gaugeConstitutiveOperatorVector couplingSquared bivector =
      (couplingSquared : ℝ) • gaugeHodgeVectorEquiv bivector := by
  rfl

/-- Euclidean coordinate pairing used only to turn the six finite components
into one scalar density. -/
def gaugePairing (first second : GaugeTwoFormVector) : ℝ :=
  ∑ index : Fin 6, first index * second index

@[simp] theorem gaugePairing_zero_left (value : GaugeTwoFormVector) :
    gaugePairing 0 value = 0 := by
  simp [gaugePairing]

@[simp] theorem gaugePairing_zero_right (value : GaugeTwoFormVector) :
    gaugePairing value 0 = 0 := by
  simp [gaugePairing]

/-- Continuous covector represented by the finite coordinate pairing. -/
def gaugePairingCovector (coefficient : GaugeTwoFormVector) : GaugeCovector :=
  ∑ index : Fin 6,
    coefficient index •
      (ContinuousLinearMap.proj index : GaugeTwoFormVector →L[ℝ] ℝ)

@[simp] theorem gaugePairingCovector_apply
    (coefficient value : GaugeTwoFormVector) :
    gaugePairingCovector coefficient value = gaugePairing coefficient value := by
  simp [gaugePairingCovector, gaugePairing]

theorem gaugePairingCovector_eq_zero_iff
    (coefficient : GaugeTwoFormVector) :
    gaugePairingCovector coefficient = 0 ↔ coefficient = 0 := by
  constructor
  · intro hzero
    funext index
    have hvalue := congrArg
      (fun covector : GaugeCovector =>
        covector (fun candidate => if candidate = index then 1 else 0))
      hzero
    simpa [gaugePairingCovector, gaugePairing] using hvalue
  · rintro rfl
    ext value
    simp

structure GaugeSectorConfiguration where
  curvature : GaugeTwoFormVector
  auxiliary : GaugeTwoFormVector
  constitutiveMultiplier : GaugeTwoFormVector

namespace GaugeSectorConfiguration

def withConstitutiveMultiplier
    (q : GaugeSectorConfiguration)
    (constitutiveMultiplier : GaugeTwoFormVector) :
    GaugeSectorConfiguration :=
  { q with constitutiveMultiplier := constitutiveMultiplier }

end GaugeSectorConfiguration

/-- Finite Lorentzian BF/YM density.  The first two terms are the standard
first-order auxiliary grammar in component pairing; the last term enforces
the exact empirical constitutive operator by genuine variation. -/
def gaugeSectorAction
    (couplingSquared : ℝˣ) (q : GaugeSectorConfiguration) : ℝ :=
  gaugePairing q.auxiliary (gaugeHodgeVectorEquiv q.curvature) +
      ((couplingSquared : ℝ) / 2) *
        gaugePairing q.auxiliary q.auxiliary +
    gaugePairing
      (q.curvature -
        gaugeConstitutiveOperatorVector couplingSquared q.auxiliary)
      q.constitutiveMultiplier

/-- The actual constitutive-multiplier variation. -/
def gaugeSectorConstitutiveVariation
    (couplingSquared : ℝˣ) (q : GaugeSectorConfiguration) : GaugeCovector :=
  gaugePairingCovector
    (q.curvature -
      gaugeConstitutiveOperatorVector couplingSquared q.auxiliary)

theorem actual_gaugeSector_constitutive_derivative
    (couplingSquared : ℝˣ) (q : GaugeSectorConfiguration) :
    HasFDerivAt
      (fun multiplier : GaugeTwoFormVector =>
        gaugeSectorAction couplingSquared
          (q.withConstitutiveMultiplier multiplier))
      (gaugeSectorConstitutiveVariation couplingSquared q)
      q.constitutiveMultiplier := by
  have hlinear :=
    (gaugePairingCovector
      (q.curvature -
        gaugeConstitutiveOperatorVector couplingSquared q.auxiliary))
      |>.hasFDerivAt (x := q.constitutiveMultiplier)
  simpa [gaugeSectorAction,
    GaugeSectorConfiguration.withConstitutiveMultiplier,
    gaugeSectorConstitutiveVariation] using
      hlinear.const_add
        (gaugePairing q.auxiliary (gaugeHodgeVectorEquiv q.curvature) +
          ((couplingSquared : ℝ) / 2) *
            gaugePairing q.auxiliary q.auxiliary)

/-- Genuine first-order auxiliary elimination from the multiplier variation.
-/
theorem gaugeSectorConstitutiveVariation_eq_zero_iff_eliminated
    (couplingSquared : ℝˣ) (q : GaugeSectorConfiguration) :
    gaugeSectorConstitutiveVariation couplingSquared q = 0 ↔
      q.auxiliary =
        (gaugeConstitutiveOperatorVector couplingSquared).symm q.curvature := by
  rw [gaugeSectorConstitutiveVariation,
    gaugePairingCovector_eq_zero_iff]
  constructor
  · intro hdefect
    apply (gaugeConstitutiveOperatorVector couplingSquared).injective
    simpa using (sub_eq_zero.mp hdefect).symm
  · intro heq
    simp [heq]

structure StandardModelGaugeConfiguration where
  strong : GaugeSectorConfiguration
  weak : GaugeSectorConfiguration
  hypercharge : GaugeSectorConfiguration

def standardModelGaugeAction
    (boundary : EmpiricalReferenceScaleCouplings)
    (q : StandardModelGaugeConfiguration) : ℝ :=
  gaugeSectorAction boundary.strongCouplingSquared q.strong +
    gaugeSectorAction boundary.weakCouplingSquared q.weak +
    gaugeSectorAction boundary.hyperchargeCouplingSquared q.hypercharge

structure UnifiedConfiguration where
  gravity : JetLocalPhysicalPlebanskiAction.Configuration
  gauge : StandardModelGaugeConfiguration

namespace UnifiedConfiguration

def withGravityConnection
    (q : UnifiedConfiguration) (connection : ConnectionJet) :
    UnifiedConfiguration :=
  { q with gravity := q.gravity.withConnection connection }

def withGravityBivector
    (q : UnifiedConfiguration) (bivector : BivectorVector) :
    UnifiedConfiguration :=
  { q with gravity := q.gravity.withBivector bivector }

def withGravityMultiplier
    (q : UnifiedConfiguration) (multiplier : BivectorVector) :
    UnifiedConfiguration :=
  { q with gravity := q.gravity.withMultiplier multiplier }

def withGravityTetrad
    (q : UnifiedConfiguration) (tetrad : TetradVector) :
    UnifiedConfiguration :=
  { q with gravity := q.gravity.withTetrad tetrad }

end UnifiedConfiguration

/-- One scalar master action containing both the physical Plebanski and all
three empirical Standard-Model gauge sectors. -/
def unifiedMasterAction
    (source : Source)
    (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) : ℝ :=
  sourceRelativeMasterAction source q.gravity +
    standardModelGaugeAction boundary q.gauge

theorem unified_actual_gravity_connection_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun connection =>
        unifiedMasterAction source boundary
          (q.withGravityConnection connection))
      (deltaOmega source q.gravity) q.gravity.connection := by
  simpa [unifiedMasterAction, UnifiedConfiguration.withGravityConnection] using
    (actual_connection_derivative source q.gravity).add_const
      (standardModelGaugeAction boundary q.gauge)

theorem unified_actual_gravity_bivector_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun bivector =>
        unifiedMasterAction source boundary
          (q.withGravityBivector bivector))
      (deltaB source q.gravity) q.gravity.bivector := by
  simpa [unifiedMasterAction, UnifiedConfiguration.withGravityBivector] using
    (actual_bivector_derivative source q.gravity).add_const
      (standardModelGaugeAction boundary q.gauge)

theorem unified_actual_gravity_multiplier_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun multiplier =>
        unifiedMasterAction source boundary
          (q.withGravityMultiplier multiplier))
      (deltaPhi source q.gravity) q.gravity.multiplier := by
  simpa [unifiedMasterAction, UnifiedConfiguration.withGravityMultiplier] using
    (actual_multiplier_derivative source q.gravity).add_const
      (standardModelGaugeAction boundary q.gauge)

theorem unified_actual_gravity_tetrad_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun tetrad =>
        unifiedMasterAction source boundary
          (q.withGravityTetrad tetrad))
      (deltaE source q.gravity) q.gravity.tetrad := by
  simpa [unifiedMasterAction, UnifiedConfiguration.withGravityTetrad] using
    (actual_tetrad_derivative source q.gravity).add_const
      (standardModelGaugeAction boundary q.gauge)

theorem unified_all_four_gravity_variations_from_one_action
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
        (fun connection =>
          unifiedMasterAction source boundary
            (q.withGravityConnection connection))
        (deltaOmega source q.gravity) q.gravity.connection ∧
      HasFDerivAt
        (fun bivector =>
          unifiedMasterAction source boundary
            (q.withGravityBivector bivector))
        (deltaB source q.gravity) q.gravity.bivector ∧
      HasFDerivAt
        (fun multiplier =>
          unifiedMasterAction source boundary
            (q.withGravityMultiplier multiplier))
        (deltaPhi source q.gravity) q.gravity.multiplier ∧
      HasFDerivAt
        (fun tetrad =>
          unifiedMasterAction source boundary
            (q.withGravityTetrad tetrad))
        (deltaE source q.gravity) q.gravity.tetrad :=
  ⟨unified_actual_gravity_connection_derivative source boundary q,
    unified_actual_gravity_bivector_derivative source boundary q,
    unified_actual_gravity_multiplier_derivative source boundary q,
    unified_actual_gravity_tetrad_derivative source boundary q⟩

def zeroGaugeSectorConfiguration : GaugeSectorConfiguration :=
  ⟨0, 0, 0⟩

def zeroStandardModelGaugeConfiguration : StandardModelGaugeConfiguration :=
  ⟨zeroGaugeSectorConfiguration, zeroGaugeSectorConfiguration,
    zeroGaugeSectorConfiguration⟩

def sourceUnifiedConfiguration (source : Source) : UnifiedConfiguration where
  gravity := sourceStationaryConfiguration source
  gauge := zeroStandardModelGaugeConfiguration

@[simp] theorem zeroGaugeSector_constitutiveVariation
    (couplingSquared : ℝˣ) :
    gaugeSectorConstitutiveVariation couplingSquared
      zeroGaugeSectorConfiguration = 0 := by
  ext value
  simp [gaugeSectorConstitutiveVariation, zeroGaugeSectorConfiguration]

structure UnifiedPhysicalStationaryAtSource
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) : Prop where
  gravity_stationary : PhysicalStationaryAtSource source
  strong_constitutive_stationary :
    gaugeSectorConstitutiveVariation boundary.strongCouplingSquared
      (sourceUnifiedConfiguration source).gauge.strong = 0
  weak_constitutive_stationary :
    gaugeSectorConstitutiveVariation boundary.weakCouplingSquared
      (sourceUnifiedConfiguration source).gauge.weak = 0
  hypercharge_constitutive_stationary :
    gaugeSectorConstitutiveVariation boundary.hyperchargeCouplingSquared
      (sourceUnifiedConfiguration source).gauge.hypercharge = 0

theorem source_generates_unifiedStationaryFamily
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    UnifiedPhysicalStationaryAtSource source boundary :=
  ⟨source_generates_stationaryFamily source,
    zeroGaugeSector_constitutiveVariation boundary.strongCouplingSquared,
    zeroGaugeSector_constitutiveVariation boundary.weakCouplingSquared,
    zeroGaugeSector_constitutiveVariation
      boundary.hyperchargeCouplingSquared⟩

end
end SaturationMonoid.PhysicsCore.UnifiedPhysicalMasterAction
