import H0mework.Physics.Geometry.PlebanskiInterfaces

/-!
# Typed Plebanski variation residuals

The stage-one gate used one undifferentiated `gravityVariationResidual` and
allowed its zero set to imply simplicity, nondegeneracy, and `II+` at once.
This module separates the four logically different variations:

* `δB`: curvature/constitutive equation;
* `δφ`: the multiplier equation and therefore the only stationarity channel
  that an optional simplicity-recovery theorem may consume;
* `δω`: the connection/spin-current equation;
* `δe`: the tetrad equation after recovery or source-domain selection of an
  `II+` branch.

The branch-recovery interface below is parameterized directly by the same
`deltaPhiResidual`; it has no second, independently supplied simplicity
residual.  Standard Plebanski stationarity still permits four sectors, so a
separate indexed selection witness is required before `II+` recovery.  The
source-domain adapter instead receives a source tetrad directly and uses
`δφ=0` only as a stationarity/consistency equation.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uConstitutive uConnection uBivector uMultiplier uMatter uTetrad
universe uDeltaB uDeltaPhi uDeltaOmega uDeltaE
universe uActionValue

/-- Fundamental Plebanski fields before choosing a tetrad branch. -/
structure PlebanskiMasterConfiguration
    (Connection : Type uConnection) (BivectorTwoForm : Type uBivector)
    (Multiplier : Type uMultiplier) (Matter : Type uMatter) where
  connection : Connection
  bivector : BivectorTwoForm
  multiplier : Multiplier
  matter : Matter

/-- Four distinct Euler--Lagrange residual carriers.

This is still a conditional action-variation interface: a concrete physical
instance must prove that these functions are the variations of one action.
The type separation prevents `δφ` simplicity from being silently replaced by
a generic terminal GR residual. -/
structure PlebanskiVariationResiduals
    (Constitutive : Type uConstitutive) (Connection : Type uConnection)
    (BivectorTwoForm : Type uBivector) (Multiplier : Type uMultiplier)
    (Matter : Type uMatter) (Tetrad : Type uTetrad)
    (DeltaBResidual : Type uDeltaB) (DeltaPhiResidual : Type uDeltaPhi)
    (DeltaOmegaResidual : Type uDeltaOmega) (DeltaEResidual : Type uDeltaE)
    [Zero DeltaBResidual] [Zero DeltaPhiResidual]
    [Zero DeltaOmegaResidual] [Zero DeltaEResidual] where
  deltaBResidual :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter →
      DeltaBResidual
  deltaPhiResidual :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter →
      DeltaPhiResidual
  deltaOmegaResidual :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter →
      DeltaOmegaResidual
  deltaEAfterIIPlusResidual :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter →
      Tetrad → DeltaEResidual

namespace PlebanskiVariationResiduals

variable {Constitutive : Type uConstitutive}
variable {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
variable {Multiplier : Type uMultiplier} {Matter : Type uMatter}
variable {Tetrad : Type uTetrad}
variable {DeltaBResidual : Type uDeltaB}
variable {DeltaPhiResidual : Type uDeltaPhi}
variable {DeltaOmegaResidual : Type uDeltaOmega}
variable {DeltaEResidual : Type uDeltaE}
variable [Zero DeltaBResidual] [Zero DeltaPhiResidual]
variable [Zero DeltaOmegaResidual] [Zero DeltaEResidual]

/-- The three pre-branch master equations.  No branch conclusion is included.
-/
def MasterOnShell
    (V : PlebanskiVariationResiduals Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual)
    (law : Constitutive)
    (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter) : Prop :=
  V.deltaBResidual law q = 0 ∧
    V.deltaPhiResidual law q = 0 ∧
      V.deltaOmegaResidual law q = 0

/-- The tetrad equation is imposed only after an `II+` tetrad has been
recovered/selected. -/
def DeltaEOnShell
    (V : PlebanskiVariationResiduals Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual)
    (law : Constitutive)
    (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter)
    (e : Tetrad) : Prop :=
  V.deltaEAfterIIPlusResidual law q e = 0

/-- Faithfulness firewall: none of the four variation channels is the
identically-zero function.  This rejects the legacy all-`Unit`/all-zero
countermodel without claiming that nonconstancy alone supplies physical
smooth variation semantics. -/
def HasNontrivialVariationChannels
    (V : PlebanskiVariationResiduals Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual) : Prop :=
  (∃ (law : Constitutive)
      (q : PlebanskiMasterConfiguration Connection BivectorTwoForm
        Multiplier Matter),
      V.deltaBResidual law q ≠ 0) ∧
    (∃ (law : Constitutive)
      (q : PlebanskiMasterConfiguration Connection BivectorTwoForm
        Multiplier Matter),
      V.deltaPhiResidual law q ≠ 0) ∧
    (∃ (law : Constitutive)
      (q : PlebanskiMasterConfiguration Connection BivectorTwoForm
        Multiplier Matter),
      V.deltaOmegaResidual law q ≠ 0) ∧
    (∃ (law : Constitutive)
      (q : PlebanskiMasterConfiguration Connection BivectorTwoForm
        Multiplier Matter)
      (e : Tetrad),
      V.deltaEAfterIIPlusResidual law q e ≠ 0)

end PlebanskiVariationResiduals

/-! ## Common-action first-variation provenance -/

/-- Typed first-variation operations.  The derived residuals below are
definitionally obtained by applying these four named operators to the master
or reduced action.  A smooth implementation must still prove that the
operators are actual derivatives/integration-by-parts constructions; the
operator fields themselves remain abstract at this stage. -/
structure PlebanskiFirstVariationOperators
    (Constitutive : Type uConstitutive) (Connection : Type uConnection)
    (BivectorTwoForm : Type uBivector) (Multiplier : Type uMultiplier)
    (Matter : Type uMatter) (Tetrad : Type uTetrad)
    (ActionValue : Type uActionValue)
    (DeltaBResidual : Type uDeltaB) (DeltaPhiResidual : Type uDeltaPhi)
    (DeltaOmegaResidual : Type uDeltaOmega) (DeltaEResidual : Type uDeltaE)
    where
  deltaBOf :
    (Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → ActionValue) →
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → DeltaBResidual
  deltaPhiOf :
    (Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → ActionValue) →
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → DeltaPhiResidual
  deltaOmegaOf :
    (Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → ActionValue) →
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → DeltaOmegaResidual
  deltaEOf :
    (Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → Tetrad → ActionValue) →
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → Tetrad → DeltaEResidual

/-- One master action and its branch-reduced action, together with the typed
first-variation operations used to derive all four residuals.

This records machine-checkable common-action provenance.  It remains a
conditional interface until a concrete smooth instance proves that
`firstVariation` implements the mathematical derivative and that
`reducedIIPlusAction` is the valid branch reduction of `masterAction`. -/
structure PlebanskiActionVariationSystem
    (Constitutive : Type uConstitutive) (Connection : Type uConnection)
    (BivectorTwoForm : Type uBivector) (Multiplier : Type uMultiplier)
    (Matter : Type uMatter) (Tetrad : Type uTetrad)
    (ActionValue : Type uActionValue)
    (DeltaBResidual : Type uDeltaB) (DeltaPhiResidual : Type uDeltaPhi)
    (DeltaOmegaResidual : Type uDeltaOmega) (DeltaEResidual : Type uDeltaE)
    where
  masterAction :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → ActionValue
  reducedIIPlusAction :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → Tetrad → ActionValue
  firstVariation :
    PlebanskiFirstVariationOperators Constitutive Connection BivectorTwoForm
      Multiplier Matter Tetrad ActionValue DeltaBResidual DeltaPhiResidual
      DeltaOmegaResidual DeltaEResidual

namespace PlebanskiActionVariationSystem

variable {Constitutive : Type uConstitutive}
variable {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
variable {Multiplier : Type uMultiplier} {Matter : Type uMatter}
variable {Tetrad : Type uTetrad} {ActionValue : Type uActionValue}
variable {DeltaBResidual : Type uDeltaB}
variable {DeltaPhiResidual : Type uDeltaPhi}
variable {DeltaOmegaResidual : Type uDeltaOmega}
variable {DeltaEResidual : Type uDeltaE}
variable [Zero DeltaBResidual] [Zero DeltaPhiResidual]
variable [Zero DeltaOmegaResidual] [Zero DeltaEResidual]

/-- All four residuals are definitionally obtained from the same action
system; `δφ` is therefore the multiplier variation channel rather than a
generic GR residual renamed after the fact. -/
def residuals
    (S : PlebanskiActionVariationSystem Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual) :
    PlebanskiVariationResiduals Constitutive Connection BivectorTwoForm
      Multiplier Matter Tetrad DeltaBResidual DeltaPhiResidual
      DeltaOmegaResidual DeltaEResidual where
  deltaBResidual := S.firstVariation.deltaBOf S.masterAction
  deltaPhiResidual := S.firstVariation.deltaPhiOf S.masterAction
  deltaOmegaResidual := S.firstVariation.deltaOmegaOf S.masterAction
  deltaEAfterIIPlusResidual :=
    S.firstVariation.deltaEOf S.reducedIIPlusAction

end PlebanskiActionVariationSystem

/-- The three legitimate places from which a Plebanski `II+` choice may come.
The stage-two adapter deliberately uses the first constructor. -/
inductive PlebanskiIIPlusSelectionOrigin where
  | sourceConfigurationDomainRestriction
  | extraBranchSelectionConstraint
  | orientationAndTimeOrientationConstruction
  deriving DecidableEq, Repr

/-- Indexed evidence recording both the chosen selection mechanism and the
predicate that it actually established for one source/configuration pair. -/
inductive PlebanskiIIPlusSelectionEvidence
    {Source Configuration : Type*}
    (sourceConfigurationAdmissible : Source → Configuration → Prop)
    (extraBranchConstraint : Configuration → Prop)
    (orientationTimeOrientationSelected : Source → Configuration → Prop)
    (χ : Source) (q : Configuration) :
    PlebanskiIIPlusSelectionOrigin → Prop
  | fromSourceConfigurationDomain
      (h : sourceConfigurationAdmissible χ q) :
      PlebanskiIIPlusSelectionEvidence sourceConfigurationAdmissible
        extraBranchConstraint orientationTimeOrientationSelected χ q
        .sourceConfigurationDomainRestriction
  | fromExtraBranchConstraint
      (h : extraBranchConstraint q) :
      PlebanskiIIPlusSelectionEvidence sourceConfigurationAdmissible
        extraBranchConstraint orientationTimeOrientationSelected χ q
        .extraBranchSelectionConstraint
  | fromOrientationAndTimeOrientation
      (h : orientationTimeOrientationSelected χ q) :
      PlebanskiIIPlusSelectionEvidence sourceConfigurationAdmissible
        extraBranchConstraint orientationTimeOrientationSelected χ q
        .orientationAndTimeOrientationConstruction

/-- Geometry of a selected Plebanski `II+` branch, independent of how a tetrad
was obtained.  The source-domain adapter uses this structure because its
premise already supplies a source tetrad and its gravitational bivector. -/
structure PlebanskiIIPlusBranchGeometry
    (BivectorTwoForm : Type uBivector) (Tetrad : Type uTetrad)
    [AddCommGroup BivectorTwoForm] where
  nondegenerate : BivectorTwoForm → Prop
  sector : BivectorTwoForm → PlebanskiSector
  tetradWedge : Tetrad → BivectorTwoForm
  internalBivectorDual : BivectorTwoForm ≃+ BivectorTwoForm
  sector_gravitationalBivector :
    ∀ e : Tetrad,
      sector (internalBivectorDual (tetradWedge e)) =
        .gravitationalPlus

namespace PlebanskiIIPlusBranchGeometry

variable {BivectorTwoForm : Type uBivector} {Tetrad : Type uTetrad}
variable [AddCommGroup BivectorTwoForm]

def gravitationalBivector
    (P : PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad)
    (e : Tetrad) : BivectorTwoForm :=
  P.internalBivectorDual (P.tetradWedge e)

@[simp]
theorem sector_gravitationalBivector_eq_gravitationalPlus
    (P : PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad)
    (e : Tetrad) :
    P.sector (P.gravitationalBivector e) = .gravitationalPlus :=
  P.sector_gravitationalBivector e

end PlebanskiIIPlusBranchGeometry

/-- Optional recovery interface for the second honest route: when no tetrad
is preselected, `δφ=0`, nondegeneracy, and an independently selected `II+`
sector may recover one.  The source-domain hard-gate adapter does not use this
recovery theorem; there `δφ` is a stationarity/consistency equation. -/
structure PlebanskiIIPlusRecoveryFromDeltaPhi
    {Constitutive : Type uConstitutive} {Connection : Type uConnection}
    {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
    {Matter : Type uMatter} {Tetrad : Type uTetrad}
    {DeltaBResidual : Type uDeltaB} {DeltaPhiResidual : Type uDeltaPhi}
    {DeltaOmegaResidual : Type uDeltaOmega} {DeltaEResidual : Type uDeltaE}
    [AddCommGroup BivectorTwoForm]
    [Zero DeltaBResidual] [Zero DeltaPhiResidual]
    [Zero DeltaOmegaResidual] [Zero DeltaEResidual]
    (V : PlebanskiVariationResiduals Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual) extends
    PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad where
  recover_gravitationalPlus_from_deltaPhi :
    ∀ (law : Constitutive)
      (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter),
      V.deltaPhiResidual law q = 0 →
        toPlebanskiIIPlusBranchGeometry.nondegenerate q.bivector →
          toPlebanskiIIPlusBranchGeometry.sector q.bivector =
            .gravitationalPlus →
            ∃ e : Tetrad,
              q.bivector =
                toPlebanskiIIPlusBranchGeometry.gravitationalBivector e

namespace PlebanskiIIPlusRecoveryFromDeltaPhi

variable {Constitutive : Type uConstitutive} {Connection : Type uConnection}
variable {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
variable {Matter : Type uMatter} {Tetrad : Type uTetrad}
variable {DeltaBResidual : Type uDeltaB}
variable {DeltaPhiResidual : Type uDeltaPhi}
variable {DeltaOmegaResidual : Type uDeltaOmega}
variable {DeltaEResidual : Type uDeltaE}
variable [AddCommGroup BivectorTwoForm]
variable [Zero DeltaBResidual] [Zero DeltaPhiResidual]
variable [Zero DeltaOmegaResidual] [Zero DeltaEResidual]
variable {V : PlebanskiVariationResiduals Constitutive Connection
  BivectorTwoForm Multiplier Matter Tetrad DeltaBResidual DeltaPhiResidual
  DeltaOmegaResidual DeltaEResidual}

def gravitationalBivector
    (R : PlebanskiIIPlusRecoveryFromDeltaPhi V) (e : Tetrad) :
    BivectorTwoForm :=
  R.toPlebanskiIIPlusBranchGeometry.gravitationalBivector e

@[simp]
theorem sector_gravitationalBivector_eq_gravitationalPlus
    (R : PlebanskiIIPlusRecoveryFromDeltaPhi V) (e : Tetrad) :
    R.sector (R.gravitationalBivector e) = .gravitationalPlus :=
  PlebanskiIIPlusBranchGeometry.sector_gravitationalBivector_eq_gravitationalPlus
    R.toPlebanskiIIPlusBranchGeometry e

/-- `δφ=0`, nondegeneracy, and an independently selected `II+` sector recover
a tetrad.  Master stationarity alone does not supply the sector premise. -/
theorem exists_tetrad_of_deltaPhi_nondegenerate_selectedIIPlus
    (R : PlebanskiIIPlusRecoveryFromDeltaPhi V)
    (law : Constitutive)
    (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter)
    (hdeltaPhi : V.deltaPhiResidual law q = 0)
    (hnondegenerate : R.nondegenerate q.bivector)
    (hsector : R.sector q.bivector = .gravitationalPlus) :
    ∃ e : Tetrad, q.bivector = R.gravitationalBivector e :=
  R.recover_gravitationalPlus_from_deltaPhi law q hdeltaPhi hnondegenerate
    hsector

end PlebanskiIIPlusRecoveryFromDeltaPhi

end PhysicsCore
end SaturationMonoid
