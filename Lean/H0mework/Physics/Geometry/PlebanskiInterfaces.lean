import Mathlib

/-!
# Layered Plebanski / Palatini interfaces

This file is a compile-checked hard-gate skeleton, not a derivation of general
relativity.  It keeps five logically different layers separate:

1. non-Abelian connection curvature `dω + ω∧ω`;
2. full simplicity, nondegeneracy, and Plebanski branch selection;
3. the zero-spin-current connection equation;
4. torsion-free recovery;
5. the conditional Palatini-to-Einstein transporter.

No structure below constructs a Lorentz connection, a tetrad, a simplicity
solution, or an Einstein equation.  Those remain producer obligations.  In
particular, Dirac matter generally has nonzero spin current, so torsion-free
recovery is deliberately restricted to the explicit zero-spin-current slice.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uConnection uCurvature uBivector uBivectorCurrent
universe uTetrad uSimplicityResidual uTorsion uMatter
universe uPalatiniResidual uEinsteinResidual uGravityVariationResidual
universe uSource uConstitutive

/-! ## Non-Abelian connection / curvature kinematics -/

/-- Abstract Lorentz-connection kinematics with the non-Abelian bracket term
kept explicit.

The name describes the intended interface.  A genuine Lorentzian instance
must still construct the connection carrier and prove that its bracket term is
nontrivial. -/
structure LorentzConnectionKinematics
    (Connection : Type uConnection) (Curvature : Type uCurvature)
    (BivectorTwoForm : Type uBivector)
    (BivectorThreeForm : Type uBivectorCurrent)
    [AddZeroClass Curvature]
    [AddCommGroup BivectorTwoForm]
    [AddCommGroup BivectorThreeForm] where
  exteriorDerivative : Connection → Curvature
  bracketWedge : Connection → Connection → Curvature
  covariantDerivativeB :
    Connection → BivectorTwoForm →+ BivectorThreeForm

namespace LorentzConnectionKinematics

variable {Connection : Type uConnection} {Curvature : Type uCurvature}
variable {BivectorTwoForm : Type uBivector}
variable {BivectorThreeForm : Type uBivectorCurrent}
variable [AddZeroClass Curvature]
variable [AddCommGroup BivectorTwoForm]
variable [AddCommGroup BivectorThreeForm]

/-- Non-Abelian curvature grammar `F(ω) = dω + ω∧ω`. -/
def curvature
    (L : LorentzConnectionKinematics Connection Curvature
      BivectorTwoForm BivectorThreeForm)
    (ω : Connection) : Curvature :=
  L.exteriorDerivative ω + L.bracketWedge ω ω

/-- A separate obligation witnessing only that the supplied quadratic bracket
term is nonzero somewhere.  This does not by itself prove a Lie bracket,
bilinearity, gauge covariance, or genuine non-Abelian geometry; a concrete
Lorentz producer must establish those stronger laws. -/
def HasNonzeroQuadraticBracketTerm
    (L : LorentzConnectionKinematics Connection Curvature
      BivectorTwoForm BivectorThreeForm) : Prop :=
  ∃ ω : Connection, L.bracketWedge ω ω ≠ 0

/-- On a bracket-zero slice, the non-Abelian grammar collapses to `dω`.
This is the precise sense in which the repository's current P272 exact slice
is too weak for a genuine Yang--Mills or Lorentz curvature. -/
theorem curvature_eq_exteriorDerivative_of_bracket_eq_zero
    (L : LorentzConnectionKinematics Connection Curvature
      BivectorTwoForm BivectorThreeForm)
    (ω : Connection) (hbracket : L.bracketWedge ω ω = 0) :
    L.curvature ω = L.exteriorDerivative ω := by
  simp [curvature, hbracket]

/-- Connection Euler--Lagrange residual with an explicit spin-current term.
The pure-gravity / bosonic slice uses `spinCurrent = 0`; fermionic matter need
not do so. -/
def masterConnectionResidual
    (L : LorentzConnectionKinematics Connection Curvature
      BivectorTwoForm BivectorThreeForm)
    (ω : Connection) (B : BivectorTwoForm)
    (spinCurrent : BivectorThreeForm) : BivectorThreeForm :=
  L.covariantDerivativeB ω B - spinCurrent

end LorentzConnectionKinematics

/-! ## Simplicity, nondegeneracy, and branch selection -/

/-- The four nondegenerate Plebanski sectors. -/
inductive PlebanskiSector where
  | topologicalPlus
  | topologicalMinus
  | gravitationalPlus
  | gravitationalMinus
  deriving DecidableEq, Repr

/-- Conditional branch-recovery interface.

`simplicityResidual = 0` stands for the full, correctly trace-restricted
volume/simplicity system, not an arbitrary single equation.  A concrete
producer must instantiate that residual and prove the recovery theorem. -/
structure PlebanskiBranchKinematics
    (BivectorTwoForm : Type uBivector) (Tetrad : Type uTetrad)
    (SimplicityResidual : Type uSimplicityResidual)
    [AddCommGroup BivectorTwoForm] [Zero SimplicityResidual] where
  simplicityResidual : BivectorTwoForm → SimplicityResidual
  nondegenerate : BivectorTwoForm → Prop
  sector : BivectorTwoForm → PlebanskiSector
  tetradWedge : Tetrad → BivectorTwoForm
  internalBivectorDual : BivectorTwoForm ≃+ BivectorTwoForm
  recover_gravitationalPlus :
    ∀ B : BivectorTwoForm,
      simplicityResidual B = 0 →
        nondegenerate B →
          sector B = .gravitationalPlus →
            ∃ e : Tetrad,
              B = internalBivectorDual (tetradWedge e)

namespace PlebanskiBranchKinematics

variable {BivectorTwoForm : Type uBivector} {Tetrad : Type uTetrad}
variable {SimplicityResidual : Type uSimplicityResidual}
variable [AddCommGroup BivectorTwoForm] [Zero SimplicityResidual]

/-- The selected gravitational bivector `⋆η(e∧e)`.  This is the internal
bivector dual, not the spacetime Hodge operator used by Yang--Mills. -/
def gravitationalBivector
    (P : PlebanskiBranchKinematics BivectorTwoForm Tetrad
      SimplicityResidual)
    (e : Tetrad) : BivectorTwoForm :=
  P.internalBivectorDual (P.tetradWedge e)

/-- Full simplicity is the zero set of the producer-supplied, correctly
restricted simplicity residual. -/
def FullSimplicity
    (P : PlebanskiBranchKinematics BivectorTwoForm Tetrad
      SimplicityResidual)
    (B : BivectorTwoForm) : Prop :=
  P.simplicityResidual B = 0

/-- Conditional readout of the tetrad branch. -/
theorem exists_tetrad_of_fullSimplicity_nondegenerate_gravitationalPlus
    (P : PlebanskiBranchKinematics BivectorTwoForm Tetrad
      SimplicityResidual)
    (B : BivectorTwoForm)
    (hsimplicity : P.FullSimplicity B)
    (hnondegenerate : P.nondegenerate B)
    (hsector : P.sector B = .gravitationalPlus) :
    ∃ e : Tetrad, B = P.gravitationalBivector e :=
  P.recover_gravitationalPlus B hsimplicity hnondegenerate hsector

end PlebanskiBranchKinematics

/-! ## Zero-spin-current torsion recovery -/

/-- Conditional transporter from the bosonic connection equation to
torsion-free geometry.  Metric compatibility and nondegeneracy are explicit;
they are not inferred from the word `connection`. -/
structure TorsionFreeRecoveryInterface
    {Connection : Type uConnection} {Curvature : Type uCurvature}
    {BivectorTwoForm : Type uBivector}
    {BivectorThreeForm : Type uBivectorCurrent}
    {Tetrad : Type uTetrad}
    {SimplicityResidual : Type uSimplicityResidual}
    [AddZeroClass Curvature]
    [AddCommGroup BivectorTwoForm]
    [AddCommGroup BivectorThreeForm]
    [Zero SimplicityResidual]
    (L : LorentzConnectionKinematics Connection Curvature
      BivectorTwoForm BivectorThreeForm)
    (P : PlebanskiBranchKinematics BivectorTwoForm Tetrad
      SimplicityResidual)
    (TorsionForm : Type uTorsion) [Zero TorsionForm] where
  metricCompatible : Connection → Prop
  torsion : Connection → Tetrad → TorsionForm
  recover_zero_spin_current :
    ∀ (ω : Connection) (e : Tetrad),
      metricCompatible ω →
        P.nondegenerate (P.gravitationalBivector e) →
          L.masterConnectionResidual ω (P.gravitationalBivector e) 0 = 0 →
            torsion ω e = 0

/-- CONDITIONAL TRANSPORTER: full simplicity plus branch selection and the
zero-spin-current connection equation recover a tetrad with zero torsion. -/
theorem exists_tetrad_torsionFree_of_plebanskiLayers
    {Connection : Type uConnection} {Curvature : Type uCurvature}
    {BivectorTwoForm : Type uBivector}
    {BivectorThreeForm : Type uBivectorCurrent}
    {Tetrad : Type uTetrad}
    {SimplicityResidual : Type uSimplicityResidual}
    {TorsionForm : Type uTorsion}
    [AddZeroClass Curvature]
    [AddCommGroup BivectorTwoForm]
    [AddCommGroup BivectorThreeForm]
    [Zero SimplicityResidual] [Zero TorsionForm]
    (L : LorentzConnectionKinematics Connection Curvature
      BivectorTwoForm BivectorThreeForm)
    (P : PlebanskiBranchKinematics BivectorTwoForm Tetrad
      SimplicityResidual)
    (R : TorsionFreeRecoveryInterface L P TorsionForm)
    (ω : Connection) (B : BivectorTwoForm)
    (hsimplicity : P.FullSimplicity B)
    (hnondegenerate : P.nondegenerate B)
    (hsector : P.sector B = .gravitationalPlus)
    (hmetric : R.metricCompatible ω)
    (hconnection : L.masterConnectionResidual ω B 0 = 0) :
    ∃ e : Tetrad,
      B = P.gravitationalBivector e ∧ R.torsion ω e = 0 := by
  obtain ⟨e, hB⟩ :=
    P.exists_tetrad_of_fullSimplicity_nondegenerate_gravitationalPlus
      B hsimplicity hnondegenerate hsector
  refine ⟨e, hB, ?_⟩
  apply R.recover_zero_spin_current ω e hmetric
  · simpa [hB] using hnondegenerate
  · simpa [hB] using hconnection

/-! ## Palatini-to-Einstein conditional transporter -/

/-- The last recovery layer.  It consumes a zero-torsion result and a genuine
tetrad-variation residual; it does not store an `equation_holds` Boolean and
does not construct either residual. -/
structure PalatiniEinsteinRecoveryInterface
    (Connection : Type uConnection) (Tetrad : Type uTetrad)
    (Matter : Type uMatter) (TorsionForm : Type uTorsion)
    (PalatiniResidual : Type uPalatiniResidual)
    (EinsteinResidual : Type uEinsteinResidual)
    [Zero TorsionForm] [Zero PalatiniResidual] [Zero EinsteinResidual]
    (torsion : Connection → Tetrad → TorsionForm) where
  palatiniTetradResidual :
    Connection → Tetrad → Matter → PalatiniResidual
  einsteinResidual :
    Connection → Tetrad → Matter → EinsteinResidual
  residualTransport : PalatiniResidual → EinsteinResidual
  residualTransport_zero : residualTransport 0 = 0
  residualTransport_matches :
    ∀ (ω : Connection) (e : Tetrad) (matter : Matter),
      torsion ω e = 0 →
        residualTransport (palatiniTetradResidual ω e matter) =
          einsteinResidual ω e matter

namespace PalatiniEinsteinRecoveryInterface

variable {Connection : Type uConnection} {Tetrad : Type uTetrad}
variable {Matter : Type uMatter} {TorsionForm : Type uTorsion}
variable {PalatiniResidual : Type uPalatiniResidual}
variable {EinsteinResidual : Type uEinsteinResidual}
variable [Zero TorsionForm] [Zero PalatiniResidual] [Zero EinsteinResidual]
variable {torsion : Connection → Tetrad → TorsionForm}

/-- The explicit residual transporter sends a zero Palatini tetrad residual
to a zero spacetime Einstein residual once the selected torsion policy holds.
-/
theorem einsteinResidual_eq_zero_of_torsion_and_palatiniResidual_zero
    (E : PalatiniEinsteinRecoveryInterface Connection Tetrad Matter
      TorsionForm PalatiniResidual EinsteinResidual torsion)
    (ω : Connection) (e : Tetrad) (matter : Matter)
    (htorsion : torsion ω e = 0)
    (hpalatini : E.palatiniTetradResidual ω e matter = 0) :
    E.einsteinResidual ω e matter = 0 := by
  calc
    E.einsteinResidual ω e matter =
        E.residualTransport (E.palatiniTetradResidual ω e matter) :=
      (E.residualTransport_matches ω e matter htorsion).symm
    _ = E.residualTransport 0 := by rw [hpalatini]
    _ = 0 := E.residualTransport_zero

end PalatiniEinsteinRecoveryInterface

/-- CONDITIONAL TRANSPORTER: compose all Plebanski layers once the tetrad
Euler--Lagrange residual has independently been produced by variation. -/
theorem exists_tetrad_einstein_of_plebanskiLayers
    {Connection : Type uConnection} {Curvature : Type uCurvature}
    {BivectorTwoForm : Type uBivector}
    {BivectorThreeForm : Type uBivectorCurrent}
    {Tetrad : Type uTetrad}
    {SimplicityResidual : Type uSimplicityResidual}
    {TorsionForm : Type uTorsion} {Matter : Type uMatter}
    {PalatiniResidual : Type uPalatiniResidual}
    {EinsteinResidual : Type uEinsteinResidual}
    [AddZeroClass Curvature]
    [AddCommGroup BivectorTwoForm]
    [AddCommGroup BivectorThreeForm]
    [Zero SimplicityResidual] [Zero TorsionForm]
    [Zero PalatiniResidual] [Zero EinsteinResidual]
    (L : LorentzConnectionKinematics Connection Curvature
      BivectorTwoForm BivectorThreeForm)
    (P : PlebanskiBranchKinematics BivectorTwoForm Tetrad
      SimplicityResidual)
    (R : TorsionFreeRecoveryInterface L P TorsionForm)
    (E : PalatiniEinsteinRecoveryInterface Connection Tetrad Matter
      TorsionForm PalatiniResidual EinsteinResidual R.torsion)
    (ω : Connection) (B : BivectorTwoForm) (matter : Matter)
    (hsimplicity : P.FullSimplicity B)
    (hnondegenerate : P.nondegenerate B)
    (hsector : P.sector B = .gravitationalPlus)
    (hmetric : R.metricCompatible ω)
    (hconnection : L.masterConnectionResidual ω B 0 = 0)
    (hpalatini : ∀ e : Tetrad,
      B = P.gravitationalBivector e →
        E.palatiniTetradResidual ω e matter = 0) :
    ∃ e : Tetrad,
      B = P.gravitationalBivector e ∧
        R.torsion ω e = 0 ∧
          E.einsteinResidual ω e matter = 0 := by
  obtain ⟨e, hB, htorsion⟩ :=
    exists_tetrad_torsionFree_of_plebanskiLayers
      L P R ω B hsimplicity hnondegenerate hsector hmetric hconnection
  refine ⟨e, hB, htorsion, ?_⟩
  exact
    E.einsteinResidual_eq_zero_of_torsion_and_palatiniResidual_zero
      ω e matter htorsion (hpalatini e hB)

/-! ## The source-generated constitutive hard gate -/

/-- The unsolved GR producer mouth.

This proposition does not assert that a producer exists.  It names what a
source-generated constitutive law must force on its gravitational projection,
so that simplicity/nondegeneracy/branch data cannot be smuggled in later as
unlabeled premises. -/
def LegacySourceGeneratedGravityConstitutiveHardGateObligation
    {Source : Type uSource} {Constitutive : Type uConstitutive}
    {BivectorTwoForm : Type uBivector} {Tetrad : Type uTetrad}
    {SimplicityResidual : Type uSimplicityResidual}
    {GravityVariationResidual : Type uGravityVariationResidual}
    [AddCommGroup BivectorTwoForm] [Zero SimplicityResidual]
    [Zero GravityVariationResidual]
    (admissible : Source → Prop)
    (sourceConstitutive : Source → Constitutive)
    (gravityVariationResidual :
      Constitutive → BivectorTwoForm → GravityVariationResidual)
    (P : PlebanskiBranchKinematics BivectorTwoForm Tetrad
      SimplicityResidual) : Prop :=
  ∀ (χ : Source), admissible χ →
    (∃ B : BivectorTwoForm,
      gravityVariationResidual (sourceConstitutive χ) B = 0) ∧
      ∀ B : BivectorTwoForm,
        gravityVariationResidual (sourceConstitutive χ) B = 0 →
          P.FullSimplicity B ∧
            P.nondegenerate B ∧
              P.sector B = .gravitationalPlus

end PhysicsCore
end SaturationMonoid
