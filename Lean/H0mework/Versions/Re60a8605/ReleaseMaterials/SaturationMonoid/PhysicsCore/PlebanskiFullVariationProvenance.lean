import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.PlebanskiFirstVariationProvenance
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# All four genuine Plebanski first-variation channels

The earlier provenance module fixed only the bivector derivative.  This file
adds concrete coordinate substitutions for the connection and multiplier and
uses the reported reduced action directly for the tetrad derivative.  All four
channels are checked by Mathlib `HasFDerivAt`; no abstract compatibility
predicate is accepted.

A single smooth real toy system then separates five native laws: exact `II+`
reduction provenance and the `δB`, `δφ`, `δω`, `δe` derivatives.  The
reduction-only countermodel shifts the reduced action by a constant, so all
four derivatives remain correct while action-level reduction provenance fails.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uScalar uConstitutive uConnection uBivector uMultiplier uMatter
universe uTetrad uActionValue

namespace PlebanskiMasterConfiguration

def withConnection
    {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
    {Multiplier : Type uMultiplier} {Matter : Type uMatter}
    (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter)
    (connection : Connection) :
    PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter where
  connection := connection
  bivector := q.bivector
  multiplier := q.multiplier
  matter := q.matter

def withMultiplier
    {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
    {Multiplier : Type uMultiplier} {Matter : Type uMatter}
    (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter)
    (multiplier : Multiplier) :
    PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter where
  connection := q.connection
  bivector := q.bivector
  multiplier := multiplier
  matter := q.matter

end PlebanskiMasterConfiguration

section SmoothProvenance

variable {Scalar : Type uScalar} {Constitutive : Type uConstitutive}
variable {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
variable {Multiplier : Type uMultiplier} {Matter : Type uMatter}
variable {Tetrad : Type uTetrad} {ActionValue : Type uActionValue}
variable [NontriviallyNormedField Scalar]
variable [NormedAddCommGroup Connection] [NormedSpace Scalar Connection]
variable [NormedAddCommGroup BivectorTwoForm]
variable [NormedSpace Scalar BivectorTwoForm]
variable [NormedAddCommGroup Multiplier] [NormedSpace Scalar Multiplier]
variable [NormedAddCommGroup Tetrad] [NormedSpace Scalar Tetrad]
variable [NormedAddCommGroup ActionValue] [NormedSpace Scalar ActionValue]

abbrev SmoothPlebanskiActionVariationSystem :=
  PlebanskiActionVariationSystem Constitutive Connection BivectorTwoForm
    Multiplier Matter Tetrad ActionValue
    (BivectorTwoForm →L[Scalar] ActionValue)
    (Multiplier →L[Scalar] ActionValue)
    (Connection →L[Scalar] ActionValue)
    (Tetrad →L[Scalar] ActionValue)

def PlebanskiMultiplierFirstVariationCorrect
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue)) :
    Prop :=
  ∀ law q,
    HasFDerivAt
      (fun multiplier : Multiplier =>
        S.masterAction law (q.withMultiplier multiplier))
      (S.firstVariation.deltaPhiOf S.masterAction law q)
      q.multiplier

def PlebanskiConnectionFirstVariationCorrect
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue)) :
    Prop :=
  ∀ law q,
    HasFDerivAt
      (fun connection : Connection =>
        S.masterAction law (q.withConnection connection))
      (S.firstVariation.deltaOmegaOf S.masterAction law q)
      q.connection

def PlebanskiTetradFirstVariationCorrect
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue)) :
    Prop :=
  ∀ law q e,
    HasFDerivAt
      (fun tetrad : Tetrad => S.reducedIIPlusAction law q tetrad)
      (S.firstVariation.deltaEOf S.reducedIIPlusAction law q e)
      e

def PlebanskiFullFirstVariationCorrect
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue)) :
    Prop :=
  PlebanskiBivectorFirstVariationCorrect S ∧
    PlebanskiMultiplierFirstVariationCorrect S ∧
      PlebanskiConnectionFirstVariationCorrect S ∧
        PlebanskiTetradFirstVariationCorrect S

def PlebanskiActionProvenanceAdmissible
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue))
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad) : Prop :=
  PlebanskiRawIIPlusReductionCoherent S P ∧
    PlebanskiFullFirstVariationCorrect S

inductive PlebanskiActionCoordinate where
  | reductionProvenance
  | bivectorVariation
  | multiplierVariation
  | connectionVariation
  | tetradVariation
  deriving DecidableEq, Repr, FintypeViaProxy

def PlebanskiActionCoordinateHolds
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue))
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad) :
    PlebanskiActionCoordinate → Prop
  | .reductionProvenance => PlebanskiRawIIPlusReductionCoherent S P
  | .bivectorVariation => PlebanskiBivectorFirstVariationCorrect S
  | .multiplierVariation => PlebanskiMultiplierFirstVariationCorrect S
  | .connectionVariation => PlebanskiConnectionFirstVariationCorrect S
  | .tetradVariation => PlebanskiTetradFirstVariationCorrect S

theorem plebanskiActionProvenanceAdmissible_iff_all_coordinates
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue))
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad) :
    PlebanskiActionProvenanceAdmissible S P ↔
      ∀ c, PlebanskiActionCoordinateHolds S P c := by
  constructor
  · rintro ⟨hreduction, hbivector, hmultiplier, hconnection, htetrad⟩ c
    cases c with
    | reductionProvenance => exact hreduction
    | bivectorVariation => exact hbivector
    | multiplierVariation => exact hmultiplier
    | connectionVariation => exact hconnection
    | tetradVariation => exact htetrad
  · intro hall
    exact ⟨hall .reductionProvenance, hall .bivectorVariation,
      hall .multiplierVariation, hall .connectionVariation,
      hall .tetradVariation⟩

theorem not_plebanskiActionProvenanceAdmissible_iff_exists_failed_coordinate
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue))
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad) :
    ¬ PlebanskiActionProvenanceAdmissible S P ↔
      ∃ c, ¬ PlebanskiActionCoordinateHolds S P c := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot
      (plebanskiActionProvenanceAdmissible_iff_all_coordinates S P |>.mpr
        hnone)
  · rintro ⟨c, hc⟩ hadmissible
    exact hc
      (plebanskiActionProvenanceAdmissible_iff_all_coordinates S P |>.mp
        hadmissible c)

def PlebanskiActionOnlyFails
    (S : SmoothPlebanskiActionVariationSystem (Scalar := Scalar)
      (Constitutive := Constitutive) (Connection := Connection)
      (BivectorTwoForm := BivectorTwoForm) (Multiplier := Multiplier)
      (Matter := Matter) (Tetrad := Tetrad) (ActionValue := ActionValue))
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad)
    (failed : PlebanskiActionCoordinate) : Prop :=
  ¬ PlebanskiActionCoordinateHolds S P failed ∧
    ∀ c, c ≠ failed → PlebanskiActionCoordinateHolds S P c

end SmoothProvenance

/-! ## One smooth real carrier separating all five laws -/

namespace PlebanskiFullVariationProvenanceToy

abbrev Configuration :=
  PlebanskiMasterConfiguration ℝ ℝ ℝ Unit

abbrev Covector := ℝ →L[ℝ] ℝ

abbrev System :=
  SmoothPlebanskiActionVariationSystem (Scalar := ℝ) (Constitutive := Unit)
    (Connection := ℝ) (BivectorTwoForm := ℝ) (Multiplier := ℝ)
    (Matter := Unit) (Tetrad := ℝ) (ActionValue := ℝ)

def masterAction : Unit → Configuration → ℝ :=
  fun _ q => q.connection ^ 2 + q.bivector ^ 2 + q.multiplier ^ 2

def rawSubstitution : RawPlebanskiIIPlusSubstitution ℝ ℝ where
  tetradWedge := id
  internalBivectorDual := id

def reducedAction : Unit → Configuration → ℝ → ℝ :=
  restrictMasterActionByIIPlusSubstitution rawSubstitution masterAction

def shiftedReducedAction : Unit → Configuration → ℝ → ℝ :=
  fun law q e => reducedAction law q e + 1

def correctFirstVariation :
    PlebanskiFirstVariationOperators Unit ℝ ℝ ℝ Unit ℝ ℝ
      Covector Covector Covector Covector where
  deltaBOf := fun _ _ q =>
    (2 * q.bivector) • ContinuousLinearMap.id ℝ ℝ
  deltaPhiOf := fun _ _ q =>
    (2 * q.multiplier) • ContinuousLinearMap.id ℝ ℝ
  deltaOmegaOf := fun _ _ q =>
    (2 * q.connection) • ContinuousLinearMap.id ℝ ℝ
  deltaEOf := fun _ _ _ e =>
    (2 * e) • ContinuousLinearMap.id ℝ ℝ

def bivectorIncorrectFirstVariation :
    PlebanskiFirstVariationOperators Unit ℝ ℝ ℝ Unit ℝ ℝ
      Covector Covector Covector Covector :=
  { correctFirstVariation with deltaBOf := fun _ _ _ => (0 : Covector) }

def multiplierIncorrectFirstVariation :
    PlebanskiFirstVariationOperators Unit ℝ ℝ ℝ Unit ℝ ℝ
      Covector Covector Covector Covector :=
  { correctFirstVariation with deltaPhiOf := fun _ _ _ => (0 : Covector) }

def connectionIncorrectFirstVariation :
    PlebanskiFirstVariationOperators Unit ℝ ℝ ℝ Unit ℝ ℝ
      Covector Covector Covector Covector :=
  { correctFirstVariation with deltaOmegaOf := fun _ _ _ => (0 : Covector) }

def tetradIncorrectFirstVariation :
    PlebanskiFirstVariationOperators Unit ℝ ℝ ℝ Unit ℝ ℝ
      Covector Covector Covector Covector :=
  { correctFirstVariation with deltaEOf := fun _ _ _ _ => (0 : Covector) }

def correctSystem : System :=
  ⟨masterAction, reducedAction, correctFirstVariation⟩

def reductionIncorrectSystem : System :=
  ⟨masterAction, shiftedReducedAction, correctFirstVariation⟩

def bivectorIncorrectSystem : System :=
  ⟨masterAction, reducedAction, bivectorIncorrectFirstVariation⟩

def multiplierIncorrectSystem : System :=
  ⟨masterAction, reducedAction, multiplierIncorrectFirstVariation⟩

def connectionIncorrectSystem : System :=
  ⟨masterAction, reducedAction, connectionIncorrectFirstVariation⟩

def tetradIncorrectSystem : System :=
  ⟨masterAction, reducedAction, tetradIncorrectFirstVariation⟩

theorem actual_bivector_derivative (q : Configuration) :
    HasFDerivAt
      (fun b : ℝ => masterAction () (q.withBivector b))
      ((2 * q.bivector) • ContinuousLinearMap.id ℝ ℝ)
      q.bivector := by
  simpa [masterAction, PlebanskiMasterConfiguration.withBivector,
    add_comm, add_left_comm, add_assoc] using
      (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := q.bivector)).add_const
        (q.connection ^ 2 + q.multiplier ^ 2)

theorem actual_multiplier_derivative (q : Configuration) :
    HasFDerivAt
      (fun multiplier : ℝ => masterAction () (q.withMultiplier multiplier))
      ((2 * q.multiplier) • ContinuousLinearMap.id ℝ ℝ)
      q.multiplier := by
  simpa [masterAction, PlebanskiMasterConfiguration.withMultiplier,
    add_comm, add_left_comm, add_assoc] using
      (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := q.multiplier)).add_const
        (q.connection ^ 2 + q.bivector ^ 2)

theorem actual_connection_derivative (q : Configuration) :
    HasFDerivAt
      (fun connection : ℝ => masterAction () (q.withConnection connection))
      ((2 * q.connection) • ContinuousLinearMap.id ℝ ℝ)
      q.connection := by
  simpa [masterAction, PlebanskiMasterConfiguration.withConnection,
    add_comm, add_left_comm, add_assoc] using
      (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := q.connection)).add_const
        (q.bivector ^ 2 + q.multiplier ^ 2)

theorem actual_tetrad_derivative (q : Configuration) (e : ℝ) :
    HasFDerivAt
      (fun tetrad : ℝ => reducedAction () q tetrad)
      ((2 * e) • ContinuousLinearMap.id ℝ ℝ)
      e := by
  simpa [reducedAction, restrictMasterActionByIIPlusSubstitution,
    rawSubstitution, RawPlebanskiIIPlusSubstitution.gravitationalBivector,
    masterAction, PlebanskiMasterConfiguration.withBivector,
    add_comm, add_left_comm, add_assoc] using
      (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := e)).add_const
        (q.connection ^ 2 + q.multiplier ^ 2)

theorem shifted_tetrad_derivative (q : Configuration) (e : ℝ) :
    HasFDerivAt
      (fun tetrad : ℝ => shiftedReducedAction () q tetrad)
      ((2 * e) • ContinuousLinearMap.id ℝ ℝ)
      e := by
  simpa [shiftedReducedAction] using
    (actual_tetrad_derivative q e).add_const 1

theorem correctSystem_reduction :
    PlebanskiRawIIPlusReductionCoherent correctSystem rawSubstitution :=
  rfl

theorem reductionIncorrectSystem_not_reduction :
    ¬ PlebanskiRawIIPlusReductionCoherent
      reductionIncorrectSystem rawSubstitution := by
  intro hreduction
  let q : Configuration :=
    { connection := 0, bivector := 0, multiplier := 0, matter := () }
  have hvalue := congrFun (congrFun (congrFun hreduction ()) q) 0
  norm_num [reductionIncorrectSystem, shiftedReducedAction, reducedAction,
    restrictMasterActionByIIPlusSubstitution, rawSubstitution,
    RawPlebanskiIIPlusSubstitution.gravitationalBivector, masterAction,
    PlebanskiMasterConfiguration.withBivector, q] at hvalue

theorem correctSystem_bivector :
    PlebanskiBivectorFirstVariationCorrect correctSystem := by
  intro law q
  simpa [correctSystem, correctFirstVariation] using actual_bivector_derivative q

theorem correctSystem_multiplier :
    PlebanskiMultiplierFirstVariationCorrect correctSystem := by
  intro law q
  simpa [correctSystem, correctFirstVariation] using
    actual_multiplier_derivative q

theorem correctSystem_connection :
    PlebanskiConnectionFirstVariationCorrect correctSystem := by
  intro law q
  simpa [correctSystem, correctFirstVariation] using
    actual_connection_derivative q

theorem correctSystem_tetrad :
    PlebanskiTetradFirstVariationCorrect correctSystem := by
  intro law q e
  simpa [correctSystem, correctFirstVariation] using
    actual_tetrad_derivative q e

theorem reductionIncorrectSystem_bivector :
    PlebanskiBivectorFirstVariationCorrect reductionIncorrectSystem := by
  intro law q
  simpa [reductionIncorrectSystem, correctFirstVariation] using
    actual_bivector_derivative q

theorem reductionIncorrectSystem_multiplier :
    PlebanskiMultiplierFirstVariationCorrect reductionIncorrectSystem := by
  intro law q
  simpa [reductionIncorrectSystem, correctFirstVariation] using
    actual_multiplier_derivative q

theorem reductionIncorrectSystem_connection :
    PlebanskiConnectionFirstVariationCorrect reductionIncorrectSystem := by
  intro law q
  simpa [reductionIncorrectSystem, correctFirstVariation] using
    actual_connection_derivative q

theorem reductionIncorrectSystem_tetrad :
    PlebanskiTetradFirstVariationCorrect reductionIncorrectSystem := by
  intro law q e
  simpa [reductionIncorrectSystem, correctFirstVariation] using
    shifted_tetrad_derivative q e

theorem bivectorIncorrectSystem_not_bivector :
    ¬ PlebanskiBivectorFirstVariationCorrect bivectorIncorrectSystem := by
  intro hcorrect
  let q : Configuration :=
    { connection := 0, bivector := 1, multiplier := 0, matter := () }
  have hbad := hcorrect () q
  have heq := (actual_bivector_derivative q).unique hbad
  have hvalue := congrArg (fun L : Covector => L 1) heq
  norm_num [bivectorIncorrectSystem, bivectorIncorrectFirstVariation, q] at hvalue

theorem multiplierIncorrectSystem_not_multiplier :
    ¬ PlebanskiMultiplierFirstVariationCorrect multiplierIncorrectSystem := by
  intro hcorrect
  let q : Configuration :=
    { connection := 0, bivector := 0, multiplier := 1, matter := () }
  have hbad := hcorrect () q
  have heq := (actual_multiplier_derivative q).unique hbad
  have hvalue := congrArg (fun L : Covector => L 1) heq
  norm_num [multiplierIncorrectSystem, multiplierIncorrectFirstVariation, q]
    at hvalue

theorem connectionIncorrectSystem_not_connection :
    ¬ PlebanskiConnectionFirstVariationCorrect connectionIncorrectSystem := by
  intro hcorrect
  let q : Configuration :=
    { connection := 1, bivector := 0, multiplier := 0, matter := () }
  have hbad := hcorrect () q
  have heq := (actual_connection_derivative q).unique hbad
  have hvalue := congrArg (fun L : Covector => L 1) heq
  norm_num [connectionIncorrectSystem, connectionIncorrectFirstVariation, q]
    at hvalue

theorem tetradIncorrectSystem_not_tetrad :
    ¬ PlebanskiTetradFirstVariationCorrect tetradIncorrectSystem := by
  intro hcorrect
  let q : Configuration :=
    { connection := 0, bivector := 0, multiplier := 0, matter := () }
  have hbad := hcorrect () q 1
  have heq := (actual_tetrad_derivative q 1).unique hbad
  have hvalue := congrArg (fun L : Covector => L 1) heq
  norm_num [tetradIncorrectSystem, tetradIncorrectFirstVariation, q] at hvalue

theorem bivectorIncorrectSystem_reduction :
    PlebanskiRawIIPlusReductionCoherent
      bivectorIncorrectSystem rawSubstitution := rfl

theorem multiplierIncorrectSystem_reduction :
    PlebanskiRawIIPlusReductionCoherent
      multiplierIncorrectSystem rawSubstitution := rfl

theorem connectionIncorrectSystem_reduction :
    PlebanskiRawIIPlusReductionCoherent
      connectionIncorrectSystem rawSubstitution := rfl

theorem tetradIncorrectSystem_reduction :
    PlebanskiRawIIPlusReductionCoherent tetradIncorrectSystem rawSubstitution :=
  rfl

theorem bivectorIncorrectSystem_multiplier :
    PlebanskiMultiplierFirstVariationCorrect bivectorIncorrectSystem := by
  intro law q
  simpa [bivectorIncorrectSystem, bivectorIncorrectFirstVariation,
    correctFirstVariation] using actual_multiplier_derivative q

theorem bivectorIncorrectSystem_connection :
    PlebanskiConnectionFirstVariationCorrect bivectorIncorrectSystem := by
  intro law q
  simpa [bivectorIncorrectSystem, bivectorIncorrectFirstVariation,
    correctFirstVariation] using actual_connection_derivative q

theorem bivectorIncorrectSystem_tetrad :
    PlebanskiTetradFirstVariationCorrect bivectorIncorrectSystem := by
  intro law q e
  simpa [bivectorIncorrectSystem, bivectorIncorrectFirstVariation,
    correctFirstVariation] using actual_tetrad_derivative q e

theorem multiplierIncorrectSystem_bivector :
    PlebanskiBivectorFirstVariationCorrect multiplierIncorrectSystem := by
  intro law q
  simpa [multiplierIncorrectSystem, multiplierIncorrectFirstVariation,
    correctFirstVariation] using actual_bivector_derivative q

theorem multiplierIncorrectSystem_connection :
    PlebanskiConnectionFirstVariationCorrect multiplierIncorrectSystem := by
  intro law q
  simpa [multiplierIncorrectSystem, multiplierIncorrectFirstVariation,
    correctFirstVariation] using actual_connection_derivative q

theorem multiplierIncorrectSystem_tetrad :
    PlebanskiTetradFirstVariationCorrect multiplierIncorrectSystem := by
  intro law q e
  simpa [multiplierIncorrectSystem, multiplierIncorrectFirstVariation,
    correctFirstVariation] using actual_tetrad_derivative q e

theorem connectionIncorrectSystem_bivector :
    PlebanskiBivectorFirstVariationCorrect connectionIncorrectSystem := by
  intro law q
  simpa [connectionIncorrectSystem, connectionIncorrectFirstVariation,
    correctFirstVariation] using actual_bivector_derivative q

theorem connectionIncorrectSystem_multiplier :
    PlebanskiMultiplierFirstVariationCorrect connectionIncorrectSystem := by
  intro law q
  simpa [connectionIncorrectSystem, connectionIncorrectFirstVariation,
    correctFirstVariation] using actual_multiplier_derivative q

theorem connectionIncorrectSystem_tetrad :
    PlebanskiTetradFirstVariationCorrect connectionIncorrectSystem := by
  intro law q e
  simpa [connectionIncorrectSystem, connectionIncorrectFirstVariation,
    correctFirstVariation] using actual_tetrad_derivative q e

theorem tetradIncorrectSystem_bivector :
    PlebanskiBivectorFirstVariationCorrect tetradIncorrectSystem := by
  intro law q
  simpa [tetradIncorrectSystem, tetradIncorrectFirstVariation,
    correctFirstVariation] using actual_bivector_derivative q

theorem tetradIncorrectSystem_multiplier :
    PlebanskiMultiplierFirstVariationCorrect tetradIncorrectSystem := by
  intro law q
  simpa [tetradIncorrectSystem, tetradIncorrectFirstVariation,
    correctFirstVariation] using actual_multiplier_derivative q

theorem tetradIncorrectSystem_connection :
    PlebanskiConnectionFirstVariationCorrect tetradIncorrectSystem := by
  intro law q
  simpa [tetradIncorrectSystem, tetradIncorrectFirstVariation,
    correctFirstVariation] using actual_connection_derivative q

theorem correctSystem_admissible :
    PlebanskiActionProvenanceAdmissible correctSystem rawSubstitution :=
  ⟨correctSystem_reduction, correctSystem_bivector,
    correctSystem_multiplier, correctSystem_connection, correctSystem_tetrad⟩

theorem reductionIncorrectSystem_onlyFails :
    PlebanskiActionOnlyFails reductionIncorrectSystem rawSubstitution
      .reductionProvenance := by
  refine ⟨reductionIncorrectSystem_not_reduction, ?_⟩
  intro c hc
  cases c with
  | reductionProvenance => exact (hc rfl).elim
  | bivectorVariation => exact reductionIncorrectSystem_bivector
  | multiplierVariation => exact reductionIncorrectSystem_multiplier
  | connectionVariation => exact reductionIncorrectSystem_connection
  | tetradVariation => exact reductionIncorrectSystem_tetrad

theorem bivectorIncorrectSystem_onlyFails :
    PlebanskiActionOnlyFails bivectorIncorrectSystem rawSubstitution
      .bivectorVariation := by
  refine ⟨bivectorIncorrectSystem_not_bivector, ?_⟩
  intro c hc
  cases c with
  | reductionProvenance => exact bivectorIncorrectSystem_reduction
  | bivectorVariation => exact (hc rfl).elim
  | multiplierVariation => exact bivectorIncorrectSystem_multiplier
  | connectionVariation => exact bivectorIncorrectSystem_connection
  | tetradVariation => exact bivectorIncorrectSystem_tetrad

theorem multiplierIncorrectSystem_onlyFails :
    PlebanskiActionOnlyFails multiplierIncorrectSystem rawSubstitution
      .multiplierVariation := by
  refine ⟨multiplierIncorrectSystem_not_multiplier, ?_⟩
  intro c hc
  cases c with
  | reductionProvenance => exact multiplierIncorrectSystem_reduction
  | bivectorVariation => exact multiplierIncorrectSystem_bivector
  | multiplierVariation => exact (hc rfl).elim
  | connectionVariation => exact multiplierIncorrectSystem_connection
  | tetradVariation => exact multiplierIncorrectSystem_tetrad

theorem connectionIncorrectSystem_onlyFails :
    PlebanskiActionOnlyFails connectionIncorrectSystem rawSubstitution
      .connectionVariation := by
  refine ⟨connectionIncorrectSystem_not_connection, ?_⟩
  intro c hc
  cases c with
  | reductionProvenance => exact connectionIncorrectSystem_reduction
  | bivectorVariation => exact connectionIncorrectSystem_bivector
  | multiplierVariation => exact connectionIncorrectSystem_multiplier
  | connectionVariation => exact (hc rfl).elim
  | tetradVariation => exact connectionIncorrectSystem_tetrad

theorem tetradIncorrectSystem_onlyFails :
    PlebanskiActionOnlyFails tetradIncorrectSystem rawSubstitution
      .tetradVariation := by
  refine ⟨tetradIncorrectSystem_not_tetrad, ?_⟩
  intro c hc
  cases c with
  | reductionProvenance => exact tetradIncorrectSystem_reduction
  | bivectorVariation => exact tetradIncorrectSystem_bivector
  | multiplierVariation => exact tetradIncorrectSystem_multiplier
  | connectionVariation => exact tetradIncorrectSystem_connection
  | tetradVariation => exact (hc rfl).elim

theorem every_plebanskiActionCoordinate_has_only_one_failure_model
    (c : PlebanskiActionCoordinate) :
    ∃ S : System, PlebanskiActionOnlyFails S rawSubstitution c := by
  cases c with
  | reductionProvenance =>
      exact ⟨reductionIncorrectSystem, reductionIncorrectSystem_onlyFails⟩
  | bivectorVariation =>
      exact ⟨bivectorIncorrectSystem, bivectorIncorrectSystem_onlyFails⟩
  | multiplierVariation =>
      exact ⟨multiplierIncorrectSystem, multiplierIncorrectSystem_onlyFails⟩
  | connectionVariation =>
      exact ⟨connectionIncorrectSystem, connectionIncorrectSystem_onlyFails⟩
  | tetradVariation =>
      exact ⟨tetradIncorrectSystem, tetradIncorrectSystem_onlyFails⟩

end PlebanskiFullVariationProvenanceToy

end PhysicsCore
end SaturationMonoid
