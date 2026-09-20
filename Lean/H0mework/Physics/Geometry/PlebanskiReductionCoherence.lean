import H0mework.Physics.Exterior.PlebanskiVariations

/-!
# Plebanski `II+` reduction provenance

`PlebanskiActionVariationSystem` stores `masterAction` and
`reducedIIPlusAction` independently.  Common first-variation packaging does
not prove that the latter was obtained from the former by the `II+`
substitution.  This module makes that missing native physical law explicit,
without using any seven-facet vocabulary.

The exact law below replaces the bivector in a master configuration by
`⋆(e∧e)` and evaluates the same master action.  It is the strict-normalization
slice of reduction provenance.  A future smooth model with boundary terms
must replace exact equality by a concrete boundary/variation theorem; it must
not supply an arbitrary compatibility proposition.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uConstitutive uConnection uBivector uMultiplier uMatter uTetrad
universe uActionValue uDeltaB uDeltaPhi uDeltaOmega uDeltaE

namespace PlebanskiMasterConfiguration

/-- Replace only the bivector field of a master configuration.  This is the
typed substitution used by the strict `II+` action restriction below. -/
def withBivector
    {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
    {Multiplier : Type uMultiplier} {Matter : Type uMatter}
    (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter)
    (bivector : BivectorTwoForm) :
    PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter where
  connection := q.connection
  bivector := bivector
  multiplier := q.multiplier
  matter := q.matter

@[simp]
theorem withBivector_bivector
    {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
    {Multiplier : Type uMultiplier} {Matter : Type uMatter}
    (q : PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
      Matter)
    (bivector : BivectorTwoForm) :
    (q.withBivector bivector).bivector = bivector :=
  rfl

end PlebanskiMasterConfiguration

/-- Raw operations used to form the `II+` bivector substitution.  No
nondegeneracy predicate, sector label, invertibility proof, or branch
certificate is stored here. -/
structure RawPlebanskiIIPlusSubstitution
    (BivectorTwoForm : Type uBivector) (Tetrad : Type uTetrad) where
  tetradWedge : Tetrad → BivectorTwoForm
  internalBivectorDual : BivectorTwoForm → BivectorTwoForm

namespace RawPlebanskiIIPlusSubstitution

/-- The bivector computed by the two raw substitution operations. -/
def gravitationalBivector
    {BivectorTwoForm : Type uBivector} {Tetrad : Type uTetrad}
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad)
    (e : Tetrad) : BivectorTwoForm :=
  P.internalBivectorDual (P.tetradWedge e)

end RawPlebanskiIIPlusSubstitution

namespace PlebanskiIIPlusBranchGeometry

/-- Forget the laws already certified by a selected branch geometry and keep
only the two operations needed for action substitution. -/
def rawSubstitution
    {BivectorTwoForm : Type uBivector} {Tetrad : Type uTetrad}
    [AddCommGroup BivectorTwoForm]
    (P : PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad) :
    RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad where
  tetradWedge := P.tetradWedge
  internalBivectorDual := P.internalBivectorDual

@[simp]
theorem rawSubstitution_gravitationalBivector
    {BivectorTwoForm : Type uBivector} {Tetrad : Type uTetrad}
    [AddCommGroup BivectorTwoForm]
    (P : PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad)
    (e : Tetrad) :
    P.rawSubstitution.gravitationalBivector e =
      P.gravitationalBivector e :=
  rfl

end PlebanskiIIPlusBranchGeometry

/-- Restrict a master action by a raw, computed bivector substitution. -/
def restrictMasterActionByIIPlusSubstitution
    {Constitutive : Type uConstitutive} {Connection : Type uConnection}
    {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
    {Matter : Type uMatter} {Tetrad : Type uTetrad}
    {ActionValue : Type uActionValue}
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad)
    (masterAction :
      Constitutive →
        PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
          Matter → ActionValue) :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → Tetrad → ActionValue :=
  fun law q e =>
    masterAction law (q.withBivector (P.gravitationalBivector e))

/-- The master action restricted by the concrete `II+` bivector substitution.
No independently supplied reduced action or compatibility predicate occurs in
this definition. -/
def restrictMasterActionToIIPlus
    {Constitutive : Type uConstitutive} {Connection : Type uConnection}
    {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
    {Matter : Type uMatter} {Tetrad : Type uTetrad}
    {ActionValue : Type uActionValue}
    [AddCommGroup BivectorTwoForm]
    (P : PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad)
    (masterAction :
      Constitutive →
        PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
          Matter → ActionValue) :
    Constitutive →
      PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
        Matter → Tetrad → ActionValue :=
  restrictMasterActionByIIPlusSubstitution P.rawSubstitution masterAction

/-- Strict reduction provenance computed from raw substitution operations. -/
def PlebanskiRawIIPlusReductionCoherent
    {Constitutive : Type uConstitutive} {Connection : Type uConnection}
    {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
    {Matter : Type uMatter} {Tetrad : Type uTetrad}
    {ActionValue : Type uActionValue}
    {DeltaBResidual : Type uDeltaB}
    {DeltaPhiResidual : Type uDeltaPhi}
    {DeltaOmegaResidual : Type uDeltaOmega}
    {DeltaEResidual : Type uDeltaE}
    (S : PlebanskiActionVariationSystem Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual)
    (P : RawPlebanskiIIPlusSubstitution BivectorTwoForm Tetrad) : Prop :=
  S.reducedIIPlusAction =
    restrictMasterActionByIIPlusSubstitution P S.masterAction

/-- Strict `II+` reduction provenance: the stored reduced action must be the
typed bivector substitution of the stored master action. -/
def PlebanskiIIPlusReductionCoherent
    {Constitutive : Type uConstitutive} {Connection : Type uConnection}
    {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
    {Matter : Type uMatter} {Tetrad : Type uTetrad}
    {ActionValue : Type uActionValue}
    {DeltaBResidual : Type uDeltaB}
    {DeltaPhiResidual : Type uDeltaPhi}
    {DeltaOmegaResidual : Type uDeltaOmega}
    {DeltaEResidual : Type uDeltaE}
    [AddCommGroup BivectorTwoForm]
    (S : PlebanskiActionVariationSystem Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual)
    (P : PlebanskiIIPlusBranchGeometry BivectorTwoForm Tetrad) : Prop :=
  PlebanskiRawIIPlusReductionCoherent S P.rawSubstitution

/-- The part of an action-variation system visible before the independently
stored reduced action is inspected. -/
structure PlebanskiMasterVariationData
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
  firstVariation :
    PlebanskiFirstVariationOperators Constitutive Connection BivectorTwoForm
      Multiplier Matter Tetrad ActionValue DeltaBResidual DeltaPhiResidual
      DeltaOmegaResidual DeltaEResidual

/-- Forget the reduced action while retaining the master action and all four
first-variation operators. -/
def forgetReducedAction
    {Constitutive : Type uConstitutive} {Connection : Type uConnection}
    {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
    {Matter : Type uMatter} {Tetrad : Type uTetrad}
    {ActionValue : Type uActionValue}
    {DeltaBResidual : Type uDeltaB}
    {DeltaPhiResidual : Type uDeltaPhi}
    {DeltaOmegaResidual : Type uDeltaOmega}
    {DeltaEResidual : Type uDeltaE}
    (S : PlebanskiActionVariationSystem Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual) :
    PlebanskiMasterVariationData Constitutive Connection BivectorTwoForm
      Multiplier Matter Tetrad ActionValue DeltaBResidual DeltaPhiResidual
      DeltaOmegaResidual DeltaEResidual where
  masterAction := S.masterAction
  firstVariation := S.firstVariation

/-- Diagnostic boundary: distinct reduced actions lie over the same master
action and first-variation data.  Thus common-action packaging alone does not
determine reduction provenance. -/
theorem forgetReducedAction_not_injective_of_distinct_reducedActions
    {Constitutive : Type uConstitutive} {Connection : Type uConnection}
    {BivectorTwoForm : Type uBivector} {Multiplier : Type uMultiplier}
    {Matter : Type uMatter} {Tetrad : Type uTetrad}
    {ActionValue : Type uActionValue}
    {DeltaBResidual : Type uDeltaB}
    {DeltaPhiResidual : Type uDeltaPhi}
    {DeltaOmegaResidual : Type uDeltaOmega}
    {DeltaEResidual : Type uDeltaE}
    (masterAction :
      Constitutive →
        PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
          Matter → ActionValue)
    (reducedAction₁ reducedAction₂ :
      Constitutive →
        PlebanskiMasterConfiguration Connection BivectorTwoForm Multiplier
          Matter → Tetrad → ActionValue)
    (firstVariation :
      PlebanskiFirstVariationOperators Constitutive Connection
        BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
        DeltaPhiResidual DeltaOmegaResidual DeltaEResidual)
    (hdistinct : reducedAction₁ ≠ reducedAction₂) :
    ¬ Function.Injective
      (fun S : PlebanskiActionVariationSystem Constitutive Connection
          BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
          DeltaPhiResidual DeltaOmegaResidual DeltaEResidual =>
        forgetReducedAction S) := by
  intro hinjective
  let system₁ : PlebanskiActionVariationSystem Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual :=
    ⟨masterAction, reducedAction₁, firstVariation⟩
  let system₂ : PlebanskiActionVariationSystem Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
      DeltaPhiResidual DeltaOmegaResidual DeltaEResidual :=
    ⟨masterAction, reducedAction₂, firstVariation⟩
  have hsystems : system₁ = system₂ := hinjective rfl
  exact hdistinct
    (congrArg
      (fun S : PlebanskiActionVariationSystem Constitutive Connection
          BivectorTwoForm Multiplier Matter Tetrad ActionValue DeltaBResidual
          DeltaPhiResidual DeltaOmegaResidual DeltaEResidual =>
        S.reducedIIPlusAction)
      hsystems)

/-! ## Nontrivial local independence witness -/

namespace PlebanskiReductionCoherenceToy

abbrev Configuration :=
  PlebanskiMasterConfiguration Unit Int Unit Unit

def masterAction : Unit → Configuration → Nat :=
  fun _ _ => 0

def coherentReducedAction : Unit → Configuration → Unit → Nat :=
  fun _ _ _ => 0

def incoherentReducedAction : Unit → Configuration → Unit → Nat :=
  fun _ _ _ => 1

def firstVariation :
    PlebanskiFirstVariationOperators Unit Unit Int Unit Unit Unit Nat
      Unit Unit Unit Unit where
  deltaBOf := fun _ _ _ => ()
  deltaPhiOf := fun _ _ _ => ()
  deltaOmegaOf := fun _ _ _ => ()
  deltaEOf := fun _ _ _ _ => ()

def rawSubstitution : RawPlebanskiIIPlusSubstitution Int Unit where
  tetradWedge := fun _ => 0
  internalBivectorDual := id

def coherentSystem :
    PlebanskiActionVariationSystem Unit Unit Int Unit Unit Unit Nat
      Unit Unit Unit Unit :=
  ⟨masterAction, coherentReducedAction, firstVariation⟩

def incoherentSystem :
    PlebanskiActionVariationSystem Unit Unit Int Unit Unit Unit Nat
      Unit Unit Unit Unit :=
  ⟨masterAction, incoherentReducedAction, firstVariation⟩

theorem coherentSystem_reductionCoherent :
    PlebanskiRawIIPlusReductionCoherent coherentSystem rawSubstitution := by
  funext law q e
  rfl

theorem incoherentSystem_not_reductionCoherent :
    ¬ PlebanskiRawIIPlusReductionCoherent
      incoherentSystem rawSubstitution := by
  intro hcoherent
  have hvalue := congrFun
    (congrFun (congrFun hcoherent ())
      ({ connection := (), bivector := 0, multiplier := (), matter := () } :
        Configuration)) ()
  norm_num [incoherentSystem, incoherentReducedAction,
    PlebanskiRawIIPlusReductionCoherent,
    restrictMasterActionByIIPlusSubstitution, rawSubstitution,
    RawPlebanskiIIPlusSubstitution.gravitationalBivector,
    masterAction] at hvalue

theorem same_masterVariationData :
    forgetReducedAction coherentSystem =
      forgetReducedAction incoherentSystem :=
  rfl

/-- Concrete local independence witness: two systems have the same master
action and the same four first-variation operators, while exact `II+`
reduction provenance holds for one and fails for the other.  The action-value
carrier is `Nat` and the bivector carrier is `Int`, so this is not a total
`Unit` model.

This proves independence from the currently stored master/variation data.  It
does not yet claim independence from every coordinate of the future complete
physical admissibility classification. -/
theorem reductionCoherence_independent_of_masterVariationData :
    ∃ good bad :
        PlebanskiActionVariationSystem Unit Unit Int Unit Unit Unit Nat
          Unit Unit Unit Unit,
      forgetReducedAction good = forgetReducedAction bad ∧
        PlebanskiRawIIPlusReductionCoherent good rawSubstitution ∧
        ¬ PlebanskiRawIIPlusReductionCoherent bad rawSubstitution :=
  ⟨coherentSystem, incoherentSystem, same_masterVariationData,
    coherentSystem_reductionCoherent,
    incoherentSystem_not_reductionCoherent⟩

end PlebanskiReductionCoherenceToy

end PhysicsCore
end SaturationMonoid
