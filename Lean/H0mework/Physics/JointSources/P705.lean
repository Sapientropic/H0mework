import H0mework.Physics.JointSources.P704

/-!
# Proposition 705: the P703 grand root induces the same unit extension

P704 proved the finite extension theorem: a shared Hamiltonian/SAT energy
producer plus an Energy/Information/Mathematics/Physics diagonal output is a
singleton package.

This file puts the P703 grand root back into the theorem.  A candidate
extension is now witnessed through a concrete
`HamiltonianSATEnergySameCarrierUnifiedRootCertificate`: that root supplies the
P698 same-carrier energy law and the P702 diagonal law.  Lean proves that this
root-indexed extension surface is still exactly the canonical package, its
subtype is still equivalent to `Unit`, every family is constant, and every
endomorphism is the identity.

Thus the Hilbert/phase-flow grand root and the finite diagonal extension are
not two parallel receipts: any P703 grand root induces the same P704 unit
extension.  The only coherence needed between the local P704 same-carrier proof
and the P703 grand-root proof is proof-irrelevance, because that local
same-carrier certificate is a proposition.

Boundary: this remains the certified finite residual/source-law interface.  It
does not construct arbitrary physical Hamiltonians, smooth Standard-Model
threshold dynamics, runtime reducer faithfulness outside the certified model,
Goldbach/RH, a polynomial SAT solver, or `P = NP`.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open ComplexityProjection
open StandardModelConstraint

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-- The canonical P703 grand root with the universe alignment used in P705:
`E` lives in the third universe, while the local same-carrier proof uses
`Clause : Type v` and `Var : Type w`. -/
def canonicalHamiltonianSATSameCarrierGrandRoot
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v} E :=
  hamiltonianSATEnergySameCarrierUnifiedRootCertificate (E := E)

/-! ## A P703-root-indexed extension surface -/

/-- The extension surface as witnessed by a concrete P703 grand root.

The definition uses the same two object-level surfaces as P704.  The theorem
below proves the collapse using the fields carried by the supplied grand root,
so the finite P704 extension is explicitly induced by P703 rather than merely
placed next to it. -/
def HamiltonianSATFullRootExtensionSurface
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (_R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (P : HamiltonianSATEnergyProducer Clause Var)
    (O : SourceLawFinitePhysicalOutput) : Prop :=
  HamiltonianSATEnergyProducerSurface P ∧
    EnergyInformationMathematicsPhysicsDiagonalSurface O

/-- THEOREM 1: any P703 grand root induces the canonical P704 extension
surface. -/
theorem hamiltonianSATFullRootExtensionSurface_iff_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (P : HamiltonianSATEnergyProducer Clause Var)
    (O : SourceLawFinitePhysicalOutput) :
    HamiltonianSATFullRootExtensionSurface R P O ↔
      P = canonicalHamiltonianSATEnergyProducer Clause Var ∧
        O = canonicalSourceLawFinitePhysicalOutput := by
  constructor
  · intro h
    constructor
    · exact
        (R.same_carrier_energy.producer_surface_iff_canonical
          (Clause := Clause) (Var := Var) P).1 h.1
    · exact
        (EnergyInformationMathematicsPhysicsDiagonalCertificate.diagonal_surface_iff_canonical
            R.p702_diagonal_no_family.p701_diagonal_root O).1 h.2
  · intro h
    constructor
    · rw [h.1]
      exact canonicalHamiltonianSATEnergyProducer_surface Clause Var
    · rw [h.2]
      exact
        (EnergyInformationMathematicsPhysicsDiagonalCertificate.diagonal_surface_iff_canonical
            R.p702_diagonal_no_family.p701_diagonal_root
            canonicalSourceLawFinitePhysicalOutput).2 rfl

/-- THEOREM 2: the root-indexed surface is definitionally the same object-level
surface as P704. -/
theorem hamiltonianSATFullRootExtensionSurface_iff_p704_surface
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (P : HamiltonianSATEnergyProducer Clause Var)
    (O : SourceLawFinitePhysicalOutput) :
    HamiltonianSATFullRootExtensionSurface R P O ↔
      HamiltonianSATDiagonalExtensionSurface P O := by
  rfl

/-- THEOREM 3: the local same-carrier proof carried by P704 is coherent with
the same-carrier proof carried by any P703 grand root. -/
theorem hamiltonianSATFullRoot_localSameCarrier_eq_p704
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    R.same_carrier_energy =
      (hamiltonianSATEnergyDiagonalExtensionCertificate Clause Var).p703_same_carrier_energy := by
  exact Subsingleton.elim _ _

/-! ## The root-indexed extension subtype is still a unit object -/

/-- Accepted extension packages induced by a concrete P703 grand root. -/
def HamiltonianSATFullRootExtensionSubtype
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    Type (max v w) :=
  { X : HamiltonianSATDiagonalExtensionPair Clause Var //
    HamiltonianSATFullRootExtensionSurface R X.1 X.2 }

/-- The canonical root-indexed extension package. -/
def canonicalHamiltonianSATFullRootExtensionSubtype
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    HamiltonianSATFullRootExtensionSubtype Clause Var R :=
  ⟨(canonicalHamiltonianSATEnergyProducer Clause Var,
      canonicalSourceLawFinitePhysicalOutput),
    (hamiltonianSATFullRootExtensionSurface_iff_canonical R
      (canonicalHamiltonianSATEnergyProducer Clause Var)
      canonicalSourceLawFinitePhysicalOutput).2 ⟨rfl, rfl⟩⟩

/-- THEOREM 4: every P703-root-indexed extension package is canonical. -/
theorem hamiltonianSATFullRootExtensionSubtype_eq_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATFullRootExtensionSubtype Clause Var R) :
    X = canonicalHamiltonianSATFullRootExtensionSubtype Clause Var R := by
  cases X with
  | mk pair hpair =>
      cases pair with
      | mk P O =>
          apply Subtype.ext
          have hc :=
            (hamiltonianSATFullRootExtensionSurface_iff_canonical R P O).1
              hpair
          exact Prod.ext hc.1 hc.2

/-- THEOREM 5: the P703-root-indexed extension subtype is equivalent to
`Unit`. -/
def hamiltonianSATFullRootExtensionSubtypeEquivUnit
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    HamiltonianSATFullRootExtensionSubtype Clause Var R ≃ Unit where
  toFun _ := ()
  invFun _ := canonicalHamiltonianSATFullRootExtensionSubtype Clause Var R
  left_inv := by
    intro X
    exact
      (hamiltonianSATFullRootExtensionSubtype_eq_canonical R X).symm
  right_inv := by
    intro x
    cases x
    rfl

/-- THEOREM 6: every family of P703-root-indexed extension packages is
constant. -/
theorem hamiltonianSATFullRootExtensionSubtypeFamily_eq_constant
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {ι : Type z}
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (F : ι -> HamiltonianSATFullRootExtensionSubtype Clause Var R) :
    F = fun _ => canonicalHamiltonianSATFullRootExtensionSubtype Clause Var R := by
  funext i
  exact hamiltonianSATFullRootExtensionSubtype_eq_canonical R (F i)

/-- THEOREM 7: every endomorphism of the P703-root-indexed extension subtype is
the identity. -/
theorem hamiltonianSATFullRootExtensionEndomorphism_eq_id
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (f : HamiltonianSATFullRootExtensionSubtype Clause Var R ->
      HamiltonianSATFullRootExtensionSubtype Clause Var R) :
    f =
      (id : HamiltonianSATFullRootExtensionSubtype Clause Var R ->
        HamiltonianSATFullRootExtensionSubtype Clause Var R) := by
  funext X
  rw [hamiltonianSATFullRootExtensionSubtype_eq_canonical R (f X),
    hamiltonianSATFullRootExtensionSubtype_eq_canonical R X]
  rfl

/-! ## Packaged full root -/

/-- P705 full root: the P703 Hilbert/phase-flow grand root induces the same
P704 unit extension into the Energy/Information/Mathematics/Physics diagonal. -/
structure HamiltonianSATEnergyFullDiagonalUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] where
  p703_grand_root :
    HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v} E
  p704_extension_root :
    HamiltonianSATEnergyDiagonalExtensionUnifiedRootCertificate Clause Var
  full_root_surface_iff_canonical :
    ∀ (P : HamiltonianSATEnergyProducer Clause Var)
      (O : SourceLawFinitePhysicalOutput),
      HamiltonianSATFullRootExtensionSurface p703_grand_root P O ↔
        P = canonicalHamiltonianSATEnergyProducer Clause Var ∧
          O = canonicalSourceLawFinitePhysicalOutput
  full_root_surface_agrees_with_p704 :
    ∀ (P : HamiltonianSATEnergyProducer Clause Var)
      (O : SourceLawFinitePhysicalOutput),
      HamiltonianSATFullRootExtensionSurface p703_grand_root P O ↔
        HamiltonianSATDiagonalExtensionSurface P O
  local_same_carrier_coherent :
    p703_grand_root.same_carrier_energy =
      p704_extension_root.p704_extension.p703_same_carrier_energy
  full_extension_subtype_equiv_unit :
    HamiltonianSATFullRootExtensionSubtype Clause Var p703_grand_root ≃ Unit
  every_full_extension_eq_canonical :
    ∀ X : HamiltonianSATFullRootExtensionSubtype Clause Var p703_grand_root,
      X =
        canonicalHamiltonianSATFullRootExtensionSubtype Clause Var
          p703_grand_root
  full_extension_family_constant :
    ∀ {ι : Type z}
      (F : ι ->
        HamiltonianSATFullRootExtensionSubtype Clause Var p703_grand_root),
      F = fun _ =>
        canonicalHamiltonianSATFullRootExtensionSubtype Clause Var
          p703_grand_root
  full_extension_endomorphism_identity :
    ∀ f : HamiltonianSATFullRootExtensionSubtype Clause Var p703_grand_root ->
      HamiltonianSATFullRootExtensionSubtype Clause Var p703_grand_root,
      f =
        (id :
          HamiltonianSATFullRootExtensionSubtype Clause Var p703_grand_root ->
            HamiltonianSATFullRootExtensionSubtype Clause Var p703_grand_root)

/-- THEOREM 8: the P705 full root is inhabited. -/
def hamiltonianSATEnergyFullDiagonalUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    HamiltonianSATEnergyFullDiagonalUnifiedRootCertificate E Clause Var where
  p703_grand_root :=
    canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E)
  p704_extension_root :=
    hamiltonianSATEnergyDiagonalExtensionUnifiedRootCertificate Clause Var
  full_root_surface_iff_canonical := by
    intro P O
    exact
      hamiltonianSATFullRootExtensionSurface_iff_canonical
        (canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E))
        P O
  full_root_surface_agrees_with_p704 := by
    intro P O
    exact
      hamiltonianSATFullRootExtensionSurface_iff_p704_surface
        (canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E))
        P O
  local_same_carrier_coherent := by
    exact
      hamiltonianSATFullRoot_localSameCarrier_eq_p704.{u, v, w, z}
        (Clause := Clause) (Var := Var)
        (canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E))
  full_extension_subtype_equiv_unit :=
    hamiltonianSATFullRootExtensionSubtypeEquivUnit Clause Var
      (canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E))
  every_full_extension_eq_canonical := by
    intro X
    exact
      hamiltonianSATFullRootExtensionSubtype_eq_canonical
        (canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E))
        X
  full_extension_family_constant := by
    intro ι F
    exact
      hamiltonianSATFullRootExtensionSubtypeFamily_eq_constant
        (canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E))
        F
  full_extension_endomorphism_identity := by
    intro f
    exact
      hamiltonianSATFullRootExtensionEndomorphism_eq_id
        (canonicalHamiltonianSATSameCarrierGrandRoot.{u, v, w, z} (E := E))
        f

end GrandUnification
end SaturationMonoid
