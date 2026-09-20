import H0mework.Computation.SelfReduction.P703

/-!
# Proposition 704: the shared energy producer extends uniquely to the diagonal

P703 proves that Hamiltonian-energy and SAT-energy are the same scalar
producer on one certified residual carrier.  P702 proves that the
Energy/Information/Mathematics/Physics diagonal is a unit object: every valid
finite face output is the canonical source-law output.

This file composes those two roots without adding a new interpretation layer.
An accepted package consists of

* one shared Hamiltonian/SAT energy producer, and
* one four-face diagonal finite output.

Lean proves that the package surface is itself a singleton/unit object.  Thus
the P703 scalar energy producer has a unique extension into the P702 diagonal:
no extra producer, no extra output, no hidden indexed family, and no
automorphism can live between them.

Boundary: this is still the certified finite residual/source-law carrier.  It
does not construct arbitrary physical Hamiltonians, smooth threshold dynamics,
runtime reducer faithfulness outside the certified model, a polynomial SAT
solver, `P = NP`, Goldbach, RH, or the final smooth Standard-Model producer.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open ComplexityProjection
open StandardModelConstraint

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Product surface: shared energy producer plus diagonal output -/

/-- A package candidate: a scalar energy producer on the P703 shared carrier
and a finite output on the P701/P702 four-face diagonal. -/
abbrev HamiltonianSATDiagonalExtensionPair
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    Type (max u v) :=
  HamiltonianSATEnergyProducer Clause Var × SourceLawFinitePhysicalOutput

/-- Accepted extension surface.

The two components are deliberately independent inputs; the theorem below
proves that accepting both surfaces collapses the package to one canonical
pair. -/
def HamiltonianSATDiagonalExtensionSurface
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (P : HamiltonianSATEnergyProducer Clause Var)
    (O : SourceLawFinitePhysicalOutput) : Prop :=
  HamiltonianSATEnergyProducerSurface P ∧
    EnergyInformationMathematicsPhysicsDiagonalSurface O

/-- THEOREM 1: the extension surface is exactly the canonical shared producer
paired with the canonical four-face diagonal output. -/
theorem hamiltonianSATDiagonalExtensionSurface_iff_canonical
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (P : HamiltonianSATEnergyProducer Clause Var)
    (O : SourceLawFinitePhysicalOutput) :
    HamiltonianSATDiagonalExtensionSurface P O ↔
      P = canonicalHamiltonianSATEnergyProducer Clause Var ∧
        O = canonicalSourceLawFinitePhysicalOutput := by
  constructor
  · intro h
    constructor
    · exact
        (hamiltonianSATEnergyProducerSurface_iff_canonical P).1 h.1
    · exact
        (energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
          O).1 h.2
  · intro h
    constructor
    · rw [h.1]
      exact canonicalHamiltonianSATEnergyProducer_surface Clause Var
    · rw [h.2]
      exact
        (energyInformationMathematicsPhysicsDiagonalSurface_iff_canonical
          canonicalSourceLawFinitePhysicalOutput).2 rfl

/-- THEOREM 2: the canonical pair lies on the extension surface. -/
theorem canonicalHamiltonianSATDiagonalExtensionSurface
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    HamiltonianSATDiagonalExtensionSurface
      (canonicalHamiltonianSATEnergyProducer Clause Var)
      canonicalSourceLawFinitePhysicalOutput := by
  exact
    (hamiltonianSATDiagonalExtensionSurface_iff_canonical
      (canonicalHamiltonianSATEnergyProducer Clause Var)
      canonicalSourceLawFinitePhysicalOutput).2
      ⟨rfl, rfl⟩

/-- Any two accepted extension packages have the same producer and the same
diagonal output. -/
theorem hamiltonianSATDiagonalExtensionSurface_noFree
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (P Q : HamiltonianSATEnergyProducer Clause Var)
    (O R : SourceLawFinitePhysicalOutput)
    (hPO : HamiltonianSATDiagonalExtensionSurface P O)
    (hQR : HamiltonianSATDiagonalExtensionSurface Q R) :
    P = Q ∧ O = R := by
  have hPOc :=
    (hamiltonianSATDiagonalExtensionSurface_iff_canonical P O).1 hPO
  have hQRc :=
    (hamiltonianSATDiagonalExtensionSurface_iff_canonical Q R).1 hQR
  constructor
  · rw [hPOc.1, hQRc.1]
  · rw [hPOc.2, hQRc.2]

/-! ## The extension subtype is a unit object -/

/-- The subtype of accepted shared-energy-to-diagonal packages. -/
def HamiltonianSATDiagonalExtensionSubtype
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    Type (max u v) :=
  { X : HamiltonianSATDiagonalExtensionPair Clause Var //
    HamiltonianSATDiagonalExtensionSurface X.1 X.2 }

/-- The canonical accepted package. -/
def canonicalHamiltonianSATDiagonalExtensionSubtype
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    HamiltonianSATDiagonalExtensionSubtype Clause Var :=
  ⟨(canonicalHamiltonianSATEnergyProducer Clause Var,
      canonicalSourceLawFinitePhysicalOutput),
    canonicalHamiltonianSATDiagonalExtensionSurface Clause Var⟩

/-- THEOREM 3: every accepted package is the canonical package. -/
theorem hamiltonianSATDiagonalExtensionSubtype_eq_canonical
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (X : HamiltonianSATDiagonalExtensionSubtype Clause Var) :
    X = canonicalHamiltonianSATDiagonalExtensionSubtype Clause Var := by
  cases X with
  | mk pair hpair =>
      cases pair with
      | mk P O =>
          apply Subtype.ext
          have hc :=
            (hamiltonianSATDiagonalExtensionSurface_iff_canonical P O).1
              hpair
          exact Prod.ext hc.1 hc.2

/-- THEOREM 4: the extension subtype is a subsingleton. -/
theorem hamiltonianSATDiagonalExtensionSubtype_subsingleton
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    Subsingleton (HamiltonianSATDiagonalExtensionSubtype Clause Var) := by
  refine ⟨?_⟩
  intro X Y
  rw [hamiltonianSATDiagonalExtensionSubtype_eq_canonical X,
    hamiltonianSATDiagonalExtensionSubtype_eq_canonical Y]

/-- THEOREM 5: the extension subtype is equivalent to `Unit`. -/
def hamiltonianSATDiagonalExtensionSubtypeEquivUnit
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    HamiltonianSATDiagonalExtensionSubtype Clause Var ≃ Unit where
  toFun _ := ()
  invFun _ := canonicalHamiltonianSATDiagonalExtensionSubtype Clause Var
  left_inv := by
    intro X
    exact
      (hamiltonianSATDiagonalExtensionSubtype_eq_canonical X).symm
  right_inv := by
    intro x
    cases x
    rfl

/-- THEOREM 6: every indexed family of accepted extension packages is
constant. -/
theorem hamiltonianSATDiagonalExtensionSubtypeFamily_eq_constant
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    {ι : Type w}
    (F : ι -> HamiltonianSATDiagonalExtensionSubtype Clause Var) :
    F = fun _ => canonicalHamiltonianSATDiagonalExtensionSubtype Clause Var := by
  funext i
  exact hamiltonianSATDiagonalExtensionSubtype_eq_canonical (F i)

/-- THEOREM 7: every endomorphism of the extension subtype is the identity. -/
theorem hamiltonianSATDiagonalExtensionEndomorphism_eq_id
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (f : HamiltonianSATDiagonalExtensionSubtype Clause Var ->
      HamiltonianSATDiagonalExtensionSubtype Clause Var) :
    f =
      (id : HamiltonianSATDiagonalExtensionSubtype Clause Var ->
        HamiltonianSATDiagonalExtensionSubtype Clause Var) := by
  funext X
  rw [hamiltonianSATDiagonalExtensionSubtype_eq_canonical (f X),
    hamiltonianSATDiagonalExtensionSubtype_eq_canonical X]
  rfl

/-! ## Packaged certificate -/

/-- P704 local certificate: the shared Hamiltonian/SAT scalar producer has a
unique extension to the four-face finite diagonal. -/
structure HamiltonianSATEnergyDiagonalExtensionCertificate
    (Clause : Type u) (Var : Type v) [Fintype Clause] where
  p703_same_carrier_energy :
    HamiltonianSATEnergySameCarrierCertificate.{u, v}
  extension_surface_iff_canonical :
    ∀ (P : HamiltonianSATEnergyProducer Clause Var)
      (O : SourceLawFinitePhysicalOutput),
      HamiltonianSATDiagonalExtensionSurface P O ↔
        P = canonicalHamiltonianSATEnergyProducer Clause Var ∧
          O = canonicalSourceLawFinitePhysicalOutput
  canonical_extension_surface :
    HamiltonianSATDiagonalExtensionSurface
      (canonicalHamiltonianSATEnergyProducer Clause Var)
      canonicalSourceLawFinitePhysicalOutput
  extension_surface_no_free :
    ∀ (P Q : HamiltonianSATEnergyProducer Clause Var)
      (O R : SourceLawFinitePhysicalOutput),
      HamiltonianSATDiagonalExtensionSurface P O ->
      HamiltonianSATDiagonalExtensionSurface Q R ->
        P = Q ∧ O = R
  extension_subtype_equiv_unit :
    HamiltonianSATDiagonalExtensionSubtype Clause Var ≃ Unit
  every_extension_eq_canonical :
    ∀ X : HamiltonianSATDiagonalExtensionSubtype Clause Var,
      X = canonicalHamiltonianSATDiagonalExtensionSubtype Clause Var
  extension_family_constant :
    ∀ {ι : Type u}
      (F : ι -> HamiltonianSATDiagonalExtensionSubtype Clause Var),
      F = fun _ => canonicalHamiltonianSATDiagonalExtensionSubtype Clause Var
  extension_endomorphism_identity :
    ∀ f : HamiltonianSATDiagonalExtensionSubtype Clause Var ->
      HamiltonianSATDiagonalExtensionSubtype Clause Var,
      f =
        (id : HamiltonianSATDiagonalExtensionSubtype Clause Var ->
          HamiltonianSATDiagonalExtensionSubtype Clause Var)

/-- THEOREM 8: the P704 local extension certificate is inhabited. -/
def hamiltonianSATEnergyDiagonalExtensionCertificate
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    HamiltonianSATEnergyDiagonalExtensionCertificate Clause Var where
  p703_same_carrier_energy := hamiltonianSATEnergySameCarrierCertificate
  extension_surface_iff_canonical := by
    intro P O
    exact hamiltonianSATDiagonalExtensionSurface_iff_canonical P O
  canonical_extension_surface :=
    canonicalHamiltonianSATDiagonalExtensionSurface Clause Var
  extension_surface_no_free := by
    intro P Q O R hPO hQR
    exact hamiltonianSATDiagonalExtensionSurface_noFree P Q O R hPO hQR
  extension_subtype_equiv_unit :=
    hamiltonianSATDiagonalExtensionSubtypeEquivUnit Clause Var
  every_extension_eq_canonical := by
    intro X
    exact hamiltonianSATDiagonalExtensionSubtype_eq_canonical X
  extension_family_constant := by
    intro ι F
    exact hamiltonianSATDiagonalExtensionSubtypeFamily_eq_constant F
  extension_endomorphism_identity := by
    intro f
    exact hamiltonianSATDiagonalExtensionEndomorphism_eq_id f

/-! ## Root packaging -/

/-- P704 root: P703 same-carrier energy plus P702 four-face diagonal collapse
to one unit extension package.

This root lives entirely on the finite residual/source-law interface.  It does
not need an additional Hilbert carrier parameter: the P703 same-carrier theorem
is already part of the local extension certificate. -/
structure HamiltonianSATEnergyDiagonalExtensionUnifiedRootCertificate
    (Clause : Type u) (Var : Type v) [Fintype Clause] where
  p704_extension :
    HamiltonianSATEnergyDiagonalExtensionCertificate Clause Var

/-- THEOREM 9: the P704 grand root is inhabited. -/
def hamiltonianSATEnergyDiagonalExtensionUnifiedRootCertificate
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    HamiltonianSATEnergyDiagonalExtensionUnifiedRootCertificate Clause Var where
  p704_extension :=
    hamiltonianSATEnergyDiagonalExtensionCertificate Clause Var

end GrandUnification
end SaturationMonoid
