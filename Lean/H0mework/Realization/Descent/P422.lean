import H0mework.Physics.JointSources.P421

/-!
# Proposition 422: current formal Poincare interface collapse

P421 reduces the concrete Standard-Model holy-grail front door to:

* an atom-native explicit nine-row sigma RG table;
* a 4D Poincare generation-slot geometry certificate.

This file audits the second item.  The current P280 geometry interface is an
abstract Poincare-duality cohomology certificate, not a smooth manifold
producer.  At that level it is already inhabited by a canonical degree-orbit
normal form: degrees `0/4`, `1/3`, and `2` are three arbitrary carriers, while
degrees above `4` are trivial.

That is an important tightening, not a physical derivation.  It proves that
the present formal holy-grail front door collapses to the nine-row table under
the current weak geometry interface, and therefore the real remaining geometry
debt must be strengthened to a smooth/de Rham/Poincare producer if the roadmap
wants a physical spacetime theorem rather than an abstract slot certificate.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

/-! ## Orbit-normal-form cohomology for the current certificate interface -/

/-- A 4D Poincare degree-orbit normal form: one carrier for `0/4`, one for
`1/3`, and one self-dual middle carrier for `2`. -/
structure FourDimensionalPoincareOrbitCohomologyNormalForm where
  h04 : Type
  h13 : Type
  h2 : Type

namespace FourDimensionalPoincareOrbitCohomologyNormalForm

/-- Cohomology carrier induced by the three Poincare degree orbits.  Degrees
above `4` are deliberately trivial because P280's certificate only needs
above-top subsingleton data there. -/
def cohomology (N : FourDimensionalPoincareOrbitCohomologyNormalForm) :
    ℕ -> Type
  | 0 => N.h04
  | 1 => N.h13
  | 2 => N.h2
  | 3 => N.h13
  | 4 => N.h04
  | _ + 5 => PUnit

/-- THEOREM 1: the orbit normal form supplies P280's abstract 4D Poincare
duality cohomology certificate. -/
def toPoincareDualityCohomologyCertificate
    (N : FourDimensionalPoincareOrbitCohomologyNormalForm) :
    PoincareDualityCohomologyCertificate 4 where
  cohomology := N.cohomology
  duality := by
    intro k hk
    interval_cases k
    · exact Equiv.refl N.h04
    · exact Equiv.refl N.h13
    · exact Equiv.refl N.h2
    · exact Equiv.refl N.h13
    · exact Equiv.refl N.h04
  above_top_subsingleton := by
    intro k hk
    have hk' : ∃ n, k = n + 5 := by
      use k - 5
      omega
    rcases hk' with ⟨n, rfl⟩
    change Subsingleton PUnit
    exact inferInstance

/-- The degenerate unit orbit normal form.  This is useful as an audit witness:
it inhabits the current abstract interface, but it is not a smooth physical
spacetime model. -/
def unitOrbitNormalForm : FourDimensionalPoincareOrbitCohomologyNormalForm where
  h04 := PUnit
  h13 := PUnit
  h2 := PUnit

/-- THEOREM 2: the current abstract 4D Poincare generation-slot certificate is
formally inhabited.  This is a weakness audit of the current interface, not a
physical Poincare-duality theorem for manifolds. -/
def currentFormalFourDimensionalPoincareGenerationSlotCertificate :
    FourDimensionalPoincareGenerationSlotCertificate where
  geometry := unitOrbitNormalForm.toPoincareDualityCohomologyCertificate

theorem currentFormalFourDimensionalPoincareGenerationSlotCertificate_nonempty :
    Nonempty FourDimensionalPoincareGenerationSlotCertificate :=
  ⟨currentFormalFourDimensionalPoincareGenerationSlotCertificate⟩

end FourDimensionalPoincareOrbitCohomologyNormalForm

end GeometryConnection
end AffineRelaxation

namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Collapse of the current formal front door -/

/-- THEOREM 3: under the current abstract geometry interface, the P421 front
door is equivalent to the atom-native nine-row sigma RG table alone. -/
theorem atomNativeNineRowPoincareGeometry_nonempty_iff_nineRow_under_currentFormalGeometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsAtomNativeNineRowPoincareGeometryProducer Index A CKMCarrier ↔
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  constructor
  · exact And.left
  · intro htable
    exact
      ⟨htable,
        FourDimensionalPoincareOrbitCohomologyNormalForm.currentFormalFourDimensionalPoincareGenerationSlotCertificate_nonempty⟩

/-- THEOREM 4: current-formal holy-grail normal form.  With P280's abstract
geometry interface, the concrete Poincare-resolved Standard-Model surface is
equivalent to the atom-native nine-row sigma table.  The theorem name keeps the
`currentFormalGeometry` qualifier because this does not construct physical
smooth spacetime geometry. -/
theorem standardModelPoincareResolved_nonempty_iff_nineRow_under_currentFormalGeometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  exact
    standardModelPoincareResolved_nonempty_iff_atomNativeNineRow_and_geometry.trans
      atomNativeNineRowPoincareGeometry_nonempty_iff_nineRow_under_currentFormalGeometry

/-- THEOREM 5: compact citation form for the current formal interface.  A
nine-row table alone yields the concrete holy-grail output package because the
current abstract geometry interface has a canonical formal inhabitant. -/
theorem nineRow_currentFormalGeometry_concrete_holy_grail_output
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer Index A CKMCarrier ->
      ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
        SingleSourceHolyGrailReceiptStatement O.receipt ∧
          Nonempty
            (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
          Function.Surjective yukawaPoincareSlot ∧
          IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) := by
  intro htable
  exact
    atomNativeNineRow_and_geometry_concrete_holy_grail_output
      ((atomNativeNineRowPoincareGeometry_nonempty_iff_nineRow_under_currentFormalGeometry).mpr
        htable)

end StandardModelConstraint
end SaturationMonoid
