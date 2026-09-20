import H0mework.Realization.Descent.P422

/-!
# Proposition 423: strict physical Poincare front door

P422 audits the current abstract P280 geometry interface: it is already
inhabited by a formal degree-orbit normal form.  That is useful because it
prevents us from mistaking the weak certificate for a physical spacetime
producer.

This file makes the corrected front door explicit.  A future smooth/de Rham /
Poincare geometry construction is represented by an independent type
`PhysicalGeometry` plus an adapter into the current certificate interface.
The strict Standard-Model holy-grail front door is therefore:

* the atom-native nine-row sigma RG table;
* a nonempty physical geometry producer.

The adapter may forget the physical construction down to P280's current
certificate, so the strict front door still supplies the existing downstream
holy-grail output.  Conversely, if the physical producer type is empty, the
strict front door is empty even though P422's weak formal geometry certificate
is inhabited.  This is the Lean-side guardrail against treating the current
formal orbit model as a physical Poincare theorem.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

/-! ## Physical geometry adapters -/

/-- A concrete smooth/de Rham/Poincare geometry producer can be used by the
current finite Standard-Model track only after it is forgotten to P280's
`FourDimensionalPoincareGenerationSlotCertificate`.

The type `PhysicalGeometry` is intentionally independent of the current weak
certificate.  In a later physics-grade file it should be instantiated by a
real smooth/de Rham/Poincare construction, not by the orbit-normal-form audit
witness from P422. -/
structure PhysicalPoincareGeometryAdapter (PhysicalGeometry : Type*) where
  toCurrentCertificate :
    PhysicalGeometry -> FourDimensionalPoincareGenerationSlotCertificate

namespace PhysicalPoincareGeometryAdapter

/-- THEOREM 1: a nonempty physical geometry producer supplies the current
P280/P416 generation-slot certificate interface. -/
theorem supplies_current_certificate
    {PhysicalGeometry : Type*}
    (A : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    Nonempty PhysicalGeometry ->
      Nonempty FourDimensionalPoincareGenerationSlotCertificate := by
  rintro ⟨G⟩
  exact ⟨A.toCurrentCertificate G⟩

/-- THEOREM 2: P422's current formal certificate is weaker than physical
geometry production.  If the physical producer type is empty, the current weak
certificate can still be inhabited. -/
theorem current_formal_certificate_does_not_force_physical_producer
    {PhysicalGeometry : Type*} [IsEmpty PhysicalGeometry] :
    Nonempty FourDimensionalPoincareGenerationSlotCertificate ∧
      ¬ Nonempty PhysicalGeometry := by
  constructor
  · exact
      FourDimensionalPoincareOrbitCohomologyNormalForm.currentFormalFourDimensionalPoincareGenerationSlotCertificate_nonempty
  · rintro ⟨G⟩
    exact isEmptyElim G

end PhysicalPoincareGeometryAdapter

end GeometryConnection
end AffineRelaxation

namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Strict Standard-Model front door -/

/-- The strict physical front door after P422:

* P415's atom-native nine-row sigma RG table;
* an independent physical geometry producer that can be forgotten to the
  current Poincare generation-slot certificate.

This is deliberately stronger than P422's current-formal front door. -/
def ExistsStrictPhysicalNineRowPoincareProducer
    (Index A CKMCarrier PhysicalGeometry : Type*) [AddCommGroup A]
    (_adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) : Prop :=
  ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ∧
    Nonempty PhysicalGeometry

/-- THEOREM 3: the strict front door is exactly "nine-row table plus physical
geometry producer"; the adapter is used only to forget the physical producer
downstream, not to add an extra hidden assumption. -/
theorem strictPhysicalNineRowPoincare_nonempty_iff_nineRow_and_physical
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalNineRowPoincareProducer
        Index A CKMCarrier PhysicalGeometry adapter ↔
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ∧
        Nonempty PhysicalGeometry := by
  rfl

/-- THEOREM 4: a strict physical front door forgets to P421's current
atom-native nine-row + Poincare-certificate front door. -/
theorem strictPhysicalNineRowPoincare_supplies_current_frontDoor
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalNineRowPoincareProducer
        Index A CKMCarrier PhysicalGeometry adapter ->
      ExistsAtomNativeNineRowPoincareGeometryProducer
        Index A CKMCarrier := by
  rintro ⟨htable, hphysical⟩
  exact ⟨htable, adapter.supplies_current_certificate hphysical⟩

/-- THEOREM 5: the strict physical front door still supplies the full current
concrete holy-grail output package, by forgetting its physical geometry through
the adapter. -/
theorem strictPhysicalNineRowPoincare_concrete_holy_grail_output
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalNineRowPoincareProducer
        Index A CKMCarrier PhysicalGeometry adapter ->
      ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
        SingleSourceHolyGrailReceiptStatement O.receipt ∧
          Nonempty
            (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
          Function.Surjective yukawaPoincareSlot ∧
          IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) := by
  intro h
  exact
    atomNativeNineRow_and_geometry_concrete_holy_grail_output
      (strictPhysicalNineRowPoincare_supplies_current_frontDoor adapter h)

/-- THEOREM 6: if the physical geometry producer is empty, the strict front
door is empty, even though P422 has shown the current weak formal geometry
interface is inhabited. -/
theorem strictPhysicalNineRowPoincare_empty_without_physicalProducer
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry)
    [IsEmpty PhysicalGeometry] :
    ¬ ExistsStrictPhysicalNineRowPoincareProducer
        Index A CKMCarrier PhysicalGeometry adapter := by
  rintro ⟨_, hphysical⟩
  rcases hphysical with ⟨G⟩
  exact isEmptyElim G

end StandardModelConstraint
end SaturationMonoid
