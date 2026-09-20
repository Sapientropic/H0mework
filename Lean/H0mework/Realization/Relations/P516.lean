import H0mework.Arithmetic.PrimeShadow.P329
import H0mework.Physics.SourceContracts.P429
import H0mework.Realization.Relations.P515

/-!
# Proposition 516: producer front door for the unified projection core

P515 bundles the current physical/mathematical projection core.  Its honest
boundary is that it still speaks at the projection level: the physical side
needs a strict matrix/geometry producer, and the arithmetic/spectral side needs
a concrete admissible prime-shadow bridge.

This file makes that front door a single Lean object.  If the two producers are
supplied, the current root projection core, the strict physical holy-grail
output, the admissible Goldbach/H¹ synchronization, the H-space FTA boundary,
and the finite pointwise Goldbach search surface all descend together.

Boundary: this still does not construct the physical producer or the
prime-shadow producer.  It closes the interface from those producer obligations
to the already formalized grand-unification projection core.
-/

noncomputable section

namespace SaturationMonoid

open AffineRelaxation
open AffineRelaxation.GeometryConnection
open StandardModelConstraint

/-! ## A single producer front door -/

/-- The two genuinely remaining producer inputs, kept independent:

* a strict physical matrix/RG + physical-geometry producer;
* a concrete admissible Euler prime-shadow bridge synchronizing the arithmetic
  and H¹ spectral projections on the arithmetic-admissible domain. -/
structure UnifiedGrandProducerFrontDoor
    (Index A CKMCarrier PhysicalGeometry : Type*) [AddCommGroup A]
    (P : AffineRelaxation.EulerPrimeCouplingProducers) where
  adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry
  physical :
    ExistsStrictPhysicalMatrixUnifiedProducer
      Index A CKMCarrier PhysicalGeometry
  prime_shadow :
    AffineRelaxation.ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P

/-- The current output forced by the unified producer front door.

The object deliberately carries both faces:

* the root P515 projection-core certificate;
* the strict physical holy-grail output surface from P429;
* the admissible arithmetic/spectral synchronization from P325;
* the H-space FTA boundary and pointwise Goldbach search surfaces from
  P327/P329 at the self-dual half-sigma slice. -/
structure UnifiedGrandProducerOutput
    (Index A CKMCarrier : Type*) [AddCommGroup A]
    (P : AffineRelaxation.EulerPrimeCouplingProducers) where
  projection_core :
    FinitePhysicsMathematicsUnificationProjectionCoreCertificate
  physical_output :
    ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
      SingleSourceHolyGrailReceiptStatement O.receipt ∧
        Nonempty
          (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
        Function.Surjective yukawaPoincareSlot ∧
        IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (ParameterVector ℝ) ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (YukawaMatrixSubvector ℝ) ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (NonYukawaSubvector ℝ) ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (YukawaMatrixSubvector ℝ × NonYukawaSubvector ℝ) ∧
        (∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
          parameterVectorComponentsEquiv ℝ
              (AffineRelaxation.relaxModule target sigma x) =
            AffineRelaxation.relaxModule
              (parameterVectorComponentsEquiv ℝ target)
              sigma
              (parameterVectorComponentsEquiv ℝ x))
  admissible_goldbach_h1_sync :
    ∀ x : AffineRelaxation.ArithmeticAdmissibleSevenFacet,
      AffineRelaxation.HalfSigmaRateGoldbachComplete x.val.rate ↔
        AffineRelaxation.H1SpectralNoObstructionComplete x.spectral
  half_sigma_fta_boundary :
    AffineRelaxation.HeadroomFtaBoundaryCertificate
      (1 / 2 : ℝ)
      AffineRelaxation.halfSigma_mem_Ioo.1
      AffineRelaxation.halfSigma_mem_Ioo.2
  half_sigma_pointwise_search :
    AffineRelaxation.P329HeadroomGoldbachSearchCertificate
      (1 / 2 : ℝ)
      AffineRelaxation.halfSigma_mem_Ioo.1
      AffineRelaxation.halfSigma_mem_Ioo.2

/-! ## Front-door theorem -/

/-- DEFINITION/THEOREM: the unified producer front door supplies the full current
physical/mathematical projection-core output.

This is the root "producer obligations imply current grand-unification core"
statement.  It keeps the real debts visible while removing all downstream
wrapper ambiguity. -/
def unifiedGrandProducerOutput_of_frontDoor
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    {P : AffineRelaxation.EulerPrimeCouplingProducers}
    (F : UnifiedGrandProducerFrontDoor
      Index A CKMCarrier PhysicalGeometry P) :
    UnifiedGrandProducerOutput Index A CKMCarrier P where
  projection_core :=
    finitePhysicsMathematicsUnificationProjectionCoreCertificate
  physical_output :=
    strictPhysicalMatrixUnified_concrete_holy_grail_output
      F.adapter F.physical
  admissible_goldbach_h1_sync := by
    intro x
    exact F.prime_shadow.rateGoldbach_iff_h1_no_obstruction x
  half_sigma_fta_boundary :=
    AffineRelaxation.headroomFtaBoundaryCertificate
      (1 / 2 : ℝ)
      AffineRelaxation.halfSigma_mem_Ioo.1
      AffineRelaxation.halfSigma_mem_Ioo.2
  half_sigma_pointwise_search :=
    AffineRelaxation.p329HeadroomGoldbachSearchCertificate
      AffineRelaxation.halfSigma_mem_Ioo.1
      AffineRelaxation.halfSigma_mem_Ioo.2

end SaturationMonoid
