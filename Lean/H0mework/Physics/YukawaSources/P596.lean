import Mathlib.Tactic
import H0mework.Physics.JointSources.P595

/-!
# Proposition 596: singleton coefficient surface for the Yukawa producer

P594 proved that the carrier-source equations pick out one coefficient vector.
P595 proved the reverse finite statement: selected-depth closure along an
endpoint-preserving SU(7) sector schedule forces those source equations.

This file packages the consequence that matters for producer debt: at the
finite coefficient layer, both accepted surfaces are singletons.

* the source-equation surface has no continuous/free coefficient parameter;
* for any sector schedule, the selected-depth closure surface has no
  continuous/free coefficient parameter;
* if the schedule is endpoint-preserving, the accepted point is exactly the
  carrier-sourced coefficient vector.

Boundary: this still does not derive the source equations from dynamical SU(7)
breaking or consolidation ordering.  It proves that once that producer hits the
source-equation interface, no additional continuous coefficient freedom remains.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Accepted coefficient surfaces -/

/-- A coefficient surface has no continuous/free parameter, in the strong
singleton sense: any two accepted coefficient vectors are equal. -/
def NoContinuousFreeYukawaCoefficientParameters
    (constraints : YukawaDepthStencilCoefficientVector -> Prop) : Prop :=
  ∀ C D : YukawaDepthStencilCoefficientVector,
    constraints C -> constraints D -> C = D

/-- The finite accepted surface for a chosen sector schedule: coefficients
close the selected nine-depth grid along that schedule. -/
def YukawaCoefficientAcceptedSurface
    (f : YukawaInteractionSector -> InformationSlot)
    (C : YukawaDepthStencilCoefficientVector) : Prop :=
  EndpointScheduleSelectedDepthClosure C f

/-! ## Source-equation surface is a singleton -/

/-- THEOREM 1: the carrier-source equation surface is a singleton. -/
theorem yukawaSourceEquationSurface_singleton :
    YukawaCoefficientCarrierSourceEquations
        carrierSourcedYukawaDepthStencilCoefficientVector ∧
      ∀ C : YukawaDepthStencilCoefficientVector,
        YukawaCoefficientCarrierSourceEquations C ->
          C = carrierSourcedYukawaDepthStencilCoefficientVector := by
  exact ⟨carrierSourcedYukawaDepthStencilCoefficientVector_sourceEquations,
    eq_carrierSourced_of_sourceEquations⟩

/-- THEOREM 2: the carrier-source equation surface has no continuous/free
coefficient parameter. -/
theorem yukawaSourceEquationSurface_noContinuousFree :
    NoContinuousFreeYukawaCoefficientParameters
      YukawaCoefficientCarrierSourceEquations := by
  intro C D hC hD
  rw [eq_carrierSourced_of_sourceEquations C hC,
    eq_carrierSourced_of_sourceEquations D hD]

/-! ## Selected-depth closure surface is the same singleton -/

/-- THEOREM 3: any accepted coefficient vector on a schedule is the
carrier-sourced vector. -/
theorem yukawaAcceptedCoefficient_eq_carrierSourced
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot)
    (hC : YukawaCoefficientAcceptedSurface f C) :
    C = carrierSourcedYukawaDepthStencilCoefficientVector :=
  eq_carrierSourced_of_endpointSchedule_reproduces_selectedDepth
    C f hC.1 hC.2

/-- THEOREM 4: for any schedule, the accepted selected-depth closure surface
has no continuous/free coefficient parameter. -/
theorem yukawaAcceptedSurface_noContinuousFree
    (f : YukawaInteractionSector -> InformationSlot) :
    NoContinuousFreeYukawaCoefficientParameters
      (YukawaCoefficientAcceptedSurface f) := by
  intro C D hC hD
  rw [yukawaAcceptedCoefficient_eq_carrierSourced C f hC,
    yukawaAcceptedCoefficient_eq_carrierSourced D f hD]

/-- THEOREM 5: if the schedule is endpoint-preserving, the accepted surface is
inhabited by exactly the carrier-sourced coefficient vector. -/
theorem yukawaAcceptedSurface_singleton
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    YukawaCoefficientAcceptedSurface
        f carrierSourcedYukawaDepthStencilCoefficientVector ∧
      ∀ C : YukawaDepthStencilCoefficientVector,
        YukawaCoefficientAcceptedSurface f C ->
          C = carrierSourcedYukawaDepthStencilCoefficientVector := by
  exact
    ⟨⟨hf, fun y =>
        coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
          carrierSourcedYukawaDepthStencilCoefficientVector
          carrierSourcedYukawaDepthStencilCoefficientVector_sourceEquations
          f hf y⟩,
      fun C hC => yukawaAcceptedCoefficient_eq_carrierSourced C f hC⟩

/-! ## Iff form -/

/-- THEOREM 6: accepted selected-depth closure is exactly endpoint preservation
plus carrier-source equations. -/
theorem yukawaAcceptedSurface_iff_sourceEquations
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot) :
    YukawaCoefficientAcceptedSurface f C ↔
      YukawaSectorEndpointSignaturePreservingSchedule f ∧
        YukawaCoefficientCarrierSourceEquations C :=
  endpointScheduleSelectedDepthClosure_iff C f

/-- THEOREM 7: along a known endpoint-preserving schedule, accepted closure is
equivalent to source equations alone. -/
theorem yukawaAcceptedSurface_iff_sourceEquations_of_endpointPreserving
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    YukawaCoefficientAcceptedSurface f C ↔
      YukawaCoefficientCarrierSourceEquations C := by
  constructor
  · intro hC
    exact (yukawaAcceptedSurface_iff_sourceEquations C f).mp hC |>.2
  · intro hsrc
    exact (yukawaAcceptedSurface_iff_sourceEquations C f).mpr
      ⟨hf, hsrc⟩

/-! ## Bundled receipt -/

/-- Compact receipt: the finite Yukawa coefficient producer surface is a
singleton/no-free surface, both in source-equation form and in selected-depth
closure form. -/
structure YukawaCoefficientSingletonSurfaceReceipt where
  source_surface_singleton :
    YukawaCoefficientCarrierSourceEquations
        carrierSourcedYukawaDepthStencilCoefficientVector ∧
      ∀ C : YukawaDepthStencilCoefficientVector,
        YukawaCoefficientCarrierSourceEquations C ->
          C = carrierSourcedYukawaDepthStencilCoefficientVector
  source_surface_no_free :
    NoContinuousFreeYukawaCoefficientParameters
      YukawaCoefficientCarrierSourceEquations
  accepted_surface_no_free :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      NoContinuousFreeYukawaCoefficientParameters
        (YukawaCoefficientAcceptedSurface f)
  accepted_surface_singleton :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      YukawaSectorEndpointSignaturePreservingSchedule f ->
        YukawaCoefficientAcceptedSurface
            f carrierSourcedYukawaDepthStencilCoefficientVector ∧
          ∀ C : YukawaDepthStencilCoefficientVector,
            YukawaCoefficientAcceptedSurface f C ->
              C = carrierSourcedYukawaDepthStencilCoefficientVector
  accepted_surface_iff :
    ∀ C : YukawaDepthStencilCoefficientVector,
      ∀ f : YukawaInteractionSector -> InformationSlot,
        YukawaCoefficientAcceptedSurface f C ↔
          YukawaSectorEndpointSignaturePreservingSchedule f ∧
            YukawaCoefficientCarrierSourceEquations C

/-- THEOREM 8: singleton/no-free receipt for the finite Yukawa coefficient
producer surface. -/
theorem yukawaCoefficientSingletonSurfaceReceipt :
    YukawaCoefficientSingletonSurfaceReceipt where
  source_surface_singleton := yukawaSourceEquationSurface_singleton
  source_surface_no_free := yukawaSourceEquationSurface_noContinuousFree
  accepted_surface_no_free := yukawaAcceptedSurface_noContinuousFree
  accepted_surface_singleton := yukawaAcceptedSurface_singleton
  accepted_surface_iff := yukawaAcceptedSurface_iff_sourceEquations

end StandardModelConstraint
end SaturationMonoid
