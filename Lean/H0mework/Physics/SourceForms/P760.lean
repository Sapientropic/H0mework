import H0mework.Physics.JointSources.P744
import H0mework.Computation.Phase.P759

/-!
# Proposition 760: producer closure as canonical-surface consequence

P759 locked the three requested producer nails:

* natural-coded even obstruction is killed exactly by the prime-pair residual
  transport / zero fixed-point producer;
* the finite `alpha_s` source surface emits the inverse residual
  `-89000/128511`;
* the SU(7) primitive representation plus endpoint/consolidation ordering
  forces the nine Yukawa depths and the CKM/Jarlskog depth seed.

This file removes the remaining bookkeeping looseness.  The P759 producers are
not merely three fields packaged next to P758.  Lean checks that:

* the P759 natural-coded obstruction killer uses exactly the same abstract
  Goldbach residual bridge as P758's residual carrier;
* the `alpha_s`, Yukawa, and CKM producer values agree with the canonical P710
  three-nail package;
* any P744 residual-split strengthened three-nail surface reads out those same
  producer values.

So the current finite layer is:

`residual split -> faithful transport -> canonical three-nail surface -> producer closure`.
-/

noncomputable section

namespace SaturationMonoid

namespace GrandUnification

open AffineRelaxation
open ComplexityProjection
open StandardModelConstraint

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z q u1 u2 u3 u4 u5 u6

/-! ## P759 producers read through the P710/P744 canonical surface -/

/-- The P759 obstruction-killer bridge and P758 residual-carrier bridge are the
same P757 Goldbach abstract residual bridge.  Naming the proposition keeps the
P760 root from duplicating the hidden universe bookkeeping in the field type. -/
def ProducerClosureGoldbachBridgeSameAsResidualCarrier
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop :=
  (producerClosureTheorem.{u, u1, u2, u3, u4, u5, u6} (E := E)).natural_coded_even_obstruction_killer.p757_abstract_bridge =
    (producerClosureTheorem.{u, u1, u2, u3, u4, u5, u6} (E := E)).residual_carrier.layer3_goldbach_trace_energy_fixed_producer.abstract_bridge

/-- THEOREM 1: the P759 obstruction killer and the P758 residual carrier point
to the same P757 Goldbach abstract residual bridge. -/
theorem producerClosure_goldbachBridge_eq_residualCarrierBridge
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    ProducerClosureGoldbachBridgeSameAsResidualCarrier E := by
  rfl

/-- THEOREM 2: the finite `alpha_s` producer output is the same number read
from the canonical P710 three-nail package. -/
theorem alphaStrongProducer_inverseResidual_eq_canonicalSurface
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.alphaInverseResidual) := by
  calc
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
        -((89000 : ℚ) / 128511) :=
      alphaStrongIndependentResidualProducerCertificate.inverse_residual
    _ =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.alphaInverseResidual) := by
      rfl

/-- THEOREM 3: the canonical P710 three-nail package reads the same
`alpha_s` inverse residual. -/
theorem canonicalSurface_alphaInverseResidual
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.alphaInverseResidual) =
      -((89000 : ℚ) / 128511) := by
  rfl

/-- THEOREM 4: the SU(7) active-source normal form used by the producer is
exactly the active-source normal form exposed on the coordinate-spine package. -/
theorem alphaStrongProducer_activeSource_iff_su7 :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongActiveResidualSource
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
        s = .su7Breaking :=
  alphaStrongIndependentResidualProducerCertificate.active_source_iff_su7

/-- THEOREM 5: the SU(7) Yukawa producer's nine-depth table is the same list
read from the canonical P710 three-nail package. -/
theorem yukawaProducer_depths_eq_canonicalSurface
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    selectedYukawaDepthTableCandidate.massOrder.map (fun n : ℕ => (n : ℚ)) =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.yukawaMassOrder) := by
  calc
    selectedYukawaDepthTableCandidate.massOrder.map (fun n : ℕ => (n : ℚ)) =
        ([50, 346, 372, 489, 583, 682, 880, 908, 982] : List ℕ).map
          (fun n : ℕ => (n : ℚ)) := by
      rw [su7YukawaCKMProducerCertificate.nine_depths]
    _ = ([50, 346, 372, 489, 583, 682, 880, 908, 982] : List ℚ) := by
      norm_num
    _ =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.yukawaMassOrder) := by
      rfl

/-- THEOREM 6: the canonical P710 three-nail package reads the same nine
Yukawa depths. -/
theorem canonicalSurface_yukawaMassOrder
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.yukawaMassOrder) =
      ([50, 346, 372, 489, 583, 682, 880, 908, 982] : List ℚ) := by
  rfl

/-- THEOREM 7: the SU(7) CKM/Jarlskog producer's depth sum is the same value
read from the canonical P710 three-nail package. -/
theorem ckmProducer_depthSum_eq_canonicalSurface
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    (ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate : ℚ) =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.ckmDepthSum) := by
  have hInt :
      ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate =
        (ckmCPDepthSum : Int) :=
    su7YukawaCKMProducerCertificate.ckm_depth_sum
  calc
    (ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate : ℚ) =
        (ckmCPDepthSum : ℚ) := by
      exact_mod_cast hInt
    _ = (386 : ℚ) := by
      norm_num [ckmCPDepthSum]
    _ =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.ckmDepthSum) := by
      rfl

/-- THEOREM 8: the canonical P710 three-nail package reads CKM/Jarlskog depth
sum `386`. -/
theorem canonicalSurface_ckmDepthSum
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.ckmDepthSum) =
      (386 : ℚ) := by
  rfl

/-- THEOREM 9: any P744 residual-split strengthened surface carries the same
three producer values. -/
theorem residualSplitSurface_producerValues
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace)
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var)
    (hX : HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
      F R X) :
    X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
      X.2.2.yukawaMassOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
      X.2.2.ckmDepthSum = (386 : ℚ) := by
  have h := residualSplitProducerNailSurface_threeNails F R X hX
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## Root certificate -/

/-- P760 root: P759 producer closure is a consequence of the same residual
carrier and the same rigid canonical three-nail surface, not a parallel list of
targets. -/
structure ProducerClosureCanonicalSurfaceConsequenceTheorem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] where
  goldbach_bridge_same_as_residual_carrier :
    ProducerClosureGoldbachBridgeSameAsResidualCarrier.{u, u1, u2, u3, u4, u5, u6} E
  canonical_surface_forall_iff :
    ∀ R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E,
      ∀ Q : HamiltonianSATPhysicalProducerPair Clause Var -> Prop,
        (∀ P : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailSurface R P -> Q P) ↔
          Q (canonicalHamiltonianSATPhysicalProducerPair Clause Var)
  residual_split_surface_iff_canonical :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E,
        ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
              F R X ↔
            X = canonicalHamiltonianSATPhysicalProducerPair Clause Var
  natural_killer_iff_fixed_point :
    Nonempty NaturalCodedEvenObstructionPrimePairTransportKiller ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  alpha_producer_matches_canonical_surface :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.alphaInverseResidual)
  alpha_active_source_iff_su7 :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongActiveResidualSource
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
        s = .su7Breaking
  yukawa_producer_matches_canonical_surface :
    selectedYukawaDepthTableCandidate.massOrder.map (fun n : ℕ => (n : ℚ)) =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.yukawaMassOrder)
  ckm_producer_matches_canonical_surface :
    (ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate : ℚ) =
      ((canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.ckmDepthSum)
  residual_split_surface_outputs :
    ∀ F : FaceLocalStructuralUpdateObserverFamily GrandUnifiedProjectionFace,
      ∀ R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E,
        ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailResidualSplitSurface
              F R X ->
            X.2.2.alphaInverseResidual =
                -((89000 : ℚ) / 128511) ∧
              X.2.2.yukawaMassOrder =
                [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
              X.2.2.ckmDepthSum = (386 : ℚ)

/-- THEOREM 10: canonical P760 root. -/
def producerClosureCanonicalSurfaceConsequenceTheorem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    ProducerClosureCanonicalSurfaceConsequenceTheorem E Clause Var where
  goldbach_bridge_same_as_residual_carrier :=
    producerClosure_goldbachBridge_eq_residualCarrierBridge (E := E)
  canonical_surface_forall_iff := by
    intro R Q
    exact hamiltonianSATCoordinateSpineProducerNailSurface_forall_iff_canonical
      R Q
  residual_split_surface_iff_canonical := by
    intro F R X
    exact
      hamiltonianSATCoordinateSpineProducerNailResidualSplitSurface_iff_canonical
        F R X
  natural_killer_iff_fixed_point :=
    naturalCodedEvenObstructionKiller_iff_fixedPoint
  alpha_producer_matches_canonical_surface :=
    alphaStrongProducer_inverseResidual_eq_canonicalSurface Clause Var
  alpha_active_source_iff_su7 :=
    alphaStrongProducer_activeSource_iff_su7
  yukawa_producer_matches_canonical_surface :=
    yukawaProducer_depths_eq_canonicalSurface Clause Var
  ckm_producer_matches_canonical_surface :=
    ckmProducer_depthSum_eq_canonicalSurface Clause Var
  residual_split_surface_outputs := by
    intro F R X hX
    exact residualSplitSurface_producerValues F R X hX

end GrandUnification

end SaturationMonoid
