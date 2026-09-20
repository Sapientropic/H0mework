/-
  Proposition 457: anomaly cancellation for the finite Standard-Model Weyl
  multiplet carrier.

  P456 opened the one-loop matter traces into the finite one-generation
  Weyl-multiplet carrier `(Q, uᶜ, dᶜ, L, eᶜ)`.  This file proves the next
  consistency constraint on that same carrier: the usual one-generation
  Standard-Model gauge/gravitational anomalies cancel.

  Boundary: this proves that the listed representation content is anomaly-free.
  It does not prove uniqueness of this content from SU(7), nor does it prove
  global anomaly statements beyond the four rational trace identities below.
-/

import H0mework.Physics.RepresentationSources.P456

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

namespace StandardModelWeylMultiplet

/-! ## Signed hypercharge data -/

/-- Signed hypercharge in left-handed notation:
`Q=1/6`, `uᶜ=-2/3`, `dᶜ=1/3`, `L=-1/2`, `eᶜ=1`. -/
def hypercharge : StandardModelWeylMultiplet -> ℚ
  | .quarkDoublet => 1 / 6
  | .upConjugate => -(2 / 3)
  | .downConjugate => 1 / 3
  | .leptonDoublet => -(1 / 2)
  | .electronConjugate => 1

/-- Multiplicity of Weyl components in a chiral multiplet. -/
def componentMultiplicity : StandardModelWeylMultiplet -> ℚ
  | .quarkDoublet => 6
  | .upConjugate => 3
  | .downConjugate => 3
  | .leptonDoublet => 2
  | .electronConjugate => 1

/-! ## One-generation anomaly traces -/

/-- `[SU(3)]² U(1)` anomaly trace per generation. -/
def colorColorHyperchargeAnomalyTrace :
    StandardModelWeylMultiplet -> ℚ
  | .quarkDoublet => 2 * (1 / 2) * hypercharge .quarkDoublet
  | .upConjugate => (1 / 2) * hypercharge .upConjugate
  | .downConjugate => (1 / 2) * hypercharge .downConjugate
  | .leptonDoublet => 0
  | .electronConjugate => 0

/-- `[SU(2)]² U(1)` anomaly trace per generation. -/
def weakWeakHyperchargeAnomalyTrace :
    StandardModelWeylMultiplet -> ℚ
  | .quarkDoublet => 3 * (1 / 2) * hypercharge .quarkDoublet
  | .upConjugate => 0
  | .downConjugate => 0
  | .leptonDoublet => (1 / 2) * hypercharge .leptonDoublet
  | .electronConjugate => 0

/-- Gravitational-`U(1)` anomaly trace per generation. -/
def gravitationalHyperchargeAnomalyTrace :
    StandardModelWeylMultiplet -> ℚ :=
  fun m => componentMultiplicity m * hypercharge m

/-- Cubic `U(1)³` anomaly trace per generation. -/
def cubicHyperchargeAnomalyTrace :
    StandardModelWeylMultiplet -> ℚ :=
  fun m => componentMultiplicity m * hypercharge m ^ 3

/-- THEOREM 1: `[SU(3)]² U(1)` anomaly cancels in one generation. -/
theorem colorColorHyperchargeAnomaly_cancel :
    generationTrace colorColorHyperchargeAnomalyTrace = 0 := by
  norm_num [generationTrace, colorColorHyperchargeAnomalyTrace, hypercharge]

/-- THEOREM 2: `[SU(2)]² U(1)` anomaly cancels in one generation. -/
theorem weakWeakHyperchargeAnomaly_cancel :
    generationTrace weakWeakHyperchargeAnomalyTrace = 0 := by
  norm_num [generationTrace, weakWeakHyperchargeAnomalyTrace, hypercharge]

/-- THEOREM 3: gravitational-`U(1)` anomaly cancels in one generation. -/
theorem gravitationalHyperchargeAnomaly_cancel :
    generationTrace gravitationalHyperchargeAnomalyTrace = 0 := by
  norm_num [generationTrace, gravitationalHyperchargeAnomalyTrace,
    componentMultiplicity, hypercharge]

/-- THEOREM 4: cubic `U(1)³` anomaly cancels in one generation. -/
theorem cubicHyperchargeAnomaly_cancel :
    generationTrace cubicHyperchargeAnomalyTrace = 0 := by
  norm_num [generationTrace, cubicHyperchargeAnomalyTrace,
    componentMultiplicity, hypercharge]

end StandardModelWeylMultiplet

/-! ## Three-generation anomaly certificate -/

/-- Total anomaly trace selected by the three Poincare generation slots. -/
def totalAnomalyTrace
    (tracePerGeneration : StandardModelWeylMultiplet -> ℚ) : ℚ :=
  (Fintype.card StandardModelFermionGeneration : ℚ) *
    StandardModelWeylMultiplet.generationTrace tracePerGeneration

theorem totalAnomalyTrace_zero_of_generationTrace_zero
    {tracePerGeneration : StandardModelWeylMultiplet -> ℚ}
    (h : StandardModelWeylMultiplet.generationTrace tracePerGeneration = 0) :
    totalAnomalyTrace tracePerGeneration = 0 := by
  rw [totalAnomalyTrace, h]
  ring

/-- Three-generation `[SU(3)]² U(1)` anomaly cancellation. -/
theorem total_colorColorHyperchargeAnomaly_cancel :
    totalAnomalyTrace
      StandardModelWeylMultiplet.colorColorHyperchargeAnomalyTrace = 0 :=
  totalAnomalyTrace_zero_of_generationTrace_zero
    StandardModelWeylMultiplet.colorColorHyperchargeAnomaly_cancel

/-- Three-generation `[SU(2)]² U(1)` anomaly cancellation. -/
theorem total_weakWeakHyperchargeAnomaly_cancel :
    totalAnomalyTrace
      StandardModelWeylMultiplet.weakWeakHyperchargeAnomalyTrace = 0 :=
  totalAnomalyTrace_zero_of_generationTrace_zero
    StandardModelWeylMultiplet.weakWeakHyperchargeAnomaly_cancel

/-- Three-generation gravitational-`U(1)` anomaly cancellation. -/
theorem total_gravitationalHyperchargeAnomaly_cancel :
    totalAnomalyTrace
      StandardModelWeylMultiplet.gravitationalHyperchargeAnomalyTrace = 0 :=
  totalAnomalyTrace_zero_of_generationTrace_zero
    StandardModelWeylMultiplet.gravitationalHyperchargeAnomaly_cancel

/-- Three-generation cubic `U(1)³` anomaly cancellation. -/
theorem total_cubicHyperchargeAnomaly_cancel :
    totalAnomalyTrace
      StandardModelWeylMultiplet.cubicHyperchargeAnomalyTrace = 0 :=
  totalAnomalyTrace_zero_of_generationTrace_zero
    StandardModelWeylMultiplet.cubicHyperchargeAnomaly_cancel

/-- Bundled anomaly-cancellation certificate for the finite multiplet carrier. -/
structure StandardModelMultipletAnomalyCancellationCertificate where
  color_color_hypercharge :
    totalAnomalyTrace
      StandardModelWeylMultiplet.colorColorHyperchargeAnomalyTrace = 0
  weak_weak_hypercharge :
    totalAnomalyTrace
      StandardModelWeylMultiplet.weakWeakHyperchargeAnomalyTrace = 0
  gravitational_hypercharge :
    totalAnomalyTrace
      StandardModelWeylMultiplet.gravitationalHyperchargeAnomalyTrace = 0
  cubic_hypercharge :
    totalAnomalyTrace
      StandardModelWeylMultiplet.cubicHyperchargeAnomalyTrace = 0

/-- The P456 finite multiplet carrier is anomaly-free under the standard
one-generation anomaly traces. -/
theorem standardModelMultipletAnomalyCancellationCertificate :
    StandardModelMultipletAnomalyCancellationCertificate :=
  { color_color_hypercharge := total_colorColorHyperchargeAnomaly_cancel
    weak_weak_hypercharge := total_weakWeakHyperchargeAnomaly_cancel
    gravitational_hypercharge := total_gravitationalHyperchargeAnomaly_cancel
    cubic_hypercharge := total_cubicHyperchargeAnomaly_cancel }

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
