import H0mework.NavierStokes.EndpointWork.QuadraticBoundaryPairWorkCompiler

/-!
# Anchored mixed work of an actual collective restart write

For one source-selected finite segment, write

```text
uᵢ = the actual contact velocity,
qᵢ = uᵢ₊₁ - uᵢ.
```

Polarizing every edge relative to the fixed actual anchor `u_start` gives

```text
‖u_(start+steps) - u_start‖²
= Σᵢ (2 Re⟪uᵢ - u_start, qᵢ⟫ + ‖qᵢ‖²).
```

Thus the complete angular cross term is not a new norm or memory carrier:
it is exactly the sum of the anchored mixed bilinear works of the literal
native edges.  The final theorem expands every such work through the
existing same-edge Fourier tangent/pair compiler before any output quotient.

No anchor, path, edge, sign, coercivity, continuity, or settlement witness
is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAnchoredMixedWork

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryPairWorkCompiler

noncomputable section

/-! ## One actual edge relative to the source-selected anchor -/

/-- Polarization of one actual native write relative to the contact at
`start`.  Both the anchor and the edge belong to the same `run current`. -/
theorem wholeRestartNativeCausalVelocityWrite_anchoredQuadraticBoundary
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start offset : ℕ) :
    ‖wholeRestartContactVelocityState current (start + offset + 1) -
        wholeRestartContactVelocityState current start‖ ^ 2 =
      ‖wholeRestartContactVelocityState current (start + offset) -
          wholeRestartContactVelocityState current start‖ ^ 2 +
        2 * RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current (start + offset) -
            wholeRestartContactVelocityState current start)
          (wholeRestartNativeCausalVelocityWrite
            current (start + offset))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2 := by
  have nextEq :
      wholeRestartContactVelocityState current (start + offset + 1) -
          wholeRestartContactVelocityState current start =
        (wholeRestartContactVelocityState current (start + offset) -
            wholeRestartContactVelocityState current start) +
          wholeRestartNativeCausalVelocityWrite
            current (start + offset) := by
    rw [wholeRestartNativeCausalVelocityWrite_eq_adjacent]
    abel
  rw [nextEq, norm_add_sq (𝕜 := ℂ)]

/-- The anchored mixed work plus the edge square is literally the increment
of the anchored distance square on that same edge. -/
theorem
    wholeRestartNativeCausalVelocityWrite_anchoredQuadraticBoundary_eq_gap
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start offset : ℕ) :
    2 * RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current (start + offset) -
            wholeRestartContactVelocityState current start)
          (wholeRestartNativeCausalVelocityWrite
            current (start + offset))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2 =
      ‖wholeRestartContactVelocityState current (start + offset + 1) -
          wholeRestartContactVelocityState current start‖ ^ 2 -
        ‖wholeRestartContactVelocityState current (start + offset) -
          wholeRestartContactVelocityState current start‖ ^ 2 := by
  rw [
    wholeRestartNativeCausalVelocityWrite_anchoredQuadraticBoundary
      current start offset]
  ring

/-! ## Finite actual-lineage telescope -/

/-- The collective square is exactly the finite sum of the anchored mixed
works and the literal native edge squares.  The anchor and every edge are
fixed internally by `current`, `start`, and `steps`. -/
theorem
    wholeRestartCollectiveCausalVelocityWrite_norm_sq_eq_sum_anchoredMixedWork
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    ‖wholeRestartCollectiveCausalVelocityWrite
        current start steps‖ ^ 2 =
      ∑ offset ∈ Finset.range steps,
        (2 * RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current (start + offset) -
              wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset))) +
          ‖wholeRestartNativeCausalVelocityWrite
            current (start + offset)‖ ^ 2) := by
  rw [wholeRestartCollectiveCausalVelocityWrite_eq_gap]
  symm
  simp_rw [
    wholeRestartNativeCausalVelocityWrite_anchoredQuadraticBoundary_eq_gap]
  rw [Finset.sum_sub_distrib]
  have telescope :=
    Finset.sum_range_sub
      (fun offset : ℕ =>
        ‖wholeRestartContactVelocityState current (start + offset) -
          wholeRestartContactVelocityState current start‖ ^ 2)
      steps
  have anchorZero :
      ‖wholeRestartContactVelocityState current (start + 0) -
          wholeRestartContactVelocityState current start‖ ^ 2 = 0 := by
    rw [Nat.add_zero, sub_self, norm_zero]
    norm_num
  rw [anchorZero, sub_zero] at telescope
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using telescope

/-- After removing the individual edge squares, the remaining angular cross
term is exactly twice the sum of the anchored mixed works. -/
theorem
    wholeRestartCollectiveCausalVelocityWrite_crossTerm_eq_anchoredMixedWork
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    ‖wholeRestartCollectiveCausalVelocityWrite
          current start steps‖ ^ 2 -
        ∑ offset ∈ Finset.range steps,
          ‖wholeRestartNativeCausalVelocityWrite
            current (start + offset)‖ ^ 2 =
      2 * ∑ offset ∈ Finset.range steps,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current (start + offset) -
            wholeRestartContactVelocityState current start)
          (wholeRestartNativeCausalVelocityWrite
            current (start + offset))) := by
  rw [
    wholeRestartCollectiveCausalVelocityWrite_norm_sq_eq_sum_anchoredMixedWork]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-! ## Incoming work minus anchor work -/

/-- Each anchored mixed work is exactly the ordinary incoming-edge work
minus the work tested against the source-selected anchor. -/
theorem wholeRestartAnchoredMixedWork_eq_incomingWork_sub_anchorWork
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start index : ℕ) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index -
          wholeRestartContactVelocityState current start)
        (wholeRestartNativeCausalVelocityWrite current index)) =
      RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index)
          (wholeRestartNativeCausalVelocityWrite current index)) -
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current start)
          (wholeRestartNativeCausalVelocityWrite current index)) := by
  rw [inner_sub_left]
  exact map_sub Complex.reCLM _ _

/-- Equivalent collective form isolating the only new angular responsibility:
the actual incoming work is already handled by the one-edge kinetic boundary,
so the second term is precisely the source-anchor work that a reflected-pair
consumer must compile. -/
theorem
    wholeRestartCollectiveCausalVelocityWrite_crossTerm_eq_incoming_sub_anchorWork
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    ‖wholeRestartCollectiveCausalVelocityWrite
          current start steps‖ ^ 2 -
        ∑ offset ∈ Finset.range steps,
          ‖wholeRestartNativeCausalVelocityWrite
            current (start + offset)‖ ^ 2 =
      2 * ∑ offset ∈ Finset.range steps,
        (RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current (start + offset))
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset))) -
          RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current start)
            (wholeRestartNativeCausalVelocityWrite
              current (start + offset)))) := by
  rw [
    wholeRestartCollectiveCausalVelocityWrite_crossTerm_eq_anchoredMixedWork]
  apply congrArg (fun value : ℝ => 2 * value)
  apply Finset.sum_congr rfl
  intro offset _offsetMem
  exact
    wholeRestartAnchoredMixedWork_eq_incomingWork_sub_anchorWork
      current start (start + offset)

/-! ## Same-edge Fourier and tangent/pair readout -/

/-- The anchored mixed work is the complete Fourier sum on the existing
physical velocity carrier. -/
theorem wholeRestartAnchoredNativeCausalVelocityWrite_realInner_eq_tsum
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start index : ℕ) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index -
          wholeRestartContactVelocityState current start)
        (wholeRestartNativeCausalVelocityWrite current index)) =
      ∑' wave : NonzeroIntegerWavevector,
        RCLike.re (inner ℂ
          ((wholeRestartContactVelocityState current index -
            wholeRestartContactVelocityState current start) wave)
          (wholeRestartNativeCausalVelocityWrite current index wave)) := by
  rw [lp.inner_eq_tsum]
  exact Complex.reCLM.map_tsum
    (lp.summable_inner
      (wholeRestartContactVelocityState current index -
        wholeRestartContactVelocityState current start)
      (wholeRestartNativeCausalVelocityWrite current index))

/-- At one output, the source anchor consumes the complete pair-innovation
series before the input-pair quotient.  This is the exact seam required by a
reflected-pair process; it does not identify that process's full nonlinear
work with the innovation work. -/
theorem wholeRestartAnchorPairInnovationVelocityRealInner_tsum
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current start wave)
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (∑' first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first)))) =
      ∑' first : IntegerWavevector,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current start wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first)))) := by
  exact
    wholeRestartPairInnovationVelocityRealInner_tsum
      current index wave
        (wholeRestartContactVelocityState current start wave)

/-- Every anchored mixed work reads the exact tangent plus complete pair
innovation generated by that same actual edge. -/
theorem
    wholeRestartAnchoredNativeCausalVelocityWrite_realInner_eq_tsum_causalTangent_add_pairInnovation
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start index : ℕ) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index -
          wholeRestartContactVelocityState current start)
        (wholeRestartNativeCausalVelocityWrite current index)) =
      ∑' wave : NonzeroIntegerWavevector,
        RCLike.re (inner ℂ
          ((wholeRestartContactVelocityState current index -
            wholeRestartContactVelocityState current start) wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartCausalTangentGain current index wave.1 •
                  wholeRestartCrossingUnforcedTangentRow
                    current index wave.1 +
                ∑' first : IntegerWavevector,
                  wholeRestartPairDuhamelInnovationOccurrence
                    current index wave.1 first)))) := by
  rw [wholeRestartAnchoredNativeCausalVelocityWrite_realInner_eq_tsum]
  apply tsum_congr
  intro wave
  rw [
    wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation]

/-- Consumer-facing form: the entire collective square is the exact finite
sum of anchored Fourier tangent/pair works plus the actual edge squares. -/
theorem
    wholeRestartCollectiveCausalVelocityWrite_norm_sq_eq_sum_anchoredDuhamelMixedWork
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    ‖wholeRestartCollectiveCausalVelocityWrite
        current start steps‖ ^ 2 =
      ∑ offset ∈ Finset.range steps,
        (2 *
            (∑' wave : NonzeroIntegerWavevector,
              RCLike.re (inner ℂ
                ((wholeRestartContactVelocityState
                      current (start + offset) -
                    wholeRestartContactVelocityState current start) wave)
                (euclideanCoordinateRow
                  (biotSavartVelocityCoefficient wave.1
                    (wholeRestartCausalTangentGain
                          current (start + offset) wave.1 •
                        wholeRestartCrossingUnforcedTangentRow
                          current (start + offset) wave.1 +
                      ∑' first : IntegerWavevector,
                        wholeRestartPairDuhamelInnovationOccurrence
                          current (start + offset) wave.1 first))))) +
          ‖wholeRestartNativeCausalVelocityWrite
            current (start + offset)‖ ^ 2) := by
  rw [
    wholeRestartCollectiveCausalVelocityWrite_norm_sq_eq_sum_anchoredMixedWork]
  apply Finset.sum_congr rfl
  intro offset _offsetMem
  rw [
    wholeRestartAnchoredNativeCausalVelocityWrite_realInner_eq_tsum_causalTangent_add_pairInnovation]

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAnchoredMixedWork
end NavierStokes
end SaturationMonoid
