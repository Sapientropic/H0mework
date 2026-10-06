import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservablePrediction.Observablelaw

/-!
# Direct consumers of source-generated observable laws

One actual source supplies the cone, all four readings, training-only Cramer inverse,
held-out prediction, loss-inclusive singles and named S1/M3/OR responses. No probability,
completed Gram or cone certificate enters the source mouth. Residual identities carry
explicit additive errors and perform no statistical inference.
-/

set_option autoImplicit false

namespace P23.Collection.Observable.Consumer

noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
variable (p : Preparation) (f : Source A B) (oA : Optic A) (oB : Optic B)

structure JointFamilyAt (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ) : Prop where
  cone : GramCone (scaledGram p f oA oB sigma)
  row_law : ∀ i, sourceFour p f oA oB sigma theta i =
    rowRead (designRows theta i) (scaledGram p f oA oB sigma)
  left_null : nullResidual (designRows theta) (sourceFour p f oA oB sigma theta) = 0
  recovery : recoverTraining (designRows theta) (sourceFour p f oA oB sigma theta) =
    scaledGram p f oA oB sigma
  held_out : predictHeldOut (designRows theta) (sourceFour p f oA oB sigma theta) =
    sourceFour p f oA oB sigma theta 2

theorem source_family_consumer (sigma : ℝ) (hs : 0 ≤ sigma) (theta : Fin 4 → ℝ × ℝ)
    (hd : trainingMinor (designRows theta) ≠ 0) : JointFamilyAt p f oA oB sigma theta where
  cone := scaled_source_cone p f oA oB sigma hs
  row_law i := source_design p f oA oB sigma (theta i).1 (theta i).2
  left_null := source_null_law p f oA oB sigma theta
  recovery := source_recovery p f oA oB sigma theta hd
  held_out := source_held_out p f oA oB sigma theta hd

/-- The source law includes the general non-mirror design; mirror is one explicit restriction. -/
theorem mirror_consumer (sigma a0 a1 : ℝ) :
    sourceFour p f oA oB sigma (mirrorSettings a0 a1) 1 =
      sourceFour p f oA oB sigma (mirrorSettings a0 a1) 2 :=
  source_mirror p f oA oB sigma a0 a1

theorem actual_mirror_sources (sigma a0 a1 : ℝ) :
    sourceFour p sourceI collectBin0 collectBin0 sigma (mirrorSettings a0 a1) 1 =
      sourceFour p sourceI collectBin0 collectBin0 sigma (mirrorSettings a0 a1) 2 ∧
    sourceFour p sourceII collectBin0 collectBin0 sigma (mirrorSettings a0 a1) 1 =
      sourceFour p sourceII collectBin0 collectBin0 sigma (mirrorSettings a0 a1) 2 :=
  ⟨source_mirror p sourceI collectBin0 collectBin0 sigma a0 a1,
    source_mirror p sourceII collectBin0 collectBin0 sigma a0 a1⟩

/-- The independent inverse cannot read the held-out fourth value. -/
theorem training_ignores_held_out (r : Fin 4 → DesignRow) (y : Fin 4 → ℝ) (held : ℝ) :
    recoverTraining r (fun i => if i = 2 then held else y i) = recoverTraining r y := by
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  simp only [recoverTraining, h02, h12, h32, if_false]

theorem held_out_change_detected (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ) (perturbation : ℝ)
    (hd : trainingMinor (designRows theta) ≠ 0) :
    heldOutResidual (designRows theta)
      (fun i => if i = 2 then sourceFour p f oA oB sigma theta i + perturbation
        else sourceFour p f oA oB sigma theta i) = perturbation := by
  have replaced :
      (fun i : Fin 4 => if i = 2 then sourceFour p f oA oB sigma theta i + perturbation
        else sourceFour p f oA oB sigma theta i) =
      (fun i : Fin 4 => if i = 2 then sourceFour p f oA oB sigma theta 2 + perturbation
        else sourceFour p f oA oB sigma theta i) := by
    funext i
    by_cases hi : i = 2
    · subst i
      rfl
    · simp only [hi, if_false]
  rw [replaced]
  unfold heldOutResidual predictHeldOut
  rw [training_ignores_held_out]
  change sourceFour p f oA oB sigma theta 2 + perturbation -
    predictHeldOut (designRows theta) (sourceFour p f oA oB sigma theta) = perturbation
  rw [source_held_out p f oA oB sigma theta hd]
  ring

/-- Noise remains a separate readout interface; this identity creates no sampling budget. -/
theorem held_out_error_consumer (sigma : ℝ) (theta : Fin 4 → ℝ × ℝ) (errors : Fin 4 → ℝ)
    (hd : trainingMinor (designRows theta) ≠ 0) :
    heldOutResidual (designRows theta)
      (fun i => sourceFour p f oA oB sigma theta i + errors i) =
        errors 2 - predictHeldOut (designRows theta) errors :=
  source_noise_residual p f oA oB sigma theta errors hd

theorem vertical_endpoints (sigma : ℝ) :
    signalJoint p f oA oB sigma 0 0 = (scaledGram p f oA oB sigma).vv ∧
    signalJoint p f oA oB sigma (Real.pi / 2) (Real.pi / 2) =
      (scaledGram p f oA oB sigma).hh ∧
    Response.aliceBorn p f oA 0 = (omegaA p f oA).2 ∧
    Response.aliceBorn p f oA (Real.pi / 2) = (omegaA p f oA).1 := by
  simp [signalJoint, Response.linearBorn, jointRead, Response.aliceBorn, scaledGram]

theorem loss_inclusive_singles (Q uA uB bgA bgB a b : ℝ) :
    Response.observedA p f oA Q uA bgA a =
      Q * uA * (p.c ^ 2 *
        (power f oA oB false false false + power f oA oB false false true) * Real.sin a ^ 2 +
        p.s ^ 2 * (power f oA oB true false false + power f oA oB true false true) *
          Real.cos a ^ 2) + bgA ∧
    Response.observedB p f oB Q uB bgB b =
      Q * uB * (p.c ^ 2 *
        (power f oA oB false false false + power f oA oB false true false) * Real.sin b ^ 2 +
        p.s ^ 2 * (power f oA oB true false false + power f oA oB true true false) *
          Real.cos b ^ 2) + bgB := by
  constructor
  · rw [Response.observedA, Response.aliceBorn_from_loss p f oA oB a]
  · rw [Response.observedB, Response.bobBorn_from_loss p f oA oB b]

theorem signal_loss_consumer (Q uA uB : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hA0 : 0 ≤ uA) (hA1 : uA ≤ 1) (hB0 : 0 ≤ uB) (hB1 : uB ≤ 1) :
    SignalLossAt p f oA oB Q uA uB :=
  source_signal_loss p f oA oB Q uA uB hQ0 hQ1 hA0 hA1 hB0 hB1

/-- The S1 response consumes only the joint Gram, with no singles readout required. -/
theorem S1_signal_derivatives (Q uA uB bgA bgB a0 a1 b0 b1 u v : ℝ) :
    HasDerivAt (Response.aliceCH p f oA oB 0 Q uA uB bgA bgB a0 b0 b1)
      (observableSlope (scaledGram p f oA oB (Q * uA * uB)) 0 0 0 b0 b1 u) u ∧
    HasDerivAt (Response.bobCH p f oA oB 0 Q uA uB bgA bgB a0 a1 b0)
      (observableSlope (scaledGram p f oA oB (Q * uA * uB)) 0 0 0 a0 a1 v) v := by
  constructor
  · simpa [observableSlope, observableZ] using
      source_alice_observable_deriv p f oA oB 0 Q uA uB bgA bgB a0 b0 b1 u
  · simpa [observableSlope, observableZ] using
      source_bob_observable_deriv p f oA oB 0 Q uA uB bgA bgB a0 a1 b0 v

/-- M3 consumes β from two measured singles at the same source and background plane. -/
theorem named_M3_derivatives (Q uA uB bgA bgB a0 a1 b0 b1 u v : ℝ)
    (hA : Real.cos (2 * a0) - Real.cos (2 * a1) ≠ 0)
    (hB : Real.cos (2 * b0) - Real.cos (2 * b1) ≠ 0) :
    let betaA := singleBetaRead (Response.observedA p f oA Q uA bgA a0)
      (Response.observedA p f oA Q uA bgA a1) a0 a1
    let betaB := singleBetaRead (Response.observedB p f oB Q uB bgB b0)
      (Response.observedB p f oB Q uB bgB b1) b0 b1
    HasDerivAt (Response.aliceCH p f oA oB 1 Q uA uB bgA bgB a0 b0 b1)
      (observableSlope (scaledGram p f oA oB (Q * uA * uB)) 1 betaA betaB b0 b1 u) u ∧
    HasDerivAt (Response.bobCH p f oA oB 1 Q uA uB bgA bgB a0 a1 b0)
      (observableSlope (scaledGram p f oA oB (Q * uA * uB)) 1 betaA betaB a0 a1 v) v := by
  dsimp only
  rw [source_single_betaA p f oA Q uA bgA a0 a1 hA,
    source_single_betaB p f oB Q uB bgB b0 b1 hB]
  exact ⟨source_alice_observable_deriv p f oA oB 1 Q uA uB bgA bgB a0 b0 b1 u,
    source_bob_observable_deriv p f oA oB 1 Q uA uB bgA bgB a0 a1 b0 v⟩

theorem S1_signal_gain (Q uA uB bgA bgB a0 a1 b0 b1 a1' b1' : ℝ) :
    Response.rawCH p f oA oB 0 Q uA uB bgA bgB a0 a1' b0 b1' -
      Response.rawCH p f oA oB 0 Q uA uB bgA bgB a0 a1 b0 b1 =
        gramCH (scaledGram p f oA oB (Q * uA * uB)) a0 a1' b0 b1' -
          gramCH (scaledGram p f oA oB (Q * uA * uB)) a0 a1 b0 b1 := by
  unfold Response.rawCH Response.coincidence gramCH
  simp_rw [← source_design]
  unfold signalJoint
  ring

theorem independent_OR_derivatives (Q uA uB bgA bgB a0 a1 b0 b1 u v : ℝ) :
    HasDerivAt (fun t => sourceORCH p f oA oB Q uA uB bgA bgB a0 t b0 b1)
      (observableSlope (scaledGram p f oA oB (orScale bgA bgB * (Q * uA * uB)))
        0 0 0 b0 b1 u) u ∧
    HasDerivAt (fun t => sourceORCH p f oA oB Q uA uB bgA bgB a0 a1 b0 t)
      (observableSlope (scaledGram p f oA oB (orScale bgA bgB * (Q * uA * uB)))
        0 0 0 a0 a1 v) v :=
  ⟨source_OR_alice_deriv p f oA oB Q uA uB bgA bgB a0 b0 b1 u,
    source_OR_bob_deriv p f oA oB Q uA uB bgA bgB a0 a1 b0 v⟩

/-- All named branches correct back to the same source-cone family, retaining their rate laws. -/
theorem named_corrections (Q uA uB bgA bgB a b : ℝ) :
    (Response.coincidence p f oA oB 0 Q uA uB bgA bgB a b =
      signalJoint p f oA oB (Q * uA * uB) a b) ∧
    (Response.coincidence p f oA oB 1 Q uA uB bgA bgB a b -
      Response.observedA p f oA Q uA bgA a * Response.observedB p f oB Q uB bgB b =
        signalJoint p f oA oB (Q * uA * uB) a b) ∧
    (sourceORJoint p f oA oB Q uA uB bgA bgB a b -
      bgB * orSingle bgA (Response.observedA p f oA Q uA 0 a) -
      bgA * orSingle bgB (Response.observedB p f oB Q uB 0 b) + bgA * bgB =
        signalJoint p f oA oB (orScale bgA bgB * (Q * uA * uB)) a b) := by
  constructor
  · simpa only [zero_mul, sub_zero] using m3_subtraction p f oA oB 0 Q uA uB bgA bgB a b
  · constructor
    · simpa only [one_mul] using m3_subtraction p f oA oB 1 Q uA uB bgA bgB a b
    · exact source_OR_correction p f oA oB Q uA uB bgA bgB a b

end
end P23.Collection.Observable.Consumer
