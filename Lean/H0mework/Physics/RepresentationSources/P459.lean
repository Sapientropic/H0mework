/-
  Proposition 459: Standard-Model matter slots from the `3+2+1+1`
  block-incidence carrier.

  P456-P458 close the coefficient/anomaly/hypercharge story after the
  one-generation matter shape `(Q,uᶜ,dᶜ,L,eᶜ)` and the Higgs doublet have been
  accepted.  This file lowers that accepted shape one layer: the four SU(7)
  blocks

      color(3), weak(2), y₊(1), y₋(1)

  have exactly six canonical off-diagonal incidences.  With the conventional
  chirality/orientation schedule, those six incidences are exactly the five
  chiral Weyl multiplets plus one Higgs doublet used by P456.

  Boundary: the incidence-to-physical-slot orientation is still a chosen
  Standard-Model schedule.  This proves that the P456 matter carrier is no
  longer an opaque list once that schedule is supplied; it does not prove that
  SU(7) uniquely forces the schedule.  In particular, the Stage-7 Phase-0
  action audit shows that the current P286 adjoint representation does not
  generate the chosen hypercharge table.  All results below therefore remain
  finite combinatorics conditional on this schedule, not an actual
  representation-restriction theorem.
-/

import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.RepresentationSources.P458

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## The four `3+2+1+1` carrier blocks -/

/-- The four blocks in the concrete `diag(C,W,z,z⁻¹)` SU(7) carrier. -/
inductive SU7CarrierBlock where
  | color
  | weak
  | positiveSinglet
  | negativeSinglet
  deriving DecidableEq, Repr, FintypeViaProxy

namespace SU7CarrierBlock

/-- A fixed order used only to name canonical unordered off-diagonal pairs. -/
def code : SU7CarrierBlock -> ℕ
  | .color => 0
  | .weak => 1
  | .positiveSinglet => 2
  | .negativeSinglet => 3

/-- THEOREM 1: the block carrier has cardinality `4`. -/
theorem card :
    Fintype.card SU7CarrierBlock = 4 := by
  decide

end SU7CarrierBlock

/-- A canonical off-diagonal block pair is written in increasing block-code
order. -/
def IsCanonicalOffDiagonalPair (a b : SU7CarrierBlock) : Prop :=
  SU7CarrierBlock.code a < SU7CarrierBlock.code b

/-! ## Six off-diagonal incidence slots -/

/-- The six canonical off-diagonal incidences among the four carrier blocks. -/
inductive SU7BlockIncidence where
  | colorWeak
  | colorPositiveSinglet
  | colorNegativeSinglet
  | weakPositiveSinglet
  | weakNegativeSinglet
  | positiveNegativeSinglet
  deriving DecidableEq, Repr, FintypeViaProxy

namespace SU7BlockIncidence

/-- The endpoint blocks of an incidence slot. -/
def endpoints : SU7BlockIncidence -> SU7CarrierBlock × SU7CarrierBlock
  | .colorWeak => (.color, .weak)
  | .colorPositiveSinglet => (.color, .positiveSinglet)
  | .colorNegativeSinglet => (.color, .negativeSinglet)
  | .weakPositiveSinglet => (.weak, .positiveSinglet)
  | .weakNegativeSinglet => (.weak, .negativeSinglet)
  | .positiveNegativeSinglet => (.positiveSinglet, .negativeSinglet)

/-- THEOREM 2: the off-diagonal incidence carrier has cardinality `6`. -/
theorem card :
    Fintype.card SU7BlockIncidence = 6 := by
  decide

/-- Every named incidence is a canonical off-diagonal pair. -/
theorem endpoints_canonical (s : SU7BlockIncidence) :
    IsCanonicalOffDiagonalPair (endpoints s).1 (endpoints s).2 := by
  cases s <;> norm_num [endpoints, IsCanonicalOffDiagonalPair,
    SU7CarrierBlock.code]

/-- THEOREM 3: the six incidence constructors are injectively identified by
their endpoint block pairs. -/
theorem endpoints_injective :
    Function.Injective endpoints := by
  intro s t h
  cases s <;> cases t <;> simp [endpoints] at h ⊢

/-- THEOREM 4: every canonical off-diagonal pair of the four blocks is one of
the six incidence slots. -/
theorem endpoints_complete
    (a b : SU7CarrierBlock)
    (h : IsCanonicalOffDiagonalPair a b) :
    ∃ s : SU7BlockIncidence, endpoints s = (a, b) := by
  cases a <;> cases b <;>
    simp [IsCanonicalOffDiagonalPair, SU7CarrierBlock.code, endpoints] at h ⊢
  · exact ⟨.colorWeak, rfl⟩
  · exact ⟨.colorPositiveSinglet, rfl⟩
  · exact ⟨.colorNegativeSinglet, rfl⟩
  · exact ⟨.weakPositiveSinglet, rfl⟩
  · exact ⟨.weakNegativeSinglet, rfl⟩
  · exact ⟨.positiveNegativeSinglet, rfl⟩

end SU7BlockIncidence

/-! ## Generated Standard-Model slots -/

/-- The six reference matter/Higgs labels assigned to the off-diagonal
incidence carrier: five chiral Weyl multiplets plus one Higgs doublet.  The
legacy `Generated` name records the historical API, not a current P286
representation-generation claim. -/
inductive SU7GeneratedCarrierSlot where
  | quarkDoublet
  | upConjugate
  | downConjugate
  | leptonDoublet
  | electronConjugate
  | higgsDoublet
  deriving DecidableEq, Repr, FintypeViaProxy

namespace SU7GeneratedCarrierSlot

/-- THEOREM 5: the generated carrier has cardinality `6`. -/
theorem card :
    Fintype.card SU7GeneratedCarrierSlot = 6 := by
  decide

/-- Forget a generated slot to the P456 Weyl multiplet carrier when it is a
fermion slot; the Higgs slot is scalar and returns `none`. -/
def toWeyl? : SU7GeneratedCarrierSlot -> Option StandardModelWeylMultiplet
  | .quarkDoublet => some .quarkDoublet
  | .upConjugate => some .upConjugate
  | .downConjugate => some .downConjugate
  | .leptonDoublet => some .leptonDoublet
  | .electronConjugate => some .electronConjugate
  | .higgsDoublet => none

/-- THEOREM 6: every P456 Weyl multiplet appears in the generated carrier. -/
theorem toWeyl?_surjective :
    ∀ m : StandardModelWeylMultiplet,
      ∃ s : SU7GeneratedCarrierSlot, toWeyl? s = some m := by
  intro m
  cases m
  · exact ⟨.quarkDoublet, rfl⟩
  · exact ⟨.upConjugate, rfl⟩
  · exact ⟨.downConjugate, rfl⟩
  · exact ⟨.leptonDoublet, rfl⟩
  · exact ⟨.electronConjugate, rfl⟩

/-- THEOREM 7: the only generated non-Weyl slot is the Higgs doublet. -/
theorem toWeyl?_eq_none_iff (s : SU7GeneratedCarrierSlot) :
    toWeyl? s = none ↔ s = .higgsDoublet := by
  cases s <;> simp [toWeyl?]

end SU7GeneratedCarrierSlot

/-- The conventional, externally chosen incidence-to-slot schedule.

The lone scalar incidence `weakPositiveSinglet` is the Higgs doublet; the
other five incidences are the one-generation chiral Weyl multiplets. -/
def generatedSlotOfIncidence : SU7BlockIncidence -> SU7GeneratedCarrierSlot
  | .colorWeak => .quarkDoublet
  | .colorPositiveSinglet => .upConjugate
  | .colorNegativeSinglet => .downConjugate
  | .weakPositiveSinglet => .higgsDoublet
  | .weakNegativeSinglet => .leptonDoublet
  | .positiveNegativeSinglet => .electronConjugate

/-- The inverse schedule from generated slots back to block incidences. -/
def incidenceOfGeneratedSlot : SU7GeneratedCarrierSlot -> SU7BlockIncidence
  | .quarkDoublet => .colorWeak
  | .upConjugate => .colorPositiveSinglet
  | .downConjugate => .colorNegativeSinglet
  | .leptonDoublet => .weakNegativeSinglet
  | .electronConjugate => .positiveNegativeSinglet
  | .higgsDoublet => .weakPositiveSinglet

/-- THEOREM 8: the six off-diagonal block incidences are exactly the six
generated Standard-Model matter/Higgs slots. -/
def blockIncidenceGeneratedSlotEquiv :
    SU7BlockIncidence ≃ SU7GeneratedCarrierSlot where
  toFun := generatedSlotOfIncidence
  invFun := incidenceOfGeneratedSlot
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

/-! ## Trace input reconstructed from block incidences -/

/-- Per-generation Weyl trace reconstructed from the five generated Weyl
slots. -/
def incidenceWeylTracePerGeneration
    (trace : StandardModelWeylMultiplet -> ℚ) : ℚ :=
  trace .quarkDoublet +
    trace .upConjugate +
    trace .downConjugate +
    trace .leptonDoublet +
    trace .electronConjugate

/-- THEOREM 9: the generated Weyl trace is definitionally the P456 generation
trace. -/
theorem incidenceWeylTracePerGeneration_eq_generationTrace
    (trace : StandardModelWeylMultiplet -> ℚ) :
    incidenceWeylTracePerGeneration trace =
      StandardModelWeylMultiplet.generationTrace trace := rfl

/-- Total Weyl trace after multiplying the generated one-generation incidence
trace by the three Poincare generation slots. -/
def incidenceTotalWeylTrace
    (trace : StandardModelWeylMultiplet -> ℚ) : ℚ :=
  (Fintype.card StandardModelFermionGeneration : ℚ) *
    incidenceWeylTracePerGeneration trace

/-- THEOREM 10: incidence-generated total traces equal P456 total traces. -/
theorem incidenceTotalWeylTrace_eq_totalWeylTrace
    (trace : StandardModelWeylMultiplet -> ℚ) :
    incidenceTotalWeylTrace trace = totalWeylTrace trace := rfl

/-- The scalar trace of the one generated Higgs incidence. -/
def incidenceHiggsScalarTrace : StandardModelGaugeFactor -> ℚ :=
  higgsScalarTrace

/-- Gauge trace input reconstructed from the six block incidences. -/
def incidenceCarrierTraceInput :
    StandardModelGaugeFactor -> GaugeTraceOneLoopInput
  | .colorSU3 =>
      { adjointCasimir := 3
        weylDynkinTrace :=
          incidenceTotalWeylTrace StandardModelWeylMultiplet.colorDynkinTrace
        scalarDynkinTrace := incidenceHiggsScalarTrace .colorSU3 }
  | .weakSU2 =>
      { adjointCasimir := 2
        weylDynkinTrace :=
          incidenceTotalWeylTrace StandardModelWeylMultiplet.weakDynkinTrace
        scalarDynkinTrace := incidenceHiggsScalarTrace .weakSU2 }
  | .hyperchargeU1 =>
      { adjointCasimir := 0
        weylDynkinTrace :=
          incidenceTotalWeylTrace StandardModelWeylMultiplet.hyperchargeSquareTrace
        scalarDynkinTrace := incidenceHiggsScalarTrace .hyperchargeU1 }

/-- THEOREM 11: the incidence-generated trace input is exactly the P456 finite
multiplet trace input. -/
theorem incidenceCarrierTraceInput_eq_multipletCarrierTraceInput
    (G : StandardModelGaugeFactor) :
    incidenceCarrierTraceInput G = multipletCarrierTraceInput G := by
  cases G <;> rfl

/-- THEOREM 12: the block-incidence carrier reconstructs the same `b0`
formula as P455/P456. -/
theorem betaCoeff_incidenceCarrierTraceInput_eq_carrierB0
    (G : StandardModelGaugeFactor) :
    betaCoeff (incidenceCarrierTraceInput G) = carrierB0 G := by
  rw [incidenceCarrierTraceInput_eq_multipletCarrierTraceInput,
    betaCoeff_multipletCarrierTraceInput_eq_carrierB0]

/-- THEOREM 13: QCD `b0=7` from the block-incidence carrier. -/
theorem qcd_b0_from_block_incidence_carrier :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = 7 := by
  rw [betaCoeff_incidenceCarrierTraceInput_eq_carrierB0, carrierB0_color]

/-- A bundled certificate for the current block-incidence matter-carrier
layer. -/
structure SU7BlockIncidenceMatterCarrierCertificate where
  block_count : Fintype.card SU7CarrierBlock = 4
  incidence_count : Fintype.card SU7BlockIncidence = 6
  generated_slot_count : Fintype.card SU7GeneratedCarrierSlot = 6
  incidence_equiv :
    SU7BlockIncidence ≃ SU7GeneratedCarrierSlot
  trace_input :
    ∀ G : StandardModelGaugeFactor,
      incidenceCarrierTraceInput G = multipletCarrierTraceInput G
  b0_formula :
    ∀ G : StandardModelGaugeFactor,
      betaCoeff (incidenceCarrierTraceInput G) = carrierB0 G
  normalized_hypercharge_two_branches :
    ∀ Y : OneGenerationHyperchargeAssignment,
      Y.colorAnomalyFree ->
      Y.weakAnomalyFree ->
      Y.gravitationalAnomalyFree ->
      Y.cubicAnomalyFree ->
      Y.e = 1 ->
      Y = OneGenerationHyperchargeAssignment.standardModel ∨
        Y = OneGenerationHyperchargeAssignment.swappedSinglets

/-- THEOREM 14: the current six-incidence matter carrier certificate. -/
def su7BlockIncidenceMatterCarrierCertificate :
    SU7BlockIncidenceMatterCarrierCertificate where
  block_count := SU7CarrierBlock.card
  incidence_count := SU7BlockIncidence.card
  generated_slot_count := SU7GeneratedCarrierSlot.card
  incidence_equiv := blockIncidenceGeneratedSlotEquiv
  trace_input := incidenceCarrierTraceInput_eq_multipletCarrierTraceInput
  b0_formula := betaCoeff_incidenceCarrierTraceInput_eq_carrierB0
  normalized_hypercharge_two_branches := by
    intro Y hc hw hg hcu he
    exact
      OneGenerationHyperchargeAssignment.normalized_anomaly_solution_two_branches
        hc hw hg hcu he

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
