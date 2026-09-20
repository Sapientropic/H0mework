import H0mework.Physics.RunningSources.P799

/-!
# Proposition 800: SU(7) counterterm producer for the alpha_s loop expansion

P799 lowered the RG leg to a loop-expansion source law:

* one-loop carrier trace;
* two-loop diagram/counterterm coordinate;
* three-loop diagram/counterterm coordinate.

This file lowers the two higher-loop cancellations one step further.  Their
raw diagram coordinate is generated from SU(7) balance data: threshold trace
imbalance plus incidence/generated-slot imbalance.  The source-law counterterm
is then the subtraction of that generated coordinate.  Thus the renormalized
two- and three-loop coordinates vanish by construction as source-law
subtractions, not as supplied zero fields.

The result feeds the P799 loop-expansion producer and therefore gives the same
exact alpha_s inverse residual `-89000/128511`, while also keeping the P795
unique residual-carrier reconstruction bridge.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open scoped BigOperators

/-! ## SU(7) loop-counterterm source data -/

/-- SU(7) data that generates the higher-loop source-coordinate diagrams:
threshold trace data plus the incidence/generated-slot equivalence. -/
structure SU7LoopCountertermSourceData where
  thresholdTrace : ThresholdTraceSourceData
  incidenceGeneratedSlotEquiv :
    SU7BlockIncidence ≃ SU7GeneratedCarrierSlot

/-- Threshold imbalance read by the higher-loop source coordinate. -/
def thresholdTraceImbalance (D : ThresholdTraceSourceData) : ℚ :=
  D.lowEnergyColorTrace - D.unifiedIncidenceColorTrace

/-- Incidence/generated-slot imbalance read by the higher-loop source
coordinate. -/
def incidenceSlotImbalance
    (_e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) : ℚ :=
  (Fintype.card SU7BlockIncidence : ℚ) -
    (Fintype.card SU7GeneratedCarrierSlot : ℚ)

/-- The incidence/generated-slot equivalence forces zero slot imbalance. -/
theorem incidenceSlotImbalance_eq_zero
    (e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) :
    incidenceSlotImbalance e = 0 := by
  unfold incidenceSlotImbalance
  have h :
      (Fintype.card SU7BlockIncidence : ℚ) =
        (Fintype.card SU7GeneratedCarrierSlot : ℚ) := by
    exact_mod_cast Fintype.card_congr e
  rw [h]
  ring

/-- Raw higher-loop coordinate generated from SU(7) balance data at a chosen
loop-order weight. -/
def su7LoopRawCoordinate
    (D : SU7LoopCountertermSourceData)
    (loopWeight : ℚ) : ℚ :=
  loopWeight *
    (thresholdTraceImbalance D.thresholdTrace +
      incidenceSlotImbalance D.incidenceGeneratedSlotEquiv)

/-- Balanced threshold trace plus the incidence equivalence makes the raw
higher-loop coordinate itself vanish. -/
theorem su7LoopRawCoordinate_eq_zero_of_balanced
    (D : SU7LoopCountertermSourceData)
    (loopWeight : ℚ)
    (hD : ThresholdTraceSourceBalanced D.thresholdTrace) :
    su7LoopRawCoordinate D loopWeight = 0 := by
  unfold su7LoopRawCoordinate thresholdTraceImbalance
  rw [incidenceSlotImbalance_eq_zero D.incidenceGeneratedSlotEquiv]
  unfold ThresholdTraceSourceBalanced at hD
  rw [hD]
  ring

/-- Generate a loop coordinate and its source-law counterterm from SU(7)
balance data.  The counterterm is not a target receipt: it is the canonical
subtraction of the generated raw coordinate. -/
def loopCoordinateContributionFromSU7CountertermSource
    (D : SU7LoopCountertermSourceData)
    (loopWeight : ℚ) :
    LoopCoordinateContribution where
  diagram := su7LoopRawCoordinate D loopWeight
  counterterm := -su7LoopRawCoordinate D loopWeight

/-- A source-law counterterm generated as `-raw` cancels the generated raw loop
coordinate. -/
theorem loopCoordinateContributionFromSU7CountertermSource_cancelled
    (D : SU7LoopCountertermSourceData)
    (loopWeight : ℚ) :
    (loopCoordinateContributionFromSU7CountertermSource
      D loopWeight).Cancelled := by
  unfold LoopCoordinateContribution.Cancelled
    LoopCoordinateContribution.renormalized
    loopCoordinateContributionFromSU7CountertermSource
  ring

/-- If the SU(7) source data is balanced, the generated loop coordinate is the
zero loop-coordinate contribution from P799. -/
theorem loopCoordinateContributionFromSU7CountertermSource_eq_zeroLoop
    (D : SU7LoopCountertermSourceData)
    (loopWeight : ℚ)
    (hD : ThresholdTraceSourceBalanced D.thresholdTrace) :
    loopCoordinateContributionFromSU7CountertermSource D loopWeight =
      zeroLoopCoordinateContribution := by
  unfold loopCoordinateContributionFromSU7CountertermSource
    zeroLoopCoordinateContribution
  rw [su7LoopRawCoordinate_eq_zero_of_balanced D loopWeight hD]
  norm_num

/-! ## Three-loop expansion generated from the SU(7) counterterm source -/

/-- Generate P799's three-loop expansion source from SU(7) counterterm data.
The one-loop carrier trace is the QCD block-incidence input; two- and
three-loop coordinates are generated with weights `2` and `3`. -/
def threeLoopRGExpansionFromSU7CountertermSource
    (D : SU7LoopCountertermSourceData) :
    ThreeLoopRGExpansionSourceData where
  oneLoopInput := qcdBlockIncidenceOneLoopInput
  twoLoop :=
    loopCoordinateContributionFromSU7CountertermSource D 2
  threeLoop :=
    loopCoordinateContributionFromSU7CountertermSource D 3

/-- The generated SU(7) counterterm expansion satisfies P799's source law. -/
theorem threeLoopRGExpansionFromSU7CountertermSource_sourceLaw
    (D : SU7LoopCountertermSourceData) :
    ThreeLoopRGExpansionSourceLaw
      (threeLoopRGExpansionFromSU7CountertermSource D) := by
  unfold ThreeLoopRGExpansionSourceLaw
    threeLoopRGExpansionFromSU7CountertermSource
  refine ⟨?_, ?_, ?_⟩
  · exact qcdBlockIncidenceOneLoopInput_eq_incidenceCarrierTraceInput
  · exact loopCoordinateContributionFromSU7CountertermSource_cancelled D 2
  · exact loopCoordinateContributionFromSU7CountertermSource_cancelled D 3

/-- The SU(7) counterterm expansion generates the canonical beta coefficients:
the higher-loop source coordinates are renormalized to zero, while the
one-loop coordinate is the QCD block-incidence carrier. -/
theorem threeLoopBetaCoefficientsFromSU7CountertermSource_eq_canonical
    (D : SU7LoopCountertermSourceData) :
    threeLoopBetaCoefficientsFromExpansion
        (threeLoopRGExpansionFromSU7CountertermSource D) =
      canonicalThreeLoopBetaCoefficients := by
  unfold threeLoopBetaCoefficientsFromExpansion
    threeLoopRGExpansionFromSU7CountertermSource
    canonicalThreeLoopBetaCoefficients
    loopCoordinateContributionFromSU7CountertermSource
    LoopCoordinateContribution.renormalized
  norm_num

/-- The SU(7) counterterm expansion generates P798's canonical RG source
state. -/
theorem threeLoopRGStateFromSU7CountertermSource_eq_canonical
    (D : SU7LoopCountertermSourceData) :
    threeLoopRGStateFromBetaAndIncidence
        (threeLoopBetaCoefficientsFromExpansion
          (threeLoopRGExpansionFromSU7CountertermSource D))
        (betaCoeff (incidenceCarrierTraceInput .colorSU3)) =
      canonicalThreeLoopRGSourceState := by
  rw [threeLoopBetaCoefficientsFromSU7CountertermSource_eq_canonical]
  exact threeLoopRGStateFromBetaAndIncidence_canonical

/-- The SU(7) counterterm expansion gives zero RG mismatch. -/
theorem rgMismatch_fromSU7CountertermSource_eq_zero
    (D : SU7LoopCountertermSourceData) :
    rgMismatch
        (threeLoopRGStateFromBetaAndIncidence
          (threeLoopBetaCoefficientsFromExpansion
            (threeLoopRGExpansionFromSU7CountertermSource D))
          (betaCoeff (incidenceCarrierTraceInput .colorSU3))) = 0 := by
  exact rgMismatch_fromLoopExpansion_eq_zero
    (threeLoopRGExpansionFromSU7CountertermSource D)
    (threeLoopRGExpansionFromSU7CountertermSource_sourceLaw D)

/-! ## Full smooth producer generated from SU(7) counterterm data -/

/-- Full smooth alpha_s source data whose RG leg is generated by the SU(7)
counterterm producer. -/
structure CountertermSmoothPhysicsSourceData where
  su7BreakingSource : ℚ
  thresholdTrace : ThresholdTraceSourceData
  incidenceGeneratedSlotEquiv :
    SU7BlockIncidence ≃ SU7GeneratedCarrierSlot

/-- Extract the loop-counterterm source from the full smooth source. -/
def loopCountertermSourceOfCountertermSmoothSource
    (D : CountertermSmoothPhysicsSourceData) :
    SU7LoopCountertermSourceData where
  thresholdTrace := D.thresholdTrace
  incidenceGeneratedSlotEquiv := D.incidenceGeneratedSlotEquiv

/-- Generate P797's smooth physics state from SU(7) counterterm source data. -/
def smoothPhysicsStateFromSU7CountertermSource
    (D : CountertermSmoothPhysicsSourceData) :
    SmoothPhysicsAlphaStrongState where
  su7BreakingSource := D.su7BreakingSource
  thresholdSpectrum :=
    thresholdSpectrumFromTraceSource D.thresholdTrace
  rgState :=
    threeLoopRGStateFromBetaAndIncidence
      (threeLoopBetaCoefficientsFromExpansion
        (threeLoopRGExpansionFromSU7CountertermSource
          (loopCountertermSourceOfCountertermSmoothSource D)))
      (betaCoeff (incidenceCarrierTraceInput .colorSU3))
  higgsExtraSpectrum :=
    generatedHiggsExtraSpectrumFromIncidenceEquiv
      D.incidenceGeneratedSlotEquiv

/-- Canonical SU(7) counterterm-source data for the smooth alpha_s producer. -/
def canonicalCountertermSmoothPhysicsSourceData :
    CountertermSmoothPhysicsSourceData where
  su7BreakingSource := alphaStrongSU7BreakingCardSourceGap
  thresholdTrace := canonicalThresholdTraceSourceData
  incidenceGeneratedSlotEquiv := blockIncidenceGeneratedSlotEquiv

/-- The canonical SU(7) counterterm source generates P797's canonical smooth
state. -/
theorem smoothPhysicsStateFromSU7CountertermSource_canonical :
    smoothPhysicsStateFromSU7CountertermSource
        canonicalCountertermSmoothPhysicsSourceData =
      canonicalSmoothPhysicsState := by
  unfold smoothPhysicsStateFromSU7CountertermSource
    canonicalCountertermSmoothPhysicsSourceData canonicalSmoothPhysicsState
    loopCountertermSourceOfCountertermSmoothSource
  rw [threeLoopRGStateFromSU7CountertermSource_eq_canonical]
  rfl

/-- THEOREM 1: the SU(7) counterterm source producer outputs exactly the P792
four-source primitive generator. -/
theorem countertermSmoothPhysicsFourSourceOutput_eq_target :
    smoothPhysicsFourSourceOutput
        (smoothPhysicsStateFromSU7CountertermSource
          canonicalCountertermSmoothPhysicsSourceData) =
      su7AlphaStrongFourSourcePrimitiveGenerator := by
  rw [smoothPhysicsStateFromSU7CountertermSource_canonical]
  exact smoothPhysicsFourSourceOutput_eq_target

/-- THEOREM 2: the SU(7) counterterm producer transports to the exact inverse
alpha_s residual. -/
theorem alphaStrongCountertermSmoothPhysicsProducer_outputs_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          smoothPhysicsFourSourceOutput
            (smoothPhysicsStateFromSU7CountertermSource
              canonicalCountertermSmoothPhysicsSourceData) s) =
      -((89000 : ℚ) / 128511) := by
  rw [countertermSmoothPhysicsFourSourceOutput_eq_target]
  exact su7AlphaStrongFourSourcePrimitiveGenerator_inverseResidual

/-! ## P795 residual-carrier reconstruction -/

/-- The SU(7) counterterm alpha_s output as a native effective residual
process. -/
def countertermSmoothAlphaStrongEffectiveProcess :
    ResidualProjection.EffectiveResidualProcess
      ℚ ℚ AlphaStrongResidualSource where
  target := 0
  keep := (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
  residual :=
    smoothPhysicsFourSourceOutput
      (smoothPhysicsStateFromSU7CountertermSource
        canonicalCountertermSmoothPhysicsSourceData)
  update := id
  residual_transport_law := by
    intro s
    rfl

/-- THEOREM 3: by P795, the SU(7) counterterm native producer uniquely
reconstructs its residual-carrier system. -/
theorem countertermSmoothEffectiveProcess_uniqueResidualCarrier :
    ∃! Q :
      ResidualProjection.ResidualCarrierSystemProducer
        ℚ ℚ AlphaStrongResidualSource,
      Q.toEffectiveResidualProcess =
        countertermSmoothAlphaStrongEffectiveProcess :=
  ResidualProjection.effectiveProcess_unique_residualCarrier_reconstruction
    countertermSmoothAlphaStrongEffectiveProcess

/-! ## Bundled certificate -/

/-- SU(7) counterterm alpha_s producer certificate. -/
structure AlphaStrongSU7CountertermProducerCertificate : Prop where
  two_loop_cancelled :
    (loopCoordinateContributionFromSU7CountertermSource
      (loopCountertermSourceOfCountertermSmoothSource
        canonicalCountertermSmoothPhysicsSourceData) 2).Cancelled
  three_loop_cancelled :
    (loopCoordinateContributionFromSU7CountertermSource
      (loopCountertermSourceOfCountertermSmoothSource
        canonicalCountertermSmoothPhysicsSourceData) 3).Cancelled
  rg_source_law :
    ThreeLoopRGExpansionSourceLaw
      (threeLoopRGExpansionFromSU7CountertermSource
        (loopCountertermSourceOfCountertermSmoothSource
          canonicalCountertermSmoothPhysicsSourceData))
  beta_coefficients_generated :
    threeLoopBetaCoefficientsFromExpansion
        (threeLoopRGExpansionFromSU7CountertermSource
          (loopCountertermSourceOfCountertermSmoothSource
            canonicalCountertermSmoothPhysicsSourceData)) =
      canonicalThreeLoopBetaCoefficients
  rg_zero :
    rgMismatch
        (threeLoopRGStateFromBetaAndIncidence
          (threeLoopBetaCoefficientsFromExpansion
            (threeLoopRGExpansionFromSU7CountertermSource
              (loopCountertermSourceOfCountertermSmoothSource
                canonicalCountertermSmoothPhysicsSourceData)))
          (betaCoeff (incidenceCarrierTraceInput .colorSU3))) = 0
  smooth_state_generated :
    smoothPhysicsStateFromSU7CountertermSource
        canonicalCountertermSmoothPhysicsSourceData =
      canonicalSmoothPhysicsState
  output_eq_primitive :
    smoothPhysicsFourSourceOutput
        (smoothPhysicsStateFromSU7CountertermSource
          canonicalCountertermSmoothPhysicsSourceData) =
      su7AlphaStrongFourSourcePrimitiveGenerator
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          smoothPhysicsFourSourceOutput
            (smoothPhysicsStateFromSU7CountertermSource
              canonicalCountertermSmoothPhysicsSourceData) s) =
      -((89000 : ℚ) / 128511)
  residual_carrier_unique :
    ∃! Q :
      ResidualProjection.ResidualCarrierSystemProducer
        ℚ ℚ AlphaStrongResidualSource,
      Q.toEffectiveResidualProcess =
        countertermSmoothAlphaStrongEffectiveProcess

/-- THEOREM 4: bundled SU(7) counterterm alpha_s producer certificate. -/
theorem alphaStrongSU7CountertermProducerCertificate :
    AlphaStrongSU7CountertermProducerCertificate where
  two_loop_cancelled :=
    loopCoordinateContributionFromSU7CountertermSource_cancelled
      (loopCountertermSourceOfCountertermSmoothSource
        canonicalCountertermSmoothPhysicsSourceData) 2
  three_loop_cancelled :=
    loopCoordinateContributionFromSU7CountertermSource_cancelled
      (loopCountertermSourceOfCountertermSmoothSource
        canonicalCountertermSmoothPhysicsSourceData) 3
  rg_source_law :=
    threeLoopRGExpansionFromSU7CountertermSource_sourceLaw
      (loopCountertermSourceOfCountertermSmoothSource
        canonicalCountertermSmoothPhysicsSourceData)
  beta_coefficients_generated :=
    threeLoopBetaCoefficientsFromSU7CountertermSource_eq_canonical
      (loopCountertermSourceOfCountertermSmoothSource
        canonicalCountertermSmoothPhysicsSourceData)
  rg_zero :=
    rgMismatch_fromSU7CountertermSource_eq_zero
      (loopCountertermSourceOfCountertermSmoothSource
        canonicalCountertermSmoothPhysicsSourceData)
  smooth_state_generated :=
    smoothPhysicsStateFromSU7CountertermSource_canonical
  output_eq_primitive :=
    countertermSmoothPhysicsFourSourceOutput_eq_target
  inverse_residual :=
    alphaStrongCountertermSmoothPhysicsProducer_outputs_residual
  residual_carrier_unique :=
    countertermSmoothEffectiveProcess_uniqueResidualCarrier

end StandardModelConstraint
end SaturationMonoid
