import H0mework.Physics.AlphaSources.P801

/-!
# Proposition 802: structural-carrier alpha_s smooth producer

P801 removes the final naked `su7BreakingSource : ℚ` scalar from the smooth
alpha_s producer input.  Its remaining full-bottom input still carries two
objects directly:

* `thresholdTrace : ThresholdTraceSourceData`;
* `incidenceGeneratedSlotEquiv : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot`.

This file lowers those two inputs to structural SU(7) carrier certificates:

* the threshold trace is generated from the all-factor one-loop carrier
  receipt, read at the color factor;
* the Higgs/extra incidence equivalence is generated from the endpoint
  orientation uniqueness certificate.

Together with the P801 card-source data for the SU(7)-breaking coordinate, the
result is a structural-carrier producer for the same smooth alpha_s output and
the same exact inverse residual `-89000/128511`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open scoped BigOperators

/-! ## Threshold trace from the one-loop carrier receipt -/

/-- Generate threshold trace source data from the unified one-loop carrier
receipt, read at the QCD/color factor. -/
def thresholdTraceSourceFromOneLoopCarrier
    (_C : StandardModelOneLoopCarrierFinalReceipt) :
    ThresholdTraceSourceData where
  lowEnergyColorTrace := standardModelAsymptoticB0 .colorSU3
  unifiedIncidenceColorTrace := betaCoeff (incidenceCarrierTraceInput .colorSU3)

/-- The one-loop carrier receipt proves that the generated threshold trace is
balanced. -/
theorem thresholdTraceSourceFromOneLoopCarrier_balanced
    (C : StandardModelOneLoopCarrierFinalReceipt) :
    ThresholdTraceSourceBalanced
      (thresholdTraceSourceFromOneLoopCarrier C) := by
  unfold ThresholdTraceSourceBalanced
    thresholdTraceSourceFromOneLoopCarrier
  exact (C.asymptotic_b0 .colorSU3).symm

/-- The canonical one-loop carrier receipt emits P798's canonical threshold
source data. -/
theorem thresholdTraceSourceFromOneLoopCarrier_canonical :
    thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt =
      canonicalThresholdTraceSourceData := by
  rfl

/-! ## Higgs/extra incidence equivalence from orientation uniqueness -/

/-- Generate the incidence/generated-slot equivalence from the endpoint
orientation uniqueness certificate. -/
def incidenceEquivFromOrientationCertificate
    (C : SU7IncidenceOrientationUniquenessCertificate) :
    SU7BlockIncidence ≃ SU7GeneratedCarrierSlot :=
  C.incidence_equiv

/-- Any incidence/generated-slot equivalence emits the canonical P797
Higgs/extra spectrum, because the spectrum records only the two finite carrier
cardinalities. -/
theorem generatedHiggsExtraSpectrumFromAnyIncidenceEquiv_eq_canonical
    (e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) :
    generatedHiggsExtraSpectrumFromIncidenceEquiv e =
      canonicalGeneratedHiggsExtraSpectrum := by
  rfl

/-- The canonical orientation certificate emits the P459/P798 equivalence. -/
theorem incidenceEquivFromOrientationCertificate_canonical :
    incidenceEquivFromOrientationCertificate
        su7IncidenceOrientationUniquenessCertificate =
      blockIncidenceGeneratedSlotEquiv := by
  rfl

/-! ## Structural-carrier source data -/

/-- Structural-carrier source data for the alpha_s smooth producer.  It no
longer contains threshold trace values or an equivalence directly; it contains
the receipts that generate them. -/
structure StructuralCarrierSmoothPhysicsSourceData where
  breakingCard : SU7BreakingCardSourceData
  oneLoopCarrier : StandardModelOneLoopCarrierFinalReceipt
  orientation :
    SU7IncidenceOrientationUniquenessCertificate

/-- Extract P800's loop-counterterm source from structural-carrier source
data. -/
def loopCountertermSourceOfStructuralCarrierSource
    (D : StructuralCarrierSmoothPhysicsSourceData) :
    SU7LoopCountertermSourceData where
  thresholdTrace :=
    thresholdTraceSourceFromOneLoopCarrier D.oneLoopCarrier
  incidenceGeneratedSlotEquiv :=
    incidenceEquivFromOrientationCertificate D.orientation

/-- Generate P797's smooth state from structural-carrier source data. -/
def smoothPhysicsStateFromStructuralCarrierSource
    (D : StructuralCarrierSmoothPhysicsSourceData) :
    SmoothPhysicsAlphaStrongState where
  su7BreakingSource := su7BreakingSourceFromCardData D.breakingCard
  thresholdSpectrum :=
    thresholdSpectrumFromTraceSource
      (thresholdTraceSourceFromOneLoopCarrier D.oneLoopCarrier)
  rgState :=
    threeLoopRGStateFromBetaAndIncidence
      (threeLoopBetaCoefficientsFromExpansion
        (threeLoopRGExpansionFromSU7CountertermSource
          (loopCountertermSourceOfStructuralCarrierSource D)))
      (betaCoeff (incidenceCarrierTraceInput .colorSU3))
  higgsExtraSpectrum :=
    generatedHiggsExtraSpectrumFromIncidenceEquiv
      (incidenceEquivFromOrientationCertificate D.orientation)

/-- Canonical structural-carrier source data. -/
def canonicalStructuralCarrierSmoothPhysicsSourceData :
    StructuralCarrierSmoothPhysicsSourceData where
  breakingCard := canonicalSU7BreakingCardSourceData
  oneLoopCarrier := standardModelOneLoopCarrierFinalReceipt
  orientation := su7IncidenceOrientationUniquenessCertificate

/-- The canonical structural-carrier source generates P797's canonical smooth
state. -/
theorem smoothPhysicsStateFromStructuralCarrierSource_canonical :
    smoothPhysicsStateFromStructuralCarrierSource
        canonicalStructuralCarrierSmoothPhysicsSourceData =
      canonicalSmoothPhysicsState := by
  unfold smoothPhysicsStateFromStructuralCarrierSource
    canonicalStructuralCarrierSmoothPhysicsSourceData canonicalSmoothPhysicsState
    loopCountertermSourceOfStructuralCarrierSource
  rw [su7BreakingSourceFromCardData_canonical,
    threeLoopRGStateFromSU7CountertermSource_eq_canonical,
    generatedHiggsExtraSpectrumFromAnyIncidenceEquiv_eq_canonical]
  rfl

/-- THEOREM 1: the structural-carrier source producer outputs exactly the P792
four-source primitive generator. -/
theorem structuralCarrierSmoothPhysicsFourSourceOutput_eq_target :
    smoothPhysicsFourSourceOutput
        (smoothPhysicsStateFromStructuralCarrierSource
          canonicalStructuralCarrierSmoothPhysicsSourceData) =
      su7AlphaStrongFourSourcePrimitiveGenerator := by
  rw [smoothPhysicsStateFromStructuralCarrierSource_canonical]
  exact smoothPhysicsFourSourceOutput_eq_target

/-- THEOREM 2: the structural-carrier producer transports to the exact inverse
alpha_s residual. -/
theorem alphaStrongStructuralCarrierSmoothPhysicsProducer_outputs_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          smoothPhysicsFourSourceOutput
            (smoothPhysicsStateFromStructuralCarrierSource
              canonicalStructuralCarrierSmoothPhysicsSourceData) s) =
      -((89000 : ℚ) / 128511) := by
  rw [structuralCarrierSmoothPhysicsFourSourceOutput_eq_target]
  exact su7AlphaStrongFourSourcePrimitiveGenerator_inverseResidual

/-! ## P795 residual-carrier reconstruction -/

/-- The structural-carrier alpha_s output as a native effective residual
process. -/
def structuralCarrierSmoothAlphaStrongEffectiveProcess :
    ResidualProjection.EffectiveResidualProcess
      ℚ ℚ AlphaStrongResidualSource where
  target := 0
  keep := (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
  residual :=
    smoothPhysicsFourSourceOutput
      (smoothPhysicsStateFromStructuralCarrierSource
        canonicalStructuralCarrierSmoothPhysicsSourceData)
  update := id
  residual_transport_law := by
    intro s
    rfl

/-- THEOREM 3: by P795, the structural-carrier native producer uniquely
reconstructs its residual-carrier system. -/
theorem structuralCarrierSmoothEffectiveProcess_uniqueResidualCarrier :
    ∃! Q :
      ResidualProjection.ResidualCarrierSystemProducer
        ℚ ℚ AlphaStrongResidualSource,
      Q.toEffectiveResidualProcess =
        structuralCarrierSmoothAlphaStrongEffectiveProcess :=
  ResidualProjection.effectiveProcess_unique_residualCarrier_reconstruction
    structuralCarrierSmoothAlphaStrongEffectiveProcess

/-! ## Bundled certificate -/

/-- Structural-carrier alpha_s producer certificate. -/
structure AlphaStrongStructuralCarrierProducerCertificate : Prop where
  threshold_from_one_loop :
    thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt =
      canonicalThresholdTraceSourceData
  threshold_balanced :
    ThresholdTraceSourceBalanced
      (thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt)
  incidence_equiv_from_orientation :
    incidenceEquivFromOrientationCertificate
        su7IncidenceOrientationUniquenessCertificate =
      blockIncidenceGeneratedSlotEquiv
  higgs_extra_generated :
    generatedHiggsExtraSpectrumFromIncidenceEquiv
      (incidenceEquivFromOrientationCertificate
        su7IncidenceOrientationUniquenessCertificate) =
      canonicalGeneratedHiggsExtraSpectrum
  smooth_state_generated :
    smoothPhysicsStateFromStructuralCarrierSource
        canonicalStructuralCarrierSmoothPhysicsSourceData =
      canonicalSmoothPhysicsState
  output_eq_primitive :
    smoothPhysicsFourSourceOutput
        (smoothPhysicsStateFromStructuralCarrierSource
          canonicalStructuralCarrierSmoothPhysicsSourceData) =
      su7AlphaStrongFourSourcePrimitiveGenerator
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          smoothPhysicsFourSourceOutput
            (smoothPhysicsStateFromStructuralCarrierSource
              canonicalStructuralCarrierSmoothPhysicsSourceData) s) =
      -((89000 : ℚ) / 128511)
  residual_carrier_unique :
    ∃! Q :
      ResidualProjection.ResidualCarrierSystemProducer
        ℚ ℚ AlphaStrongResidualSource,
      Q.toEffectiveResidualProcess =
        structuralCarrierSmoothAlphaStrongEffectiveProcess

/-- THEOREM 4: bundled structural-carrier alpha_s producer certificate. -/
theorem alphaStrongStructuralCarrierProducerCertificate :
    AlphaStrongStructuralCarrierProducerCertificate where
  threshold_from_one_loop :=
    thresholdTraceSourceFromOneLoopCarrier_canonical
  threshold_balanced :=
    thresholdTraceSourceFromOneLoopCarrier_balanced
      standardModelOneLoopCarrierFinalReceipt
  incidence_equiv_from_orientation :=
    incidenceEquivFromOrientationCertificate_canonical
  higgs_extra_generated :=
    generatedHiggsExtraSpectrumFromAnyIncidenceEquiv_eq_canonical
      (incidenceEquivFromOrientationCertificate
        su7IncidenceOrientationUniquenessCertificate)
  smooth_state_generated :=
    smoothPhysicsStateFromStructuralCarrierSource_canonical
  output_eq_primitive :=
    structuralCarrierSmoothPhysicsFourSourceOutput_eq_target
  inverse_residual :=
    alphaStrongStructuralCarrierSmoothPhysicsProducer_outputs_residual
  residual_carrier_unique :=
    structuralCarrierSmoothEffectiveProcess_uniqueResidualCarrier

end StandardModelConstraint
end SaturationMonoid
