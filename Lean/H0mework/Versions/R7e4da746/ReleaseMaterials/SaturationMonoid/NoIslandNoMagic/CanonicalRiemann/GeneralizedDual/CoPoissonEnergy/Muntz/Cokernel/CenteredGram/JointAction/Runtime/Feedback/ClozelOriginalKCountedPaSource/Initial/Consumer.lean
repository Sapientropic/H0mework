import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Gram.Action
import H0mework.Realization.Topology.DualExtension
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial
open Complex Filter MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward
open SourceGeneratedTestHilbertGeneralizedDual
open scoped BigOperators Topology InnerProductSpace
namespace Native
export CenteredGram.IntegralGraphJointAction.OriginalKCountedPaSource (actualField counted)
end Native
namespace Actual
export CenteredGram.IntegralGraphJointAction.OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
  (actual_raw_field sourceIndex)
end Actual
namespace PA
export CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalPaAction (E Q wholePa_normal_read)
end PA
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
abbrev PaSourceFace : Type := ↥(burnolCompactCoPoissonClosedRange.toSubmodule)
local instance : CompleteSpace PaSourceFace := by
  apply IsComplete.completeSpace_coe
  exact burnolCompactCoPoissonClosedRange.isClosed.isComplete

/-- This is the original complete two-parity source landing, restricted to its generated closure. -/
def landingFeature : BurnolCompactCoPoissonLinearSource →ₗ[ℂ] PaSourceFace :=
  burnolCompactCoPoissonLanding.codRestrict burnolCompactCoPoissonClosedRange.toSubmodule
    (fun u=>(LinearMap.range burnolCompactCoPoissonLanding).le_topologicalClosure ⟨u,rfl⟩)

private theorem feature_dense : DenseRange landingFeature := by
  change Dense (Set.range landingFeature)
  rw [Subtype.dense_iff]
  have image : Subtype.val '' (Set.range landingFeature)=Set.range burnolCompactCoPoissonLanding := by
    ext x
    constructor
    · rintro ⟨y,⟨u,rfl⟩,rfl⟩
      exact ⟨u,rfl⟩
    · rintro ⟨u,rfl⟩
      exact ⟨landingFeature u,⟨u,rfl⟩,rfl⟩
  intro x hx
  change x∈closure (Set.range burnolCompactCoPoissonLanding) at hx
  exact Eq.mpr (congrArg (fun s:Set BurnolPaAmbientCarrier=>x∈closure s) image) hx

private theorem functional_bound (c:BurnolCompletedMellinCoordinate) (k N:ℕ) :
    ∃C:ℝ,∀u,‖arithmeticFunctional c k N u‖≤C*‖landingFeature u‖ := by
  refine ⟨‖DualSource.source N (Material.actualIterate c
    (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k)‖,?_⟩
  intro u
  rw [functional_read]
  exact norm_inner_le_norm _ _

/-- The extension is built from the arithmetic functional, not from a projection of the target. -/
def sourceExtension (c:BurnolCompletedMellinCoordinate) (k N:ℕ) :
    BoundedExtension (C:=BurnolCompactCoPoissonLinearSource) (H:=PaSourceFace)
      landingFeature (arithmeticFunctional c k N) where
  extension := (arithmeticFunctional c k N).extendOfNorm landingFeature
  restricts := by
    apply LinearMap.ext
    intro u
    exact LinearMap.extendOfNorm_eq feature_dense (functional_bound c k N) u

def paSource (c:BurnolCompletedMellinCoordinate) (k N:ℕ) : PaSourceFace :=
  (sourceExtension c k N).rieszRepresentative

theorem pa_source_read (c:BurnolCompletedMellinCoordinate) (k N:ℕ)
    (u:BurnolCompactCoPoissonLinearSource) :
    inner ℂ (paSource c k N) (landingFeature u)=arithmeticFunctional c k N u :=
  (sourceExtension c k N).riesz_readback u

private theorem projected_pair (value:BurnolL2) (test:PaSourceFace) :
    inner ℂ (PA.E value:BurnolL2) (test.1:BurnolL2)=inner ℂ value (test.1:BurnolL2) := by
  change inner ℂ (PA.E value) test.1=inner ℂ value (test.1:BurnolL2)
  rw [←inner_conj_symm,PA.wholePa_normal_read value test.1 test.property]
  exact inner_conj_symm _ _

/-- Orthogonal recognition is downstream of the independently generated scalar functional. -/
theorem pa_source_projection (c:BurnolCompletedMellinCoordinate) (k N:ℕ) :
    (paSource c k N:BurnolPaAmbientCarrier)=PA.E
      (DualSource.source N (Material.actualIterate c
        (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k)) := by
  let raw:=DualSource.source N (Material.actualIterate c
        (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k)
  let target:PaSourceFace:=⟨PA.E raw,Submodule.starProjection_apply_mem _ _⟩
  have pair:∀u,inner ℂ (paSource c k N) (landingFeature u)=inner ℂ target (landingFeature u) := by
    intro u
    rw [pa_source_read,functional_read]
    exact (projected_pair raw (landingFeature u)).symm
  have full := feature_dense.equalizer (innerSL ℂ (paSource c k N)).continuous
    (innerSL ℂ target).continuous (funext pair)
  have equal:paSource c k N=target := ext_inner_right ℂ (congrFun full)
  exact congrArg Subtype.val equal

/-- Both parity and the inherited constant cell remain in every finite window of the generated Pa source. -/
theorem source_finite_window (c:BurnolCompletedMellinCoordinate) (k N K:ℕ) (X:ℝ) (covers:4*X≤K) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff X (paSource c k N:BurnolL2)=
      OriginalPaPhysicalGreen.originalPhysicalCutoff X
        (OriginalPaPhysicalGreen.finiteSourceAction (burnolMobiusSourceL2 (paSource c k N:BurnolPaAmbientCarrier)) K)+
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius (paSource c k N:BurnolPaAmbientCarrier) •
        OriginalPaPhysicalGreen.physicalMeanCell X :=
  OriginalPaPhysicalGreen.original_pa_finite_source_action _ (paSource c k N).property X K covers

private theorem comb_source : (burnolPaCombApproximation 0:BurnolL2)=
    2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2)) := by
  have original:=burnolPaCombApproximation_raw 0
  norm_num [burnolPaCombSourceWidth] at original
  simpa only [two_smul] using original

section Original
open CenteredGram.IntegralGraphJointAction
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

/-- The original Xi-order source, with its original occurrence, is consumed only at readback. -/
theorem actual_initial_source (depth N:ℕ) :
    (paSource c (m+2) N:BurnolPaAmbientCarrier)=PA.E
      (Native.actualField observation nontrivial half depth 0 N) := by
  rw [pa_source_projection]
  unfold Native.actualField Native.counted
  rw [Actual.actual_raw_field,comb_source]
  rfl

def initialSigma (N:ℕ) : BurnolL2 :=
  burnolTateReciprocalL2 (burnolMobiusSourceL2 (paSource c (m+2) N:BurnolPaAmbientCarrier))

theorem actual_initial_sigma (depth N:ℕ) :
    initialSigma observation half N=burnolTateReciprocalL2
      (burnolMobiusSourceL2 (PA.E (Native.actualField observation nontrivial half depth 0 N))) := by
  unfold initialSigma
  rw [actual_initial_source observation nontrivial half depth N]

theorem actual_initial_fee (depth N:ℕ) :
    inner ℂ (FiniteForcing.source N (OriginalKFiniteOrderRelease.UnitPowerSource.paPowerField observation half:BurnolL2))
      (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth 0)=
      OriginalKFiniteOrderRelease.UnitPowerSource.feedbackCoefficient observation half*
        burnolPaResolventSourceCoefficient c (paSource c (m+2) N:BurnolPaAmbientCarrier) := by
  rw [actual_initial_source observation nontrivial half depth N]
  exact OriginalKCountedPaSource.Consumer.actual_pa_fee observation nontrivial half depth 0 N

theorem actual_initial_Q_price (depth N:ℕ) :
    inner ℂ (FiniteForcing.source N (OriginalKFiniteOrderRelease.UnitPowerJordanSource.sourceQ observation half))
      (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth 0)=
      inner ℂ (FiniteForcing.source N (OriginalKFiniteOrderRelease.UnitPowerSource.fulladjointPowerZ observation half))
        (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth 0)-
      OriginalKFiniteOrderRelease.UnitPowerSource.feedbackCoefficient observation half*
        burnolPaResolventSourceCoefficient c (paSource c (m+2) N:BurnolPaAmbientCarrier)-
      inner ℂ (CountedSchur.RContact.outsideFinite c m N)
        (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth 0) := by
  rw [actual_initial_source observation nontrivial half depth N]
  exact OriginalKCountedPaSource.Consumer.actual_counted_Q_price observation nontrivial half depth 0 N

/-- The original receipt/whole-next remains the owner of the counted action; no new actor is made. -/
def read (depth N:ℕ) :=
  PProd.mk (OriginalKCountedPaSource.Consumer.read observation nontrivial half depth 0 N) <|
  PProd.mk (paSource c (m+2) N) <| PProd.mk (initialSigma observation half N) <|
  PProd.mk (actual_initial_source observation nontrivial half depth N) <|
  PProd.mk (actual_initial_sigma observation nontrivial half depth N) <|
  PProd.mk (actual_initial_fee observation nontrivial half depth N)
    (actual_initial_Q_price observation nontrivial half depth N)
end Original
end CountedPaInitial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
