import H0mework.Physics.DiracEvolution.SafeCanonicalAffineGreenGeneratedLimitRecognition
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Canonical affine tail-energy center

This module extracts the unique minimum-energy point of the complete
source-owned affine history and proves that continuous reads which stabilize
along the history are inherited by that point.  No selector, target field,
residual, or new evolution is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenAssembly
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenGeneratedLimitRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineRieszActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracMatterSpatialEnergyBalance
open scoped BoundedContinuousFunction

noncomputable section

set_option autoImplicit false

def canonicalAffineTimeMeasure (timeEnd : ℝ) : Measure (Icc 0 timeEnd) :=
  Measure.comap (Subtype.val : Icc 0 timeEnd → ℝ) (volume : Measure ℝ)

instance canonicalAffineTimeFiniteMeasure (timeEnd : ℝ) :
    IsFiniteMeasure (canonicalAffineTimeMeasure timeEnd) where
  measure_univ_lt_top := by
    letI : MeasureSpace (Icc 0 timeEnd) := Measure.Subtype.measureSpace
    change (volume : Measure (Icc 0 timeEnd)) Set.univ < ⊤
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top

def canonicalAffineCorrectionMassHistoryAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D)
    (testCount : ℕ) : CauchySafeMatterSpatialL2 a b :=
  fixedP506L0CauchySafeMatterL2MassEquiv
    time.1 a b boxOrder D matrixBound
    (canonicalAffineCorrectionL2
      timeEnd timeNonnegative a b testCount time.1)

def canonicalAffineCorrectionMassTailAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D)
    (tailStart : ℕ) : Set (CauchySafeMatterSpatialL2 a b) :=
  closedConvexHull ℝ (Set.range fun offset ↦
    canonicalAffineCorrectionMassHistoryAt
      timeEnd timeNonnegative a b boxOrder time D matrixBound
      (tailStart + offset))

theorem canonicalAffineCorrectionMassHistoryAt_subsequence_tendsto_weak
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) :
    Tendsto
      (fun sequenceIndex ↦ toWeakSpace ℝ (CauchySafeMatterSpatialL2 a b)
        (canonicalAffineCorrectionMassHistoryAt
          timeEnd timeNonnegative a b boxOrder time D matrixBound
          (occurrence.weakLimit.subsequence sequenceIndex)))
      atTop
      (nhds (toWeakSpace ℝ (CauchySafeMatterSpatialL2 a b)
        (occurrence.correctionMassRepresentative time))) := by
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ (CauchySafeMatterSpatialL2 a b)).flip)
    (l := atTop)
    (f := fun sequenceIndex ↦
      toWeakSpace ℝ (CauchySafeMatterSpatialL2 a b)
        (canonicalAffineCorrectionMassHistoryAt
          timeEnd timeNonnegative a b boxOrder time D matrixBound
          (occurrence.weakLimit.subsequence sequenceIndex)))
    (x := toWeakSpace ℝ (CauchySafeMatterSpatialL2 a b)
      (occurrence.correctionMassRepresentative time))
    (by
      intro first second equalEvaluations
      by_contra distinct
      obtain ⟨test, separated⟩ :=
        SeparatingDual.exists_separating_of_ne (R := ℝ) distinct
      exact separated (DFunLike.congr_fun equalEvaluations test))).2 ?_
  intro test
  let physicalTest : CauchySafeMatterSpatialL2 a b :=
    (InnerProductSpace.toDual ℝ
      (CauchySafeMatterSpatialL2 a b)).symm test
  have readConvergence :=
    canonicalAffineCorrectionAllL2MassRead_weakConvergence
      timeEnd timeNonnegative a b boxOrder occurrence time physicalTest
  change Tendsto
    (fun sequenceIndex ↦ test
      (canonicalAffineCorrectionMassHistoryAt
        timeEnd timeNonnegative a b boxOrder time D matrixBound
        (occurrence.weakLimit.subsequence sequenceIndex)))
    atTop (nhds (test (occurrence.correctionMassRepresentative time)))
  have limitRead :
      test (occurrence.correctionMassRepresentative time) =
        inner ℝ (occurrence.correctionMassRepresentative time) physicalTest := by
    rw [← InnerProductSpace.toDual_symm_apply]
    exact real_inner_comm _ _
  rw [limitRead]
  apply readConvergence.congr'
  exact Filter.Eventually.of_forall fun sequenceIndex ↦ by
    have readEq := congrArg
      (fun read : CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ ↦
        read physicalTest)
      (canonicalAffineCorrectionAllL2MassRead_eq_massForm
        timeEnd timeNonnegative a b boxOrder occurrence.C
        occurrence.CNonnegative occurrence.operatorBound
        (occurrence.weakLimit.subsequence sequenceIndex) time D matrixBound)
    symm
    let massHistory := canonicalAffineCorrectionMassHistoryAt
      timeEnd timeNonnegative a b boxOrder time D matrixBound
      (occurrence.weakLimit.subsequence sequenceIndex)
    change test massHistory = _
    calc
      test massHistory = inner ℝ physicalTest massHistory := by
        exact (InnerProductSpace.toDual_symm_apply
          (x := massHistory) (y := test)).symm
      _ = inner ℝ massHistory physicalTest := real_inner_comm _ _
      _ = fixedP506L0CauchySafeMatterL2MassForm
          time.1 a b D matrixBound
          (canonicalAffineCorrectionL2 timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) time.1)
          physicalTest := by
        exact fixedP506L0CauchySafeMatterL2MassEquiv_pairing
          time.1 a b boxOrder D matrixBound _ _
      _ = canonicalAffineCorrectionAllL2MassRead
          timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
          (occurrence.weakLimit.subsequence sequenceIndex) time
          physicalTest := readEq.symm

private theorem weakLimit_mem_closedConvexHull_tail
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (history : ℕ → H)
    (subsequence : ℕ → ℕ)
    (subsequenceStrict : StrictMono subsequence)
    (limit : H)
    (weakConvergence : Tendsto
      (fun sequenceIndex ↦ toWeakSpace ℝ H
        (history (subsequence sequenceIndex)))
      atTop (nhds (toWeakSpace ℝ H limit)))
    (tailStart : ℕ) :
    limit ∈ closedConvexHull ℝ
      (Set.range fun offset ↦ history (tailStart + offset)) := by
  let strongTail : Set H := Set.range fun offset ↦ history (tailStart + offset)
  let weakTail : Set (WeakSpace ℝ H) :=
    toWeakSpace ℝ H '' strongTail
  have eventuallyTail : ∀ᶠ sequenceIndex : ℕ in atTop,
      toWeakSpace ℝ H (history (subsequence sequenceIndex)) ∈ weakTail := by
    have indexEventually : ∀ᶠ sequenceIndex : ℕ in atTop,
        tailStart ≤ subsequence sequenceIndex :=
      subsequenceStrict.tendsto_atTop (eventually_ge_atTop tailStart)
    filter_upwards [indexEventually] with sequenceIndex indexLarge
    refine ⟨history (subsequence sequenceIndex), ?_, rfl⟩
    refine ⟨subsequence sequenceIndex - tailStart, ?_⟩
    exact congrArg history (Nat.add_sub_of_le indexLarge)
  have weakMemClosure :
      toWeakSpace ℝ H limit ∈ closure weakTail :=
    mem_closure_of_tendsto weakConvergence eventuallyTail
  have weakMemHull :
      toWeakSpace ℝ H limit ∈ closedConvexHull ℝ weakTail :=
    (closure_subset_closedConvexHull (𝕜 := ℝ)) weakMemClosure
  have imageHull :
      toWeakSpace ℝ H '' closedConvexHull ℝ strongTail =
        closedConvexHull ℝ weakTail :=
    toWeakSpace_closedConvexHull_eq (𝕜 := ℝ) (E := H)
  rw [← imageHull] at weakMemHull
  obtain ⟨representative, representativeMem, representativeEq⟩ := weakMemHull
  have representativeIdentity : representative = limit :=
    (toWeakSpace ℝ H).injective representativeEq
  simpa [strongTail, representativeIdentity] using representativeMem

theorem correctionMassRepresentative_mem_canonicalAffineCorrectionMassTailAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D)
    (tailStart : ℕ) :
    occurrence.correctionMassRepresentative time ∈
      canonicalAffineCorrectionMassTailAt
        timeEnd timeNonnegative a b boxOrder time D matrixBound tailStart := by
  let H := CauchySafeMatterSpatialL2 a b
  let history : ℕ → H := fun testCount ↦
    canonicalAffineCorrectionMassHistoryAt
      timeEnd timeNonnegative a b boxOrder time D matrixBound testCount
  have weakConvergence : Tendsto
      (fun sequenceIndex ↦ toWeakSpace ℝ H
        (history (occurrence.weakLimit.subsequence sequenceIndex)))
      atTop
      (nhds (toWeakSpace ℝ H
        (occurrence.correctionMassRepresentative time))) := by
    exact canonicalAffineCorrectionMassHistoryAt_subsequence_tendsto_weak
      timeEnd timeNonnegative a b boxOrder occurrence time D matrixBound
  change occurrence.correctionMassRepresentative time ∈
    closedConvexHull ℝ (Set.range fun offset ↦ history (tailStart + offset))
  exact weakLimit_mem_closedConvexHull_tail history
    occurrence.weakLimit.subsequence occurrence.weakLimit.subsequenceStrict
    (occurrence.correctionMassRepresentative time) weakConvergence tailStart

def canonicalAffineCorrectionMassTailCoreAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) : Set (CauchySafeMatterSpatialL2 a b) :=
  ⋂ tailStart, canonicalAffineCorrectionMassTailAt
    timeEnd timeNonnegative a b boxOrder time D matrixBound tailStart

theorem correctionMassRepresentative_mem_canonicalAffineCorrectionMassTailCoreAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) :
    occurrence.correctionMassRepresentative time ∈
      canonicalAffineCorrectionMassTailCoreAt
        timeEnd timeNonnegative a b boxOrder time D matrixBound := by
  rw [canonicalAffineCorrectionMassTailCoreAt, mem_iInter]
  intro tailStart
  exact correctionMassRepresentative_mem_canonicalAffineCorrectionMassTailAt
    timeEnd timeNonnegative a b boxOrder occurrence time D matrixBound tailStart

theorem canonicalAffineCorrectionMassTailCoreAt_isClosed
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) :
    IsClosed (canonicalAffineCorrectionMassTailCoreAt
      timeEnd timeNonnegative a b boxOrder time D matrixBound) := by
  unfold canonicalAffineCorrectionMassTailCoreAt
  exact isClosed_iInter fun _ ↦ isClosed_closedConvexHull

theorem canonicalAffineCorrectionMassTailCoreAt_convex
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) :
    Convex ℝ (canonicalAffineCorrectionMassTailCoreAt
      timeEnd timeNonnegative a b boxOrder time D matrixBound) := by
  unfold canonicalAffineCorrectionMassTailCoreAt
  exact convex_iInter fun _ ↦ convex_closedConvexHull

private theorem norm_minimizer_unique
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    {K : Set H}
    (convexK : Convex ℝ K)
    {first second : H}
    (firstMem : first ∈ K)
    (secondMem : second ∈ K)
    (firstMinimal :
      ‖(0 : H) - first‖ = ⨅ candidate : K, ‖(0 : H) - candidate‖)
    (secondMinimal :
      ‖(0 : H) - second‖ = ⨅ candidate : K, ‖(0 : H) - candidate‖) :
    first = second := by
  have firstCharacterization :=
    (norm_eq_iInf_iff_real_inner_le_zero convexK firstMem).1 firstMinimal
  have secondCharacterization :=
    (norm_eq_iInf_iff_real_inner_le_zero convexK secondMem).1 secondMinimal
  have firstAgainstSecond := firstCharacterization second secondMem
  have secondAgainstFirst := secondCharacterization first firstMem
  have identity :
      inner ℝ (second - first) (second - first) =
        inner ℝ ((0 : H) - first) (second - first) +
          inner ℝ ((0 : H) - second) (first - second) := by
    simp only [zero_sub, inner_neg_left, inner_sub_left, inner_sub_right]
    ring
  have selfNonpositive :
      inner ℝ (second - first) (second - first) ≤ 0 := by
    rw [identity]
    exact add_nonpos firstAgainstSecond secondAgainstFirst
  have differenceZero : second - first = 0 :=
    inner_self_eq_zero.mp
      (le_antisymm selfNonpositive (real_inner_self_nonneg :
        0 ≤ inner ℝ (second - first) (second - first)))
  exact (sub_eq_zero.mp differenceZero).symm

private def hilbertHistoryTail
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (history : ℕ → H)
    (tailStart : ℕ) : Set H :=
  closedConvexHull ℝ (Set.range fun offset ↦ history (tailStart + offset))

private def hilbertHistoryTailCore
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (history : ℕ → H) : Set H :=
  ⋂ tailStart, hilbertHistoryTail history tailStart

private theorem hilbertHistoryTailCore_read_eq_of_eventually_exact
    {H E : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (history : ℕ → H)
    (read : H →L[ℝ] E)
    (value : E)
    (entry : ℕ)
    (readExact : ∀ index, entry ≤ index → read (history index) = value)
    {candidate : H}
    (candidateMem : candidate ∈ hilbertHistoryTailCore history) :
    read candidate = value := by
  have candidateTail : candidate ∈ hilbertHistoryTail history entry :=
    mem_iInter.mp candidateMem entry
  have tailRangeSubset :
      Set.range (fun offset ↦ history (entry + offset)) ⊆ read ⁻¹' {value} := by
    rintro point ⟨offset, rfl⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      readExact (entry + offset) (Nat.le_add_right entry offset)
  have tailHullSubset :
      hilbertHistoryTail history entry ⊆ read ⁻¹' {value} := by
    exact closedConvexHull_min tailRangeSubset
      ((convex_singleton value).linear_preimage read.toLinearMap)
      (isClosed_singleton.preimage read.continuous)
  exact Set.mem_singleton_iff.mp (tailHullSubset candidateTail)

private theorem hilbertHistoryTailCore_read_eq_of_tendsto
    {H E : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (history : ℕ → H)
    (read : H →L[ℝ] E)
    (value : E)
    (readTendsto : Tendsto (fun index ↦ read (history index)) atTop
      (nhds value))
    {candidate : H}
    (candidateMem : candidate ∈ hilbertHistoryTailCore history) :
    read candidate = value := by
  by_contra readNe
  have readDistancePositive : 0 < dist (read candidate) value :=
    dist_pos.mpr readNe
  let radius := dist (read candidate) value / 2
  have radiusPositive : 0 < radius := by
    dsimp [radius]
    positivity
  obtain ⟨entry, tailClose⟩ :=
    Metric.tendsto_atTop.mp readTendsto radius radiusPositive
  have candidateTail : candidate ∈ hilbertHistoryTail history entry :=
    mem_iInter.mp candidateMem entry
  have tailRangeSubset :
      Set.range (fun offset ↦ history (entry + offset)) ⊆
        read ⁻¹' Metric.closedBall value radius := by
    rintro point ⟨offset, rfl⟩
    exact Metric.mem_closedBall'.mpr (by
      simpa [dist_comm] using (tailClose (entry + offset)
        (Nat.le_add_right entry offset)).le)
  have tailHullSubset :
      hilbertHistoryTail history entry ⊆
        read ⁻¹' Metric.closedBall value radius := by
    exact closedConvexHull_min tailRangeSubset
      ((convex_closedBall value radius).linear_preimage read.toLinearMap)
      (Metric.isClosed_closedBall.preimage read.continuous)
  have candidateClose :=
    Metric.mem_closedBall'.mp (tailHullSubset candidateTail)
  dsimp [radius] at candidateClose
  rw [dist_comm] at candidateClose
  linarith

private theorem hilbertHistoryTail_nonempty
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (history : ℕ → H)
    (tailStart : ℕ) :
    (hilbertHistoryTail history tailStart).Nonempty := by
  refine ⟨history tailStart, subset_closedConvexHull ?_⟩
  exact ⟨0, by simp⟩

private theorem hilbertHistoryTail_antitone
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (history : ℕ → H) :
    Antitone (hilbertHistoryTail history) := by
  intro firstStart secondStart startOrder
  apply (closedConvexHull ℝ).monotone
  rintro point ⟨offset, rfl⟩
  refine ⟨secondStart - firstStart + offset, ?_⟩
  change history (firstStart + (secondStart - firstStart + offset)) =
    history (secondStart + offset)
  rw [← Nat.add_assoc, Nat.add_sub_of_le startOrder]

private theorem hilbertHistoryTail_isClosed
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (history : ℕ → H)
    (tailStart : ℕ) :
    IsClosed (hilbertHistoryTail history tailStart) :=
  isClosed_closedConvexHull

private theorem hilbertHistoryTail_convex
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (history : ℕ → H)
    (tailStart : ℕ) :
    Convex ℝ (hilbertHistoryTail history tailStart) :=
  convex_closedConvexHull

private noncomputable def hilbertHistoryTailProjection
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (history : ℕ → H)
    (tailStart : ℕ) : H :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex
    (hilbertHistoryTail_nonempty history tailStart)
    (hilbertHistoryTail_isClosed history tailStart).isComplete
    (hilbertHistoryTail_convex history tailStart)
    (0 : H))

private theorem hilbertHistoryTailProjection_mem
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (history : ℕ → H)
    (tailStart : ℕ) :
    hilbertHistoryTailProjection history tailStart ∈
      hilbertHistoryTail history tailStart :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (hilbertHistoryTail_nonempty history tailStart)
    (hilbertHistoryTail_isClosed history tailStart).isComplete
    (hilbertHistoryTail_convex history tailStart)
    (0 : H))).1

private theorem hilbertHistoryTailProjection_minimal
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (history : ℕ → H)
    (tailStart : ℕ) :
    ‖hilbertHistoryTailProjection history tailStart‖ =
      ⨅ candidate : hilbertHistoryTail history tailStart,
        ‖(candidate : H)‖ := by
  simpa [hilbertHistoryTailProjection] using
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
      (hilbertHistoryTail_nonempty history tailStart)
      (hilbertHistoryTail_isClosed history tailStart).isComplete
      (hilbertHistoryTail_convex history tailStart)
      (0 : H))).2

private theorem hilbertHistoryTailCore_nonempty_of_bounded
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (history : ℕ → H)
    (B : ℝ)
    (historyBound : ∀ index, ‖history index‖ ≤ B) :
    (hilbertHistoryTailCore history).Nonempty := by
  let projection : ℕ → H := hilbertHistoryTailProjection history
  let radius : ℕ → ℝ := fun index ↦ ‖projection index‖
  have projectionMem (index : ℕ) :
      projection index ∈ hilbertHistoryTail history index :=
    hilbertHistoryTailProjection_mem history index
  have projectionMinimal (index : ℕ) :
      radius index = ⨅ candidate : hilbertHistoryTail history index,
        ‖(candidate : H)‖ :=
    hilbertHistoryTailProjection_minimal history index
  have normRangeBddBelow (K : Set H) :
      BddBelow (Set.range fun candidate : K ↦ ‖(candidate : H)‖) := by
    refine ⟨(0 : ℝ), ?_⟩
    rintro _ ⟨candidate, rfl⟩
    exact norm_nonneg (candidate : H)
  have radiusMonotone : Monotone radius := by
    intro firstIndex secondIndex indexOrder
    have secondMemFirst :
        projection secondIndex ∈ hilbertHistoryTail history firstIndex :=
      hilbertHistoryTail_antitone history indexOrder (projectionMem secondIndex)
    rw [projectionMinimal firstIndex]
    exact ciInf_le (normRangeBddBelow (hilbertHistoryTail history firstIndex))
      ⟨projection secondIndex, secondMemFirst⟩
  have historyMem (index : ℕ) :
      history index ∈ hilbertHistoryTail history index := by
    refine subset_closedConvexHull ⟨0, ?_⟩
    simp
  have radiusBound (index : ℕ) : radius index ≤ B := by
    calc
      radius index = ⨅ candidate : hilbertHistoryTail history index,
          ‖(candidate : H)‖ := projectionMinimal index
      _ ≤ ‖history index‖ := ciInf_le
        (normRangeBddBelow (hilbertHistoryTail history index))
        ⟨history index, historyMem index⟩
      _ ≤ B := historyBound index
  have radiusBddAbove : BddAbove (Set.range radius) :=
    ⟨B, by rintro _ ⟨index, rfl⟩; exact radiusBound index⟩
  let limitRadius : ℝ := ⨆ index, radius index
  have radiusTendsto : Tendsto radius atTop (nhds limitRadius) :=
    tendsto_atTop_ciSup radiusMonotone radiusBddAbove
  have radiusLeLimit (index : ℕ) : radius index ≤ limitRadius :=
    le_ciSup radiusBddAbove index
  have limitRadiusNonnegative : 0 ≤ limitRadius :=
    (norm_nonneg (projection 0)).trans (radiusLeLimit 0)
  have projectionCauchy : CauchySeq projection := by
    rw [cauchySeq_iff_le_tendsto_0]
    let control : ℕ → ℝ := fun index ↦
      √(4 * (limitRadius ^ 2 - radius index ^ 2))
    refine ⟨control, fun index ↦ Real.sqrt_nonneg _, ?_, ?_⟩
    · intro firstIndex secondIndex tailStart firstLarge secondLarge
      have firstMemTail :
          projection firstIndex ∈ hilbertHistoryTail history tailStart :=
        hilbertHistoryTail_antitone history firstLarge (projectionMem firstIndex)
      have secondMemTail :
          projection secondIndex ∈ hilbertHistoryTail history tailStart :=
        hilbertHistoryTail_antitone history secondLarge (projectionMem secondIndex)
      let half : ℝ := 1 / 2
      let midpoint : H := half • (projection firstIndex + projection secondIndex)
      have midpointMem : midpoint ∈ hilbertHistoryTail history tailStart := by
        dsimp [midpoint]
        rw [smul_add]
        apply hilbertHistoryTail_convex history tailStart firstMemTail secondMemTail
        · norm_num [half]
        · norm_num [half]
        · norm_num [half]
      have radiusLeMidpoint : radius tailStart ≤ ‖midpoint‖ := by
        rw [projectionMinimal tailStart]
        exact ciInf_le
          (normRangeBddBelow (hilbertHistoryTail history tailStart))
          ⟨midpoint, midpointMem⟩
      have firstRadiusLe : ‖projection firstIndex‖ ≤ limitRadius :=
        radiusLeLimit firstIndex
      have secondRadiusLe : ‖projection secondIndex‖ ≤ limitRadius :=
        radiusLeLimit secondIndex
      have controlRadicandNonnegative :
          0 ≤ 4 * (limitRadius ^ 2 - radius tailStart ^ 2) := by
        have radiusNonnegative : 0 ≤ radius tailStart := norm_nonneg _
        have radiusSquareLe : radius tailStart ^ 2 ≤ limitRadius ^ 2 :=
          (sq_le_sq₀ radiusNonnegative limitRadiusNonnegative).2
            (radiusLeLimit tailStart)
        nlinarith
      rw [dist_eq_norm]
      apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
      rw [Real.mul_self_sqrt controlRadicandNonnegative]
      have parallelogram :
          4 * ‖midpoint‖ * ‖midpoint‖ +
              ‖projection firstIndex - projection secondIndex‖ *
                ‖projection firstIndex - projection secondIndex‖ =
            2 * (‖projection firstIndex‖ * ‖projection firstIndex‖ +
              ‖projection secondIndex‖ * ‖projection secondIndex‖) := by
        calc
          _ = ‖(2 : ℝ) • midpoint‖ * ‖(2 : ℝ) • midpoint‖ +
              ‖projection firstIndex - projection secondIndex‖ *
                ‖projection firstIndex - projection secondIndex‖ := by
                simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
                ring
          _ = ‖projection firstIndex + projection secondIndex‖ *
                ‖projection firstIndex + projection secondIndex‖ +
              ‖projection firstIndex - projection secondIndex‖ *
                ‖projection firstIndex - projection secondIndex‖ := by
                simp [midpoint, half, smul_smul]
          _ = _ := parallelogram_law_with_norm_mul ℝ _ _
      calc
        ‖projection firstIndex - projection secondIndex‖ *
              ‖projection firstIndex - projection secondIndex‖ =
            2 * (‖projection firstIndex‖ ^ 2 +
              ‖projection secondIndex‖ ^ 2) - 4 * ‖midpoint‖ ^ 2 := by
              simp only [pow_two]
              nlinarith [parallelogram]
        _ ≤ 2 * (limitRadius ^ 2 + limitRadius ^ 2) -
            4 * radius tailStart ^ 2 := by
              gcongr
        _ = 4 * (limitRadius ^ 2 - radius tailStart ^ 2) := by ring
    · have controlTendsto : Tendsto
          (fun value : ℝ ↦ √(4 * (limitRadius ^ 2 - value ^ 2)))
          (nhds limitRadius) (nhds 0) := by
        exact Continuous.tendsto'
          (by fun_prop) limitRadius 0 (by simp)
      exact controlTendsto.comp radiusTendsto
  obtain ⟨center, projectionTendsto⟩ :=
    cauchySeq_tendsto_of_complete projectionCauchy
  refine ⟨center, ?_⟩
  rw [hilbertHistoryTailCore, mem_iInter]
  intro tailStart
  apply (hilbertHistoryTail_isClosed history tailStart).mem_of_tendsto
    projectionTendsto
  filter_upwards [eventually_ge_atTop tailStart] with index indexLarge
  exact hilbertHistoryTail_antitone history indexLarge (projectionMem index)

private theorem existsUnique_hilbertHistoryTailEnergyCenter_of_bounded
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (history : ℕ → H)
    (B : ℝ)
    (historyBound : ∀ index, ‖history index‖ ≤ B) :
    ∃! center : H,
      center ∈ hilbertHistoryTailCore history ∧
        ∀ candidate ∈ hilbertHistoryTailCore history,
          ‖center‖ ≤ ‖candidate‖ := by
  let core := hilbertHistoryTailCore history
  have coreNonempty : core.Nonempty :=
    hilbertHistoryTailCore_nonempty_of_bounded history B historyBound
  have coreClosed : IsClosed core := by
    unfold core hilbertHistoryTailCore
    exact isClosed_iInter fun _ ↦ isClosed_closedConvexHull
  have coreConvex : Convex ℝ core := by
    unfold core hilbertHistoryTailCore
    exact convex_iInter fun _ ↦ convex_closedConvexHull
  obtain ⟨center, centerMem, centerMinimal⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      coreNonempty coreClosed.isComplete coreConvex (0 : H)
  have normRangeBddBelow :
      BddBelow (Set.range fun candidate : core ↦ ‖(candidate : H)‖) := by
    refine ⟨(0 : ℝ), ?_⟩
    rintro _ ⟨candidate, rfl⟩
    exact norm_nonneg (candidate : H)
  have centerLeast : ∀ candidate ∈ core, ‖center‖ ≤ ‖candidate‖ := by
    intro candidate candidateMem
    rw [show ‖center‖ = ⨅ point : core, ‖(point : H)‖ by
      simpa using centerMinimal]
    exact ciInf_le normRangeBddBelow ⟨candidate, candidateMem⟩
  refine ⟨center, ⟨centerMem, centerLeast⟩, ?_⟩
  intro candidate candidateProperty
  symm
  apply norm_minimizer_unique coreConvex centerMem candidateProperty.1
  · simpa using centerMinimal
  · simp only [zero_sub, norm_neg]
    apply le_antisymm
    · rw [← show ‖center‖ = ⨅ point : core, ‖(point : H)‖ by
        simpa using centerMinimal]
      exact candidateProperty.2 center centerMem
    · exact ciInf_le normRangeBddBelow ⟨candidate, candidateProperty.1⟩

def canonicalAffineCorrectionMassTailEnergyAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) : ℝ :=
  ⨅ candidate : canonicalAffineCorrectionMassTailCoreAt
      timeEnd timeNonnegative a b boxOrder time D matrixBound,
    ‖(candidate : CauchySafeMatterSpatialL2 a b)‖

/-- The full canonical finite history determines one unique minimum
mother-mass-energy point in its fixed-time asymptotic convex core.  The
occurrence producer is used only to prove that the core is nonempty; the
center itself is characterized solely by the source history. -/
theorem existsUnique_canonicalAffineCorrectionMassTailEnergyCenterAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) :
    ∃! center : CauchySafeMatterSpatialL2 a b,
      center ∈ canonicalAffineCorrectionMassTailCoreAt
          timeEnd timeNonnegative a b boxOrder time D matrixBound ∧
        ‖center‖ = canonicalAffineCorrectionMassTailEnergyAt
          timeEnd timeNonnegative a b boxOrder time D matrixBound := by
  let core := canonicalAffineCorrectionMassTailCoreAt
    timeEnd timeNonnegative a b boxOrder time D matrixBound
  obtain ⟨occurrence⟩ :=
    nonempty_fixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
      timeEnd timeNonnegative a b boxOrder
  have coreNonempty : core.Nonempty :=
    ⟨occurrence.correctionMassRepresentative time,
      correctionMassRepresentative_mem_canonicalAffineCorrectionMassTailCoreAt
        timeEnd timeNonnegative a b boxOrder occurrence time D matrixBound⟩
  have coreClosed : IsClosed core :=
    canonicalAffineCorrectionMassTailCoreAt_isClosed
      timeEnd timeNonnegative a b boxOrder time D matrixBound
  have coreConvex : Convex ℝ core :=
    canonicalAffineCorrectionMassTailCoreAt_convex
      timeEnd timeNonnegative a b boxOrder time D matrixBound
  obtain ⟨center, centerMem, centerMinimal⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      coreNonempty coreClosed.isComplete coreConvex
      (0 : CauchySafeMatterSpatialL2 a b)
  refine ⟨center, ⟨centerMem, ?_⟩, ?_⟩
  · simpa [canonicalAffineCorrectionMassTailEnergyAt] using centerMinimal
  · intro candidate candidateProperty
    symm
    apply norm_minimizer_unique coreConvex centerMem candidateProperty.1
    · simpa using centerMinimal
    · simpa [canonicalAffineCorrectionMassTailEnergyAt] using
        candidateProperty.2

def canonicalAffineCorrectionL2BoundedPath
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    (Icc 0 timeEnd : Set ℝ) →ᵇ CauchySafeMatterSpatialL2 a b :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time ↦ canonicalAffineCorrectionL2
        timeEnd timeNonnegative a b testCount time.1,
      continuousOn_iff_continuous_restrict.mp (by
        intro time timeMem
        exact (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount).continuous.continuousAt.comp_continuousWithinAt
            ((fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_evolution
              timeEnd timeNonnegative a b testCount time timeMem
              ).continuousWithinAt))⟩

def canonicalAffineCorrectionTimeL2History
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd) :=
  BoundedContinuousFunction.toLp 2 (canonicalAffineTimeMeasure timeEnd) ℝ
    (canonicalAffineCorrectionL2BoundedPath
      timeEnd timeNonnegative a b testCount)

def canonicalAffineCorrectionTimeL2TailAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (tailStart : ℕ) :
    Set (Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd)) :=
  closedConvexHull ℝ (Set.range fun offset ↦
    canonicalAffineCorrectionTimeL2History
      timeEnd timeNonnegative a b (tailStart + offset))

def canonicalAffineCorrectionTimeL2TailCore
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates) :
    Set (Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd)) :=
  ⋂ tailStart, canonicalAffineCorrectionTimeL2TailAt
    timeEnd timeNonnegative a b tailStart

theorem canonicalAffineCorrectionTimeL2History_bounded
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ B : ℝ, ∀ testCount,
      ‖canonicalAffineCorrectionTimeL2History
        timeEnd timeNonnegative a b testCount‖ ≤ B := by
  have sourceBound : ∃ R : ℝ, 0 ≤ R ∧ ∀ testCount : ℕ,
      ∀ time ∈ Icc 0 timeEnd,
        ‖fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
          (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
            timeEnd timeNonnegative a b testCount time)‖ ≤ R :=
    StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy.exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound
      timeEnd timeNonnegative a b boxOrder
  obtain ⟨R, RNonnegative, correctionBound⟩ := sourceBound
  let toTimeL2 :
      ((Icc 0 timeEnd : Set ℝ) →ᵇ CauchySafeMatterSpatialL2 a b) →L[ℝ]
        Lp (CauchySafeMatterSpatialL2 a b) 2
          (canonicalAffineTimeMeasure timeEnd) :=
    BoundedContinuousFunction.toLp 2
      (canonicalAffineTimeMeasure timeEnd) ℝ
  refine ⟨‖toTimeL2‖ * R, ?_⟩
  intro testCount
  have pathBound :
      ‖canonicalAffineCorrectionL2BoundedPath
        timeEnd timeNonnegative a b testCount‖ ≤ R := by
    apply (BoundedContinuousFunction.norm_le RNonnegative).2
    intro time
    exact correctionBound testCount time.1 time.2
  calc
    ‖canonicalAffineCorrectionTimeL2History
        timeEnd timeNonnegative a b testCount‖ ≤
        ‖toTimeL2‖ * ‖canonicalAffineCorrectionL2BoundedPath
          timeEnd timeNonnegative a b testCount‖ :=
      toTimeL2.le_opNorm _
    _ ≤ ‖toTimeL2‖ * R :=
      mul_le_mul_of_nonneg_left pathBound (norm_nonneg _)

private theorem canonicalAffineCorrectionTimeL2TailCore_eq_hilbertHistoryTailCore
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates) :
    canonicalAffineCorrectionTimeL2TailCore timeEnd timeNonnegative a b =
      hilbertHistoryTailCore
        (canonicalAffineCorrectionTimeL2History
          timeEnd timeNonnegative a b) :=
  rfl

/-- The complete source-owned affine history generates one unique minimum
mother-energy correction in the whole-time Bochner `L²` carrier.  No weak
subsequence, representative, target field, or residual enters this mouth. -/
theorem existsUnique_canonicalAffineCorrectionTimeL2TailEnergyCenter
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃! center : Lp (CauchySafeMatterSpatialL2 a b) 2
        (canonicalAffineTimeMeasure timeEnd),
      center ∈ canonicalAffineCorrectionTimeL2TailCore
          timeEnd timeNonnegative a b ∧
        ∀ candidate ∈ canonicalAffineCorrectionTimeL2TailCore
            timeEnd timeNonnegative a b,
          ‖center‖ ≤ ‖candidate‖ := by
  have bounded : ∃ B : ℝ, ∀ testCount : ℕ,
      ‖canonicalAffineCorrectionTimeL2History
        timeEnd timeNonnegative a b testCount‖ ≤ B :=
    canonicalAffineCorrectionTimeL2History_bounded
      timeEnd timeNonnegative a b boxOrder
  obtain ⟨B, historyBound⟩ := bounded
  change ∃! center,
    center ∈ hilbertHistoryTailCore
        (canonicalAffineCorrectionTimeL2History
          timeEnd timeNonnegative a b) ∧
      ∀ candidate ∈ hilbertHistoryTailCore
          (canonicalAffineCorrectionTimeL2History
            timeEnd timeNonnegative a b),
        ‖center‖ ≤ ‖candidate‖
  exact existsUnique_hilbertHistoryTailEnergyCenter_of_bounded
    (canonicalAffineCorrectionTimeL2History
      timeEnd timeNonnegative a b) B historyBound

noncomputable def canonicalAffineCorrectionTimeL2TailEnergyCenter
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd) :=
  Classical.choose
    (existsUnique_canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder)

theorem canonicalAffineCorrectionTimeL2TailEnergyCenter_spec
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    canonicalAffineCorrectionTimeL2TailEnergyCenter
        timeEnd timeNonnegative a b boxOrder ∈
      canonicalAffineCorrectionTimeL2TailCore
        timeEnd timeNonnegative a b ∧
      ∀ candidate ∈ canonicalAffineCorrectionTimeL2TailCore
          timeEnd timeNonnegative a b,
        ‖canonicalAffineCorrectionTimeL2TailEnergyCenter
          timeEnd timeNonnegative a b boxOrder‖ ≤ ‖candidate‖ :=
  (Classical.choose_spec
    (existsUnique_canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder)).1

/-- Every closed convex invariant of the complete source-owned history also
contains its canonical minimum-energy center. -/
theorem canonicalAffineCorrectionTimeL2TailEnergyCenter_mem_of_history_mem
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (invariant : Set (Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd)))
    (invariantClosed : IsClosed invariant)
    (invariantConvex : Convex ℝ invariant)
    (historyMem : ∀ testCount,
      canonicalAffineCorrectionTimeL2History
        timeEnd timeNonnegative a b testCount ∈ invariant) :
    canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder ∈ invariant := by
  have centerTailZero :
      canonicalAffineCorrectionTimeL2TailEnergyCenter
          timeEnd timeNonnegative a b boxOrder ∈
        canonicalAffineCorrectionTimeL2TailAt
          timeEnd timeNonnegative a b 0 :=
    mem_iInter.mp
      (canonicalAffineCorrectionTimeL2TailEnergyCenter_spec
        timeEnd timeNonnegative a b boxOrder).1 0
  apply closedConvexHull_min _ invariantConvex invariantClosed centerTailZero
  rintro history ⟨testCount, rfl⟩
  simpa only [zero_add] using historyMem testCount

theorem canonicalAffineCorrectionTimeL2TailEnergyCenter_eq_of_minimal
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (candidate : Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd))
    (candidateMem : candidate ∈ canonicalAffineCorrectionTimeL2TailCore
      timeEnd timeNonnegative a b)
    (candidateLeast : ∀ point ∈ canonicalAffineCorrectionTimeL2TailCore
        timeEnd timeNonnegative a b,
      ‖candidate‖ ≤ ‖point‖) :
    candidate = canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder :=
  (Classical.choose_spec
    (existsUnique_canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder)).2 candidate
        ⟨candidateMem, candidateLeast⟩

theorem canonicalAffineCorrectionTimeL2TailEnergyCenter_read_eq_of_eventually_exact
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (read :
      Lp (CauchySafeMatterSpatialL2 a b) 2
          (canonicalAffineTimeMeasure timeEnd) →L[ℝ] E)
    (value : E)
    (entry : ℕ)
    (readExact : ∀ testCount, entry ≤ testCount →
      read (canonicalAffineCorrectionTimeL2History
        timeEnd timeNonnegative a b testCount) = value) :
    read (canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder) = value := by
  apply hilbertHistoryTailCore_read_eq_of_eventually_exact
    (canonicalAffineCorrectionTimeL2History
      timeEnd timeNonnegative a b) read value entry readExact
  exact (canonicalAffineCorrectionTimeL2TailEnergyCenter_spec
    timeEnd timeNonnegative a b boxOrder).1

theorem canonicalAffineCorrectionTimeL2TailEnergyCenter_read_eq_of_tendsto
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (read :
      Lp (CauchySafeMatterSpatialL2 a b) 2
          (canonicalAffineTimeMeasure timeEnd) →L[ℝ] E)
    (value : E)
    (readTendsto : Tendsto
      (fun testCount ↦ read (canonicalAffineCorrectionTimeL2History
        timeEnd timeNonnegative a b testCount)) atTop (nhds value)) :
    read (canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder) = value := by
  apply hilbertHistoryTailCore_read_eq_of_tendsto
    (canonicalAffineCorrectionTimeL2History
      timeEnd timeNonnegative a b) read value readTendsto
  exact (canonicalAffineCorrectionTimeL2TailEnergyCenter_spec
    timeEnd timeNonnegative a b boxOrder).1

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
