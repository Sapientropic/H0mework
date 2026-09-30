import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryTimeStrongRefinement

set_option autoImplicit false
open scoped BigOperators Topology ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeRecoveryJointTimeKernel

open Set Filter Matrix MeasureTheory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open NativeEndpointVelocityCarrier
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

structure Realization (stress : StressAt escape) (pointLe : point ≤ 1) where
  kernel : NativePositiveKernelCarrier.Kernel Index
  refinement : Ultrafilter ℕ
  cofinal : (refinement : Filter ℕ) ≤ atTop
  converges : Tendsto (fun index => gram escape pointLe (stress.refinement index))
    (refinement : Filter ℕ) (𝓝 kernel.matrix)
  fixedStrong : ∀ᵐ time ∂commonTimeMeasure 1,
    Tendsto (fun index => wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed time)))
      (refinement : Filter ℕ) (𝓝 (receipt.wholePath time))

private theorem realization_nonempty (stress : StressAt escape) (pointLe : point ≤ 1)
    (source : NativeRecoveryTimeStrongRefinement.StrongRefinement stress pointLe) :
    Nonempty (Realization stress pointLe) := by
  let box : Set (Matrix Index Index ℂ) := Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall 0 (bound receipt ^ 2)
  have compact : IsCompact box := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have inside (index : ℕ) : gram escape pointLe (stress.refinement (source.index index)) ∈ box := by
    intro left _ right _
    simpa only [Metric.mem_closedBall, dist_zero_right] using gram_bound escape pointLe (stress.refinement (source.index index)) left right
  have visits : ∀ᶠ index : ℕ in atTop, gram escape pointLe (stress.refinement (source.index index)) ∈ box := Eventually.of_forall inside
  obtain ⟨matrix, _, cluster⟩ := compact.exists_mapClusterPt_of_frequently visits.frequently
  obtain ⟨refinement, cofinal, converges⟩ := mapClusterPt_iff_ultrafilter.mp cluster
  have row (left right : Index) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp converges left) right
  have positive : matrix.PosSemidef := by
    constructor
    · ext left right
      change star (matrix right left) = matrix left right
      have reflected := (row right left).star
      have raw (index) : star (gram escape pointLe (stress.refinement (source.index index)) right left) =
          gram escape pointLe (stress.refinement (source.index index)) left right :=
        congrFun (congrFun (gram_positive escape pointLe (stress.refinement (source.index index))).1 left) right
      simp only [raw] at reflected
      exact tendsto_nhds_unique reflected (row left right)
    · intro coefficients
      have quadratic := tendsto_finsetSum coefficients.support (fun left _ =>
        tendsto_finsetSum coefficients.support (fun right _ =>
          ((tendsto_const_nhds (x := star (coefficients left))).mul (row left right)).mul
            (tendsto_const_nhds (x := coefficients right))))
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds quadratic
        (fun index => (gram_positive escape pointLe (stress.refinement (source.index index))).2 coefficients)
  refine ⟨⟨⟨matrix, positive⟩, Ultrafilter.map source.index refinement, ?_, ?_, ?_⟩⟩
  · rw [Ultrafilter.coe_map]
    exact source.strict.tendsto_atTop.mono_left cofinal
  · rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact converges
  · filter_upwards [source.converges] with time original
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact original.mono_left cofinal

def generated (stress : StressAt escape) (pointLe : point ≤ 1) : Realization stress pointLe :=
  Classical.choice (realization_nonempty stress pointLe (NativeRecoveryTimeStrongRefinement.generated stress pointLe))

abbrev Space (stress : StressAt escape) (pointLe : point ≤ 1) :=
  NativePositiveKernelCarrier.Space (generated stress pointLe).kernel

def vector (stress : StressAt escape) (pointLe : point ≤ 1) (entry : Index) : Space stress pointLe :=
  NativePositiveKernelCarrier.vector (generated stress pointLe).kernel entry

theorem vector_inner (stress : StressAt escape) (pointLe : point ≤ 1) (left right : Index) :
    inner ℂ (vector stress pointLe left) (vector stress pointLe right) =
      (generated stress pointLe).kernel.matrix left right := NativePositiveKernelCarrier.vector_inner _ left right

theorem pairing_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (left right : Index) :
    Tendsto (fun index => gram escape pointLe (stress.refinement index) left right)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (vector stress pointLe left) (vector stress pointLe right))) := by
  rw [vector_inner]
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (generated stress pointLe).converges left) right

theorem anchor_stress (stress : StressAt escape) (pointLe : point ≤ 1) (left right : IntegerWavevector × Coordinate) :
    inner ℂ (vector stress pointLe (.inr (.anchor, left))) (vector stress pointLe (.inr (.anchor, right))) =
      -stress.stress (left.1 - right.1) left.2 right.2 := by
  have selected := pairing_tendsto stress pointLe (.inr (.anchor, left)) (.inr (.anchor, right))
  simp only [anchor_gram] at selected
  have original := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
    (tendsto_pi_nhds.mp stress.stress_tendsto (left.1 - right.1)) left.2) right.2).neg
  exact tendsto_nhds_unique selected (original.mono_left (generated stress pointLe).cofinal)

end
end SaturationMonoid.NavierStokes.NativeRecoveryJointTimeKernel
