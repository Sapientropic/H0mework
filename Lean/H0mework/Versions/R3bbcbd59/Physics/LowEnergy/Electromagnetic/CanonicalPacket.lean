import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.CanonicalQuantumUnits
import H0mework.Versions.AB.Physics.LowEnergy.PacketNoise.Filtered
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryCurrent.Words

/-! The existing canonical preparation enters the original physical-space
packet and the original source time. Complete CAR words are returned only
after composition. The canonical density left leg retains phaseInverse. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalPacket
open FullQuantum FullSpace HistoryPrepared SpatialGreen HistoryGenerator
open YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9DEF
open Stage10.ChargedPreparation Stage10.CanonicalMatter MatterSpace.SpatialCAR
open Stage9C.Material.SpinPair StageNineMatterPointwiseEquation StageNineHolonomicField
noncomputable section
abbrev SourceMother := YangMills.FullPairing.Mother

def preparation (momentum : Fin 3 → ℝ) : Hilbert →L[ℂ] FullMatterL2 :=
  HistoryPrepared.preparation.comp (operator (CanonicalParticle.normalizedPreparation momentum))

def packet (momentum : Fin 3 → ℝ) : FullMatterL2 :=
  preparation momentum (YangMills.FullPairing.prepared 0)

theorem packet_original (momentum : Fin 3 → ℝ) :
    packet momentum = HistoryPrepared.preparation (CanonicalParticle.state 0 momentum) := by
  simp only [packet, preparation, ContinuousLinearMap.comp_apply,
    YangMills.FullPairing.prepared, operator_coordinates, CanonicalParticle.state]

theorem packet_unit (momentum : Fin 3 → ℝ) : ‖packet momentum‖ = 1 := by
  rw [packet_original, HistoryPrepared.preparation_norm]
  have real := congrArg Complex.re (CanonicalParticle.state_unit 0 momentum)
  change RCLike.re (inner ℂ (CanonicalParticle.state 0 momentum)
    (CanonicalParticle.state 0 momentum)) = 1 at real
  rw [inner_self_eq_norm_sq] at real
  nlinarith [norm_nonneg (CanonicalParticle.state 0 momentum)]

def mother (momentum : Fin 3 → ℝ) (A : FullMatterL2 →L[ℂ] FullMatterL2) : SourceMother :=
  fromOperator ((preparation momentum).adjoint.comp (A.comp (preparation momentum)))

theorem mother_read (momentum : Fin 3 → ℝ) (A : FullMatterL2 →L[ℂ] FullMatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (mother momentum A)) =
      inner ℂ (packet momentum) (A (packet momentum)) := by
  rw [mother, origin_response, operator_fromOperator]
  change inner ℂ (YangMills.FullPairing.prepared 0) ((preparation momentum).adjoint
    (A (preparation momentum (YangMills.FullPairing.prepared 0)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem mother_fullWord (momentum : Fin 3 → ℝ) {ι : Type*} [Fintype ι]
    (tests : ι → FullMatterL2) (word : List (Letter (Option ι))) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (mother momentum (wordObservable (packet momentum) tests word))) =
      spatialMoment (packet momentum) tests word := by
  rw [mother_read]
  exact wordObservable_response (packet momentum) tests word

/-- The density leg is the original canonical dual, before spatial evolution. -/
def densityReader (vertex : SourceMother) : Hilbert →L[ℂ] Hilbert :=
  operator (phaseInverse.comp vertex)

theorem original_density (momentum : Fin 3 → ℝ) (vertex : SourceMother) :
    actual.conjugateMatter 0
      (canonicalDual (CanonicalParticle.normalizedPreparation momentum)
        (vertex (CanonicalParticle.normalizedPreparation momentum (actual.matter 0)))) =
      4 * (Stage9C.Material.SpinPair.spinScale : ℂ) *
        inner ℂ (CanonicalParticle.state 0 momentum)
          (densityReader vertex (CanonicalParticle.state 0 momentum)) := by
  rw [ExternalState.original_prepared_vertex]
  simp only [CanonicalParticle.state, densityReader, YangMills.FullPairing.prepared,
    operator_coordinates, LinearMap.comp_apply]

theorem original_charge_unit (momentum : Fin 3 → ℝ) :
    inner ℂ (CanonicalParticle.state 0 momentum)
      (densityReader (Compatibility.currentAction 0 Stage10.HyperchargeResponse.chargeDirection)
        (CanonicalParticle.state 0 momentum)) = -1 := by
  have source := CanonicalParticle.original_current 0 momentum
  rw [original_density] at source
  have nonzero : (4 * (spinScale : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr spinScale_pos.ne')
  apply (mul_left_cancel₀ nonzero)
  simpa only [mul_neg_one, neg_mul] using source

theorem phase_noether_unit (momentum : Fin 3 → ℝ) :
    Stage10.ActionNormalization.actionScale *
      matterDifferentialMomentum Stage10.Runtime.source
        (CanonicalParticle.normalizedConfiguration momentum)
        (StageNineHolonomicField.matterCoordinateEquiv
          ((-Complex.I) • (CanonicalParticle.normalizedConfiguration momentum).matter 0)) 0 0 = 1 :=
  CanonicalParticle.action_unit_phase 0 momentum

/-- The original inverse time carries the independent momentum dual. -/
def timeReader (time : ℝ) (A : FullMatterL2 →L[ℂ] FullMatterL2) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (spatialFlow 0 (-time)).comp (A.comp (spatialFlow 0 time))

theorem timeReader_dual (momentum : Fin 3 → ℝ) (time : ℝ)
    (A : FullMatterL2 →L[ℂ] FullMatterL2) :
    inner ℂ (packet momentum) (timeReader time A (packet momentum)) =
      inner ℂ (dualMomentumFlow 0 time (packet momentum))
        (A (spatialFlow 0 time (packet momentum))) := by
  rw [dualMomentumFlow, ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem momentum_pair_unit (momentum : Fin 3 → ℝ) (time : ℝ) :
    inner ℂ (dualMomentumFlow 0 time (packet momentum))
      (spatialFlow 0 time (packet momentum)) = 1 := by
  rw [momentum_pair_preserved, inner_self_eq_norm_sq_to_K, packet_unit]
  norm_num

def twoTimeTests (momentum : Fin 3 → ℝ) (time age : ℝ)
    (current force : FullMatterL2 →L[ℂ] FullMatterL2) : Fin 4 → FullMatterL2 :=
  HistoryCurrent.commutatorTests 1 (timeReader age force) (timeReader time current)
    (packet momentum) (packet momentum)

def kuboMother (momentum : Fin 3 → ℝ) (time age : ℝ)
    (current force : FullMatterL2 →L[ℂ] FullMatterL2) : SourceMother :=
  mother momentum (Complex.I • (wordObservable (packet momentum)
      (twoTimeTests momentum time age current force)
      [.create none, .annihilate (some 0), .create (some 1), .annihilate none] -
    wordObservable (packet momentum)
      (twoTimeTests momentum time age current force)
      [.create none, .annihilate (some 2), .create (some 3), .annihilate none]))

theorem kubo_fullWord (momentum : Fin 3 → ℝ) (time age : ℝ)
    (current force : FullMatterL2 →L[ℂ] FullMatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (kuboMother momentum time age current force)) =
      Complex.I * inner ℂ (packet momentum)
        (timeReader age force (timeReader time current (packet momentum)) -
          timeReader time current (timeReader age force (packet momentum))) := by
  have generated := HistoryCurrent.commutatorCAR_read
    (1 : FullMatterL2 →L[ℂ] FullMatterL2) (timeReader age force) (timeReader time current)
    (packet momentum) (packet momentum) (packet_unit momentum)
  simp only [HistoryCurrent.commutatorCAR] at generated
  rw [kuboMother, mother_read]
  simp only [smul_apply, sub_apply,
    inner_smul_right, inner_sub_right, wordObservable_response]
  simpa only [twoTimeTests, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    inner_sub_right] using congrArg (fun z : ℂ => Complex.I*z) generated

/-- The temporal principal is the original source insertion. It converts the
Dirac Green to its Hamiltonian resolvent without changing physical time. -/
def rawFilter (energy damping : ℝ) (positive : 0 < damping) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (green 0 energy damping positive).comp (principal 0)

def rawPacket (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping) : FullMatterL2 :=
  rawFilter energy damping positive (packet momentum)

def spectralKernel (energy damping : ℝ) (field : Domain 0 energy damping) : FullMatterL2 :=
  Complex.I • inversePrincipal 0 (dirac 0 energy damping field)

theorem source_symbol_factor (momentum : Fin 3 → ℝ) (z : ℂ) :
    Triangular.diracKernel actual 0 momentum z = (-Complex.I) •
      (StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipal (actual.coframe 0) *
        Triangular.fullKernel actual 0 momentum z) :=
  Triangular.diracKernel_factor actual 0 momentum z (actual_noncharacteristic 0)

theorem rawFilter_right (energy damping : ℝ) (positive : 0 < damping) (source : FullMatterL2) :
    spectralKernel energy damping (domainGreen 0 energy damping positive (principal 0 source)) =
      Complex.I • source := by
  rw [spectralKernel, dirac_green, inversePrincipal_left]

theorem rawFilter_left (energy damping : ℝ) (positive : 0 < damping)
    (field : Domain 0 energy damping) :
    rawFilter energy damping positive (spectralKernel energy damping field) = Complex.I • field.val := by
  change green 0 energy damping positive
    (principal 0 (Complex.I • inversePrincipal 0 (dirac 0 energy damping field))) = _
  rw [map_smul, inversePrincipal_right, map_smul, green_dirac]

theorem rawPacket_nonzero (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping) :
    rawPacket momentum energy damping positive ≠ 0 := by
  apply nonzero_response 0 energy damping positive (principal 0 (packet momentum))
  intro zero
  have recovered := inversePrincipal_left 0 (packet momentum)
  rw [zero, map_zero] at recovered
  have unit := packet_unit momentum
  rw [← recovered, norm_zero] at unit
  norm_num at unit

def sourceFilter (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  ((‖rawPacket momentum energy damping positive‖⁻¹ : ℝ) : ℂ) • rawFilter energy damping positive

def filteredPacket (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping) : FullMatterL2 :=
  sourceFilter momentum energy damping positive (packet momentum)

theorem filteredPacket_unit (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping) :
    ‖filteredPacket momentum energy damping positive‖ = 1 := by
  change ‖((‖rawPacket momentum energy damping positive‖⁻¹ : ℝ) : ℂ) •
    rawPacket momentum energy damping positive‖ = 1
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (rawPacket_nonzero momentum energy damping positive))

theorem filteredPacket_domain (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping) :
    filteredPacket momentum energy damping positive ∈ Quantum.Generator.domain GaugeHistory.freeAction := by
  have raw := (generator_domain_iff_original energy damping positive _).mpr
    (green_domain 0 energy damping positive (principal 0 (packet momentum)))
  exact (Quantum.Generator.domain GaugeHistory.freeAction).smul_mem
    ((‖rawPacket momentum energy damping positive‖⁻¹ : ℝ) : ℂ) raw

def filteredMother (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (A : FullMatterL2 →L[ℂ] FullMatterL2) : SourceMother :=
  mother momentum ((sourceFilter momentum energy damping positive).adjoint.comp
    (A.comp (sourceFilter momentum energy damping positive)))

theorem filtered_read (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (A : FullMatterL2 →L[ℂ] FullMatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (filteredMother momentum energy damping positive A)) =
      inner ℂ (filteredPacket momentum energy damping positive)
        (A (filteredPacket momentum energy damping positive)) := by
  rw [filteredMother, mother_read]
  change inner ℂ (packet momentum) ((sourceFilter momentum energy damping positive).adjoint
    (A (sourceFilter momentum energy damping positive (packet momentum)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem filtered_fullWord (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    {ι : Type*} [Fintype ι] (tests : ι → FullMatterL2) (word : List (Letter (Option ι))) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (filteredMother momentum energy damping positive
        (wordObservable (filteredPacket momentum energy damping positive) tests word))) =
      spatialMoment (filteredPacket momentum energy damping positive) tests word := by
  rw [filtered_read]
  exact wordObservable_response _ tests word

theorem filtered_oneParticle_read (momentum : Fin 3 → ℝ) (energy damping : ℝ)
    (positive : 0 < damping) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (filteredMother momentum energy damping positive
        (wordObservable (filteredPacket momentum energy damping positive)
          (fun i : Fin 0 => Fin.elim0 i) [.create none, .annihilate none]))) = 1 := by
  rw [filtered_fullWord, spatialMoment_twoPoint]
  simp only [family, inner_self_eq_norm_sq_to_K, filteredPacket_unit]
  norm_num

theorem filtered_momentum_pair_unit (momentum : Fin 3 → ℝ) (energy damping : ℝ)
    (positive : 0 < damping) (time : ℝ) :
    inner ℂ (dualMomentumFlow 0 time (filteredPacket momentum energy damping positive))
      (spatialFlow 0 time (filteredPacket momentum energy damping positive)) = 1 := by
  rw [momentum_pair_preserved, inner_self_eq_norm_sq_to_K, filteredPacket_unit]
  norm_num

def filteredTwoTimeTests (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (time age : ℝ) (current force : FullMatterL2 →L[ℂ] FullMatterL2) : Fin 4 → FullMatterL2 :=
  HistoryCurrent.commutatorTests 1 (timeReader age force) (timeReader time current)
    (filteredPacket momentum energy damping positive) (filteredPacket momentum energy damping positive)

def filteredKuboMother (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (time age : ℝ) (current force : FullMatterL2 →L[ℂ] FullMatterL2) : SourceMother :=
  filteredMother momentum energy damping positive (Complex.I •
    (wordObservable (filteredPacket momentum energy damping positive)
      (filteredTwoTimeTests momentum energy damping positive time age current force)
      [.create none, .annihilate (some 0), .create (some 1), .annihilate none] -
    wordObservable (filteredPacket momentum energy damping positive)
      (filteredTwoTimeTests momentum energy damping positive time age current force)
      [.create none, .annihilate (some 2), .create (some 3), .annihilate none]))

theorem filtered_kubo_fullWord (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (time age : ℝ) (current force : FullMatterL2 →L[ℂ] FullMatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix
        (filteredKuboMother momentum energy damping positive time age current force)) =
      Complex.I * inner ℂ (filteredPacket momentum energy damping positive)
        (timeReader age force (timeReader time current (filteredPacket momentum energy damping positive)) -
          timeReader time current (timeReader age force (filteredPacket momentum energy damping positive))) := by
  have generated := HistoryCurrent.commutatorCAR_read
    (1 : FullMatterL2 →L[ℂ] FullMatterL2) (timeReader age force) (timeReader time current)
    (filteredPacket momentum energy damping positive) (filteredPacket momentum energy damping positive)
    (filteredPacket_unit momentum energy damping positive)
  simp only [HistoryCurrent.commutatorCAR] at generated
  rw [filteredKuboMother, filtered_read]
  simp only [smul_apply, sub_apply, inner_smul_right, inner_sub_right, wordObservable_response]
  simpa only [filteredTwoTimeTests, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    inner_sub_right] using congrArg (fun z : ℂ => Complex.I*z) generated

/-- The original spatial native-Y density includes the source coframe volume.
Its canonical left leg is retained before the physical-space lift. -/
def nativeY3 : FullMatterL2 →L[ℂ] FullMatterL2 :=
  ((lapse : ℂ) • densityReader
    (Compatibility.currentAction 3 Stage10.HyperchargeResponse.chargeDirection)).compLpL 2 volume

def nativeY3Mother (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (time age : ℝ) : SourceMother :=
  filteredKuboMother momentum energy damping positive time age nativeY3 (-nativeY3)

theorem nativeY3_read (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0 < damping)
    (time age : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (nativeY3Mother momentum energy damping positive time age)) =
      Complex.I * inner ℂ (filteredPacket momentum energy damping positive)
        (timeReader age (-nativeY3) (timeReader time nativeY3 (filteredPacket momentum energy damping positive)) -
          timeReader time nativeY3 (timeReader age (-nativeY3) (filteredPacket momentum energy damping positive))) :=
  filtered_kubo_fullWord momentum energy damping positive time age nativeY3 (-nativeY3)

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalPacket
