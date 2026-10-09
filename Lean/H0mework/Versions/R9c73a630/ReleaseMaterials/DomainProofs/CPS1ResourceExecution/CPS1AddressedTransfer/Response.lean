import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Site
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Population

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedTransfer
noncomputable section
open CPS1Deformation CPS1ElectronicSource InnerProductSpace CPS1PositivePulse
open CPS1MolecularFrame.FiniteNormed
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame}

def seedOccupation (state : Material frame) (time : ℝ) : Occupation state.reference :=
  normalizedOccupationCandidate state.reference (state.movedPositions time) (state.transportedOccupation time)

def seedFields (state : Material frame) (time : ℝ) : ElectronIndex state.reference.geometry → SpinSpace :=
  occupiedFieldsAt state.reference (state.movedPositions time) (seedOccupation state time)

def responseFields (state : Material frame) (time : ℝ) : ElectronIndex state.reference.geometry → SpinSpace :=
  occupiedFieldsAt state.reference (state.movedPositions time)
    (physicalFockResponse state.reference (state.movedPositions time) (seedOccupation state time) time)

def responseAction (state : Material frame) (time : ℝ) : SpinSpace →L[ℂ] SpinSpace :=
  physicalAction state.reference (state.movedPositions time) (seedOccupation state time)

def responseFlux (state : Material frame) (nuclear : CPS1MolecularFrame.NuclearIndex state.reference)
    (time : ℝ) : ℝ :=
  Generic.midpointFlux (siteProjection state.reference (state.movedPositions time) nuclear)
    (responseAction state time) (seedFields state time) (responseFields state time)

def transferredPopulation (state : Material frame)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (time : ℝ) : ℝ :=
  Generic.population (siteProjection state.reference (state.movedPositions time) nuclear) (responseFields state time) -
    Generic.population (siteProjection state.reference (state.movedPositions time) nuclear) (seedFields state time)

theorem response_midpoint (state : Material frame) (time : ℝ)
    (slot : ElectronIndex state.reference.geometry) :
    responseFields state time slot-seedFields state time slot =
      -(Complex.I*(time : ℂ)) • responseAction state time
        (Generic.midpoint (seedFields state time slot) (responseFields state time slot)) := by
  have paid := physical_fock_midpoint state.reference (state.movedPositions time)
    (seedOccupation state time) time slot
  change responseFields state time slot +
    (Complex.I*((time/2 : ℝ) : ℂ)) • responseAction state time (responseFields state time slot) =
      seedFields state time slot -
        (Complex.I*((time/2 : ℝ) : ℂ)) • responseAction state time (seedFields state time slot) at paid
  have scalar : -(Complex.I*(time : ℂ))*(1/2 : ℂ) =
      -(Complex.I*((time/2 : ℝ) : ℂ)) := by push_cast; ring
  calc
    _ = (seedFields state time slot-
        (Complex.I*((time/2 : ℝ) : ℂ)) • responseAction state time (seedFields state time slot)-
        (Complex.I*((time/2 : ℝ) : ℂ)) • responseAction state time (responseFields state time slot))-
        seedFields state time slot :=
      congrArg (fun field => field-seedFields state time slot) (eq_sub_of_add_eq paid)
    _ = _ := by
      simp only [Generic.midpoint,map_smul,map_add,smul_smul,scalar,smul_add,neg_smul]
      abel

theorem response_population (state : Material frame)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (time : ℝ) :
    transferredPopulation state nuclear time = 2*time*responseFlux state nuclear time :=
  Generic.total_cayley_population_change _ _ _ _ time (response_midpoint state time)

theorem seed_fields_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions)) : seedFields state 0 = state.currentFields := by
  have normalized := (candidate_normalization_eventually_success state good).self_of_nhds
  rw [Material.movedPositions,kick_positions_zero,transported_occupation_zero,
    normalize_good_at_unit _ _ _ unit good] at normalized
  have same : seedOccupation state 0 = state.occupied := by
    simpa only [seedOccupation,Material.movedPositions,kick_positions_zero,transported_occupation_zero]
      using (Except.ok.inj normalized).symm
  rw [seedFields,same,Material.movedPositions,kick_positions_zero]
  rfl

theorem response_fields_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions)) : responseFields state 0 = state.currentFields := by
  rw [responseFields,physical_fock_response_zero]
  exact seed_fields_zero state good unit

theorem seed_fields_continuousAt_zero (state : Material frame) (good : Good state)
    (slot : ElectronIndex state.reference.geometry) : ContinuousAt (fun time => seedFields state time slot) 0 := by
  have normalizedContinuous := normalized_occupation_candidate_continuousAt state.reference
    state.movedPositions state.transportedOccupation 0
    (moved_positions_continuous state).continuousAt (transported_occupation_continuous state).continuousAt
    (transported_good_at_zero state good)
  exact occupied_fields_continuousAt state.reference state.movedPositions (seedOccupation state) 0
    (moved_positions_continuous state).continuousAt normalizedContinuous slot

theorem response_fields_continuousAt_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions)) (slot : ElectronIndex state.reference.geometry) :
    ContinuousAt (fun time => responseFields state time slot) 0 :=
  occupied_fields_continuousAt state.reference state.movedPositions
    (fun time => (continuousPulseCandidate state time).occupied) 0
    (moved_positions_continuous state).continuousAt (candidate_occupied_continuousAt_zero state good unit) slot

theorem response_seed_actual (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) :
    next.1 = (continuousPulseCandidate state time).reprice
      (state.reserve-((continuousPulseCandidate state time).energy-state.energy)) := by
  obtain ⟨generated,generatedActual,same,_⟩ := pulse_outcome state next time actual
  have exactSeed : generated = seedOccupation state time := Except.ok.inj (generatedActual.symm.trans normalized)
  rw [same,exactSeed]
  rfl

theorem response_seed_good (state : Material frame) (time : ℝ)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) : Orthonormal ℂ (seedFields state time) :=
  (normalize_generated state.reference _ _ _ normalized).1

theorem response_after_good (state : Material frame) (time : ℝ)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) : Orthonormal ℂ (responseFields state time) :=
  physical_fock_response_good state.reference _ _ time (response_seed_good state time normalized)

theorem response_population_whole (state : Material frame)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (time : ℝ)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) :
    Generic.population (siteProjection state.reference (state.movedPositions time) nuclear) (responseFields state time) +
      Generic.population (siteSpace state.reference (state.movedPositions time) nuclear)ᗮ.starProjection
        (responseFields state time) = electronCount frame state.reference.geometry.originJoint := by
  have good := response_after_good state time normalized
  have result := Generic.whole_population (siteSpace state.reference (state.movedPositions time) nuclear)
    (responseFields state time) (fun slot => by rw [good.1 slot]; norm_num)
  simpa only [Fintype.card_fin,ElectronIndex,siteProjection] using result

private def fullBasis (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (index : CPS1MolecularFrame.ActualIndex source) : SpinSpace :=
  gramSchmidtNormed ℂ (ordered (basisAt source positions))
    (Fintype.equivFin (CPS1MolecularFrame.ActualIndex source) index)

private def fullFock (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  (totalNormalization (𝕜 := ℂ) (basisAt source positions)).conjTranspose *
    physicalFockAt source positions occupied * totalNormalization (𝕜 := ℂ) (basisAt source positions)

private def representedAction (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (field : SpinSpace) : SpinSpace :=
  ∑ first, ∑ second, fullFock source positions occupied first second •
    (inner ℂ (fullBasis source positions second) field • fullBasis source positions first)

private theorem represented_action_eq (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (field : SpinSpace)
    (nonzero : ∀ index, gramSchmidtNormed ℂ (ordered (basisAt source positions)) index ≠ 0) :
    physicalAction source positions occupied field = representedAction source positions occupied field := by
  classical
  let index : CPS1MolecularFrame.ActualIndex source ≃ NormedBasisIndex source positions :=
    fullNormedIndex (basisAt source positions) nonzero
  have synthesis : (basisSynthesis source positions).submatrix id index =
      totalNormalization (𝕜 := ℂ) (basisAt source positions) := rfl
  have fock : (normedPhysicalFock source positions occupied).submatrix index index =
      fullFock source positions occupied := by
    unfold normedPhysicalFock fullFock
    rw [← Matrix.submatrix_mul_equiv _ _ index (Equiv.refl _) index]
    simp only [Equiv.coe_refl]
    rw [← Matrix.submatrix_mul_equiv _ _ index (Equiv.refl _) id]
    simp only [Matrix.submatrix_id_id,Equiv.coe_refl,← Matrix.conjTranspose_submatrix,synthesis]
  simp only [physicalAction,sum_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply]
  rw [← index.sum_comp (fun first => ∑ second,
    normedPhysicalFock source positions occupied first second •
      (inner ℂ (normedBasisAt source positions second) field • normedBasisAt source positions first))]
  apply Finset.sum_congr rfl
  intro first _
  rw [← index.sum_comp (fun second => normedPhysicalFock source positions occupied (index first) second •
    (inner ℂ (normedBasisAt source positions second) field • normedBasisAt source positions (index first)))]
  apply Finset.sum_congr rfl
  intro second _
  have entry := congrArg (fun matrix => matrix first second) fock
  change normedPhysicalFock source positions occupied (index first) (index second) = _ at entry
  rw [entry]
  rfl

theorem physical_action_continuousAt_apply {X : Type*} [TopologicalSpace X]
    (source : CPS1ElectronicSource.State frame) (positions : X → NuclearConfiguration source)
    (occupied : X → Occupation source) (fields : X → SpinSpace) (current : X)
    (positionsContinuous : ContinuousAt positions current)
    (occupiedContinuous : ContinuousAt occupied current) (fieldsContinuous : ContinuousAt fields current)
    (unit : IsUnit (gramAt source (positions current))) :
    ContinuousAt (fun point => physicalAction source (positions point) (occupied point) (fields point)) current := by
  classical
  have independent := basis_independent_at_unit source (positions current) unit
  have rawContinuous (index : CPS1MolecularFrame.ActualIndex source) :
      ContinuousAt (fun point => basisAt source (positions point) index) current :=
    (basis_hasFDerivAt source (positions current) index).continuousAt.comp positionsContinuous
  have basisContinuous (index : CPS1MolecularFrame.ActualIndex source) :
      ContinuousAt (fun point => fullBasis source (positions point) index) current :=
    canonical_normed_continuousAt _ current rawContinuous independent _
  have normalizationContinuous := total_normalization_continuousAt _ current rawContinuous independent
  have fockContinuous : ContinuousAt (fun point => fullFock source (positions point) (occupied point)) current :=
    (normalizationContinuous.star.mul (physical_fock_continuousAt source positions occupied current
      positionsContinuous occupiedContinuous)).mul normalizationContinuous
  have representedContinuous : ContinuousAt
      (fun point => representedAction source (positions point) (occupied point) (fields point)) current :=
    tendsto_finsetSum Finset.univ fun first _ =>
      tendsto_finsetSum Finset.univ fun second _ =>
        ((continuous_apply_apply first second).continuousAt.comp fockContinuous).smul
          (((basisContinuous second).inner (𝕜 := ℂ) fieldsContinuous).smul (basisContinuous first))
  apply representedContinuous.congr
  filter_upwards [basis_unit_eventually source positions current positionsContinuous unit] with point generated
  have nonzero (index : Fin (Fintype.card (CPS1MolecularFrame.ActualIndex source))) :
      gramSchmidtNormed ℂ (ordered (basisAt source (positions point))) index ≠ 0 := by
    have norm := gramSchmidtNormed_unit_length index
      (ordered_independent _ (basis_independent_at_unit source (positions point) generated))
    intro zero
    rw [zero,norm_zero] at norm
    exact zero_ne_one norm
  exact (represented_action_eq source _ _ _ nonzero).symm

private theorem finite_flux_continuousAt {X E ι : Type*} [TopologicalSpace X] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (first second : X → ι → E) (current : X)
    (firstContinuous : ∀ slot, ContinuousAt (fun point => first point slot) current)
    (secondContinuous : ∀ slot, ContinuousAt (fun point => second point slot) current) :
    ContinuousAt (fun point => ∑ slot, (inner ℂ (first point slot) (second point slot)).im) current := by
  apply tendsto_finsetSum (Finset.univ : Finset ι)
  intro slot _
  exact Complex.continuous_im.continuousAt.comp
    ((firstContinuous slot).inner (𝕜 := ℂ) (secondContinuous slot))

theorem response_flux_continuousAt_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions))
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) : ContinuousAt (responseFlux state nuclear) 0 := by
  have positionsContinuous : ContinuousAt state.movedPositions (0 : ℝ) :=
    (moved_positions_continuous state).continuousAt
  have seedContinuous : ContinuousAt (seedOccupation state) (0 : ℝ) :=
    normalized_occupation_candidate_continuousAt state.reference
    state.movedPositions state.transportedOccupation 0 positionsContinuous
    (transported_occupation_continuous state).continuousAt (transported_good_at_zero state good)
  have currentUnit : IsUnit (gramAt state.reference (state.movedPositions 0)) := by
    simpa only [Material.movedPositions,kick_positions_zero] using unit
  let midpointFields : ℝ → ElectronIndex state.reference.geometry → SpinSpace :=
    fun time slot => Generic.midpoint (seedFields state time slot) (responseFields state time slot)
  let actionFields : ℝ → ElectronIndex state.reference.geometry → SpinSpace :=
    fun time slot => responseAction state time (midpointFields time slot)
  have midpointContinuous (slot : ElectronIndex state.reference.geometry) :
      ContinuousAt (fun time : ℝ => midpointFields time slot) (0 : ℝ) :=
    ((seed_fields_continuousAt_zero state good slot).add
      (response_fields_continuousAt_zero state good unit slot)).const_smul (1/2 : ℂ)
  have actionContinuous (slot : ElectronIndex state.reference.geometry) :
      ContinuousAt (fun time : ℝ => actionFields time slot) (0 : ℝ) :=
    physical_action_continuousAt_apply state.reference state.movedPositions (seedOccupation state)
      (fun time : ℝ => midpointFields time slot) 0 positionsContinuous seedContinuous
      (midpointContinuous slot) currentUnit
  let projectedMidpoint : ℝ → ElectronIndex state.reference.geometry → SpinSpace :=
    fun time slot => siteProjection state.reference (state.movedPositions time) nuclear (midpointFields time slot)
  let projectedAction : ℝ → ElectronIndex state.reference.geometry → SpinSpace :=
    fun time slot => siteProjection state.reference (state.movedPositions time) nuclear (actionFields time slot)
  have firstContinuous (slot : ElectronIndex state.reference.geometry) :
      ContinuousAt (fun time : ℝ => projectedMidpoint time slot) (0 : ℝ) :=
    site_projection_continuousAt state.reference state.movedPositions
      (fun time : ℝ => midpointFields time slot) 0 positionsContinuous (midpointContinuous slot) nuclear
  have secondContinuous (slot : ElectronIndex state.reference.geometry) :
      ContinuousAt (fun time : ℝ => projectedAction time slot) (0 : ℝ) :=
    site_projection_continuousAt state.reference state.movedPositions
      (fun time : ℝ => actionFields time slot) 0 positionsContinuous (actionContinuous slot) nuclear
  exact finite_flux_continuousAt projectedMidpoint projectedAction (0 : ℝ) firstContinuous secondContinuous

end
end CPS1AddressedTransfer
