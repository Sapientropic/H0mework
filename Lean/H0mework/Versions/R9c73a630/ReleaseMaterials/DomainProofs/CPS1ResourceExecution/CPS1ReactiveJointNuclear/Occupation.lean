import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveJointNuclear.Motion
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.State
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.CanonicalContinuity
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/- Cache construction draft; the next parent-released lane must kernel-check it. -/
namespace CPS1ReactiveJointNuclear
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear InnerProductSpace
open CPS1ReactiveField CPS1ReactiveField.Carried
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.Elementwise Topology
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame}
variable {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}

@[reducible] def occupiedPivot (state : Snapshot) (index : Fin (Fintype.card state.ElectronIndex)) : SpinSpace :=
  gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields) index

def NonzeroPivots (state : Snapshot) : Prop := ∀ index : Fin (Fintype.card state.ElectronIndex), occupiedPivot state index ≠ 0

/-- Total coefficients of the already-owned full Gram-Schmidt recurrence. No
rank-dependent reindexing, arbitrary inverse raw Gram, or supplied frame enters. -/
@[reducible] def normalizationMatrix (state : Snapshot) : Matrix state.ElectronIndex state.ElectronIndex ℂ :=
  CPS1PositivePulse.totalNormalization (𝕜 := ℂ) state.fields

@[reducible] def normalizedField (state : Snapshot) (slot : state.ElectronIndex) : SpinSpace :=
  gramSchmidtNormed ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields)
    (Fintype.equivFin state.ElectronIndex slot)

@[reducible] def normalize (state : Snapshot) : Snapshot :=
  CPS1ReactiveFieldDynamics.withOccupation state (state.occupied * normalizationMatrix state)

theorem normalization_synthesis (state : Snapshot) (slot : state.ElectronIndex) :
    normalizedField state slot =
      ∑ old : state.ElectronIndex, normalizationMatrix state old slot • state.fields old := by
  classical
  let index := Fintype.equivFin state.ElectronIndex slot
  change (‖occupiedPivot state index‖ : ℂ)⁻¹ • occupiedPivot state index = _
  calc
    _ = (‖occupiedPivot state index‖ : ℂ)⁻¹ •
        (∑ old : Fin (Fintype.card state.ElectronIndex),
          CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) state.fields index old •
            CPS1MolecularFrame.FiniteNormed.ordered state.fields old) :=
      congrArg (fun value => (‖occupiedPivot state index‖ : ℂ)⁻¹ • value)
        (CPS1MolecularFrame.FiniteNormed.gs_coefficients_synthesis state.fields index)
    _ = ∑ old : Fin (Fintype.card state.ElectronIndex),
        ((‖occupiedPivot state index‖ : ℂ)⁻¹ *
          CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) state.fields index old) •
            CPS1MolecularFrame.FiniteNormed.ordered state.fields old := by
      rw [Finset.smul_sum]
      simp only [← mul_smul]
    _ = _ := by
      simpa only [normalizationMatrix,CPS1PositivePulse.totalNormalization,occupiedPivot,
        CPS1MolecularFrame.FiniteNormed.ordered,
        Equiv.symm_apply_apply,index] using!
        ((Fintype.equivFin state.ElectronIndex).sum_comp (fun old : Fin (Fintype.card state.ElectronIndex) =>
          ((‖occupiedPivot state index‖ : ℂ)⁻¹ *
            CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) state.fields index old) •
              CPS1MolecularFrame.FiniteNormed.ordered state.fields old)).symm

theorem normalized_fields (state : Snapshot) : (normalize state).fields = normalizedField state := by
  funext slot
  change CPS1ElectronicEvolution.fields (fun primitive => (state.primitive primitive).jet 0)
    (state.occupied * normalizationMatrix state) slot = normalizedField state slot
  rw [CPS1Deformation.fields_mul]
  exact (normalization_synthesis state slot).symm

theorem normalized_good (state : Snapshot) (pivots : NonzeroPivots state) : (normalize state).Good := by
  classical
  have normedNonzero (index : Fin (Fintype.card state.ElectronIndex)) :
      gramSchmidtNormed ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields) index ≠ 0 := by
    change (‖occupiedPivot state index‖ : ℂ)⁻¹ • occupiedPivot state index ≠ 0
    exact smul_ne_zero (inv_ne_zero (RCLike.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (pivots index)))) (pivots index)
  let select : state.ElectronIndex → CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) state.fields :=
    fun slot => ⟨Fintype.equivFin state.ElectronIndex slot,normedNonzero _⟩
  have injective : Function.Injective select := by
    intro first second same
    exact (Fintype.equivFin state.ElectronIndex).injective (congrArg Subtype.val same)
  have generated := (CPS1MolecularFrame.FiniteNormed.field_orthonormal state.fields).comp select injective
  change Orthonormal ℂ (normalize state).fields
  rw [normalized_fields]
  exact generated

theorem good_pivots (state : Snapshot) (good : state.Good) : NonzeroPivots state := by
  have ordered : Orthonormal ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields) :=
    good.comp _ (Fintype.equivFin state.ElectronIndex).symm.injective
  intro index
  exact gramSchmidt_ne_zero index ordered.linearIndependent

private theorem projection_ratio_zero (state : Snapshot) (good : state.Good)
    (previous current : Fin (Fintype.card state.ElectronIndex)) (less : previous < current) :
    CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) state.fields previous current = 0 := by
  have ordered : Orthonormal ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields) :=
    good.comp _ (Fintype.equivFin state.ElectronIndex).symm.injective
  change inner ℂ (gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields) previous)
    (CPS1MolecularFrame.FiniteNormed.ordered state.fields current) /
      (‖gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields) previous‖ : ℂ)^2 = 0
  rw [gramSchmidt_of_orthogonal ℂ ordered.2,
    orthonormal_iff_ite.mp ordered previous current,if_neg less.ne,zero_div]

private theorem gs_coefficients_current (state : Snapshot) (good : state.Good)
    (current source : Fin (Fintype.card state.ElectronIndex)) :
    CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) state.fields current source =
      if source = current then 1 else 0 := by
  rw [CPS1MolecularFrame.FiniteNormed.gs_coefficients_step]
  have zero : (∑ previous : Finset.Iio current,
      CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) state.fields previous.val current *
        CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) state.fields previous.val source) = 0 := by
    apply Finset.sum_eq_zero
    intro previous _
    rw [projection_ratio_zero state good _ _ (Finset.mem_Iio.mp previous.property),zero_mul]
  rw [zero,sub_zero]

/-- This pays exact stored-C recovery even if the full raw primitive family has
null relations. Field equality is never used to infer coefficient equality. -/
theorem normalization_matrix_current (state : Snapshot) (good : state.Good) :
    normalizationMatrix state = 1 := by
  have ordered : Orthonormal ℂ (CPS1MolecularFrame.FiniteNormed.ordered state.fields) :=
    good.comp _ (Fintype.equivFin state.ElectronIndex).symm.injective
  ext old slot
  simp only [normalizationMatrix,CPS1PositivePulse.totalNormalization,
    gramSchmidt_of_orthogonal ℂ ordered.2,
    ordered.1,RCLike.ofReal_one,inv_one,one_mul,gs_coefficients_current state good,
    (Fintype.equivFin state.ElectronIndex).injective.eq_iff,Matrix.one_apply]

theorem normalize_current (state : Snapshot) (good : state.Good) : normalize state = state := by
  rw [normalize,normalization_matrix_current state good,Matrix.mul_one]
  all_goals (cases state; rfl)

theorem normalization_storage (state : Snapshot) :
    (normalize state).primitive = state.primitive ∧
    (normalize state).nuclei = state.nuclei ∧
    (normalize state).waterOrigins = state.waterOrigins ∧
    (normalize state).electronInertia = state.electronInertia ∧
    (normalize state).Ne = state.Ne ∧
    (normalize state).occupied = state.occupied * normalizationMatrix state :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

@[reducible] def response (germ : Germ root state) (time : ℝ) : Snapshot := normalize (preResponse germ time)

def energyDelta (germ : Germ root state) (time : ℝ) : ℝ := (response germ time).energy-state.energy

@[reducible] def paidResponse (germ : Germ root state) (time : ℝ) : Snapshot :=
  (response germ time).reprice (state.reserve-energyDelta germ time)

theorem response_zero (germ : Germ root state) (good : state.Good) : response germ 0 = state := by
  rw [response,pre_response_zero,normalize_current state good]

theorem energy_delta_zero (germ : Germ root state) (good : state.Good) : energyDelta germ 0 = 0 := by
  rw [energyDelta,response_zero germ good,sub_self]

theorem response_good (germ : Germ root state) (time : ℝ)
    (pivots : NonzeroPivots (preResponse germ time)) : (response germ time).Good :=
  normalized_good _ pivots

theorem paid_response_account (germ : Germ root state) (time : ℝ) :
    (paidResponse germ time).energy = (response germ time).energy ∧
    (paidResponse germ time).reserve = state.reserve-energyDelta germ time ∧
    (paidResponse germ time).account = state.account ∧
    (paidResponse germ time).Ne = state.Ne ∧
    (paidResponse germ time).occupied =
      electronicKick state time * (show Matrix state.ElectronIndex state.ElectronIndex ℂ from normalizationMatrix (preResponse germ time)) ∧
    (paidResponse germ time).nuclei =
      List.ofFn (germ.nodeAt (movedPositions germ time) (movedMomenta germ time)) := by
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl⟩
  change (response germ time).energy+(state.reserve-energyDelta germ time) = state.energy+state.reserve
  unfold energyDelta
  ring

theorem moving_primitive_continuousAt (germ : Germ root state) (point : ℝ)
    (primitive : state.PrimitiveIndex) (jet : Fin 3 → Nat) :
    ContinuousAt (fun time : ℝ => primitiveJetAt germ (movedPositions germ time) primitive jet) point :=
  (primitive_jet_hasFDerivAt germ (movedPositions germ point) primitive jet).continuousAt.comp
    (moved_positions_continuousAt germ point)

theorem pre_response_jet_continuousAt (germ : Germ root state) (point : ℝ)
    (electron : state.ElectronIndex) (jet : Fin 3 → Nat) :
    ContinuousAt (fun time : ℝ => (preResponse germ time).jet electron jet) point := by
  classical
  have coefficients : ContinuousAt (electronicKick state) point :=
    CPS1ReactiveFieldDynamics.response_occupation_continuous state point
  change ContinuousAt (fun time : ℝ => ∑ primitive,
    electronicKick state time primitive electron •
      primitiveJetAt germ (movedPositions germ time) primitive jet) point
  exact tendsto_finsetSum Finset.univ fun primitive _ =>
    ((continuous_apply_apply primitive electron).continuousAt.comp coefficients).smul
      (moving_primitive_continuousAt germ point primitive jet)

private theorem pre_response_fields_zero (germ : Germ root state) :
    (fun electron : state.ElectronIndex => (preResponse germ 0).fields electron) = state.fields := by
  funext electron
  change (∑ primitive : state.PrimitiveIndex,
    electronicKick state 0 primitive electron •
      primitiveJetAt germ (movedPositions germ 0) primitive 0) = state.fields electron
  rw [electronic_kick_zero,moved_positions_zero]
  exact germ.jet_current electron 0

theorem normalization_matrix_continuous_zero (germ : Germ root state) (good : state.Good) :
    ContinuousAt (fun time : ℝ => (show Matrix state.ElectronIndex state.ElectronIndex ℂ from normalizationMatrix (preResponse germ time))) 0 := by
  have initialGood : Orthonormal ℂ (fun electron : state.ElectronIndex =>
      (preResponse germ 0).fields electron) := by
    rw [pre_response_fields_zero]
    exact good
  exact CPS1PositivePulse.total_normalization_continuousAt
    (fun time : ℝ => fun electron : state.ElectronIndex => (preResponse germ time).fields electron) 0
    (fun electron => pre_response_jet_continuousAt germ 0 electron 0) initialGood.linearIndependent

theorem pivots_eventually_nonzero (germ : Germ root state) (good : state.Good) :
    ∀ᶠ time in 𝓝 (0 : ℝ), NonzeroPivots (preResponse germ time) := by
  have initialGood : Orthonormal ℂ (fun electron : state.ElectronIndex =>
      (preResponse germ 0).fields electron) := by
    rw [pre_response_fields_zero]
    exact good
  have initialPivots : NonzeroPivots (preResponse germ 0) := good_pivots _ initialGood
  exact Filter.eventually_all.mpr fun index =>
    (CPS1PositivePulse.canonical_gs_continuousAt
      (fun time : ℝ => fun electron : state.ElectronIndex => (preResponse germ time).fields electron) 0
      (fun electron => pre_response_jet_continuousAt germ 0 electron 0)
      initialGood.linearIndependent index).eventually_ne (initialPivots index)

theorem response_occupation_continuous_zero (germ : Germ root state) (good : state.Good) :
    ContinuousAt (fun time : ℝ => (show germ.Coefficients from (response germ time).occupied)) 0 :=
  CPS1PositivePulse.matrix_mul_continuousAt (electronicKick state)
    (fun time => (show Matrix state.ElectronIndex state.ElectronIndex ℂ from normalizationMatrix (preResponse germ time))) 0
    (CPS1ReactiveFieldDynamics.response_occupation_continuous state 0)
    (normalization_matrix_continuous_zero germ good)

theorem nuclear_energy_continuous_zero (germ : Germ root state) :
    ContinuousAt (fun time : ℝ =>
      CPS1AtomicDynamics.Body.energy (preResponse germ time).nuclei) 0 := by
  have phaseContinuous : ContinuousAt (fun time : ℝ =>
      (movedPositions germ time,movedMomenta germ time)) 0 :=
    (moved_positions_continuousAt germ 0).prodMk (moved_momenta_continuousAt germ 0)
  have fullContinuous : ContinuousAt (fullNuclearEnergy germ)
      (movedPositions germ 0,movedMomenta germ 0) := by
    simpa only [moved_positions_zero,moved_momenta_zero] using
      (full_nuclear_hasFDerivAt germ).continuousAt
  have electronicContinuous : ContinuousAt (fieldEnergyAt germ) (movedPositions germ 0) := by
    simpa only [moved_positions_zero] using
      (field_energy_differentiable germ germ.positions).continuousAt
  have generated : ContinuousAt (fun time : ℝ => fullNuclearEnergy germ
      (movedPositions germ time,movedMomenta germ time) - fieldEnergyAt germ (movedPositions germ time)) 0 :=
    (ContinuousAt.comp (f := fun time : ℝ => (movedPositions germ time,movedMomenta germ time))
      (g := fullNuclearEnergy germ) fullContinuous phaseContinuous).sub
        (ContinuousAt.comp (f := movedPositions germ) (g := fieldEnergyAt germ)
          electronicContinuous (moved_positions_continuousAt germ 0))
  simpa only [full_nuclear_energy_eq,add_sub_cancel_right,Germ.nuclearEnergy,preResponse,
    Germ.snapshotAt] using generated

private theorem raw_kinetic_continuous_zero (germ : Germ root state)
    (p q : state.PrimitiveIndex) :
    ContinuousAt (fun time : ℝ => CPS1ReactiveFieldDynamics.rawKinetic (preResponse germ time) p q) 0 := by
  change ContinuousAt (fun time : ℝ => ((1/(2*state.electronInertia) : ℝ) : ℂ) *
    ∑ axis : Fin 3, inner ℂ
      (primitiveJetAt germ (movedPositions germ time) p (raise 0 axis))
      (primitiveJetAt germ (movedPositions germ time) q (raise 0 axis))) 0
  exact continuousAt_const.mul (tendsto_finsetSum Finset.univ fun axis _ =>
    (moving_primitive_continuousAt germ 0 p (raise 0 axis)).inner
      (moving_primitive_continuousAt germ 0 q (raise 0 axis)))

private theorem raw_attraction_continuous_zero (germ : Germ root state)
    (p q : state.PrimitiveIndex) :
    ContinuousAt (fun time : ℝ => CPS1ReactiveFieldDynamics.rawAttraction (preResponse germ time) p q) 0 := by
  have kernel (spin : Bool) (id : germ.Id) :
      ContinuousAt (fun time : ℝ => rawNuclearAt germ (movedPositions germ time) p q spin id) 0 := by
    have primitive : ContinuousAt (fun positions => rawNuclearAt germ positions p q spin id)
        (movedPositions germ 0) := by
      simpa only [moved_positions_zero] using
        (raw_nuclear_differentiable germ germ.positions p q spin id).continuousAt
    exact primitive.comp (moved_positions_continuousAt germ 0)
  have expression : (fun time : ℝ => CPS1ReactiveFieldDynamics.rawAttraction (preResponse germ time) p q) =
      fun time : ℝ => ∑ slot : Fin state.nuclei.length,
        -((state.nuclei.get slot).particle.charge : ℂ) *
          ∑ spin : Bool, rawNuclearAt germ (movedPositions germ time) p q spin (germ.nuclearId slot) := by
    funext time
    unfold CPS1ReactiveFieldDynamics.rawAttraction
    change ((List.ofFn (germ.nodeAt (movedPositions germ time) (movedMomenta germ time))).map
      (fun nuclear => -(nuclear.particle.charge : ℂ) *
        ∑ spin : Bool, (preResponse germ time).nuclearIntegral p q spin
          (Geometry.nucleusPosition nuclear))).sum = _
    rw [List.map_ofFn,List.sum_ofFn]
    rfl
  rw [expression]
  exact tendsto_finsetSum Finset.univ fun slot _ =>
    continuousAt_const.mul (tendsto_finsetSum Finset.univ fun spin _ => kernel spin (germ.nuclearId slot))

theorem raw_core_continuous_zero (germ : Germ root state) :
    ContinuousAt (fun time : ℝ => (show Matrix state.PrimitiveIndex state.PrimitiveIndex ℂ from
      CPS1ReactiveFieldDynamics.rawCore (preResponse germ time))) 0 := by
  apply continuousAt_pi.mpr
  intro p
  apply continuousAt_pi.mpr
  intro q
  exact (raw_kinetic_continuous_zero germ p q).add (raw_attraction_continuous_zero germ p q)

theorem raw_tensor_continuous_zero (germ : Germ root state) :
    ContinuousAt (fun time : ℝ => (show state.PrimitiveIndex → state.PrimitiveIndex →
      state.PrimitiveIndex → state.PrimitiveIndex → ℂ from
      CPS1ReactiveFieldDynamics.rawTensor (preResponse germ time))) 0 := by
  apply continuousAt_pi.mpr
  intro p
  apply continuousAt_pi.mpr
  intro q
  apply continuousAt_pi.mpr
  intro r
  apply continuousAt_pi.mpr
  intro s
  change ContinuousAt (fun time : ℝ => ∑ spin : Bool, ∑ secondSpin : Bool,
    rawPairAt germ (movedPositions germ time) p r q s spin secondSpin) 0
  exact tendsto_finsetSum Finset.univ fun spin _ =>
    tendsto_finsetSum Finset.univ fun secondSpin _ => by
      have primitive : ContinuousAt
          (fun positions => rawPairAt germ positions p r q s spin secondSpin) (movedPositions germ 0) := by
        simpa only [moved_positions_zero] using
          (raw_pair_differentiable germ germ.positions p r q s spin secondSpin).continuousAt
      exact primitive.comp (moved_positions_continuousAt germ 0)

private theorem occupied_energy_joint_continuousAt {X n m : Type*}
    [TopologicalSpace X] [Fintype n] [Fintype m]
    (core : X → Matrix n n ℂ) (tensor : X → n → n → n → n → ℂ)
    (coefficients : X → Matrix n m ℂ) (point : X)
    (coreContinuous : ContinuousAt core point) (tensorContinuous : ContinuousAt tensor point)
    (coefficientsContinuous : ContinuousAt coefficients point) :
    ContinuousAt (fun x => CPS1ReactiveFieldDynamics.Polynomial.occupiedEnergy
      (core x) (tensor x) (coefficients x)) point := by
  have c (p : n) (i : m) := (continuous_apply_apply p i).continuousAt.comp coefficientsContinuous
  have h (p q : n) := (continuous_apply_apply p q).continuousAt.comp coreContinuous
  have v (p q r s : n) : ContinuousAt (fun x => tensor x p q r s) point :=
    continuousAt_pi.mp (continuousAt_pi.mp (continuousAt_pi.mp (continuousAt_pi.mp tensorContinuous p) q) r) s
  have one : ContinuousAt (fun x => ∑ i : m, ∑ p : n, ∑ q : n,
      star (coefficients x p i) * coefficients x q i * core x p q) point :=
    tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun p _ =>
      tendsto_finsetSum Finset.univ fun q _ => ((c p i).star.mul (c q i)).mul (h p q)
  have pair : ContinuousAt (fun x => ∑ i : m, ∑ j : m, ∑ p : n, ∑ q : n, ∑ r : n, ∑ s : n,
      (star (coefficients x p i) * coefficients x q i * star (coefficients x r j) * coefficients x s j) *
        (tensor x p r q s - tensor x p r s q)) point :=
    tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_finsetSum Finset.univ fun p _ => tendsto_finsetSum Finset.univ fun q _ =>
      tendsto_finsetSum Finset.univ fun r _ => tendsto_finsetSum Finset.univ fun s _ =>
        ((((c p i).star.mul (c q i)).mul ((c r j).star)).mul (c s j)).mul
          ((v p r q s).sub (v p r s q))
  exact (Complex.continuous_re.continuousAt.comp one).add
    (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp pair))

theorem response_energy_continuous_zero (germ : Germ root state) (good : state.Good) :
    ContinuousAt (fun time : ℝ => (response germ time).energy) 0 := by
  have polynomial := occupied_energy_joint_continuousAt
    (fun time : ℝ => (show Matrix state.PrimitiveIndex state.PrimitiveIndex ℂ from
      CPS1ReactiveFieldDynamics.rawCore (preResponse germ time)))
    (fun time : ℝ => (show state.PrimitiveIndex → state.PrimitiveIndex →
      state.PrimitiveIndex → state.PrimitiveIndex → ℂ from
      CPS1ReactiveFieldDynamics.rawTensor (preResponse germ time)))
    (fun time : ℝ => (show germ.Coefficients from (response germ time).occupied)) 0
    (raw_core_continuous_zero germ) (raw_tensor_continuous_zero germ)
    (response_occupation_continuous_zero germ good)
  have generated : ContinuousAt (fun time : ℝ =>
      CPS1AtomicDynamics.Body.energy (preResponse germ time).nuclei +
        CPS1ReactiveFieldDynamics.Polynomial.occupiedEnergy
          (CPS1ReactiveFieldDynamics.rawCore (preResponse germ time))
          (CPS1ReactiveFieldDynamics.rawTensor (preResponse germ time))
          (response germ time).occupied) 0 :=
    (nuclear_energy_continuous_zero germ).add polynomial
  have physical : (fun time : ℝ =>
      CPS1AtomicDynamics.Body.energy (preResponse germ time).nuclei +
        CPS1ReactiveFieldDynamics.Polynomial.occupiedEnergy
          (CPS1ReactiveFieldDynamics.rawCore (preResponse germ time))
          (CPS1ReactiveFieldDynamics.rawTensor (preResponse germ time))
          (response germ time).occupied) = (fun time : ℝ => (response germ time).energy) := by
    funext time
    exact (CPS1ReactiveFieldDynamics.energy_occupied (preResponse germ time)
      ((preResponse germ time).occupied * normalizationMatrix (preResponse germ time))).symm
  exact physical ▸ generated

theorem energy_delta_continuous_zero (germ : Germ root state) (good : state.Good) :
    ContinuousAt (energyDelta germ) 0 :=
  (response_energy_continuous_zero germ good).sub continuousAt_const

private theorem gs_differentiableAt {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype ι] (raw : X → ι → SpinSpace) (point : X)
    (generated : ∀ index, DifferentiableAt ℝ (fun x => raw x index) point)
    (independent : LinearIndependent ℂ (raw point)) (current : Fin (Fintype.card ι)) :
    DifferentiableAt ℝ (fun x => gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) current) point := by
  classical
  have ordered := CPS1PositivePulse.ordered_independent (raw point) independent
  apply wellFounded_lt.induction current
  intro current previous
  have each (prior : Finset.Iio current) : DifferentiableAt ℝ (fun x =>
      CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (raw x) prior.val current •
        gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) prior.val) point := by
    have before := previous prior.val (Finset.mem_Iio.mp prior.property)
    have nonzero := gramSchmidt_ne_zero prior.val ordered
    have denominator : DifferentiableAt ℝ (fun x =>
        (‖gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) prior.val‖ : ℂ)^2) point :=
      (Complex.ofRealCLM.differentiableAt.comp point (before.norm ℂ nonzero)).pow 2
    have ratio : DifferentiableAt ℝ (fun x =>
        CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (raw x) prior.val current) point := by
      change DifferentiableAt ℝ (fun x =>
        inner ℂ (gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) prior.val)
          (CPS1MolecularFrame.FiniteNormed.ordered (raw x) current) /
          (‖gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) prior.val‖ : ℂ)^2) point
      have numerator : DifferentiableAt ℝ (fun x =>
          inner ℂ (gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) prior.val)
            (CPS1MolecularFrame.FiniteNormed.ordered (raw x) current)) point :=
        before.inner ℂ (generated ((Fintype.equivFin ι).symm current))
      have denominatorNonzero :
          (‖gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw point)) prior.val‖ : ℂ)^2 ≠ 0 :=
        pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero))
      simpa only [div_eq_mul_inv] using! numerator.mul (denominator.inv denominatorNonzero)
    exact ratio.smul before
  have total : DifferentiableAt ℝ (fun x => ∑ prior : Finset.Iio current,
      CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (raw x) prior.val current •
        gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) prior.val) point :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun prior _ => each prior)
  have next : DifferentiableAt ℝ (fun x => CPS1MolecularFrame.FiniteNormed.ordered (raw x) current -
      ∑ prior : Finset.Iio current,
        CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (raw x) prior.val current •
          gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) prior.val) point :=
    (generated ((Fintype.equivFin ι).symm current)).sub total
  simpa only [← CPS1PositivePulse.canonical_gs_step] using next

private theorem ratio_differentiableAt {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype ι] (raw : X → ι → SpinSpace) (point : X)
    (generated : ∀ index, DifferentiableAt ℝ (fun x => raw x index) point)
    (independent : LinearIndependent ℂ (raw point)) (previous current : Fin (Fintype.card ι)) :
    DifferentiableAt ℝ
      (fun x => CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (raw x) previous current) point := by
  have before := gs_differentiableAt raw point generated independent previous
  have nonzero := gramSchmidt_ne_zero previous (CPS1PositivePulse.ordered_independent (raw point) independent)
  have denominator : DifferentiableAt ℝ (fun x =>
      (‖gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) previous‖ : ℂ)^2) point :=
    (Complex.ofRealCLM.differentiableAt.comp point (before.norm ℂ nonzero)).pow 2
  change DifferentiableAt ℝ (fun x =>
    inner ℂ (gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) previous)
      (CPS1MolecularFrame.FiniteNormed.ordered (raw x) current) /
      (‖gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) previous‖ : ℂ)^2) point
  have numerator : DifferentiableAt ℝ (fun x =>
      inner ℂ (gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw x)) previous)
        (CPS1MolecularFrame.FiniteNormed.ordered (raw x) current)) point :=
    before.inner ℂ (generated ((Fintype.equivFin ι).symm current))
  have denominatorNonzero :
      (‖gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (raw point)) previous‖ : ℂ)^2 ≠ 0 :=
    pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero))
  simpa only [div_eq_mul_inv] using! numerator.mul (denominator.inv denominatorNonzero)

private theorem gs_coefficients_differentiableAt {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype ι] (raw : X → ι → SpinSpace) (point : X)
    (generated : ∀ index, DifferentiableAt ℝ (fun x => raw x index) point)
    (independent : LinearIndependent ℂ (raw point)) (current source : Fin (Fintype.card ι)) :
    DifferentiableAt ℝ (fun x =>
      CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) (raw x) current source) point := by
  classical
  apply wellFounded_lt.induction current
  intro current previous
  have sum : DifferentiableAt ℝ (fun x => ∑ prior : Finset.Iio current,
      CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (raw x) prior.val current *
        CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) (raw x) prior.val source) point :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun prior _ =>
      (ratio_differentiableAt raw point generated independent prior.val current).mul
        (previous prior.val (Finset.mem_Iio.mp prior.property)))
  have result : DifferentiableAt ℝ (fun x => (if source = current then (1 : ℂ) else 0) -
      ∑ prior : Finset.Iio current,
        CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (raw x) prior.val current *
          CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) (raw x) prior.val source) point :=
    (differentiableAt_const (if source = current then (1 : ℂ) else 0)).sub sum
  simpa only [← CPS1MolecularFrame.FiniteNormed.gs_coefficients_step] using result

private theorem total_normalization_differentiableAt {X ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]
    (raw : X → ι → SpinSpace) (point : X)
    (generated : ∀ index, DifferentiableAt ℝ (fun x => raw x index) point)
    (independent : LinearIndependent ℂ (raw point)) :
    DifferentiableAt ℝ (fun x => CPS1PositivePulse.totalNormalization (𝕜 := ℂ) (raw x)) point := by
  apply differentiableAt_pi.mpr
  intro source
  apply differentiableAt_pi.mpr
  intro slot
  have before := gs_differentiableAt raw point generated independent (Fintype.equivFin ι slot)
  have nonzero := gramSchmidt_ne_zero (Fintype.equivFin ι slot)
    (CPS1PositivePulse.ordered_independent (raw point) independent)
  have normed := (Complex.ofRealCLM.differentiableAt.comp point (before.norm ℂ nonzero)).inv
    (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero))
  exact normed.mul (gs_coefficients_differentiableAt raw point generated independent
    (Fintype.equivFin ι slot) (Fintype.equivFin ι source))

theorem normalization_at_current (germ : Germ root state) (good : state.Good) :
    normalizationAt germ germ.positions = 1 := by
  have current : (fun electron => occupiedJetAt germ germ.positions electron 0) = state.fields := by
    funext electron
    exact germ.jet_current electron 0
  rw [normalizationAt,current]
  exact normalization_matrix_current state good

theorem normalization_at_differentiable (germ : Germ root state) (good : state.Good) :
    DifferentiableAt ℝ (normalizationAt germ) germ.positions := by
  have current : (fun electron => occupiedJetAt germ germ.positions electron 0) = state.fields := by
    funext electron
    exact germ.jet_current electron 0
  have independent : LinearIndependent ℂ (fun electron => occupiedJetAt germ germ.positions electron 0) :=
    current.symm ▸ good.linearIndependent
  exact total_normalization_differentiableAt
    (fun positions electron => occupiedJetAt germ positions electron 0) germ.positions
    (fun electron => (occupied_jet_hasFDerivAt germ germ.positions electron 0).differentiableAt) independent

@[reducible] def phaseCore (germ : Germ root state) (phase : NuclearPhase germ) :
    Matrix state.PrimitiveIndex state.PrimitiveIndex ℂ :=
  CPS1ReactiveFieldDynamics.rawCore (germ.snapshotAt (phase,state.occupied))

@[reducible] def phaseTensor (germ : Germ root state) (phase : NuclearPhase germ) :
    state.PrimitiveIndex → state.PrimitiveIndex → state.PrimitiveIndex → state.PrimitiveIndex → ℂ :=
  CPS1ReactiveFieldDynamics.rawTensor (germ.snapshotAt (phase,state.occupied))

theorem full_energy_joint_form (germ : Germ root state) (configuration : germ.FullConfiguration) :
    germ.energy configuration = germ.nuclearEnergy configuration.1.1 configuration.1.2 +
      CPS1ReactiveFieldDynamics.Polynomial.occupiedEnergy
        (phaseCore germ configuration.1) (phaseTensor germ configuration.1) configuration.2 := by
  have stored : germ.snapshotAt configuration = CPS1ReactiveFieldDynamics.withOccupation
      (germ.snapshotAt (configuration.1,state.occupied)) configuration.2 := rfl
  rw [Germ.energy,stored,CPS1ReactiveFieldDynamics.energy_occupied]
  all_goals rfl

private theorem phase_core_differentiable (germ : Germ root state) :
    DifferentiableAt ℝ (phaseCore germ) (germ.positions,germ.momenta) := by
  let phasePoint : NuclearPhase germ := (germ.positions,germ.momenta)
  have position : DifferentiableAt ℝ (fun phase : NuclearPhase germ => phase.1) phasePoint :=
    (ContinuousLinearMap.fst ℝ germ.Configuration germ.Configuration).differentiableAt
  have jet (primitive : state.PrimitiveIndex) (order : Fin 3 → Nat) :=
    (primitive_jet_hasFDerivAt germ germ.positions primitive order).differentiableAt.comp phasePoint position
  apply differentiableAt_pi.mpr
  intro p
  apply differentiableAt_pi.mpr
  intro q
  have kinetic : DifferentiableAt ℝ (fun phase : NuclearPhase germ =>
      CPS1ReactiveFieldDynamics.rawKinetic (germ.snapshotAt (phase,state.occupied)) p q) phasePoint := by
    change DifferentiableAt ℝ (fun phase : NuclearPhase germ =>
      ((1/(2*state.electronInertia) : ℝ) : ℂ) * ∑ axis : Fin 3,
        inner ℂ (primitiveJetAt germ phase.1 p (raise 0 axis))
          (primitiveJetAt germ phase.1 q (raise 0 axis))) phasePoint
    exact (DifferentiableAt.fun_sum (u := Finset.univ)
      (fun axis _ => (jet p (raise 0 axis)).inner ℂ (jet q (raise 0 axis)))).const_mul _
  have expression : (fun phase : NuclearPhase germ =>
      CPS1ReactiveFieldDynamics.rawAttraction (germ.snapshotAt (phase,state.occupied)) p q) =
      fun phase : NuclearPhase germ => ∑ slot : Fin state.nuclei.length,
        -((state.nuclei.get slot).particle.charge : ℂ) *
          ∑ spin : Bool, rawNuclearAt germ phase.1 p q spin (germ.nuclearId slot) := by
    funext phase
    unfold CPS1ReactiveFieldDynamics.rawAttraction
    change ((List.ofFn (germ.nodeAt phase.1 phase.2)).map
      (fun nuclear => -(nuclear.particle.charge : ℂ) * ∑ spin : Bool,
        (germ.snapshotAt (phase,state.occupied)).nuclearIntegral p q spin
          (Geometry.nucleusPosition nuclear))).sum = _
    rw [List.map_ofFn,List.sum_ofFn]
    rfl
  have attraction : DifferentiableAt ℝ (fun phase : NuclearPhase germ =>
      CPS1ReactiveFieldDynamics.rawAttraction (germ.snapshotAt (phase,state.occupied)) p q) phasePoint := by
    rw [expression]
    exact DifferentiableAt.fun_sum (u := Finset.univ) (fun slot _ =>
      (DifferentiableAt.fun_sum (u := Finset.univ) (fun spin _ =>
        (raw_nuclear_differentiable germ germ.positions p q spin (germ.nuclearId slot)).comp phasePoint position)).const_mul _)
  exact kinetic.add attraction

private theorem phase_tensor_differentiable (germ : Germ root state) :
    DifferentiableAt ℝ (phaseTensor germ) (germ.positions,germ.momenta) := by
  let phasePoint : NuclearPhase germ := (germ.positions,germ.momenta)
  have position : DifferentiableAt ℝ (fun phase : NuclearPhase germ => phase.1) phasePoint :=
    (ContinuousLinearMap.fst ℝ germ.Configuration germ.Configuration).differentiableAt
  apply differentiableAt_pi.mpr
  intro p
  apply differentiableAt_pi.mpr
  intro q
  apply differentiableAt_pi.mpr
  intro r
  apply differentiableAt_pi.mpr
  intro s
  change DifferentiableAt ℝ (fun phase : NuclearPhase germ =>
    ∑ spin : Bool, ∑ secondSpin : Bool, rawPairAt germ phase.1 p r q s spin secondSpin) phasePoint
  exact DifferentiableAt.fun_sum (u := Finset.univ) (fun spin _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun secondSpin _ =>
      DifferentiableAt.comp (f := fun phase : NuclearPhase germ => phase.1)
        (g := fun positions : germ.Configuration => rawPairAt germ positions p r q s spin secondSpin)
        phasePoint (raw_pair_differentiable germ germ.positions p r q s spin secondSpin) position))

private theorem polynomial_joint_differentiableAt {X n m : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype n] [Fintype m]
    (core : X → Matrix n n ℂ) (tensor : X → n → n → n → n → ℂ)
    (coefficients : X → Matrix n m ℂ) (point : X)
    (coreGenerated : DifferentiableAt ℝ core point) (tensorGenerated : DifferentiableAt ℝ tensor point)
    (coefficientsGenerated : DifferentiableAt ℝ coefficients point) :
    DifferentiableAt ℝ (fun x => CPS1ReactiveFieldDynamics.Polynomial.occupiedEnergy
      (core x) (tensor x) (coefficients x)) point := by
  have c (p : n) (i : m) := (differentiableAt_pi.mp (differentiableAt_pi.mp coefficientsGenerated p) i)
  have h (p q : n) := (differentiableAt_pi.mp (differentiableAt_pi.mp coreGenerated p) q)
  have v (p q r s : n) := differentiableAt_pi.mp
    (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp tensorGenerated p) q) r) s
  have one : DifferentiableAt ℝ (fun x => ∑ i : m, ∑ p : n, ∑ q : n,
      star (coefficients x p i) * coefficients x q i * core x p q) point :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun i _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ =>
          ((c p i).star.mul (c q i)).mul (h p q))))
  have pair : DifferentiableAt ℝ (fun x => ∑ i : m, ∑ j : m, ∑ p : n, ∑ q : n, ∑ r : n, ∑ s : n,
      (star (coefficients x p i) * coefficients x q i * star (coefficients x r j) * coefficients x s j) *
        (tensor x p r q s - tensor x p r s q)) point :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun i _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ =>
          DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ =>
            DifferentiableAt.fun_sum (u := Finset.univ) (fun r _ =>
              DifferentiableAt.fun_sum (u := Finset.univ) (fun s _ =>
                ((((c p i).star.mul (c q i)).mul ((c r j).star)).mul (c s j)).mul
                  ((v p r q s).sub (v p r s q))))))))
  exact (Complex.reCLM.differentiableAt.comp point one).add
    ((Complex.reCLM.differentiableAt.comp point pair).const_smul (1/2 : ℝ))

/-- Joint differentiability is constructed from all moving source kernels and
the actual finite coefficient polynomial; the two partial laws are only used
after this fact to identify its restrictions. -/
theorem full_joint_energy_differentiable (germ : Germ root state) :
    DifferentiableAt ℝ germ.energy germ.current := by
  have position : DifferentiableAt ℝ (fun current : NuclearPhase germ => current.1)
      (germ.positions,germ.momenta) :=
    (ContinuousLinearMap.fst ℝ germ.Configuration germ.Configuration).differentiableAt
  have electronic := (field_energy_differentiable germ germ.positions).comp
    (germ.positions,germ.momenta) position
  have nuclei : DifferentiableAt ℝ
      (fun phase : NuclearPhase germ => germ.nuclearEnergy phase.1 phase.2)
      (germ.positions,germ.momenta) := by
    have generated := (full_nuclear_hasFDerivAt germ).differentiableAt.sub electronic
    change DifferentiableAt ℝ (fun phase : NuclearPhase germ =>
      fullNuclearEnergy germ phase-fieldEnergyAt germ phase.1) (germ.positions,germ.momenta) at generated
    simpa only [full_nuclear_energy_eq,add_sub_cancel_right] using generated
  have projection : DifferentiableAt ℝ (fun current : germ.FullConfiguration => current.1) germ.current :=
    (ContinuousLinearMap.fst ℝ (NuclearPhase germ) germ.Coefficients).differentiableAt
  have nuclear := nuclei.comp germ.current projection
  have core := (phase_core_differentiable germ).comp germ.current projection
  have tensor := (phase_tensor_differentiable germ).comp germ.current projection
  have coefficients : DifferentiableAt ℝ (fun current : germ.FullConfiguration => current.2) germ.current :=
    (ContinuousLinearMap.snd ℝ (NuclearPhase germ) germ.Coefficients).differentiableAt
  have polynomial := polynomial_joint_differentiableAt _ _ _ germ.current core tensor coefficients
  have generated : DifferentiableAt ℝ (fun current : germ.FullConfiguration =>
      germ.nuclearEnergy current.1.1 current.1.2 +
        CPS1ReactiveFieldDynamics.Polynomial.occupiedEnergy
          (phaseCore germ current.1) (phaseTensor germ current.1) current.2) germ.current :=
    nuclear.add polynomial
  have physical : (fun current : germ.FullConfiguration =>
      germ.nuclearEnergy current.1.1 current.1.2 +
        CPS1ReactiveFieldDynamics.Polynomial.occupiedEnergy
          (phaseCore germ current.1) (phaseTensor germ current.1) current.2) = germ.energy :=
    funext (fun current => (full_energy_joint_form germ current).symm)
  exact physical ▸ generated

def jointDifferential (germ : Germ root state) : germ.FullConfiguration →L[ℝ] ℝ :=
  fderiv ℝ germ.energy germ.current

theorem full_joint_energy_hasFDerivAt (germ : Germ root state) :
    HasFDerivAt germ.energy (jointDifferential germ) germ.current :=
  (full_joint_energy_differentiable germ).hasFDerivAt

theorem joint_differential_restrictions (germ : Germ root state)
    (direction : NuclearPhase germ) (coefficients : germ.Coefficients) :
    jointDifferential germ (direction,coefficients) =
      nuclearDifferential germ direction + occupiedDifferential germ coefficients := by
  have nuclearEmbedding : HasFDerivAt (fun phase : NuclearPhase germ => (phase,state.occupied))
      ((ContinuousLinearMap.id ℝ (NuclearPhase germ)).prod 0) (germ.positions,germ.momenta) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  have occupiedEmbedding : HasFDerivAt (fun current : germ.Coefficients =>
      ((germ.positions,germ.momenta),current))
      ((0 : germ.Coefficients →L[ℝ] NuclearPhase germ).prod
        (ContinuousLinearMap.id ℝ germ.Coefficients)) state.occupied :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have nuclear := ((full_joint_energy_hasFDerivAt germ).comp (germ.positions,germ.momenta) nuclearEmbedding).unique
    (full_nuclear_hasFDerivAt germ)
  have occupied := ((full_joint_energy_hasFDerivAt germ).comp state.occupied occupiedEmbedding).unique
    (full_occupied_hasFDerivAt germ)
  have first := congrArg (fun map : NuclearPhase germ →L[ℝ] ℝ => map direction) nuclear
  have second := congrArg (fun map : germ.Coefficients →L[ℝ] ℝ => map coefficients) occupied
  change jointDifferential germ (direction,0) = nuclearDifferential germ direction at first
  change jointDifferential germ (0,coefficients) = occupiedDifferential germ coefficients at second
  calc
    jointDifferential germ (direction,coefficients) =
        jointDifferential germ (direction,0) + jointDifferential germ (0,coefficients) := by
      simpa only [Prod.mk_add_mk,add_zero,zero_add] using
        (jointDifferential germ).map_add (direction,0) (0,coefficients)
    _ = _ := congrArg₂ (fun a b : ℝ => a+b) first second

theorem full_energy_metric_force (germ : Germ root state) (good : state.Good)
    (direction : germ.Configuration) :
    HasDerivAt (fun time : ℝ =>
      (normalize (germ.snapshotAt ((germ.positions+time • direction,germ.momenta),state.occupied))).energy)
      (nuclearWork germ direction) 0 := by
  have line : HasDerivAt (fun time : ℝ => germ.positions+time • direction) direction 0 := by
    simpa only [one_smul,id_eq,zero_add,Pi.add_apply] using!
      (hasDerivAt_const (0 : ℝ) germ.positions).add ((hasDerivAt_id (0 : ℝ)).smul_const direction)
  have normalParent : HasFDerivAt (normalizationAt germ) (fderiv ℝ (normalizationAt germ) germ.positions)
      (germ.positions+(0 : ℝ) • direction) := by
    simpa only [zero_smul,add_zero] using (normalization_at_differentiable germ good).hasFDerivAt
  have normal := normalParent.comp_hasDerivAt 0 line
  have coefficients : HasDerivAt (fun time : ℝ => state.occupied *
      normalizationAt germ (germ.positions+time • direction)) (occupiedMetricTangent germ direction) 0 := by
    apply hasDerivAt_pi.mpr
    intro primitive
    apply hasDerivAt_pi.mpr
    intro electron
    change HasDerivAt (fun time : ℝ => ∑ slot : state.ElectronIndex,
      state.occupied primitive slot * normalizationAt germ (germ.positions+time • direction) slot electron)
      (∑ slot : state.ElectronIndex, state.occupied primitive slot * normalizationRate germ direction slot electron) 0
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun slot _ =>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp normal slot) electron).const_mul (state.occupied primitive slot))
  have phase := line.prodMk (hasDerivAt_const (0 : ℝ) germ.momenta)
  have configuration := phase.prodMk coefficients
  have parent : HasFDerivAt germ.energy (jointDifferential germ)
      (((germ.positions+(0 : ℝ) • direction),germ.momenta),
        state.occupied * normalizationAt germ (germ.positions+(0 : ℝ) • direction)) := by
    simpa only [zero_smul,add_zero,normalization_at_current germ good,Matrix.mul_one,Germ.current] using
      full_joint_energy_hasFDerivAt germ
  have generated := parent.comp_hasDerivAt 0 configuration
  have recognized := generated.congr_deriv
    (joint_differential_restrictions germ (direction,0) (occupiedMetricTangent germ direction))
  have scalar : HasDerivAt (germ.energy ∘ (fun time : ℝ =>
      ((germ.positions+time • direction,germ.momenta),
        state.occupied * normalizationAt germ (germ.positions+time • direction))))
      (nuclearWork germ direction) 0 := by
    simpa only [nuclearWork] using! recognized
  apply scalar.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun time => by
    rfl

end
end CPS1ReactiveJointNuclear
