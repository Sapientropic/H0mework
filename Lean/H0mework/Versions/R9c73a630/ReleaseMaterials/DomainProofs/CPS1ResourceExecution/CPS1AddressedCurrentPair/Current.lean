import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedCurrentPair.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondRenewal.Contract
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Material

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

namespace CPS1AddressedCurrentPair
noncomputable section
open CPS1Deformation CPS1AddressedTransfer CPS1AddressedBondRenewal
open CPS1ElectronicSource (ElectronIndex SpinSpace electronCount)
open CPS1MolecularFrame (NuclearIndex)
open scoped BigOperators
variable {frame : CPS1Recycling.Frame}

/-- This reads the current reference's native raw gather. It neither accepts
address coverage nor predicts any future successful pulse. -/
def sourceRows? (geometry : CPS1ElectronicSource.Geometry frame) : Bool := by
  classical
  exact decide (CPS1AtomicDynamics.Body.gather
    (CPS1EnzymeBath.Joint.particles frame geometry.originJoint) geometry.originJoint.rows = .ok geometry.nodes)

theorem source_addresses_injective (reference : CPS1ElectronicSource.State frame)
    (generated : sourceRows? reference.geometry = true) :
    Function.Injective (CPS1MolecularFrame.address reference) := by
  classical
  have gathered : CPS1AtomicDynamics.Body.gather
      (CPS1EnzymeBath.Joint.particles frame reference.geometry.originJoint)
        reference.geometry.originJoint.rows = .ok reference.geometry.nodes := of_decide_eq_true generated
  have source := (CPS1AtomicDynamics.Body.gather_source _ _ _ gathered).1
  have mapped := congrArg (List.map CPS1AtomicDynamics.Charged.Particle.address) source
  have unique := CPS1EnzymeBath.Joint.particle_unique frame reference.geometry.originJoint
  rw [← mapped] at unique
  have nodeUnique : (reference.geometry.nodes.map
      (fun node => node.particle.address)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using unique
  have nuclearUnique : (reference.geometry.nuclei.map
      (fun node => node.particle.address)).Nodup :=
    nodeUnique.sublist (List.filter_sublist.map _)
  apply List.nodup_ofFn.mp
  have represented : List.ofFn (CPS1MolecularFrame.address reference) =
      reference.geometry.nuclei.map (fun node => node.particle.address) := by
    change List.ofFn ((fun node : CPS1AtomicDynamics.Body.Node => node.particle.address) ∘
      CPS1MolecularFrame.nucleus reference) = _
    rw [← List.map_ofFn,CPS1MolecularFrame.actual_nuclei_complete]
  rw [represented]
  exact nuclearUnique

theorem source_rows_from_joint (joint : CPS1EnzymeBath.Joint.State frame)
    (geometry : CPS1ElectronicSource.Geometry frame)
    (actual : CPS1ElectronicSource.Geometry.fromJoint? frame joint = .ok geometry) :
    sourceRows? geometry = true := by
  classical
  unfold CPS1ElectronicSource.Geometry.fromJoint? at actual
  cases gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame joint) joint.rows with
  | error failure => simp only [gathered] at actual; cases actual
  | ok nodes =>
    simp only [gathered] at actual
    split at actual
    · cases actual
    · split at actual
      · cases Except.ok.inj actual
        exact decide_eq_true gathered
      · cases actual

theorem source_rows_from_molecular_adopt (reference : CPS1ElectronicSource.State frame)
    (material : CPS1MolecularFrame.Material frame)
    (actual : CPS1MolecularFrame.adopt? reference = .ok material) :
    sourceRows? reference.geometry = true := by
  classical
  unfold CPS1MolecularFrame.adopt? at actual
  split at actual
  · cases actual
  · cases gathered : CPS1AtomicDynamics.Body.gather
      (CPS1EnzymeBath.Joint.particles frame reference.geometry.originJoint) reference.geometry.originJoint.rows with
    | error failure => simp only [gathered] at actual; cases actual
    | ok nodes =>
      simp only [gathered] at actual
      split at actual
      · cases actual
      · rename_i matched
        have same : nodes = reference.geometry.nodes := not_ne_iff.mp matched
        exact decide_eq_true (gathered.trans (congrArg Except.ok same))

def AddressDisposition (state : Material frame) (first partner : NuclearIndex state.reference) : Prop :=
  if sourceRows? state.reference.geometry then
    CPS1MolecularFrame.address state.reference partner ≠ CPS1MolecularFrame.address state.reference first
  else CPS1AtomicDynamics.Body.gather
    (CPS1EnzymeBath.Joint.particles frame state.reference.geometry.originJoint)
      state.reference.geometry.originJoint.rows ≠ .ok state.reference.geometry.nodes

theorem address_disposition (state : Material frame) (first partner : NuclearIndex state.reference)
    (different : partner ≠ first) : AddressDisposition state first partner := by
  classical
  unfold AddressDisposition
  split
  · rename_i generated
    exact fun equality => different (source_addresses_injective state.reference generated equality)
  · rename_i unrecognized
    intro actual
    exact unrecognized (decide_eq_true actual)

def partnerAt {current : Source.Occurrence frame} (admission : NativeSource.Admission current) (index : Nat) :
    NuclearIndex (trajectory (NativeSource.initial admission) index).material.reference :=
  (signed_partner_exists
    (trajectory (NativeSource.initial admission) index).material
    (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
    (NativeSource.timeAt (NativeSource.initial admission) index)
    (NativeSource.generated_time_positive admission index)
    (NativeSource.generated_step_signed admission index)).choose

structure StepProperties (state : Material frame) (first : NuclearIndex state.reference)
    (time : ℝ) (partner : NuclearIndex state.reference) : Prop where
  differentRow : partner ≠ first
  signed : 0 < responseFlux state first 0 * pairCurrent state first time first partner
  nonzero : pairCurrent state first time first partner ≠ 0
  antisymmetric : ∀ left right, pairCurrent state first time right left = -pairCurrent state first time left right
  diagonal : ∀ index, pairCurrent state first time index index = 0
  firstRow : (∑ right, pairCurrent state first time first right) = responseFlux state first time
  localChange : ∀ index, sectorPopulation state first time index true-sectorPopulation state first time index false =
    2*time*(∑ right, pairCurrent state first time index right)
  beforeNumber : (∑ index, sectorPopulation state first time index false) =
    electronCount frame state.reference.geometry.originJoint
  afterNumber : (∑ index, sectorPopulation state first time index true) =
    electronCount frame state.reference.geometry.originJoint
  totalConserved : (∑ left, ∑ right, pairCurrent state first time left right) = 0
  beforeWhole : ∀ slot : ElectronIndex state.reference.geometry,
    (∑ index, projection state.reference (state.movedPositions time) first index (seedFields state time slot)) =
      seedFields state time slot
  afterWhole : ∀ slot : ElectronIndex state.reference.geometry,
    (∑ index, projection state.reference (state.movedPositions time) first index (responseFields state time slot)) =
      responseFields state time slot
  firstProjection : projection state.reference (state.movedPositions time) first first =
    siteProjection state.reference (state.movedPositions time) first

theorem actual_step {current : Source.Occurrence frame} (admission : NativeSource.Admission current)
    (index : Nat) :
    let state := (trajectory (NativeSource.initial admission) index).material
    let first := (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
    let time := NativeSource.timeAt (NativeSource.initial admission) index
    StepProperties state first time (partnerAt admission index) := by
  dsimp only
  have selected : partnerAt admission index ≠
      (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear ∧
      0 < responseFlux (trajectory (NativeSource.initial admission) index).material
        (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear 0 *
        pairCurrent (trajectory (NativeSource.initial admission) index).material
          (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
          (NativeSource.timeAt (NativeSource.initial admission) index)
          (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear (partnerAt admission index) :=
    (signed_partner_exists _ _ _ (NativeSource.generated_time_positive admission index)
      (NativeSource.generated_step_signed admission index)).choose_spec
  have normalized := advance_normalized (trajectory (NativeSource.initial admission) index)
  refine ⟨selected.1,selected.2,?_,pair_antisymmetric _ _ _,pair_diagonal _ _ _,
    first_row_sum _ _ _,sector_population_change _ _ _,population_number _ _ _ false normalized,
    population_number _ _ _ true normalized,total_pair_conserved _ _ _,?_,?_,first_projection _ _ _⟩
  · intro zero
    rw [zero,mul_zero] at selected
    exact lt_irrefl _ selected.2
  · intro slot
    exact projections_reconstruct _ _ _ _ (occupied_in_full _ _ _ slot)
  · intro slot
    exact projections_reconstruct _ _ _ _ (occupied_in_full _ _ _ slot)

def currentPair? (current : Source.Occurrence frame) (index : Nat) :
    Option ((state : Material frame) × NuclearIndex state.reference × NuclearIndex state.reference) :=
  (CPS1AddressedBondResponse.NativeSource.autoBondResponse? current).map (fun admission =>
    ⟨(trajectory (NativeSource.initial admission) index).material,
      (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear,partnerAt admission index⟩)

def PairSeriesAt (current : Source.Occurrence frame) (depth : Nat) : Prop :=
  match CPS1AddressedBondResponse.NativeSource.autoBondResponse? current with
  | none => currentPair? current depth = none ∧ NativeSource.next current depth = Source.resume frame current [] []
  | some admission => SeriesProperties admission depth ∧
      NativeSource.next current depth = NativeSource.continued admission depth ∧
      ∀ index < depth,
        let state := (trajectory (NativeSource.initial admission) index).material
        let first := (trajectory (NativeSource.initial admission) index).site.phosphate.nuclear
        let time := NativeSource.timeAt (NativeSource.initial admission) index
        currentPair? current index = some ⟨state,first,partnerAt admission index⟩ ∧
        StepProperties state first time (partnerAt admission index) ∧
        AddressDisposition state first (partnerAt admission index) ∧
        (CPS1MolecularFrame.address state.reference first =
          (state.reference.geometry.nuclei.get first).particle.address) ∧
        (CPS1MolecularFrame.address state.reference (partnerAt admission index) =
          (state.reference.geometry.nuclei.get (partnerAt admission index)).particle.address)

theorem source_generated_pair_series (current : Source.Occurrence frame) (depth : Nat) :
    PairSeriesAt current depth := by
  cases generated : CPS1AddressedBondResponse.NativeSource.autoBondResponse? current with
  | none =>
    simp only [PairSeriesAt,generated,currentPair?,Option.map_none,true_and]
    simpa only [CPS1AddressedBondRenewal.CurrentResult,generated] using current_result current depth
  | some admission =>
    simp only [PairSeriesAt,generated]
    refine ⟨series_properties admission depth,?_,?_⟩
    · have paid := current_result current depth
      simp only [CPS1AddressedBondRenewal.CurrentResult,generated] at paid
      exact paid.1
    · intro index _
      refine ⟨?_,actual_step admission index,
        address_disposition _ _ _ (actual_step admission index).differentRow,rfl,rfl⟩
      simp only [currentPair?,generated,Option.map_some]

end
end CPS1AddressedCurrentPair
