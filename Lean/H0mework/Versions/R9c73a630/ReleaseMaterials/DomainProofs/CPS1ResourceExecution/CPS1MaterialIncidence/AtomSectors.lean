import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.SourceCAR
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ChargedAction
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open MeasureTheory
open scoped BigOperators InnerProductSpace Matrix

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

abbrev AtomSector (source : Common before step raw) := Fin source.atoms.length

theorem current_atoms_nonempty (current : NativeCurrent source) : 0 < source.atoms.length := by
  obtain ⟨node,held,_,_,_⟩ := common_electron_present source
  have particleHeld : node.particle ∈ current.nodes.map Body.Node.particle := by
    rw [current.atomsActual]
    exact List.mem_map_of_mem held
  obtain ⟨actual,actualHeld,_⟩ := List.mem_map.mp particleHeld
  exact lt_of_le_of_lt (Nat.zero_le actual.particle.address.slot)
    (current_atom_slot_lt source current actual actualHeld)

theorem current_nucleus_generated (current : NativeCurrent source) (index : AtomSector source) :
    ∃ node ∈ current.nodes, node.particle.address = .nucleus index.val := by
  let atom := source.atoms.get index
  let particle : Charged.Particle :=
    ⟨.nucleus index.val,atom.descriptor,(Charged.atomicNumber atom.descriptor.source.element : ℤ)⟩
  have rowHeld : (atom,index.val) ∈ source.atoms.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [atom])
  have table : commonParticles before.packet.source raw.fuel =
      source.atoms.zipIdx.flatMap (fun entry => Charged.atomParticles (entry.1.descriptor,entry.2)) := by
    rw [source.atomSource]
    rfl
  have particleHeld : particle ∈ commonParticles before.packet.source raw.fuel := by
    rw [table]
    exact List.mem_flatMap.mpr ⟨(atom,index.val),rowHeld,by simp [Charged.atomParticles,particle]⟩
  rw [← current_particles_source source current] at particleHeld
  obtain ⟨node,nodeHeld,actual⟩ := List.mem_map.mp particleHeld
  exact ⟨node,nodeHeld,congrArg Charged.Particle.address actual⟩

def sectorNucleus (current : NativeCurrent source) (index : AtomSector source) : Body.Node :=
  Classical.choose (current_nucleus_generated current index)

theorem sector_nucleus_held (current : NativeCurrent source) (index : AtomSector source) :
    sectorNucleus current index ∈ current.nodes :=
  (Classical.choose_spec (current_nucleus_generated current index)).1

theorem sector_nucleus_address (current : NativeCurrent source) (index : AtomSector source) :
    (sectorNucleus current index).particle.address = .nucleus index.val :=
  (Classical.choose_spec (current_nucleus_generated current index)).2

theorem current_addresses_unique (current : NativeCurrent source) :
    (current.nodes.map (fun node => node.particle.address)).Nodup := by
  have actual := congrArg (List.map Charged.Particle.address) (current_particles_source source current)
  simp only [List.map_map,Function.comp_def] at actual
  rw [actual]
  exact common_addresses_unique _ _

theorem sector_nucleus_exact (current : NativeCurrent source) (index : AtomSector source)
    (node : Body.Node) (held : node ∈ current.nodes) (address : node.particle.address = .nucleus index.val) :
    sectorNucleus current index = node := by
  exact List.inj_on_of_nodup_map (current_addresses_unique current)
    (sector_nucleus_held current index) held ((sector_nucleus_address current index).trans address.symm)

def sectorOrigin (_current : NativeCurrent source) (index : AtomSector source) : AtomOrigin cursor :=
  originAt source index

theorem sector_origin_actual (current : NativeCurrent source) (index : AtomSector source) :
    originAt? source.atoms (sectorNucleus current index).particle.address = some (sectorOrigin current index) := by
  rw [sector_nucleus_address]
  change (source.atoms[index.val]?).map Atom.origin = some (source.atoms.get index).origin
  have found : source.atoms[index.val]? = some (source.atoms.get index) := by simp
  rw [found]
  rfl

def sectorPoint (current : NativeCurrent source) (index : AtomSector source) : Point :=
  fun axis => (sectorNucleus current index).row.position axis

private theorem ready_distinct_positions (nodes : List Body.Node) (ready : Body.ready nodes)
    (first second : Body.Node) (firstHeld : first ∈ nodes) (secondHeld : second ∈ nodes)
    (different : first ≠ second) : first.row.position ≠ second.row.position := by
  induction nodes with
  | nil => simp at firstHeld
  | cons head rest ih =>
    obtain ⟨headReady,restReady⟩ := List.pairwise_cons.mp ready
    rcases List.mem_cons.mp firstHeld with firstIsHead | firstInRest
    · subst first
      rcases List.mem_cons.mp secondHeld with secondIsHead | secondInRest
      · subst second
        exact False.elim (different rfl)
      · exact headReady _ secondInRest
    · rcases List.mem_cons.mp secondHeld with secondIsHead | secondInRest
      · subst second
        exact (headReady _ firstInRest).symm
      · exact ih restReady firstInRest secondInRest

theorem sector_points_injective (current : NativeCurrent source) : Function.Injective (sectorPoint current) := by
  intro first second same
  by_contra different
  have nodesDifferent : sectorNucleus current first ≠ sectorNucleus current second := by
    intro equal
    have addresses := congrArg (fun node : Body.Node => node.particle.address) equal
    rw [sector_nucleus_address,sector_nucleus_address] at addresses
    exact different (Fin.ext (Charged.Address.nucleus.inj addresses))
  have positionsSame : (sectorNucleus current first).row.position = (sectorNucleus current second).row.position := by
    apply PiLp.ext
    intro axis
    exact congrFun same axis
  exact ready_distinct_positions current.nodes current.ready _ _
    (sector_nucleus_held current first) (sector_nucleus_held current second) nodesDifferent positionsSame

def sectorDistance (current : NativeCurrent source) (index : AtomSector source) (point : Point) : ℝ :=
  ‖(WithLp.toLp 2 (point-sectorPoint current index) : Body.Point)‖

-- The source's ordered nuclei resolve equality of distances.
def sectorCell (current : NativeCurrent source) (index : AtomSector source) : Set Point :=
  {point | ∀ other : AtomSector source,
    if other < index then sectorDistance current index point < sectorDistance current other point
    else sectorDistance current index point ≤ sectorDistance current other point}

theorem sector_cell_measurable (current : NativeCurrent source) (index : AtomSector source) :
    MeasurableSet (sectorCell current index) := by
  classical
  rw [sectorCell,← Set.iInter_ofPred]
  have continuousDistance (atom : AtomSector source) : Continuous (sectorDistance current atom) :=
    ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp (continuous_id.sub continuous_const)).norm
  apply MeasurableSet.iInter
  intro other
  by_cases earlier : other < index
  · simp only [if_pos earlier]
    exact measurableSet_lt (continuousDistance index).measurable (continuousDistance other).measurable
  · simp only [if_neg earlier]
    exact measurableSet_le (continuousDistance index).measurable (continuousDistance other).measurable

theorem sector_cell_complete (current : NativeCurrent source) (point : Point) :
    ∃ index : AtomSector source, point ∈ sectorCell current index := by
  classical
  have : Nonempty (AtomSector source) := ⟨⟨0,current_atoms_nonempty current⟩⟩
  obtain ⟨nearest,_,minimal⟩ := Finset.exists_min_image Finset.univ
    (fun index : AtomSector source => sectorDistance current index point) Finset.univ_nonempty
  let tied := Finset.univ.filter (fun index : AtomSector source =>
    sectorDistance current index point = sectorDistance current nearest point)
  have tiedNonempty : tied.Nonempty := ⟨nearest,by simp [tied]⟩
  let first := tied.min' tiedNonempty
  have firstHeld : first ∈ tied := Finset.min'_mem tied tiedNonempty
  have firstDistance : sectorDistance current first point = sectorDistance current nearest point :=
    (Finset.mem_filter.mp firstHeld).2
  refine ⟨first,?_⟩
  intro other
  have weak : sectorDistance current first point ≤ sectorDistance current other point := by
    rw [firstDistance]
    exact minimal other (Finset.mem_univ _)
  by_cases earlier : other < first
  · simp only [if_pos earlier]
    rcases lt_or_eq_of_le weak with strict | equal
    · exact strict
    · have otherHeld : other ∈ tied :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,equal.symm.trans firstDistance⟩
      exact False.elim ((not_le_of_gt earlier) (Finset.min'_le tied other otherHeld))
  · simpa only [if_neg earlier] using weak

theorem sector_cell_unique (current : NativeCurrent source) (point : Point)
    (first second : AtomSector source) (firstHeld : point ∈ sectorCell current first)
    (secondHeld : point ∈ sectorCell current second) : first = second := by
  by_contra different
  rcases lt_or_gt_of_ne different with earlier | later
  · have strict := secondHeld first
    have weak := firstHeld second
    rw [if_pos earlier] at strict
    rw [if_neg (not_lt_of_ge earlier.le)] at weak
    exact (not_lt_of_ge weak) strict
  · have strict := firstHeld second
    have weak := secondHeld first
    rw [if_pos later] at strict
    rw [if_neg (not_lt_of_ge later.le)] at weak
    exact (not_lt_of_ge weak) strict

theorem sector_point_in_cell (current : NativeCurrent source) (index : AtomSector source) :
    sectorPoint current index ∈ sectorCell current index := by
  intro other
  by_cases earlier : other < index
  · have pointsDifferent : sectorPoint current index ≠ sectorPoint current other :=
      (sector_points_injective current).ne (Ne.symm earlier.ne)
    simp only [if_pos earlier,sectorDistance,sub_self,WithLp.toLp_zero,norm_zero]
    exact norm_pos_iff.mpr (fun zero => pointsDifferent
      (sub_eq_zero.mp ((WithLp.toLp_eq_zero 2).mp zero)))
  · simp only [if_neg earlier,sectorDistance,sub_self,WithLp.toLp_zero,norm_zero]
    exact norm_nonneg _

private def spatialCut (set : Set Point) (measurable : MeasurableSet set) (field : SpatialLp) : SpatialLp :=
  (MemLp.indicator measurable (Lp.memLp field)).toLp (set.indicator field)

private theorem spatial_cut_value (set : Set Point) (measurable : MeasurableSet set) (field : SpatialLp) :
    ∀ᵐ point ∂volume, spatialCut set measurable field point = set.indicator field point :=
  (MemLp.indicator measurable (Lp.memLp field)).coeFn_toLp

private theorem spatial_cut_add (set : Set Point) (measurable : MeasurableSet set) (first second : SpatialLp) :
    spatialCut set measurable (first+second) = spatialCut set measurable first+spatialCut set measurable second := by
  apply Lp.ext
  filter_upwards [spatial_cut_value set measurable (first+second),spatial_cut_value set measurable first,
    spatial_cut_value set measurable second,Lp.coeFn_add first second,
    Lp.coeFn_add (spatialCut set measurable first) (spatialCut set measurable second)] with point sumValue left right sumSource sumTarget
  rw [sumTarget,sumValue]
  simp only [Pi.add_apply]
  rw [left,right]
  by_cases held : point ∈ set
  · simpa only [Set.indicator_of_mem held,Pi.add_apply] using sumSource
  · simp only [Set.indicator_of_notMem held,add_zero]

private theorem spatial_cut_smul (set : Set Point) (measurable : MeasurableSet set) (scalar : ℂ) (field : SpatialLp) :
    spatialCut set measurable (scalar • field) = scalar • spatialCut set measurable field := by
  apply Lp.ext
  filter_upwards [spatial_cut_value set measurable (scalar • field),spatial_cut_value set measurable field,
    Lp.coeFn_smul scalar field,Lp.coeFn_smul scalar (spatialCut set measurable field)] with point scaled value sourceValue targetValue
  rw [scaled,targetValue]
  simp only [Pi.smul_apply]
  rw [value]
  by_cases held : point ∈ set
  · simpa only [Set.indicator_of_mem held,Pi.smul_apply] using sourceValue
  · simp only [Set.indicator_of_notMem held,smul_zero]

def atomCut (current : NativeCurrent source) (index : AtomSector source) : SpinSpace →ₗ[ℂ] SpinSpace where
  toFun field := WithLp.toLp 2 (fun spin => spatialCut (sectorCell current index) (sector_cell_measurable current index) (field spin))
  map_add' first second := by
    apply PiLp.ext
    intro spin
    change spatialCut (sectorCell current index) (sector_cell_measurable current index) (first spin+second spin) =
      spatialCut (sectorCell current index) (sector_cell_measurable current index) (first spin)+
        spatialCut (sectorCell current index) (sector_cell_measurable current index) (second spin)
    exact spatial_cut_add _ _ _ _
  map_smul' scalar field := by
    apply PiLp.ext
    intro spin
    change spatialCut (sectorCell current index) (sector_cell_measurable current index) (scalar • field spin) =
      scalar • spatialCut (sectorCell current index) (sector_cell_measurable current index) (field spin)
    exact spatial_cut_smul _ _ _ _

theorem atom_cut_value (current : NativeCurrent source) (index : AtomSector source) (field : SpinSpace) (spin : Bool) :
    ∀ᵐ point ∂volume, atomCut current index field spin point = (sectorCell current index).indicator (field spin) point :=
  spatial_cut_value (sectorCell current index) (sector_cell_measurable current index) (field spin)

theorem atom_cut_complete (current : NativeCurrent source) (field : SpinSpace) :
    ∑ index : AtomSector source, atomCut current index field = field := by
  classical
  apply PiLp.ext
  intro spin
  have sumSpin : (∑ index : AtomSector source, atomCut current index field) spin =
      ∑ index : AtomSector source, atomCut current index field spin :=
    map_sum (PiLp.projₗ (𝕜 := ℂ) (p := 2) (β := fun _ : Bool => SpatialLp) spin) _ _
  rw [sumSpin]
  have allValues := Filter.eventually_all.mpr (fun index : AtomSector source => atom_cut_value current index field spin)
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun index => atomCut current index field spin),allValues] with point sumValue each
  change (∑ index : AtomSector source, atomCut current index field spin) point = field spin point
  rw [sumValue]
  obtain ⟨selected,selectedHeld⟩ := sector_cell_complete current point
  rw [Finset.sum_eq_single selected]
  · rw [each selected]
    exact Set.indicator_of_mem selectedHeld _
  · intro other _ different
    rw [each other]
    exact Set.indicator_of_notMem (fun held => different (sector_cell_unique current point other selected held selectedHeld)) _
  · exact fun missing => False.elim (missing (Finset.mem_univ _))

theorem atom_cut_projection (current : NativeCurrent source) (first second : AtomSector source) (field : SpinSpace) :
    atomCut current first (atomCut current second field) = if first = second then atomCut current first field else 0 := by
  classical
  apply PiLp.ext
  intro spin
  apply Lp.ext
  filter_upwards [atom_cut_value current first (atomCut current second field) spin,
    atom_cut_value current second field spin,atom_cut_value current first field spin,
    Lp.coeFn_zero ℂ 2 (volume : Measure Point)] with point outer inner firstValue zeroValue
  by_cases same : first = second
  · subst second
    simp only [ite_true,outer]
    by_cases held : point ∈ sectorCell current first
    · simp only [Set.indicator_of_mem held,inner]
    · simp only [Set.indicator_of_notMem held,inner]
  · simp only [if_neg same,PiLp.zero_apply,zeroValue,Pi.zero_apply,outer]
    by_cases firstHeld : point ∈ sectorCell current first
    · rw [Set.indicator_of_mem firstHeld,inner]
      exact Set.indicator_of_notMem
        (fun secondHeld => same (sector_cell_unique current point first second firstHeld secondHeld)) _
    · exact Set.indicator_of_notMem firstHeld _

theorem atom_cut_inner (current : NativeCurrent source) (first second : AtomSector source) (different : first ≠ second)
    (left right : SpinSpace) : inner ℂ (atomCut current first left) (atomCut current second right) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro spin _
  rw [MeasureTheory.L2.inner_def]
  have zero : (fun point : Point =>
      inner ℂ (atomCut current first left spin point) (atomCut current second right spin point)) =ᵐ[volume] 0 := by
    filter_upwards [atom_cut_value current first left spin,atom_cut_value current second right spin] with point leftValue rightValue
    rw [leftValue,rightValue]
    by_cases firstHeld : point ∈ sectorCell current first
    · have secondMissing : point ∉ sectorCell current second :=
        fun secondHeld => different (sector_cell_unique current point first second firstHeld secondHeld)
      rw [Set.indicator_of_notMem secondMissing]
      exact inner_zero_right _
    · rw [Set.indicator_of_notMem firstHeld]
      exact inner_zero_left _
  rw [integral_congr_ae zero]
  change (∫ _ : Point, (0 : ℂ)) = 0
  exact integral_zero Point ℂ

abbrev AtomBasisIndex (current : NativeCurrent source) (index : AtomSector source) :=
  CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (fun rawIndex : RawIndex current => atomCut current index (rawField current rawIndex))

def atomBasis (current : NativeCurrent source) (index : AtomSector source) (mode : AtomBasisIndex current index) : SpinSpace :=
  CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (fun rawIndex : RawIndex current => atomCut current index (rawField current rawIndex)) mode

theorem atom_basis_orthonormal (current : NativeCurrent source) (index : AtomSector source) :
    Orthonormal ℂ (atomBasis current index) :=
  CPS1MolecularFrame.FiniteNormed.field_orthonormal _

theorem atom_basis_synthesis (current : NativeCurrent source) (index : AtomSector source) (mode : AtomBasisIndex current index) :
    atomBasis current index mode =
      ∑ rawIndex, CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
        (fun rawIndex : RawIndex current => atomCut current index (rawField current rawIndex)) rawIndex mode •
          atomCut current index (rawField current rawIndex) :=
  CPS1MolecularFrame.FiniteNormed.field_synthesis _ _

theorem atom_basis_supported (current : NativeCurrent source) (index : AtomSector source) (mode : AtomBasisIndex current index) :
    atomCut current index (atomBasis current index mode) = atomBasis current index mode := by
  classical
  rw [atom_basis_synthesis,map_sum]
  simp only [map_smul,atom_cut_projection,ite_true]

theorem atom_bases_cross_inner (current : NativeCurrent source) (first second : AtomSector source) (different : first ≠ second)
    (left : AtomBasisIndex current first) (right : AtomBasisIndex current second) :
    inner ℂ (atomBasis current first left) (atomBasis current second right) = 0 := by
  rw [← atom_basis_supported current first left,← atom_basis_supported current second right]
  exact atom_cut_inner current first second different _ _

abbrev AddressedBasisIndex (current : NativeCurrent source) :=
  (index : AtomSector source) × AtomBasisIndex current index

def addressedBasis (current : NativeCurrent source) (mode : AddressedBasisIndex current) : SpinSpace :=
  atomBasis current mode.1 mode.2

theorem addressed_basis_orthonormal (current : NativeCurrent source) : Orthonormal ℂ (addressedBasis current) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro first second
  rcases first with ⟨first,left⟩
  rcases second with ⟨second,right⟩
  by_cases same : first = second
  · subst second
    change inner ℂ (atomBasis current first left) (atomBasis current first right) = _
    simpa using (orthonormal_iff_ite.mp (atom_basis_orthonormal current first)) left right
  · have modesDifferent : (Sigma.mk first left : AddressedBasisIndex current) ≠ Sigma.mk second right :=
      fun equal => same (congrArg Sigma.fst equal)
    rw [if_neg modesDifferent]
    exact atom_bases_cross_inner current first second same left right

def atomCoordinates (current : NativeCurrent source) : Matrix (AddressedBasisIndex current) (RawIndex current) ℂ :=
  fun mode rawIndex => CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ)
    (fun rawIndex : RawIndex current => atomCut current mode.1 (rawField current rawIndex)) mode.2 rawIndex

theorem atom_raw_synthesis (current : NativeCurrent source) (rawIndex : RawIndex current) :
    rawField current rawIndex =
      ∑ mode : AddressedBasisIndex current, atomCoordinates current mode rawIndex • addressedBasis current mode := by
  classical
  rw [← atom_cut_complete current (rawField current rawIndex),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro index _
  exact CPS1MolecularFrame.FiniteNormed.raw_synthesis
    (fun rawIndex : RawIndex current => atomCut current index (rawField current rawIndex)) rawIndex

def atomOccupation (current : NativeCurrent source) := atomCoordinates current * rawOccupation current

theorem atom_occupation_wave (current : NativeCurrent source) :
    CPS1ElectronicEvolution.fields (addressedBasis current) (atomOccupation current) = currentField current := by
  funext slot
  rw [atomOccupation,CPS1Deformation.fields_mul]
  have complete : CPS1ElectronicEvolution.fields (addressedBasis current) (atomCoordinates current) = rawField current := by
    funext rawIndex
    exact (atom_raw_synthesis current rawIndex).symm
  rw [complete,raw_current_fields]

theorem atom_occupation_gram (current : NativeCurrent source) :
    (atomOccupation current).conjTranspose * atomOccupation current = 1 := by
  ext first second
  rw [← CPS1ElectronicEvolution.field_gram (addressedBasis current) (addressed_basis_orthonormal current),
    atom_occupation_wave]
  exact orthonormal_iff_ite.mp (current_fields_orthonormal current) first second

theorem atom_electron_number (current : NativeCurrent source) :
    Matrix.trace (atomOccupation current * (atomOccupation current).conjTranspose) = (electronCount source.nodes : ℂ) := by
  rw [Matrix.trace_mul_comm,atom_occupation_gram]
  simp only [Matrix.trace_one,Fintype.card_fin,Electron]

def atomFieldProjection (current : NativeCurrent source) (index : AtomSector source) : SpinSpace →ₗ[ℂ] SpinSpace :=
  ∑ mode : AtomBasisIndex current index,
    (innerSL ℂ (atomBasis current index mode)).toLinearMap.smulRight (atomBasis current index mode)

theorem atom_projection_raw (current : NativeCurrent source) (observed index : AtomSector source) (rawIndex : RawIndex current) :
    atomFieldProjection current observed (atomCut current index (rawField current rawIndex)) =
      if observed = index then atomCut current index (rawField current rawIndex) else 0 := by
  classical
  simp only [atomFieldProjection,LinearMap.sum_apply,LinearMap.smulRight_apply]
  change (∑ mode : AtomBasisIndex current observed,
    inner ℂ (atomBasis current observed mode) (atomCut current index (rawField current rawIndex)) •
      atomBasis current observed mode) = _
  by_cases same : observed = index
  · subst index
    rw [if_pos rfl]
    exact (CPS1MolecularFrame.FiniteNormed.raw_synthesis
      (fun rawIndex : RawIndex current => atomCut current observed (rawField current rawIndex)) rawIndex).symm
  · rw [if_neg same]
    apply Finset.sum_eq_zero
    intro mode _
    rw [← atom_basis_supported current observed mode,atom_cut_inner current observed index same]
    exact zero_smul _ _

def atomNumber (current : NativeCurrent source) (index : AtomSector source) : Module.End ℂ SourceFermion :=
  ∑ mode : AtomBasisIndex current index, physicalPair (atomBasis current index mode) (atomBasis current index mode)

theorem atom_number_creation (current : NativeCurrent source) (index : AtomSector source)
    (field : SpinSpace) (state : SourceFermion) :
    atomNumber current index (physicalCreation field state)-
      physicalCreation field (atomNumber current index state) =
        physicalCreation (atomFieldProjection current index field) state := by
  change (∑ mode : AtomBasisIndex current index,
      physicalPair (atomBasis current index mode) (atomBasis current index mode)) (ExteriorAlgebra.ι ℂ field * state)-
    ExteriorAlgebra.ι ℂ field *
      (∑ mode : AtomBasisIndex current index, physicalPair (atomBasis current index mode) (atomBasis current index mode)) state = _
  simp only [LinearMap.sum_apply,physical_pair_first,Finset.sum_add_distrib,Finset.mul_sum,add_sub_cancel_right]
  simp only [physical_creation_apply,atomFieldProjection,LinearMap.sum_apply,LinearMap.smulRight_apply]
  change (∑ mode : AtomBasisIndex current index, inner ℂ (atomBasis current index mode) field •
    (ExteriorAlgebra.ι ℂ (atomBasis current index mode) * state)) =
      ExteriorAlgebra.ι ℂ (∑ mode : AtomBasisIndex current index,
        inner ℂ (atomBasis current index mode) field • atomBasis current index mode) * state
  rw [map_sum]
  simp only [map_smul,Finset.sum_mul,smul_mul_assoc]

theorem atom_number_annihilation (current : NativeCurrent source) (index : AtomSector source)
    (field : SpinSpace) (state : SourceFermion) :
    atomNumber current index (physicalAnnihilation field state)-
      physicalAnnihilation field (atomNumber current index state) =
        -physicalAnnihilation (atomFieldProjection current index field) state := by
  have represented : physicalAnnihilation (atomFieldProjection current index field) =
      ∑ mode : AtomBasisIndex current index,
        inner ℂ field (atomBasis current index mode) • physicalAnnihilation (atomBasis current index mode) := by
    unfold atomFieldProjection
    simp only [LinearMap.sum_apply,LinearMap.smulRight_apply]
    change physicalAnnihilation (∑ mode : AtomBasisIndex current index,
      inner ℂ (atomBasis current index mode) field • atomBasis current index mode) = _
    rw [physical_annihilation_sum]
    simp only [physical_annihilation_smul,← starRingEnd_apply,inner_conj_symm]
  simp only [atomNumber,LinearMap.sum_apply,map_sum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [physical_pair_annihilation]
  rw [represented]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,neg_smul,Finset.sum_neg_distrib]

theorem atom_cut_creation_integer (current : NativeCurrent source) (observed creating : AtomSector source)
    (rawIndex : RawIndex current) (state : SourceFermion) :
    atomNumber current observed (physicalCreation (atomCut current creating (rawField current rawIndex)) state)-
      physicalCreation (atomCut current creating (rawField current rawIndex)) (atomNumber current observed state) =
        (if observed = creating then (1 : ℂ) else 0) •
          physicalCreation (atomCut current creating (rawField current rawIndex)) state := by
  classical
  rw [atom_number_creation,atom_projection_raw]
  by_cases same : observed = creating
  · rw [if_pos same,if_pos same,one_smul]
  · rw [if_neg same,if_neg same,physical_creation_zero,LinearMap.zero_apply,zero_smul]

theorem atom_cut_annihilation_integer (current : NativeCurrent source) (observed removing : AtomSector source)
    (rawIndex : RawIndex current) (state : SourceFermion) :
    atomNumber current observed (physicalAnnihilation (atomCut current removing (rawField current rawIndex)) state)-
      physicalAnnihilation (atomCut current removing (rawField current rawIndex)) (atomNumber current observed state) =
        (-(if observed = removing then (1 : ℂ) else 0)) •
          physicalAnnihilation (atomCut current removing (rawField current rawIndex)) state := by
  classical
  rw [atom_number_annihilation,atom_projection_raw]
  by_cases same : observed = removing
  · rw [if_pos same,if_pos same,neg_one_smul]
  · simp only [if_neg same,physical_annihilation_zero,LinearMap.zero_apply,neg_zero,zero_smul]

def atomDelta (_current : NativeCurrent source) (observed creating removing : AtomSector source) : ℤ :=
  (if observed = creating then 1 else 0)-(if observed = removing then 1 else 0)

theorem atom_delta_total (current : NativeCurrent source) (creating removing : AtomSector source) :
    ∑ observed, atomDelta current observed creating removing = 0 := by
  classical
  simp [atomDelta,Finset.sum_sub_distrib]

theorem atom_pair_integer (current : NativeCurrent source) (observed creating removing : AtomSector source)
    (creatingRaw removingRaw : RawIndex current) (state : SourceFermion) :
    atomNumber current observed
        (physicalPair (atomCut current creating (rawField current creatingRaw))
          (atomCut current removing (rawField current removingRaw)) state)-
      physicalPair (atomCut current creating (rawField current creatingRaw))
        (atomCut current removing (rawField current removingRaw)) (atomNumber current observed state) =
        (atomDelta current observed creating removing : ℂ) •
          physicalPair (atomCut current creating (rawField current creatingRaw))
            (atomCut current removing (rawField current removingRaw)) state := by
  classical
  have creation := (sub_eq_iff_eq_add).mp
    (atom_cut_creation_integer current observed creating creatingRaw
      (physicalAnnihilation (atomCut current removing (rawField current removingRaw)) state))
  have removal := (sub_eq_iff_eq_add).mp (atom_cut_annihilation_integer current observed removing removingRaw state)
  change atomNumber current observed
      (physicalCreation (atomCut current creating (rawField current creatingRaw))
        (physicalAnnihilation (atomCut current removing (rawField current removingRaw)) state))-
      physicalCreation (atomCut current creating (rawField current creatingRaw))
        (physicalAnnihilation (atomCut current removing (rawField current removingRaw)) (atomNumber current observed state)) = _
  rw [creation,removal,map_add,map_smul]
  simp only [atomDelta,Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero,sub_smul,neg_smul]
  change _ = (if observed = creating then (1 : ℂ) else 0) •
      physicalCreation (atomCut current creating (rawField current creatingRaw))
        (physicalAnnihilation (atomCut current removing (rawField current removingRaw)) state)-
    (if observed = removing then (1 : ℂ) else 0) •
      physicalCreation (atomCut current creating (rawField current creatingRaw))
        (physicalAnnihilation (atomCut current removing (rawField current removingRaw)) state)
  abel

theorem physical_pair_split_atoms (current : NativeCurrent source) (creating removing : SpinSpace) :
    physicalPair creating removing =
      ∑ pair : AtomSector source × AtomSector source,
        physicalPair (atomCut current pair.1 creating) (atomCut current pair.2 removing) := by
  classical
  calc
    physicalPair creating removing =
        physicalPair (∑ atom : AtomSector source, atomCut current atom creating)
          (∑ atom : AtomSector source, atomCut current atom removing) :=
      congrArg₂ physicalPair (atom_cut_complete current creating).symm (atom_cut_complete current removing).symm
    _ = _ := by
      unfold physicalPair
      rw [physical_creation_sum,physical_annihilation_sum]
      apply LinearMap.ext
      intro state
      simp only [LinearMap.comp_apply,LinearMap.sum_apply,map_sum]
      rw [Fintype.sum_prod_type,Finset.sum_comm]

def atomFockCAR (current : NativeCurrent source) : Module.End ℂ SourceFermion :=
  ∑ rawPair : RawIndex current × RawIndex current,
    ∑ atomPair : AtomSector source × AtomSector source,
      effectiveSourceFock current rawPair.1 rawPair.2 •
        physicalPair (atomCut current atomPair.1 (rawField current rawPair.1))
          (atomCut current atomPair.2 (rawField current rawPair.2))

theorem atom_fock_car_exact (current : NativeCurrent source) : atomFockCAR current = sourceFockCAR current := by
  unfold atomFockCAR sourceFockCAR
  apply Finset.sum_congr rfl
  intro rawPair _
  rw [physical_pair_split_atoms current,Finset.smul_sum]

theorem actual_atom_number_source_action (current : NativeCurrent source) (observed : AtomSector source)
    (state : SourceFermion) :
    atomNumber current observed (sourceFockCAR current state)-
      sourceFockCAR current (atomNumber current observed state) =
        ∑ rawPair : RawIndex current × RawIndex current, ∑ atomPair : AtomSector source × AtomSector source,
          (effectiveSourceFock current rawPair.1 rawPair.2 * (atomDelta current observed atomPair.1 atomPair.2 : ℂ)) •
            physicalPair (atomCut current atomPair.1 (rawField current rawPair.1))
              (atomCut current atomPair.2 (rawField current rawPair.2)) state := by
  rw [← atom_fock_car_exact]
  simp only [atomFockCAR,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rawPair _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro atomPair _
  rw [← smul_sub,atom_pair_integer,smul_smul]

theorem actual_atom_fock_slater (current : NativeCurrent source) :
    atomFockCAR current (actualSourceSlater current) =
      ∑ slot : Electron source.nodes, ExteriorAlgebra.ιMulti ℂ (electronCount source.nodes)
        (Function.update (currentField current) slot (physicalFock current (currentField current slot))) := by
  rw [atom_fock_car_exact]
  exact actual_source_fock_action current

def atomUpdatedOccupation (current : NativeCurrent source) (time : ℝ) := atomCoordinates current * updatedRaw current time

theorem atom_updated_wave (current : NativeCurrent source) (time : ℝ) :
    CPS1ElectronicEvolution.fields (addressedBasis current) (atomUpdatedOccupation current time) =
      CPS1ElectronicEvolution.fields (rawField current) (updatedRaw current time) := by
  funext slot
  rw [atomUpdatedOccupation,CPS1Deformation.fields_mul]
  have complete : CPS1ElectronicEvolution.fields (addressedBasis current) (atomCoordinates current) = rawField current := by
    funext rawIndex
    exact (atom_raw_synthesis current rawIndex).symm
  rw [complete]

theorem atom_updated_gram (current : NativeCurrent source) (time : ℝ) :
    (atomUpdatedOccupation current time).conjTranspose * atomUpdatedOccupation current time = 1 := by
  ext first second
  rw [← CPS1ElectronicEvolution.field_gram (addressedBasis current) (addressed_basis_orthonormal current),
    atom_updated_wave,updated_raw_increment,raw_increment_fields]
  rw [CPS1ElectronicEvolution.field_gram (basis current) (basis_orthonormal current)]
  exact congrArg (fun occupied => occupied first second) (updated_gram current time)

theorem atom_updated_zero (current : NativeCurrent source) : atomUpdatedOccupation current 0 = atomOccupation current := by
  rw [atomUpdatedOccupation,updated_raw_zero]
  rfl

theorem atom_actual_cayley (current : NativeCurrent source) (time : ℝ) (slot : Electron source.nodes) :
    let after := CPS1ElectronicEvolution.fields (addressedBasis current) (atomUpdatedOccupation current time) slot
    after+(Complex.I*((time/2 : ℝ) : ℂ)) • physicalFock current after =
      currentField current slot-(Complex.I*((time/2 : ℝ) : ℂ)) • physicalFock current (currentField current slot) := by
  dsimp only
  rw [atom_updated_wave]
  exact actual_field_midpoint current time slot

structure AtomCARMonomial (current : NativeCurrent source) where
  creating : AtomSector source
  removing : AtomSector source
  creatingRaw : RawIndex current
  removingRaw : RawIndex current
  coefficient : ℂ

def AtomCARMonomial.operator {current : NativeCurrent source} (term : AtomCARMonomial current) : Module.End ℂ SourceFermion :=
  term.coefficient • physicalPair (atomCut current term.creating (rawField current term.creatingRaw))
    (atomCut current term.removing (rawField current term.removingRaw))

def AtomCARMonomial.instruction? {current : NativeCurrent source} (term : AtomCARMonomial current) : Option (ChargedInstruction cursor) :=
  if term.creating = term.removing then none
  else some (.electron (sectorOrigin current term.removing) (sectorOrigin current term.creating))

def AtomCARMonomial.chargeDelta {current : NativeCurrent source} (term : AtomCARMonomial current) : Charges cursor :=
  Finsupp.single (sectorOrigin current term.removing) 1-Finsupp.single (sectorOrigin current term.creating) 1

def sourceAtomCARWord (current : NativeCurrent source) : List (AtomCARMonomial current) :=
  (Finset.univ : Finset ((RawIndex current × RawIndex current) × (AtomSector source × AtomSector source))).toList.map
    (fun pair => ⟨pair.2.1,pair.2.2,pair.1.1,pair.1.2,effectiveSourceFock current pair.1.1 pair.1.2⟩)

theorem source_atom_word_operator (current : NativeCurrent source) :
    ((sourceAtomCARWord current).map AtomCARMonomial.operator).sum = sourceFockCAR current := by
  simp only [sourceAtomCARWord,List.map_map,Function.comp_def,AtomCARMonomial.operator]
  rw [Finset.sum_map_toList,Fintype.sum_prod_type]
  exact atom_fock_car_exact current

theorem source_atom_instruction_vertices (current : NativeCurrent source) (term : AtomCARMonomial current) :
    sectorOrigin current term.removing ∈ vertices source ∧ sectorOrigin current term.creating ∈ vertices source := by
  constructor <;> exact List.mem_map_of_mem (List.get_mem _ _)

theorem source_atom_charge_delta (current : NativeCurrent source) (term : AtomCARMonomial current) (observed : AtomSector source) :
    term.chargeDelta (sectorOrigin current observed) = -atomDelta current observed term.creating term.removing := by
  classical
  have originEqual (first second : AtomSector source) : sectorOrigin current first = sectorOrigin current second ↔ first = second :=
    (source_origin_injective source).eq_iff
  simp only [AtomCARMonomial.chargeDelta,Finsupp.sub_apply,Finsupp.single_apply,originEqual,atomDelta]
  by_cases create : observed = term.creating <;> by_cases remove : observed = term.removing <;>
    simp [create,remove,eq_comm]

theorem source_atom_charge_action (current : NativeCurrent source) (term : AtomCARMonomial current)
    (observed : AtomSector source) (state : SourceFermion) :
    atomNumber current observed (term.operator state)-term.operator (atomNumber current observed state) =
      (-(term.chargeDelta (sectorOrigin current observed)) : ℂ) • term.operator state := by
  change atomNumber current observed
      (term.coefficient • physicalPair (atomCut current term.creating (rawField current term.creatingRaw))
        (atomCut current term.removing (rawField current term.removingRaw)) state)-
      term.coefficient • physicalPair (atomCut current term.creating (rawField current term.creatingRaw))
        (atomCut current term.removing (rawField current term.removingRaw)) (atomNumber current observed state) = _
  rw [map_smul,← smul_sub,atom_pair_integer,source_atom_charge_delta]
  simp only [Int.cast_neg,neg_neg,AtomCARMonomial.operator,LinearMap.smul_apply,smul_smul]
  rw [mul_comm]

theorem source_atom_diagonal_charge (current : NativeCurrent source) (term : AtomCARMonomial current)
    (diagonal : term.creating = term.removing) : term.chargeDelta = 0 ∧ term.instruction? = none := by
  simp [AtomCARMonomial.chargeDelta,AtomCARMonomial.instruction?,diagonal]

theorem source_atom_instruction_actual (current : NativeCurrent source) (term : AtomCARMonomial current)
    (instruction : ChargedInstruction cursor) (actual : term.instruction? = some instruction) :
    term.creating ≠ term.removing ∧
      instruction = .electron (sectorOrigin current term.removing) (sectorOrigin current term.creating) ∧
      sectorOrigin current term.removing ≠ sectorOrigin current term.creating := by
  unfold AtomCARMonomial.instruction? at actual
  split at actual
  · cases actual
  · rename_i different
    refine ⟨different,(Option.some.inj actual).symm,?_⟩
    intro same
    exact different ((source_origin_injective source same).symm)

theorem atom_source_null (current : NativeCurrent source) (index : AtomSector source) (relation : CoordinateSpace current)
    (null : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) *ᵥ relation = 0) :
    ∑ rawIndex, relation rawIndex • atomCut current index (rawField current rawIndex) = 0 := by
  have projected := congrArg (atomCut current index) (source_null_field current relation null)
  rw [raw_synthesis_apply,map_sum] at projected
  simpa only [map_smul,map_zero] using projected

theorem atom_null_creation (current : NativeCurrent source) (index : AtomSector source) (relation : CoordinateSpace current)
    (null : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) *ᵥ relation = 0) :
    ∑ rawIndex, relation rawIndex • physicalCreation (atomCut current index (rawField current rawIndex)) = 0 := by
  simp_rw [← physical_creation_smul]
  rw [← physical_creation_sum,atom_source_null current index relation null,physical_creation_zero]

theorem atom_null_annihilation (current : NativeCurrent source) (index : AtomSector source) (relation : CoordinateSpace current)
    (null : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) *ᵥ relation = 0) :
    ∑ rawIndex, star (relation rawIndex) • physicalAnnihilation (atomCut current index (rawField current rawIndex)) = 0 := by
  simp_rw [← physical_annihilation_smul]
  rw [← physical_annihilation_sum,atom_source_null current index relation null,physical_annihilation_zero]

def atomReadbackMatrix (current : NativeCurrent source) : Matrix (BasisIndex current) (AddressedBasisIndex current) ℂ :=
  fun index mode => inner ℂ (basis current index) (addressedBasis current mode)

def atomReadback (current : NativeCurrent source) (occupied : Matrix (AddressedBasisIndex current) (Electron source.nodes) ℂ) :=
  atomReadbackMatrix current * occupied

theorem atom_readback_coordinates (current : NativeCurrent source) :
    atomReadbackMatrix current * atomCoordinates current =
      CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) := by
  ext index rawIndex
  have represented := congrArg (inner ℂ (basis current index)) (atom_raw_synthesis current rawIndex)
  simp only [inner_sum,inner_smul_right] at represented
  change (∑ mode, inner ℂ (basis current index) (addressedBasis current mode) * atomCoordinates current mode rawIndex) =
    inner ℂ (basis current index) (rawField current rawIndex)
  rw [represented]
  apply Finset.sum_congr rfl
  intro mode _
  rw [mul_comm]

theorem atom_readback_current (current : NativeCurrent source) : atomReadback current (atomOccupation current) = coordinates current := by
  rw [atomReadback,atomOccupation,← Matrix.mul_assoc,atom_readback_coordinates]
  rfl

theorem atom_readback_updated (current : NativeCurrent source) (time : ℝ) :
    atomReadback current (atomUpdatedOccupation current time) = updatedCoordinates current time := by
  rw [atomReadback,atomUpdatedOccupation,← Matrix.mul_assoc,atom_readback_coordinates]
  ext index slot
  have sourceValue := congrArg (inner ℂ (basis current index))
    (congrFun (raw_increment_fields current (updatedCoordinates current time)) slot)
  rw [← updated_raw_increment current time] at sourceValue
  simp only [CPS1ElectronicEvolution.fields,inner_sum,inner_smul_right,
    (basis_orthonormal current).inner_right_fintype] at sourceValue
  change (∑ rawIndex, inner ℂ (basis current index) (rawField current rawIndex) * updatedRaw current time rawIndex slot) = _
  rw [← sourceValue]
  apply Finset.sum_congr rfl
  intro rawIndex _
  rw [mul_comm]

def atomReadbackEnergy (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (AddressedBasisIndex current) (Electron source.nodes) ℂ) : ℝ :=
  rawEnergy current pose (rawIncrement current (atomReadback current occupied))

theorem atom_energy_current (current : NativeCurrent source) (pose : List Body.Node) :
    atomReadbackEnergy current pose (atomOccupation current) =
      wholeEnergyAt source.nodes pose source.electronInertia current.occupied := by
  rw [atomReadbackEnergy,atom_readback_current,raw_increment_current]
  exact current_energy_restriction current pose

theorem atom_energy_updated (current : NativeCurrent source) (pose : List Body.Node) (time : ℝ) :
    atomReadbackEnergy current pose (atomUpdatedOccupation current time) = rawEnergy current pose (updatedRaw current time) := by
  rw [atomReadbackEnergy,atom_readback_updated,← updated_raw_increment]

def atomJointValue (current : NativeCurrent source) (atom : AtomSector source) (index : BasisIndex current)
    (spin : Bool) (point : Body.Point) : ℂ :=
  (sectorCell current atom).indicator (basisValue current index spin) (fun axis => point axis)

theorem atom_joint_value_sum (current : NativeCurrent source) (index : BasisIndex current) (spin : Bool) (point : Body.Point) :
    ∑ atom : AtomSector source, atomJointValue current atom index spin point =
      basisValue current index spin (fun axis => point axis) := by
  classical
  obtain ⟨selected,selectedHeld⟩ := sector_cell_complete current (fun axis => point axis)
  rw [Finset.sum_eq_single selected]
  · exact Set.indicator_of_mem selectedHeld _
  · intro other _ different
    exact Set.indicator_of_notMem
      (fun held => different (sector_cell_unique current (fun axis => point axis) other selected held selectedHeld)) _
  · exact fun missing => False.elim (missing (Finset.mem_univ _))

def atomJointKernel (current : NativeCurrent source) (left right : AtomSector source) (first second : Body.Point) : ℂ :=
  ∑ spin : Bool, ∑ i : BasisIndex current, ∑ j : BasisIndex current,
    star (atomJointValue current left i spin first) * jointDensity current i j *
      atomJointValue current right j spin second

theorem atomic_joint_kernel_complete (current : NativeCurrent source) (first second : Body.Point) :
    ∑ atomPair : AtomSector source × AtomSector source, atomJointKernel current atomPair.1 atomPair.2 first second =
      densityKernelAt source.nodes current.occupied first second := by
  rw [← joint_density_kernel_exact current first second]
  simp only [atomJointKernel,jointDensityKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro spin _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum]
  rw [atom_joint_value_sum]
  simp only [← Finset.sum_mul,← star_sum]
  rw [atom_joint_value_sum]

end
end CPS1MaterialIncidence
