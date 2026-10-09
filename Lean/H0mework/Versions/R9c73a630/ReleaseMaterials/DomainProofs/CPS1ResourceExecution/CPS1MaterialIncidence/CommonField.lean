import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Native
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Normed
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Integrals
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Mechanics
import Mathlib.MeasureTheory.Measure.OpenPos
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.OriginGraph

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open MeasureTheory
open scoped BigOperators InnerProductSpace Matrix
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

private def SpatialReal (field : SpatialLp) : Prop := ∀ᵐ point ∂volume, star (field point) = field point

private theorem spatial_real_zero : SpatialReal 0 := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure Point)] with point actual
  simp only [actual,Pi.zero_apply,star_zero]

private theorem spatial_real_add (first second : SpatialLp) (hf : SpatialReal first) (hg : SpatialReal second) :
    SpatialReal (first+second) := by
  filter_upwards [Lp.coeFn_add first second,hf,hg] with point actual left right
  simp only [actual,Pi.add_apply,star_add,left,right]

private theorem spatial_real_sub (first second : SpatialLp) (hf : SpatialReal first) (hg : SpatialReal second) :
    SpatialReal (first-second) := by
  filter_upwards [Lp.coeFn_sub first second,hf,hg] with point actual left right
  simp only [actual,Pi.sub_apply,star_sub,left,right]

private theorem spatial_real_smul (scalar : ℂ) (field : SpatialLp)
    (real : star scalar = scalar) (actual : SpatialReal field) : SpatialReal (scalar • field) := by
  filter_upwards [Lp.coeFn_smul scalar field,actual] with point value realValue
  simp only [value,Pi.smul_apply,smul_eq_mul,star_mul,real,realValue]
  ring

private theorem spatial_real_inner (first second : SpatialLp) (hf : SpatialReal first) (hg : SpatialReal second) :
    star (inner ℂ first second) = inner ℂ first second := by
  rw [MeasureTheory.L2.inner_def,Complex.star_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [hf,hg] with point left right
  simp only [RCLike.inner_apply',map_mul,Complex.conj_conj]
  change first point * star (second point) = star (first point) * second point
  rw [left,right]

private theorem finite_real_sum {E : Type*} [AddCommMonoid E] (property : E → Prop)
    (zero : property 0) (add : ∀ f g, property f → property g → property (f+g))
    {index : Type*} (items : Finset index) (fields : index → E)
    (actual : ∀ index ∈ items, property (fields index)) : property (∑ index ∈ items, fields index) := by
  classical
  induction items using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero
  | @insert index items missing ih =>
    rw [Finset.sum_insert missing]
    exact add _ _ (actual index (Finset.mem_insert_self _ _))
      (ih (fun other held => actual other (Finset.mem_insert_of_mem held)))

private theorem gram_schmidt_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {count : Nat} (fields : Fin count → E) (property : E → Prop)
    (zero : property 0) (add : ∀ f g, property f → property g → property (f+g))
    (sub : ∀ f g, property f → property g → property (f-g))
    (smul : ∀ (scalar : ℂ) (f : E), star scalar = scalar → property f → property (scalar • f))
    (pair : ∀ f g, property f → property g → star (inner ℂ f g) = inner ℂ f g)
    (actual : ∀ index, property (fields index)) (index : Fin count) :
    property (InnerProductSpace.gramSchmidt ℂ fields index) := by
  apply wellFounded_lt.induction index
  intro index previous
  have recurrence : InnerProductSpace.gramSchmidt ℂ fields index = fields index-
      ∑ earlier ∈ Finset.Iio index,
        (inner ℂ (InnerProductSpace.gramSchmidt ℂ fields earlier) (fields index)/
          (‖InnerProductSpace.gramSchmidt ℂ fields earlier‖ : ℂ)^2) •
            InnerProductSpace.gramSchmidt ℂ fields earlier := by
    exact (eq_sub_iff_add_eq).mpr (InnerProductSpace.gramSchmidt_def'' ℂ fields index).symm
  rw [recurrence]
  apply sub _ _ (actual index)
  apply finite_real_sum property zero add
  intro earlier held
  have earlierReal := previous earlier (Finset.mem_Iio.mp held)
  apply smul _ _ _ earlierReal
  simp only [Complex.star_def,map_div₀,map_pow,Complex.conj_ofReal]
  exact congrArg (fun value : ℂ => value/(‖InnerProductSpace.gramSchmidt ℂ fields earlier‖ : ℂ)^2)
    (pair _ _ earlierReal (actual index))

private theorem gram_schmidt_normed_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {count : Nat} (fields : Fin count → E) (property : E → Prop)
    (zero : property 0) (add : ∀ f g, property f → property g → property (f+g))
    (sub : ∀ f g, property f → property g → property (f-g))
    (smul : ∀ (scalar : ℂ) (f : E), star scalar = scalar → property f → property (scalar • f))
    (pair : ∀ f g, property f → property g → star (inner ℂ f g) = inner ℂ f g)
    (actual : ∀ index, property (fields index)) (index : Fin count) :
    property (InnerProductSpace.gramSchmidtNormed ℂ fields index) := by
  unfold InnerProductSpace.gramSchmidtNormed
  exact smul _ _ (by simp) (gram_schmidt_real fields property zero add sub smul pair actual index)

private theorem orbital_value_real (centre : Point) (mode : Nat) (jet : Fin 3 → Nat) (point : Point) :
    star (orbitalValue centre mode jet point) = orbitalValue centre mode jet point := by
  simp [orbitalValue,SourceGaussianModel.orbital]

private theorem orbital_field_real (centre : Point) (mode : Nat) : SpatialReal (orbitalField centre mode 0) := by
  filter_upwards [orbital_field_source centre mode 0] with point actual
  rw [actual,orbital_value_real]

private theorem normalized_field_real (centre : Point) (count : Nat) (index : Fin count) :
    SpatialReal (normalizedField centre count index) :=
  gram_schmidt_normed_real (rawFields centre count) SpatialReal spatial_real_zero spatial_real_add
    spatial_real_sub spatial_real_smul spatial_real_inner (fun index => orbital_field_real centre index.val) index

private theorem spatial_value_real (centre : Point) (count : Nat) (index : Fin count) (point : Point) :
    star (spatialValue centre count index 0 point) = spatialValue centre count index 0 point := by
  have actual : ∀ᵐ point ∂volume, star (spatialValue centre count index 0 point) = spatialValue centre count index 0 point := by
    have real := normalized_field_real centre count index
    rw [← spatial_field_normalized] at real
    filter_upwards [real,(spatial_memLp centre count index 0).coeFn_toLp] with point realValue value
    change spatialField centre count index 0 point = spatialValue centre count index 0 point at value
    rwa [value] at realValue
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq actual
    (spatial_continuous centre count index 0).star (spatial_continuous centre count index 0)) point

private def SpinReal (field : SpinSpace) : Prop := ∀ spin, SpatialReal (field spin)

private theorem spin_real_zero : SpinReal 0 := by
  intro spin
  simpa only [PiLp.zero_apply] using spatial_real_zero

private theorem spin_real_add (first second : SpinSpace) (hf : SpinReal first) (hg : SpinReal second) :
    SpinReal (first+second) := by
  intro spin
  simpa only [PiLp.add_apply] using spatial_real_add _ _ (hf spin) (hg spin)

private theorem spin_real_sub (first second : SpinSpace) (hf : SpinReal first) (hg : SpinReal second) :
    SpinReal (first-second) := by
  intro spin
  simpa only [PiLp.sub_apply] using spatial_real_sub _ _ (hf spin) (hg spin)

private theorem spin_real_smul (scalar : ℂ) (field : SpinSpace)
    (real : star scalar = scalar) (actual : SpinReal field) : SpinReal (scalar • field) := by
  intro spin
  simpa only [PiLp.smul_apply] using spatial_real_smul _ _ real (actual spin)

private theorem spin_real_inner (first second : SpinSpace) (hf : SpinReal first) (hg : SpinReal second) :
    star (inner ℂ first second) = inner ℂ first second := by
  simp only [PiLp.inner_apply,star_sum]
  exact Finset.sum_congr rfl (fun spin _ => spatial_real_inner _ _ (hf spin) (hg spin))

abbrev LocalIndex (current : NativeCurrent source) := Fin (nucleusNodes current.nodes).length × Bool
abbrev RawIndex (current : NativeCurrent source) := Spin source.nodes ⊕ LocalIndex current

def hermiteField (nodes : List Body.Node) (index : Spin nodes) : SpinSpace :=
  PiLp.single 2 index.2 (normalizedField 0 (electronCount nodes+1) index.1)

def currentField (current : NativeCurrent source) : Electron source.nodes → SpinSpace :=
  CPS1ElectronicEvolution.fields (hermiteField source.nodes) current.occupied

def localNode (current : NativeCurrent source) (index : LocalIndex current) : Body.Node :=
  (nucleusNodes current.nodes).get index.1

private theorem local_node_held (current : NativeCurrent source) (index : LocalIndex current) :
    localNode current index ∈ nucleusNodes current.nodes := List.get_mem _ index.1

def localOrigin (current : NativeCurrent source) (index : LocalIndex current) : AtomOrigin cursor :=
  atomOriginAtNode source current (localNode current index) (List.mem_of_mem_filter (local_node_held current index))

theorem local_origin_actual (current : NativeCurrent source) (index : LocalIndex current) :
    originAt? source.atoms (localNode current index).particle.address = some (localOrigin current index) :=
  current_atom_origin source current _ (List.mem_of_mem_filter (local_node_held current index))

inductive FieldOrigin (cursor : CPS1ReactiveNuclear.SourceCursor frame) (nodes : List Body.Node)
  | storedMode (index : Spin nodes)
  | localAtom (origin : AtomOrigin cursor) (spin : Bool)
  deriving DecidableEq

def rawOrigin (current : NativeCurrent source) : RawIndex current → FieldOrigin cursor source.nodes
  | .inl index => .storedMode index
  | .inr index => .localAtom (localOrigin current index) index.2

def localField (current : NativeCurrent source) (index : LocalIndex current) : SpinSpace :=
  PiLp.single 2 index.2 (orbitalField (Geometry.nucleusPosition (localNode current index)) 0 0)

def rawField (current : NativeCurrent source) : RawIndex current → SpinSpace :=
  Sum.elim (hermiteField source.nodes) (localField current)

def rawOccupation (current : NativeCurrent source) : Matrix (RawIndex current) (Electron source.nodes) ℂ
  | .inl index,slot => current.occupied index slot
  | .inr _,_ => 0

abbrev BasisIndex (current : NativeCurrent source) :=
  CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (rawField current)

def basis (current : NativeCurrent source) : BasisIndex current → SpinSpace :=
  CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (rawField current)

def coordinates (current : NativeCurrent source) : Matrix (BasisIndex current) (Electron source.nodes) ℂ :=
  CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) * rawOccupation current

theorem hermite_orthonormal (nodes : List Body.Node) : Orthonormal ℂ (hermiteField nodes) := by
  apply orthonormal_iff_ite.mpr
  rintro ⟨i,spin⟩ ⟨j,otherSpin⟩
  have spatial := orthonormal_iff_ite.mp (normalized_orthonormal (0 : Point) (electronCount nodes+1)) i j
  cases spin <;> cases otherSpin <;> simp [hermiteField,PiLp.inner_apply,PiLp.single_apply]
  all_goals exact spatial

theorem raw_occupation_old (current : NativeCurrent source) (index : Spin source.nodes)
    (slot : Electron source.nodes) : rawOccupation current (.inl index) slot = current.occupied index slot := rfl

theorem raw_occupation_local (current : NativeCurrent source) (index : LocalIndex current)
    (slot : Electron source.nodes) : rawOccupation current (.inr index) slot = 0 := rfl

theorem raw_current_fields (current : NativeCurrent source) :
    CPS1ElectronicEvolution.fields (rawField current) (rawOccupation current) = currentField current := by
  funext slot
  simp only [CPS1ElectronicEvolution.fields,Fintype.sum_sum_type,rawOccupation,rawField,
    Sum.elim_inl,Sum.elim_inr,zero_smul,Finset.sum_const_zero,add_zero,currentField]

theorem basis_orthonormal (current : NativeCurrent source) : Orthonormal ℂ (basis current) :=
  CPS1MolecularFrame.FiniteNormed.field_orthonormal _

theorem complete_source_span (current : NativeCurrent source) :
    Submodule.span ℂ (Set.range (basis current)) = Submodule.span ℂ (Set.range (rawField current)) :=
  CPS1MolecularFrame.FiniteNormed.span_exact _

theorem current_coordinates (current : NativeCurrent source) :
    CPS1ElectronicEvolution.fields (basis current) (coordinates current) = currentField current := by
  funext slot
  rw [coordinates,CPS1Deformation.fields_mul]
  have complete : CPS1ElectronicEvolution.fields (basis current)
      (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)) = rawField current := by
    funext index
    exact (CPS1MolecularFrame.FiniteNormed.raw_synthesis (rawField current) index).symm
  rw [complete,raw_current_fields]

theorem current_fields_orthonormal (current : NativeCurrent source) : Orthonormal ℂ (currentField current) :=
  CPS1ElectronicEvolution.occupied_fields _ (hermite_orthonormal _) _ current.occupiedGram

theorem coordinates_gram (current : NativeCurrent source) :
    (coordinates current).conjTranspose * coordinates current = 1 := by
  ext first second
  rw [← CPS1ElectronicEvolution.field_gram (basis current) (basis_orthonormal current),current_coordinates]
  exact orthonormal_iff_ite.mp (current_fields_orthonormal current) first second

def jointDensity (current : NativeCurrent source) := coordinates current * (coordinates current).conjTranspose

theorem joint_electron_number (current : NativeCurrent source) :
    Matrix.trace (jointDensity current) = (electronCount source.nodes : ℂ) := by
  rw [jointDensity,Matrix.trace_mul_comm,coordinates_gram]
  simp only [Matrix.trace_one,Fintype.card_fin,Electron]

def rawJet (current : NativeCurrent source) : RawIndex current → (Fin 3 → Nat) → SpinSpace
  | .inl index,jet => PiLp.single 2 index.2 (spatialField 0 (electronCount source.nodes+1) index.1 jet)
  | .inr index,jet => PiLp.single 2 index.2 (orbitalField (Geometry.nucleusPosition (localNode current index)) 0 jet)

def rawValue (current : NativeCurrent source) : RawIndex current → (Fin 3 → Nat) → Bool → Point → ℂ
  | .inl index,jet,spin,point =>
    if index.2 = spin then spatialValue 0 (electronCount source.nodes+1) index.1 jet point else 0
  | .inr index,jet,spin,point =>
    if index.2 = spin then orbitalValue (Geometry.nucleusPosition (localNode current index)) 0 jet point else 0

def basisValue (current : NativeCurrent source) (index : BasisIndex current) (spin : Bool) (point : Point) : ℂ :=
  ∑ primitive, CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
    (rawField current) primitive index * rawValue current primitive 0 spin point

def occupiedValue (current : NativeCurrent source)
    (occupied : Matrix (BasisIndex current) (Electron source.nodes) ℂ)
    (slot : Electron source.nodes) (spin : Bool) (point : Point) : ℂ :=
  ∑ index, occupied index slot * basisValue current index spin point

private def rawOccupiedValue (current : NativeCurrent source)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ)
    (slot : Electron source.nodes) (spin : Bool) (point : Point) : ℂ :=
  ∑ primitive, occupied primitive slot * rawValue current primitive 0 spin point

theorem raw_value_continuous (current : NativeCurrent source) (index : RawIndex current) (spin : Bool) :
    Continuous (rawValue current index 0 spin) := by
  cases index with
  | inl index =>
    change Continuous (fun point => if index.2 = spin then
      spatialValue 0 (electronCount source.nodes+1) index.1 0 point else 0)
    by_cases same : index.2 = spin
    · simpa only [if_pos same] using spatial_continuous (0 : Point) (electronCount source.nodes+1) index.1 0
    · simpa only [if_neg same] using (continuous_const : Continuous (fun _ : Point => (0 : ℂ)))
  | inr index =>
    change Continuous (fun point => if index.2 = spin then
      orbitalValue (Geometry.nucleusPosition (localNode current index)) 0 0 point else 0)
    by_cases same : index.2 = spin
    · simpa only [if_pos same] using orbital_continuous (Geometry.nucleusPosition (localNode current index)) 0 0
    · simpa only [if_neg same] using (continuous_const : Continuous (fun _ : Point => (0 : ℂ)))

theorem raw_field_value (current : NativeCurrent source) (index : RawIndex current) (spin : Bool) :
    rawField current index spin =ᵐ[volume] rawValue current index 0 spin := by
  cases index with
  | inl index =>
    by_cases same : index.2 = spin
    · subst spin
      have known : normalizedField 0 (electronCount source.nodes+1) index.1 =ᵐ[volume]
          spatialValue 0 (electronCount source.nodes+1) index.1 0 := by
        rw [← spatial_field_normalized]
        exact (spatial_memLp _ _ _ _).coeFn_toLp
      filter_upwards [known] with point actual
      simpa [rawField,hermiteField,rawValue] using actual
    · filter_upwards [] with point
      simp [rawField,hermiteField,rawValue,same]
  | inr index =>
    by_cases same : index.2 = spin
    · subst spin
      filter_upwards [orbital_field_source (Geometry.nucleusPosition (localNode current index)) 0 0] with point actual
      simpa [rawField,localField,rawValue] using actual
    · filter_upwards [] with point
      simp [rawField,localField,rawValue,same]

theorem basis_field_value (current : NativeCurrent source) (index : BasisIndex current) (spin : Bool) :
    basis current index spin =ᵐ[volume] basisValue current index spin := by
  have each (primitive : RawIndex current) :
      (fun point : Point => (CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
        (rawField current) primitive index • rawField current primitive spin) point) =ᵐ[volume]
      fun point => CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
        (rawField current) primitive index * rawValue current primitive 0 spin point := by
    filter_upwards [Lp.coeFn_smul (CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
      (rawField current) primitive index) (rawField current primitive spin),raw_field_value current primitive spin]
      with point scalar actual
    simpa only [Pi.smul_apply,smul_eq_mul,actual] using scalar
  have coordinate : basis current index spin =
      ∑ primitive, CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
        (rawField current) primitive index • rawField current primitive spin := by
    rw [basis,CPS1MolecularFrame.FiniteNormed.field_synthesis]
    change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => SpatialLp) spin) _ = _
    simp only [map_sum,map_smul,PiLp.proj_apply]
  rw [coordinate]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun primitive =>
      CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
        (rawField current) primitive index • rawField current primitive spin),
    Filter.eventually_all.mpr each] with point summed scalar
  exact summed.trans (Finset.sum_congr rfl (fun primitive _ => scalar primitive))

private theorem fields_pointwise {index : Type*} [Fintype index] [DecidableEq index]
    (fields : index → SpinSpace) (values : index → Bool → Point → ℂ)
    (occupied : Matrix index (Electron source.nodes) ℂ)
    (actual : ∀ index spin, fields index spin =ᵐ[volume] values index spin)
    (slot : Electron source.nodes) (spin : Bool) :
    CPS1ElectronicEvolution.fields fields occupied slot spin =ᵐ[volume]
      fun point => ∑ index, occupied index slot * values index spin point := by
  have each (index) : (fun point : Point => (occupied index slot • fields index spin) point) =ᵐ[volume]
      fun point => occupied index slot * values index spin point := by
    filter_upwards [Lp.coeFn_smul (occupied index slot) (fields index spin),actual index spin] with point scalar value
    simpa only [Pi.smul_apply,smul_eq_mul,value] using scalar
  have coordinate : CPS1ElectronicEvolution.fields fields occupied slot spin =
      ∑ index, occupied index slot • fields index spin := by
    change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => SpatialLp) spin) _ = _
    simp only [CPS1ElectronicEvolution.fields,map_sum,map_smul,PiLp.proj_apply]
  rw [coordinate]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun index => occupied index slot • fields index spin),
    Filter.eventually_all.mpr each] with point summed scalar
  exact summed.trans (Finset.sum_congr rfl (fun index _ => scalar index))

private theorem represented_fields (current : NativeCurrent source)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) :
    CPS1ElectronicEvolution.fields (basis current)
      (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)*occupied) =
        CPS1ElectronicEvolution.fields (rawField current) occupied := by
  funext slot
  rw [CPS1Deformation.fields_mul]
  have complete : CPS1ElectronicEvolution.fields (basis current)
      (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)) = rawField current := by
    funext index
    exact (CPS1MolecularFrame.FiniteNormed.raw_synthesis (rawField current) index).symm
  rw [complete]

private theorem represented_values (current : NativeCurrent source)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ)
    (slot : Electron source.nodes) (spin : Bool) (point : Point) :
    occupiedValue current (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)*occupied)
      slot spin point = rawOccupiedValue current occupied slot spin point := by
  have left := fields_pointwise (basis current) (basisValue current)
    (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)*occupied)
    (basis_field_value current) slot spin
  have right := fields_pointwise (rawField current) (fun index => rawValue current index 0) occupied
    (raw_field_value current) slot spin
  rw [represented_fields] at left
  have continuousLeft : Continuous (occupiedValue current
      (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)*occupied) slot spin) := by
    unfold occupiedValue basisValue
    apply continuous_finsetSum
    intro index _
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro primitive _
    exact (raw_value_continuous current primitive spin).const_mul _
  have continuousRight : Continuous (rawOccupiedValue current occupied slot spin) := by
    unfold rawOccupiedValue
    apply continuous_finsetSum
    intro primitive _
    exact (raw_value_continuous current primitive spin).const_mul _
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq (left.symm.trans right) continuousLeft continuousRight) point

theorem current_pointwise_wave (current : NativeCurrent source) (slot : Electron source.nodes)
    (spin : Bool) (point : Point) :
    occupiedValue current (coordinates current) slot spin point =
      ∑ index, current.occupied index slot *
        (if index.2 = spin then spatialValue 0 (electronCount source.nodes+1) index.1 0 point else 0) := by
  rw [coordinates,represented_values]
  simp only [rawOccupiedValue,Fintype.sum_sum_type,rawOccupation,rawValue,zero_mul,
    Finset.sum_const_zero,add_zero]

-- This is the existing source kernel's dual evaluation convention; it is a
-- readout of the retained phase, not another captured occupation.
private def dualRawOccupation (current : NativeCurrent source) : Matrix (RawIndex current) (Electron source.nodes) ℂ
  | .inl index,slot => star (current.occupied index slot)
  | .inr _,_ => 0

private def dualCoordinates (current : NativeCurrent source) :=
  CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)*dualRawOccupation current

private theorem raw_value_real (current : NativeCurrent source) (index : RawIndex current)
    (spin : Bool) (point : Point) : star (rawValue current index 0 spin point) = rawValue current index 0 spin point := by
  cases index with
  | inl index =>
    change star (if index.2 = spin then spatialValue 0 (electronCount source.nodes+1) index.1 0 point else 0) =
      if index.2 = spin then spatialValue 0 (electronCount source.nodes+1) index.1 0 point else 0
    split_ifs
    · exact spatial_value_real _ _ _ _
    · simp only [star_zero]
  | inr index =>
    change star (if index.2 = spin then orbitalValue (Geometry.nucleusPosition (localNode current index)) 0 0 point else 0) =
      if index.2 = spin then orbitalValue (Geometry.nucleusPosition (localNode current index)) 0 0 point else 0
    split_ifs
    · exact orbital_value_real _ _ _ _
    · simp only [star_zero]

private theorem raw_field_real (current : NativeCurrent source) (index : RawIndex current) :
    SpinReal (rawField current index) := by
  intro spin
  filter_upwards [raw_field_value current index spin] with point actual
  rw [actual,raw_value_real]

private theorem ordered_gs_real (current : NativeCurrent source) (index : Fin (Fintype.card (RawIndex current))) :
    SpinReal (InnerProductSpace.gramSchmidt ℂ (CPS1MolecularFrame.FiniteNormed.ordered (rawField current)) index) :=
  gram_schmidt_real _ SpinReal spin_real_zero spin_real_add spin_real_sub spin_real_smul spin_real_inner
    (fun _index => raw_field_real current _) index

private theorem basis_real (current : NativeCurrent source) (index : BasisIndex current) :
    SpinReal (basis current index) :=
  gram_schmidt_normed_real _ SpinReal spin_real_zero spin_real_add spin_real_sub spin_real_smul spin_real_inner
    (fun _index => raw_field_real current _) index.val

private theorem projection_ratio_real (current : NativeCurrent source)
    (previous index : Fin (Fintype.card (RawIndex current))) :
    star (CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (rawField current) previous index) =
      CPS1MolecularFrame.FiniteNormed.projectionRatio (𝕜 := ℂ) (rawField current) previous index := by
  unfold CPS1MolecularFrame.FiniteNormed.projectionRatio
  have orderedReal : SpinReal (CPS1MolecularFrame.FiniteNormed.ordered (rawField current) index) :=
    raw_field_real current ((Fintype.equivFin (RawIndex current)).symm index)
  rw [star_div₀,star_pow,spin_real_inner _ _ (ordered_gs_real current previous) orderedReal]
  simp

private theorem gs_coefficients_real (current : NativeCurrent source)
    (index coefficient : Fin (Fintype.card (RawIndex current))) :
    star (CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) (rawField current) index coefficient) =
      CPS1MolecularFrame.FiniteNormed.gsCoefficients (𝕜 := ℂ) (rawField current) index coefficient := by
  apply wellFounded_lt.induction index
  intro index previous
  rw [CPS1MolecularFrame.FiniteNormed.gs_coefficients_step]
  simp only [star_sub,apply_ite star,star_one,star_zero,star_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro earlier _
  rw [star_mul,projection_ratio_real,previous earlier.val (Finset.mem_Iio.mp earlier.property)]
  ring

theorem source_coefficients_real (current : NativeCurrent source) (primitive : RawIndex current)
    (index : BasisIndex current) :
    star (CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (rawField current) primitive index) =
      CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (rawField current) primitive index := by
  simp only [CPS1MolecularFrame.FiniteNormed.coefficients,star_mul,gs_coefficients_real]
  simp [mul_comm]

theorem raw_coordinates_real (current : NativeCurrent source) (index : BasisIndex current)
    (primitive : RawIndex current) :
    star (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) index primitive) =
      CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) index primitive :=
  spin_real_inner _ _ (basis_real current index) (raw_field_real current primitive)

theorem basis_value_real (current : NativeCurrent source) (index : BasisIndex current)
    (spin : Bool) (point : Point) : star (basisValue current index spin point) = basisValue current index spin point := by
  simp only [basisValue,star_sum,star_mul,source_coefficients_real,raw_value_real]
  exact Finset.sum_congr rfl (fun primitive _ => mul_comm _ _)

private theorem dual_coordinates_actual (current : NativeCurrent source) :
    dualCoordinates current = fun index slot => star (coordinates current index slot) := by
  ext index slot
  simp only [dualCoordinates,coordinates,Matrix.mul_apply,star_sum,star_mul,raw_coordinates_real]
  apply Finset.sum_congr rfl
  intro primitive _
  cases primitive <;> simp only [rawOccupation,dualRawOccupation,star_zero] <;> ring

private theorem dual_pointwise_wave (current : NativeCurrent source) (slot : Electron source.nodes)
    (spin : Bool) (point : Point) :
    occupiedValue current (dualCoordinates current) slot spin point =
      ∑ index : Spatial source.nodes, star (current.occupied (index,spin) slot)*
        spatialValue 0 (electronCount source.nodes+1) index 0 point := by
  rw [dualCoordinates,represented_values]
  cases spin <;> simp [rawOccupiedValue,Fintype.sum_sum_type,dualRawOccupation,rawValue,Fintype.sum_prod_type]

def sourceDensityKernel (current : NativeCurrent source) (first second : Body.Point) : ℂ :=
  ∑ spin : Bool, ∑ slot : Electron source.nodes,
    star (occupiedValue current (dualCoordinates current) slot spin (fun axis => first axis))*
      occupiedValue current (dualCoordinates current) slot spin (fun axis => second axis)

theorem source_density_kernel_exact (current : NativeCurrent source) (first second : Body.Point) :
    sourceDensityKernel current first second = densityKernelAt source.nodes current.occupied first second := by
  simp only [sourceDensityKernel,dual_pointwise_wave,star_sum,star_mul,star_star,Finset.sum_mul,Finset.mul_sum]
  unfold densityKernelAt densityKernel density
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro spin _
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro other _
  apply Finset.sum_congr rfl
  intro slot _
  ring

theorem source_bond_weight_exact (current : NativeCurrent source) (first second : Body.Point) :
    Complex.normSq (sourceDensityKernel current first second) = bondWeight source.nodes current.occupied first second := by
  rw [source_density_kernel_exact]
  rfl

def jointDensityKernel (current : NativeCurrent source) (first second : Body.Point) : ℂ :=
  ∑ spin : Bool, ∑ i : BasisIndex current, ∑ j : BasisIndex current,
    star (basisValue current i spin (fun axis => first axis)) * jointDensity current i j *
      basisValue current j spin (fun axis => second axis)

theorem joint_density_uses_actual_phase (current : NativeCurrent source) (first second : Body.Point) :
    jointDensityKernel current first second = sourceDensityKernel current first second := by
  simp only [jointDensityKernel,jointDensity,sourceDensityKernel,dual_coordinates_actual,occupiedValue,
    Matrix.mul_apply,Matrix.conjTranspose_apply,star_sum,star_mul,star_star,Finset.mul_sum,Finset.sum_mul]
  symm
  apply Finset.sum_congr rfl
  intro spin _
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro other _
  apply Finset.sum_congr rfl
  intro slot _
  ring

theorem joint_density_kernel_exact (current : NativeCurrent source) (first second : Body.Point) :
    jointDensityKernel current first second = densityKernelAt source.nodes current.occupied first second :=
  (joint_density_uses_actual_phase current first second).trans (source_density_kernel_exact current first second)

theorem joint_bond_weight_exact (current : NativeCurrent source) (first second : Body.Point) :
    Complex.normSq (jointDensityKernel current first second) = bondWeight source.nodes current.occupied first second := by
  rw [joint_density_kernel_exact]
  rfl

def rawNuclearIntegral (current : NativeCurrent source) (i j : RawIndex current) (spin : Bool) (nuclear : Point) : ℂ :=
  ∫ point : Point, (SourceCoulomb.kernel (point-nuclear) : ℂ)*
    star (rawValue current i 0 spin point)*rawValue current j 0 spin point

def rawPairIntegral (current : NativeCurrent source) (i j k l : RawIndex current) (spin secondSpin : Bool) : ℂ :=
  ∫ pair : Point × Point, (SourceCoulomb.kernel (pair.1-pair.2) : ℂ)*
    star (rawValue current i 0 spin pair.1)*rawValue current j 0 spin pair.1*
    star (rawValue current k 0 secondSpin pair.2)*rawValue current l 0 secondSpin pair.2
    ∂(volume : Measure Point).prod volume

def rawCore (current : NativeCurrent source) (pose : List Body.Node) : Matrix (RawIndex current) (RawIndex current) ℂ :=
  fun i j => ((1/(2*source.electronInertia) : ℝ) : ℂ)*
      ∑ axis : Fin 3, inner ℂ (rawJet current i (Pi.single axis 1)) (rawJet current j (Pi.single axis 1))+
    ((nucleusNodes pose).map (fun nuclear => -(nuclear.particle.charge : ℂ)*
      ∑ spin : Bool, rawNuclearIntegral current i j spin (Geometry.nucleusPosition nuclear))).sum

def rawTwoBody (current : NativeCurrent source) (i j k l : RawIndex current) : ℂ :=
  ∑ spin : Bool, ∑ secondSpin : Bool, rawPairIntegral current i k j l spin secondSpin

def rawDensity (current : NativeCurrent source) (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) :=
  occupied * occupied.conjTranspose

def rawFock (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) : Matrix (RawIndex current) (RawIndex current) ℂ :=
  fun i k => rawCore current pose i k+∑ j, ∑ l,
    rawDensity current occupied l j*(rawTwoBody current i j k l-rawTwoBody current i j l k)

def rawEnergy (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) : ℝ :=
  Body.energy (nucleusNodes pose)+(Matrix.trace (rawCore current pose*rawDensity current occupied)).re+
    (1/2)*(∑ i, ∑ j, ∑ k, ∑ l, rawDensity current occupied k i*rawDensity current occupied l j*
      (rawTwoBody current i j k l-rawTwoBody current i j l k)).re

theorem raw_core_old (current : NativeCurrent source) (pose : List Body.Node) (i j : Spin source.nodes) :
    rawCore current pose (.inl i) (.inl j) = coreAt source.nodes pose source.electronInertia i j := by
  rcases i with ⟨i,spin⟩
  rcases j with ⟨j,otherSpin⟩
  cases spin <;> cases otherSpin <;>
    simp [rawCore,rawJet,rawNuclearIntegral,rawValue,coreAt,CPS1PhosphorylExchange.kinetic,attractionAt,
      PiLp.inner_apply,PiLp.single_apply,CPS1ElectronicSource.nuclearIntegral]
  all_goals rfl

theorem raw_two_body_old (current : NativeCurrent source) (i j k l : Spin source.nodes) :
    rawTwoBody current (.inl i) (.inl j) (.inl k) (.inl l) = twoBody source.nodes i j k l := by
  rcases i with ⟨i,si⟩
  rcases j with ⟨j,sj⟩
  rcases k with ⟨k,sk⟩
  rcases l with ⟨l,sl⟩
  cases si <;> cases sj <;> cases sk <;> cases sl <;>
    simp [rawTwoBody,rawPairIntegral,rawValue,CPS1PhosphorylExchange.twoBody,CPS1ElectronicSource.pairIntegral]

theorem raw_density_old (current : NativeCurrent source) (i j : Spin source.nodes) :
    rawDensity current (rawOccupation current) (.inl i) (.inl j) = density current.occupied i j := rfl

theorem raw_density_local_left (current : NativeCurrent source) (i : LocalIndex current) (j : RawIndex current) :
    rawDensity current (rawOccupation current) (.inr i) j = 0 := by
  simp [rawDensity,Matrix.mul_apply,Matrix.conjTranspose_apply,rawOccupation]

theorem raw_density_local_right (current : NativeCurrent source) (i : RawIndex current) (j : LocalIndex current) :
    rawDensity current (rawOccupation current) i (.inr j) = 0 := by
  simp [rawDensity,Matrix.mul_apply,Matrix.conjTranspose_apply,rawOccupation]

theorem raw_fock_old (current : NativeCurrent source) (pose : List Body.Node) (i j : Spin source.nodes) :
    rawFock current pose (rawOccupation current) (.inl i) (.inl j) =
      fockAt source.nodes pose source.electronInertia current.occupied i j := by
  simp only [rawFock,Fintype.sum_sum_type,raw_density_old,raw_density_local_left,
    raw_density_local_right,zero_mul,Finset.sum_const_zero,add_zero,raw_core_old,raw_two_body_old,fockAt]

theorem current_energy_restriction (current : NativeCurrent source) (pose : List Body.Node) :
    rawEnergy current pose (rawOccupation current) =
      wholeEnergyAt source.nodes pose source.electronInertia current.occupied := by
  simp only [rawEnergy,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_sum_type,
    raw_density_old,raw_density_local_left,raw_density_local_right,mul_zero,zero_mul,
    Finset.sum_const_zero,add_zero,raw_core_old,raw_two_body_old,wholeEnergyAt]

end
end CPS1MaterialIncidence
