import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NumberAction
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

abbrev SourceFermion := ExteriorAlgebra ℂ SpinSpace

def physicalCreationMap : SpinSpace →ₗ[ℂ] Module.End ℂ SourceFermion :=
  (Algebra.lmul ℂ SourceFermion).toLinearMap.comp (ExteriorAlgebra.ι ℂ)

def physicalCreation (field : SpinSpace) : Module.End ℂ SourceFermion :=
  physicalCreationMap field

def physicalAnnihilation (field : SpinSpace) : Module.End ℂ SourceFermion :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ SpinSpace))
    (innerSL ℂ field).toLinearMap

def physicalPair (creating removing : SpinSpace) : Module.End ℂ SourceFermion :=
  (physicalCreation creating).comp (physicalAnnihilation removing)

theorem physical_creation_apply (field : SpinSpace) (state : SourceFermion) :
    physicalCreation field state = ExteriorAlgebra.ι ℂ field * state := rfl

theorem physical_annihilation_creation (first second : SpinSpace) (state : SourceFermion) :
    physicalAnnihilation first (physicalCreation second state)+
      physicalCreation second (physicalAnnihilation first state) = inner ℂ first second • state := by
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ SpinSpace))
      (innerSL ℂ first).toLinearMap (ExteriorAlgebra.ι ℂ second * state)+
        ExteriorAlgebra.ι ℂ second *
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ SpinSpace))
            (innerSL ℂ first).toLinearMap state = _
  rw [CliffordAlgebra.contractLeft_ι_mul]
  exact sub_add_cancel _ _

theorem physical_creation_pauli (field : SpinSpace) (state : SourceFermion) :
    physicalCreation field (physicalCreation field state) = 0 := by
  simp only [physical_creation_apply,← mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]

theorem physical_annihilation_pauli (field : SpinSpace) (state : SourceFermion) :
    physicalAnnihilation field (physicalAnnihilation field state) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft (innerSL ℂ field).toLinearMap state

theorem physical_creations_anticommute (first second : SpinSpace) (state : SourceFermion) :
    physicalCreation first (physicalCreation second state)+
      physicalCreation second (physicalCreation first state) = 0 := by
  simp only [physical_creation_apply,← mul_assoc,← add_mul,
    ExteriorAlgebra.ι_add_mul_swap,zero_mul]

theorem physical_creation_sum {index : Type*} (items : Finset index) (fields : index → SpinSpace) :
    physicalCreation (∑ index ∈ items, fields index) = ∑ index ∈ items, physicalCreation (fields index) :=
  map_sum physicalCreationMap _ _

theorem physical_creation_smul (scalar : ℂ) (field : SpinSpace) :
    physicalCreation (scalar • field) = scalar • physicalCreation field :=
  map_smul physicalCreationMap _ _

theorem physical_annihilation_sum {index : Type*} (items : Finset index) (fields : index → SpinSpace) :
    physicalAnnihilation (∑ index ∈ items, fields index) = ∑ index ∈ items, physicalAnnihilation (fields index) := by
  have dualSum : (innerSL ℂ (∑ index ∈ items, fields index)).toLinearMap =
      ∑ index ∈ items, (innerSL ℂ (fields index)).toLinearMap := by
    ext field
    simp only [LinearMap.sum_apply]
    change inner ℂ (∑ index ∈ items, fields index) field =
      ∑ index ∈ items, inner ℂ (fields index) field
    simp only [sum_inner]
  unfold physicalAnnihilation
  rw [dualSum]
  exact map_sum _ _ _

theorem physical_annihilation_smul (scalar : ℂ) (field : SpinSpace) :
    physicalAnnihilation (scalar • field) = star scalar • physicalAnnihilation field := by
  have dualSmul : (innerSL ℂ (scalar • field)).toLinearMap =
      star scalar • (innerSL ℂ field).toLinearMap := by
    ext other
    simp only [LinearMap.smul_apply,smul_eq_mul]
    change inner ℂ (scalar • field) other = star scalar * inner ℂ field other
    simp only [inner_smul_left,starRingEnd_apply]
  unfold physicalAnnihilation
  rw [dualSmul]
  exact map_smul _ _ _

theorem physical_creation_zero : physicalCreation (0 : SpinSpace) = 0 :=
  map_zero physicalCreationMap

theorem physical_annihilation_zero : physicalAnnihilation (0 : SpinSpace) = 0 := by
  unfold physicalAnnihilation
  have zeroDual : (innerSL ℂ (0 : SpinSpace)).toLinearMap = 0 := by
    ext other
    simp
  rw [zeroDual,map_zero]

theorem physical_pair_first (creating removing field : SpinSpace) (state : SourceFermion) :
    physicalPair creating removing (ExteriorAlgebra.ι ℂ field * state) =
      inner ℂ removing field • (ExteriorAlgebra.ι ℂ creating * state)+
        ExteriorAlgebra.ι ℂ field * physicalPair creating removing state := by
  change ExteriorAlgebra.ι ℂ creating *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ SpinSpace))
        (innerSL ℂ removing).toLinearMap (ExteriorAlgebra.ι ℂ field * state) = _
  rw [CliffordAlgebra.contractLeft_ι_mul,mul_sub,mul_smul_comm]
  have swap : ExteriorAlgebra.ι ℂ creating * ExteriorAlgebra.ι ℂ field =
      -(ExteriorAlgebra.ι ℂ field * ExteriorAlgebra.ι ℂ creating) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap creating field)
  rw [← mul_assoc,swap,neg_mul,sub_neg_eq_add,mul_assoc]
  rfl

theorem physical_pair_one (creating removing : SpinSpace) : physicalPair creating removing 1 = 0 := by
  unfold physicalPair physicalAnnihilation
  rw [LinearMap.comp_apply,CliffordAlgebra.contractLeft_one,map_zero]

theorem physical_pair_square (field : SpinSpace) (state : SourceFermion) :
    physicalPair field field (physicalPair field field state) =
      inner ℂ field field • physicalPair field field state := by
  have contract := physical_annihilation_creation field field (physicalAnnihilation field state)
  rw [physical_annihilation_pauli,map_zero,add_zero] at contract
  change physicalCreation field
    (physicalAnnihilation field (physicalCreation field (physicalAnnihilation field state))) = _
  rw [contract,map_smul]
  rfl

def sourceModeNumber (current : NativeCurrent source) (index : BasisIndex current) :
    Module.End ℂ SourceFermion := physicalPair (basis current index) (basis current index)

theorem source_mode_number_idempotent (current : NativeCurrent source) (index : BasisIndex current) :
    (sourceModeNumber current index).comp (sourceModeNumber current index) = sourceModeNumber current index := by
  classical
  apply LinearMap.ext
  intro state
  change physicalPair (basis current index) (basis current index)
    (physicalPair (basis current index) (basis current index) state) =
      physicalPair (basis current index) (basis current index) state
  rw [physical_pair_square]
  have unitInner : inner ℂ (basis current index) (basis current index) = 1 := by
    simpa using (orthonormal_iff_ite.mp (basis_orthonormal current)) index index
  rw [unitInner,one_smul]

theorem source_mode_creation_integer (current : NativeCurrent source) (index creating : BasisIndex current)
    (state : SourceFermion) :
    sourceModeNumber current index (physicalCreation (basis current creating) state)-
      physicalCreation (basis current creating) (sourceModeNumber current index state) =
        (if index = creating then (1 : ℂ) else 0) • physicalCreation (basis current creating) state := by
  classical
  have pairInner := (orthonormal_iff_ite.mp (basis_orthonormal current)) index creating
  change physicalPair (basis current index) (basis current index)
      (ExteriorAlgebra.ι ℂ (basis current creating) * state)-
        ExteriorAlgebra.ι ℂ (basis current creating) *
          physicalPair (basis current index) (basis current index) state = _
  rw [physical_pair_first,pairInner,add_sub_cancel_right]
  by_cases same : index = creating
  · subst creating
    rfl
  · simp only [if_neg same,zero_smul]

theorem physical_pair_annihilation (field removing : SpinSpace) (state : SourceFermion) :
    physicalPair field field (physicalAnnihilation removing state)-
      physicalAnnihilation removing (physicalPair field field state) =
        (-inner ℂ removing field) • physicalAnnihilation field state := by
  have swap : physicalAnnihilation field (physicalAnnihilation removing state) =
      -physicalAnnihilation removing (physicalAnnihilation field state) :=
    CliffordAlgebra.contractLeft_comm (innerSL ℂ field).toLinearMap (innerSL ℂ removing).toLinearMap state
  have contract := physical_annihilation_creation removing field (physicalAnnihilation field state)
  change physicalCreation field (physicalAnnihilation field (physicalAnnihilation removing state))-
      physicalAnnihilation removing (physicalCreation field (physicalAnnihilation field state)) = _
  rw [swap,map_neg]
  calc
    _ = -(physicalAnnihilation removing (physicalCreation field (physicalAnnihilation field state))+
      physicalCreation field (physicalAnnihilation removing (physicalAnnihilation field state))) := by abel
    _ = -(inner ℂ removing field • physicalAnnihilation field state) := congrArg Neg.neg contract
    _ = _ := (neg_smul _ _).symm

theorem source_mode_annihilation_integer (current : NativeCurrent source) (index removing : BasisIndex current)
    (state : SourceFermion) :
    sourceModeNumber current index (physicalAnnihilation (basis current removing) state)-
      physicalAnnihilation (basis current removing) (sourceModeNumber current index state) =
        (-(if index = removing then (1 : ℂ) else 0)) • physicalAnnihilation (basis current removing) state := by
  classical
  change physicalPair (basis current index) (basis current index) (physicalAnnihilation (basis current removing) state)-
    physicalAnnihilation (basis current removing) (physicalPair (basis current index) (basis current index) state) = _
  rw [physical_pair_annihilation]
  have pairInner := (orthonormal_iff_ite.mp (basis_orthonormal current)) removing index
  by_cases same : index = removing
  · subst removing
    simp only [pairInner]
  · simp only [pairInner,if_neg same,if_neg (Ne.symm same),neg_zero,zero_smul]

theorem source_mode_pair_integer (current : NativeCurrent source) (index creating removing : BasisIndex current)
    (state : SourceFermion) :
    sourceModeNumber current index (physicalPair (basis current creating) (basis current removing) state)-
      physicalPair (basis current creating) (basis current removing) (sourceModeNumber current index state) =
        ((if index = creating then (1 : ℂ) else 0)-(if index = removing then (1 : ℂ) else 0)) •
          physicalPair (basis current creating) (basis current removing) state := by
  classical
  have creation := (sub_eq_iff_eq_add).mp
    (source_mode_creation_integer current index creating (physicalAnnihilation (basis current removing) state))
  have removal := (sub_eq_iff_eq_add).mp (source_mode_annihilation_integer current index removing state)
  change sourceModeNumber current index
      (physicalCreation (basis current creating) (physicalAnnihilation (basis current removing) state))-
        physicalCreation (basis current creating)
          (physicalAnnihilation (basis current removing) (sourceModeNumber current index state)) = _
  rw [creation,removal,map_add,map_smul]
  simp only [sub_smul,neg_smul]
  change _ = (if index = creating then (1 : ℂ) else 0) •
      physicalCreation (basis current creating) (physicalAnnihilation (basis current removing) state)-
    (if index = removing then (1 : ℂ) else 0) •
      physicalCreation (basis current creating) (physicalAnnihilation (basis current removing) state)
  abel

def sourceModeDelta (current : NativeCurrent source) (index creating removing : BasisIndex current) : ℤ :=
  (if index = creating then 1 else 0)-(if index = removing then 1 else 0)

theorem source_mode_delta_total (current : NativeCurrent source) (creating removing : BasisIndex current) :
    ∑ index, sourceModeDelta current index creating removing = 0 := by
  classical
  simp [sourceModeDelta,Finset.sum_sub_distrib]

theorem source_mode_pair_delta (current : NativeCurrent source) (index creating removing : BasisIndex current)
    (state : SourceFermion) :
    sourceModeNumber current index (physicalPair (basis current creating) (basis current removing) state)-
      physicalPair (basis current creating) (basis current removing) (sourceModeNumber current index state) =
        (sourceModeDelta current index creating removing : ℂ) •
          physicalPair (basis current creating) (basis current removing) state := by
  simpa only [sourceModeDelta,Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using
    source_mode_pair_integer current index creating removing state

theorem raw_field_coordinates (current : NativeCurrent source) (relation : CoordinateSpace current) :
    rawSynthesis current relation =
      ∑ index, (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) *ᵥ relation) index •
        basis current index := by
  classical
  rw [raw_synthesis_apply]
  have represented (rawIndex : RawIndex current) : rawField current rawIndex =
      ∑ index, CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) index rawIndex •
        basis current index :=
    CPS1MolecularFrame.FiniteNormed.raw_synthesis (rawField current) rawIndex
  simp_rw [represented]
  simp only [Finset.smul_sum,smul_smul,Matrix.mulVec,dotProduct,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro rawIndex _
  rw [mul_comm]

theorem source_null_field (current : NativeCurrent source) (relation : CoordinateSpace current)
    (null : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) *ᵥ relation = 0) :
    rawSynthesis current relation = 0 := by
  rw [raw_field_coordinates,null]
  simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero]

theorem source_null_creation (current : NativeCurrent source) (relation : CoordinateSpace current)
    (null : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) *ᵥ relation = 0) :
    ∑ index, relation index • physicalCreation (rawField current index) = 0 := by
  simp_rw [← physical_creation_smul]
  rw [← physical_creation_sum,← raw_synthesis_apply current relation]
  rw [source_null_field current relation null,physical_creation_zero]

theorem source_null_annihilation (current : NativeCurrent source) (relation : CoordinateSpace current)
    (null : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current) *ᵥ relation = 0) :
    ∑ index, star (relation index) • physicalAnnihilation (rawField current index) = 0 := by
  simp_rw [← physical_annihilation_smul]
  rw [← physical_annihilation_sum,← raw_synthesis_apply current relation]
  rw [source_null_field current relation null,physical_annihilation_zero]

def effectiveSourceFock (current : NativeCurrent source) : Matrix (RawIndex current) (RawIndex current) ℂ :=
  fun creating removing => ∑ pair : BasisIndex current × BasisIndex current,
    sourceCoefficient current creating pair.1 * jointFock current current.nodes pair.1 pair.2 *
      star (sourceCoefficient current removing pair.2)

theorem effective_source_fock_matrix (current : NativeCurrent source) :
    effectiveSourceFock current =
      sourceCoefficient current * jointFock current current.nodes * (sourceCoefficient current).conjTranspose := by
  ext creating removing
  simp only [effectiveSourceFock,Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

def physicalFock (current : NativeCurrent source) : SpinSpace →ₗ[ℂ] SpinSpace :=
  ∑ pair : BasisIndex current × BasisIndex current,
    jointFock current current.nodes pair.1 pair.2 •
      (innerSL ℂ (basis current pair.2)).toLinearMap.smulRight (basis current pair.1)

def fullFockCAR (current : NativeCurrent source) : Module.End ℂ SourceFermion :=
  ∑ pair : BasisIndex current × BasisIndex current,
    jointFock current current.nodes pair.1 pair.2 • physicalPair (basis current pair.1) (basis current pair.2)

def sourceFockCAR (current : NativeCurrent source) : Module.End ℂ SourceFermion :=
  ∑ pair : RawIndex current × RawIndex current,
    effectiveSourceFock current pair.1 pair.2 •
      physicalPair (rawField current pair.1) (rawField current pair.2)

theorem physical_fock_fields (current : NativeCurrent source)
    (occupied : Matrix (BasisIndex current) (Electron source.nodes) ℂ) (slot : Electron source.nodes) :
    physicalFock current (CPS1ElectronicEvolution.fields (basis current) occupied slot) =
      CPS1ElectronicEvolution.fields (basis current) (jointFock current current.nodes * occupied) slot := by
  simp only [physicalFock,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.smulRight_apply]
  change (∑ pair : BasisIndex current × BasisIndex current,
    jointFock current current.nodes pair.1 pair.2 •
      (inner ℂ (basis current pair.2) (CPS1ElectronicEvolution.fields (basis current) occupied slot) •
        basis current pair.1)) = _
  rw [Fintype.sum_prod_type]
  simp only [CPS1ElectronicEvolution.fields,
    (basis_orthonormal current).inner_right_fintype,Matrix.mul_apply,smul_smul,Finset.sum_smul]

theorem actual_field_midpoint (current : NativeCurrent source) (time : ℝ) (slot : Electron source.nodes) :
    let after := CPS1ElectronicEvolution.fields (rawField current) (updatedRaw current time) slot
    after+(Complex.I*((time/2 : ℝ) : ℂ)) • physicalFock current after =
      currentField current slot-(Complex.I*((time/2 : ℝ) : ℂ)) • physicalFock current (currentField current slot) := by
  dsimp only
  have matrix := congrArg (fun operator => operator * coordinates current)
    (CPS1ElectronicEvolution.actual_equation (jointFock current current.nodes)
      (joint_fock_hermitian current current.nodes) (time/2))
  have paid : updatedCoordinates current time+(Complex.I*((time/2 : ℝ) : ℂ)) •
      (jointFock current current.nodes * updatedCoordinates current time) =
      coordinates current-(Complex.I*((time/2 : ℝ) : ℂ)) •
        (jointFock current current.nodes * coordinates current) := by
    simpa only [updatedCoordinates,CPS1ElectronicEvolution.denominator,CPS1ElectronicEvolution.generator,
      Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.mul_assoc,
      CPS1ElectronicEvolution.occupiedUpdate] using matrix
  have fields := congrArg (fun occupied => CPS1ElectronicEvolution.fields (basis current) occupied slot) paid
  rw [CPS1ElectronicSource.fields_add,CPS1ElectronicSource.fields_sub,
    CPS1ElectronicSource.fields_smul,CPS1ElectronicSource.fields_smul] at fields
  rw [updated_raw_increment,raw_increment_fields]
  rw [← current_coordinates current,physical_fock_fields,physical_fock_fields]
  exact fields

theorem physical_pair_basis (current : NativeCurrent source) (first second : BasisIndex current) :
    physicalPair (basis current first) (basis current second) =
      ∑ pair : RawIndex current × RawIndex current,
        (sourceCoefficient current pair.1 first * star (sourceCoefficient current pair.2 second)) •
          physicalPair (rawField current pair.1) (rawField current pair.2) := by
  classical
  have represented (index : BasisIndex current) : basis current index =
      ∑ rawIndex, sourceCoefficient current rawIndex index • rawField current rawIndex :=
    CPS1MolecularFrame.FiniteNormed.field_synthesis (rawField current) index
  unfold physicalPair
  rw [represented first,represented second,physical_creation_sum,physical_annihilation_sum]
  simp_rw [physical_creation_smul,physical_annihilation_smul]
  apply LinearMap.ext
  intro state
  simp only [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  rw [Fintype.sum_prod_type]
  simp only [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro creating _
  apply Finset.sum_congr rfl
  intro removing _
  rw [mul_comm]

theorem source_fock_car_exact (current : NativeCurrent source) : sourceFockCAR current = fullFockCAR current := by
  classical
  symm
  calc
    fullFockCAR current =
        ∑ pair : BasisIndex current × BasisIndex current, ∑ rawPair : RawIndex current × RawIndex current,
          (jointFock current current.nodes pair.1 pair.2 *
            (sourceCoefficient current rawPair.1 pair.1 * star (sourceCoefficient current rawPair.2 pair.2))) •
              physicalPair (rawField current rawPair.1) (rawField current rawPair.2) := by
      unfold fullFockCAR
      simp_rw [physical_pair_basis]
      simp only [Finset.smul_sum,smul_smul]
    _ = ∑ rawPair : RawIndex current × RawIndex current, ∑ pair : BasisIndex current × BasisIndex current,
          (jointFock current current.nodes pair.1 pair.2 *
            (sourceCoefficient current rawPair.1 pair.1 * star (sourceCoefficient current rawPair.2 pair.2))) •
              physicalPair (rawField current rawPair.1) (rawField current rawPair.2) := Finset.sum_comm
    _ = sourceFockCAR current := by
      unfold sourceFockCAR effectiveSourceFock
      apply Finset.sum_congr rfl
      intro rawPair _
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro pair _
      congr 1
      ring

theorem physical_number_source_action (current : NativeCurrent source) (index : BasisIndex current)
    (state : SourceFermion) :
    sourceModeNumber current index (sourceFockCAR current state)-
      sourceFockCAR current (sourceModeNumber current index state) =
        ∑ pair : BasisIndex current × BasisIndex current,
          (jointFock current current.nodes pair.1 pair.2 * (sourceModeDelta current index pair.1 pair.2 : ℂ)) •
            physicalPair (basis current pair.1) (basis current pair.2) state := by
  rw [source_fock_car_exact]
  simp only [fullFockCAR,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  rw [← smul_sub,source_mode_pair_delta,smul_smul]

theorem full_fock_car_one (current : NativeCurrent source) : fullFockCAR current 1 = 0 := by
  simp only [fullFockCAR,LinearMap.sum_apply,LinearMap.smul_apply,
    physical_pair_one,smul_zero,Finset.sum_const_zero]

theorem full_fock_car_first (current : NativeCurrent source) (field : SpinSpace) (state : SourceFermion) :
    fullFockCAR current (ExteriorAlgebra.ι ℂ field * state) =
      ExteriorAlgebra.ι ℂ (physicalFock current field) * state+
        ExteriorAlgebra.ι ℂ field * fullFockCAR current state := by
  simp only [fullFockCAR,LinearMap.sum_apply,LinearMap.smul_apply,physical_pair_first,
    smul_add,Finset.sum_add_distrib]
  simp only [physicalFock,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.smulRight_apply]
  rw [map_sum]
  simp only [map_smul,smul_smul,Finset.sum_mul,Finset.mul_sum]
  apply congrArg₂ (fun first second : SourceFermion => first+second)
  · apply Finset.sum_congr rfl
    intro pair _
    rw [smul_mul_assoc]
    simp only [ContinuousLinearMap.coe_coe,innerSL_apply_apply]
  · apply Finset.sum_congr rfl
    intro pair _
    rw [mul_smul_comm]

theorem full_fock_car_wedge (current : NativeCurrent source) (count : Nat) (fields : Fin count → SpinSpace) :
    fullFockCAR current (ExteriorAlgebra.ιMulti ℂ count fields) =
      ∑ slot, ExteriorAlgebra.ιMulti ℂ count (Function.update fields slot (physicalFock current (fields slot))) := by
  classical
  induction count with
  | zero => simp only [ExteriorAlgebra.ιMulti_zero_apply,full_fock_car_one,Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ count ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply,full_fock_car_first,ih]
    have head : ExteriorAlgebra.ιMulti ℂ (count+1)
        (Function.update fields 0 (physicalFock current (fields 0))) =
        ExteriorAlgebra.ι ℂ (physicalFock current (fields 0)) *
          ExteriorAlgebra.ιMulti ℂ count (Matrix.vecTail fields) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 1
    have tail (slot : Fin count) : ExteriorAlgebra.ιMulti ℂ (count+1)
        (Function.update fields slot.succ (physicalFock current (fields slot.succ))) =
        ExteriorAlgebra.ι ℂ (fields 0) *
          ExteriorAlgebra.ιMulti ℂ count
            (Function.update (Matrix.vecTail fields) slot (physicalFock current (Matrix.vecTail fields slot))) := by
      have atHead : Function.update fields slot.succ
          (physicalFock current (fields slot.succ)) 0 = fields 0 := rfl
      have tailUpdate : Matrix.vecTail
          (Function.update fields slot.succ (physicalFock current (fields slot.succ))) =
          Function.update (Matrix.vecTail fields) slot (physicalFock current (Matrix.vecTail fields slot)) := by
        funext index
        by_cases same : index = slot
        · subst index
          simp [Matrix.vecTail]
        · simp [Matrix.vecTail,Fin.succ_inj,same]
      rw [ExteriorAlgebra.ιMulti_succ_apply,atHead,tailUpdate]
    rw [Fin.sum_univ_succ,head]
    simp_rw [tail]
    rw [Finset.mul_sum]

def actualSourceSlater (current : NativeCurrent source) : SourceFermion :=
  ExteriorAlgebra.ιMulti ℂ (electronCount source.nodes) (currentField current)

theorem actual_source_fock_action (current : NativeCurrent source) :
    sourceFockCAR current (actualSourceSlater current) =
      ∑ slot : Electron source.nodes, ExteriorAlgebra.ιMulti ℂ (electronCount source.nodes)
        (Function.update (currentField current) slot (physicalFock current (currentField current slot))) := by
  rw [source_fock_car_exact]
  exact full_fock_car_wedge current _ _

theorem source_fock_degree (current : NativeCurrent source) :
    sourceFockCAR current (actualSourceSlater current) ∈
      (⋀[ℂ]^(electronCount source.nodes) SpinSpace) := by
  rw [actual_source_fock_action]
  apply Submodule.sum_mem
  intro slot _
  exact ExteriorAlgebra.ιMulti_range ℂ _ (Set.mem_range_self _)

structure SourceCARMonomial (current : NativeCurrent source) where
  creating : RawIndex current
  removing : RawIndex current
  coefficient : ℂ

def SourceCARMonomial.operator {current : NativeCurrent source} (term : SourceCARMonomial current) :
    Module.End ℂ SourceFermion :=
  term.coefficient • physicalPair (rawField current term.creating) (rawField current term.removing)

def SourceCARMonomial.origins {current : NativeCurrent source} (term : SourceCARMonomial current) :=
  (rawOrigin current term.creating,rawOrigin current term.removing)

def sourceCARWord (current : NativeCurrent source) : List (SourceCARMonomial current) :=
  (Finset.univ : Finset (RawIndex current × RawIndex current)).toList.map (fun pair =>
    ⟨pair.1,pair.2,effectiveSourceFock current pair.1 pair.2⟩)

theorem source_car_word_actual (current : NativeCurrent source) (term : SourceCARMonomial current)
    (held : term ∈ sourceCARWord current) :
    term.coefficient = effectiveSourceFock current term.creating term.removing := by
  obtain ⟨pair,_,same⟩ := List.mem_map.mp held
  subst term
  rfl

theorem source_car_word_operator (current : NativeCurrent source) :
    ((sourceCARWord current).map SourceCARMonomial.operator).sum = sourceFockCAR current := by
  simp only [sourceCARWord,List.map_map,Function.comp_def,SourceCARMonomial.operator]
  rw [Finset.sum_map_toList]
  rfl

theorem source_car_word_physical (current : NativeCurrent source) :
    ((sourceCARWord current).map SourceCARMonomial.operator).sum = fullFockCAR current :=
  (source_car_word_operator current).trans (source_fock_car_exact current)

end
end CPS1MaterialIncidence
