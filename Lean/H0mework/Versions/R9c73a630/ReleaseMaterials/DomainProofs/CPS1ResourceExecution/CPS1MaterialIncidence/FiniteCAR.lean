import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeIncidence
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

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

abbrev AtomCoordinateSpace (current : NativeCurrent source) := AddressedBasisIndex current → ℂ
abbrev AtomConfiguration (current : NativeCurrent source) :=
  Set.powersetCard (AddressedBasisIndex current) (electronCount source.nodes)
abbrev AtomNumberSpace (current : NativeCurrent source) :=
  ExteriorAlgebra.exteriorPower ℂ (electronCount source.nodes) (AtomCoordinateSpace current)

instance addressedIndexLinearOrder (current : NativeCurrent source) : LinearOrder (AddressedBasisIndex current) :=
  LinearOrder.lift' (Fintype.equivFin (AddressedBasisIndex current)) (Fintype.equivFin _).injective

def atomCoordinateBasis (current : NativeCurrent source) :
    Module.Basis (AddressedBasisIndex current) ℂ (AtomCoordinateSpace current) := Pi.basisFun ℂ _

def atomNumberBasis (current : NativeCurrent source) :
    Module.Basis (AtomConfiguration current) ℂ (AtomNumberSpace current) :=
  (atomCoordinateBasis current).exteriorPower (electronCount source.nodes)

def configurationModes (current : NativeCurrent source) (configuration : AtomConfiguration current) :
    List (AddressedBasisIndex current) := List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm configuration)

theorem configuration_modes_nodup (current : NativeCurrent source) (configuration : AtomConfiguration current) :
    (configurationModes current configuration).Nodup :=
  List.nodup_ofFn.mpr (Set.powersetCard.ofFinEmbEquiv.symm configuration).injective

theorem configuration_modes_length (current : NativeCurrent source) (configuration : AtomConfiguration current) :
    (configurationModes current configuration).length = electronCount source.nodes := by
  simp only [configurationModes,List.length_ofFn]

theorem configuration_modes_mem (current : NativeCurrent source) (configuration : AtomConfiguration current)
    (mode : AddressedBasisIndex current) : mode ∈ configurationModes current configuration ↔ mode ∈ configuration.val := by
  rw [configurationModes,List.mem_ofFn']
  exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem configuration mode

def addressedSynthesis (current : NativeCurrent source) : AtomCoordinateSpace current →ₗ[ℂ] SpinSpace :=
  ∑ mode, (LinearMap.proj mode : AtomCoordinateSpace current →ₗ[ℂ] ℂ).smulRight (addressedBasis current mode)

theorem addressed_synthesis_apply (current : NativeCurrent source) (vector : AtomCoordinateSpace current) :
    addressedSynthesis current vector = ∑ mode, vector mode • addressedBasis current mode := by
  simp only [addressedSynthesis,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply]

theorem addressed_synthesis_basis (current : NativeCurrent source) (mode : AddressedBasisIndex current) :
    addressedSynthesis current (atomCoordinateBasis current mode) = addressedBasis current mode := by
  classical
  simp [addressed_synthesis_apply,atomCoordinateBasis,Pi.basisFun_apply]

def atomNumberSynthesis (current : NativeCurrent source) : AtomNumberSpace current →ₗ[ℂ] SourceFermion :=
  (Submodule.subtype (ExteriorAlgebra.exteriorPower ℂ (electronCount source.nodes) SpinSpace)).comp
    (exteriorPower.map (electronCount source.nodes) (addressedSynthesis current))

def creationModes (current : NativeCurrent source) : List (AddressedBasisIndex current) → Module.End ℂ SourceFermion
  | [] => LinearMap.id
  | mode :: rest => (physicalCreation (addressedBasis current mode)).comp (creationModes current rest)

def annihilationModes (current : NativeCurrent source) : List (AddressedBasisIndex current) → Module.End ℂ SourceFermion
  | [] => LinearMap.id
  | mode :: rest => (annihilationModes current rest).comp (physicalAnnihilation (addressedBasis current mode))

def configurationSlater (current : NativeCurrent source) (configuration : AtomConfiguration current) : SourceFermion :=
  creationModes current (configurationModes current configuration) 1

theorem creation_modes_product (current : NativeCurrent source) (modes : List (AddressedBasisIndex current)) :
    creationModes current modes 1 = (modes.map (fun mode => ExteriorAlgebra.ι ℂ (addressedBasis current mode))).prod := by
  induction modes with
  | nil => rfl
  | cons mode rest ih =>
    change ExteriorAlgebra.ι ℂ (addressedBasis current mode) * creationModes current rest 1 = _
    rw [ih]
    rfl

theorem atom_number_basis_physical (current : NativeCurrent source) (configuration : AtomConfiguration current) :
    atomNumberSynthesis current (atomNumberBasis current configuration) = configurationSlater current configuration := by
  rw [atomNumberBasis,exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  simp only [atomNumberSynthesis,LinearMap.comp_apply,exteriorPower.map_apply_ιMulti,
    Submodule.subtype_apply,Function.comp_def,addressed_synthesis_basis]
  rw [configurationSlater,creation_modes_product,exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_apply]
  simp only [configurationModes]
  congr 1
  exact List.ofFn_comp' (Set.powersetCard.ofFinEmbEquiv.symm configuration)
    (fun mode => ExteriorAlgebra.ι ℂ (addressedBasis current mode))

private theorem annihilation_missing (current : NativeCurrent source) (mode : AddressedBasisIndex current)
    (modes : List (AddressedBasisIndex current)) (missing : mode ∉ modes) :
    physicalAnnihilation (addressedBasis current mode) (creationModes current modes 1) = 0 := by
  induction modes with
  | nil =>
    exact CliffordAlgebra.contractLeft_one _ _
  | cons first rest ih =>
    have different : mode ≠ first := fun same => missing (List.mem_cons.mpr (.inl same))
    have absent : mode ∉ rest := fun held => missing (List.mem_cons_of_mem _ held)
    have cross : inner ℂ (addressedBasis current mode) (addressedBasis current first) = 0 :=
      (orthonormal_iff_ite.mp (addressed_basis_orthonormal current) mode first).trans (if_neg different)
    have law := physical_annihilation_creation (addressedBasis current mode) (addressedBasis current first)
      (creationModes current rest 1)
    rw [cross,ih absent,map_zero,add_zero,zero_smul] at law
    exact law

private theorem annihilation_word_killed (current : NativeCurrent source)
    (mode : AddressedBasisIndex current) (modes : List (AddressedBasisIndex current))
    (held : mode ∈ modes) (state : SourceFermion)
    (killed : physicalAnnihilation (addressedBasis current mode) state = 0) :
    annihilationModes current modes state = 0 := by
  induction modes generalizing state with
  | nil => cases held
  | cons first rest ih =>
    rcases List.mem_cons.mp held with same | later
    · subst first
      change annihilationModes current rest (physicalAnnihilation (addressedBasis current mode) state) = 0
      rw [killed,map_zero]
    · have commute : physicalAnnihilation (addressedBasis current mode)
          (physicalAnnihilation (addressedBasis current first) state) =
          -physicalAnnihilation (addressedBasis current first)
            (physicalAnnihilation (addressedBasis current mode) state) :=
        CliffordAlgebra.contractLeft_comm (innerSL ℂ (addressedBasis current mode)).toLinearMap
          (innerSL ℂ (addressedBasis current first)).toLinearMap state
      rw [killed,map_zero,neg_zero] at commute
      exact ih later _ commute

private theorem annihilation_creation_modes (current : NativeCurrent source)
    (modes : List (AddressedBasisIndex current)) (unique : modes.Nodup) :
    annihilationModes current modes (creationModes current modes 1) = 1 := by
  induction modes with
  | nil => rfl
  | cons first rest ih =>
    have paid := List.nodup_cons.mp unique
    have unitInner : inner ℂ (addressedBasis current first) (addressedBasis current first) = 1 := by
      simpa using (orthonormal_iff_ite.mp (addressed_basis_orthonormal current)) first first
    have head := physical_annihilation_creation (addressedBasis current first) (addressedBasis current first)
      (creationModes current rest 1)
    rw [annihilation_missing current first rest paid.1,map_zero,add_zero,unitInner,one_smul] at head
    change annihilationModes current rest
      (physicalAnnihilation (addressedBasis current first)
        (physicalCreation (addressedBasis current first) (creationModes current rest 1))) = 1
    rw [head]
    exact ih paid.2

def normalCAROperator (current : NativeCurrent source) (after previous : AtomConfiguration current) :
    Module.End ℂ SourceFermion :=
  (creationModes current (configurationModes current after)).comp
    (annihilationModes current (configurationModes current previous))

inductive SourceCARSymbol (current : NativeCurrent source)
  | creating (mode : AddressedBasisIndex current)
  | annihilating (mode : AddressedBasisIndex current)

def SourceCARSymbol.operator {current : NativeCurrent source} : SourceCARSymbol current → Module.End ℂ SourceFermion
  | .creating mode => physicalCreation (addressedBasis current mode)
  | .annihilating mode => physicalAnnihilation (addressedBasis current mode)

def SourceCARSymbol.charge {current : NativeCurrent source} : SourceCARSymbol current → Charges cursor
  | .creating mode => -Finsupp.single (sectorOrigin current mode.1) 1
  | .annihilating mode => Finsupp.single (sectorOrigin current mode.1) 1

def evaluateCARWord {current : NativeCurrent source} : List (SourceCARSymbol current) → Module.End ℂ SourceFermion
  | [] => LinearMap.id
  | symbol :: rest => symbol.operator.comp (evaluateCARWord rest)

def normalCARWord (current : NativeCurrent source) (after previous : AtomConfiguration current) : List (SourceCARSymbol current) :=
  (configurationModes current after).map SourceCARSymbol.creating ++
    (configurationModes current previous).reverse.map SourceCARSymbol.annihilating

theorem evaluate_car_word_append {current : NativeCurrent source}
    (first second : List (SourceCARSymbol current)) :
    evaluateCARWord (first++second) = (evaluateCARWord first).comp (evaluateCARWord second) := by
  induction first with
  | nil => rfl
  | cons symbol rest ih =>
    simp only [List.cons_append,evaluateCARWord,ih,LinearMap.comp_assoc]

theorem evaluate_normal_car_word (current : NativeCurrent source) (after previous : AtomConfiguration current) :
    evaluateCARWord (normalCARWord current after previous) = normalCAROperator current after previous := by
  have creating (modes : List (AddressedBasisIndex current)) :
      evaluateCARWord (modes.map SourceCARSymbol.creating) = creationModes current modes := by
    induction modes with
    | nil => rfl
    | cons mode rest ih =>
      simp only [List.map_cons,evaluateCARWord,SourceCARSymbol.operator,creationModes,ih]
  have annihilating (modes : List (AddressedBasisIndex current)) :
      evaluateCARWord (modes.reverse.map SourceCARSymbol.annihilating) = annihilationModes current modes := by
    induction modes with
    | nil => rfl
    | cons mode rest ih =>
      rw [List.reverse_cons,List.map_append,evaluate_car_word_append,ih]
      rfl
  rw [normalCARWord,evaluate_car_word_append,creating,annihilating]
  rfl

theorem addressed_basis_atom_projection (current : NativeCurrent source) (observed : AtomSector source)
    (mode : AddressedBasisIndex current) :
    atomFieldProjection current observed (addressedBasis current mode) =
      if observed = mode.1 then addressedBasis current mode else 0 := by
  classical
  rcases mode with ⟨atom,index⟩
  by_cases same : observed = atom
  · subst observed
    simp only [atomFieldProjection,LinearMap.sum_apply,LinearMap.smulRight_apply,addressedBasis]
    change (∑ other, inner ℂ (atomBasis current atom other) (atomBasis current atom index) • atomBasis current atom other) =
      atomBasis current atom index
    simp only [(orthonormal_iff_ite.mp (atom_basis_orthonormal current atom)),ite_smul,
      one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  · simp only [if_neg same,atomFieldProjection,LinearMap.sum_apply,LinearMap.smulRight_apply,addressedBasis]
    apply Finset.sum_eq_zero
    intro other _
    change inner ℂ (atomBasis current observed other) (atomBasis current atom index) • atomBasis current observed other = 0
    rw [atom_bases_cross_inner current observed atom same other index,zero_smul]

theorem source_car_symbol_atom_charge {current : NativeCurrent source} (symbol : SourceCARSymbol current)
    (observed : AtomSector source) (state : SourceFermion) :
    atomNumber current observed (symbol.operator state)-symbol.operator (atomNumber current observed state) =
      (-(symbol.charge (sectorOrigin current observed)) : ℂ) • symbol.operator state := by
  classical
  have originEqual (first second : AtomSector source) :
      sectorOrigin current first = sectorOrigin current second ↔ first = second :=
    (source_origin_injective source).eq_iff
  cases symbol with
  | creating mode =>
    rw [SourceCARSymbol.operator,atom_number_creation,addressed_basis_atom_projection]
    by_cases same : observed = mode.1
    · simp [SourceCARSymbol.charge,same]
    · simp [SourceCARSymbol.charge,same,originEqual,physical_creation_zero]
  | annihilating mode =>
    rw [SourceCARSymbol.operator,atom_number_annihilation,addressed_basis_atom_projection]
    by_cases same : observed = mode.1
    · simp [SourceCARSymbol.charge,same]
    · simp [SourceCARSymbol.charge,same,originEqual,physical_annihilation_zero]

theorem source_car_word_atom_charge {current : NativeCurrent source}
    (word : List (SourceCARSymbol current)) (observed : AtomSector source) (state : SourceFermion) :
    atomNumber current observed (evaluateCARWord word state)-evaluateCARWord word (atomNumber current observed state) =
      (-((word.map SourceCARSymbol.charge).sum (sectorOrigin current observed)) : ℂ) • evaluateCARWord word state := by
  induction word generalizing state with
  | nil => simp only [evaluateCARWord,LinearMap.id_apply,sub_self,List.map_nil,List.sum_nil,Finsupp.zero_apply,
      neg_zero,Int.cast_zero,zero_smul]
  | cons symbol rest ih =>
    change atomNumber current observed (symbol.operator (evaluateCARWord rest state))-
      symbol.operator (evaluateCARWord rest (atomNumber current observed state)) = _
    calc
      _ = (atomNumber current observed (symbol.operator (evaluateCARWord rest state))-
        symbol.operator (atomNumber current observed (evaluateCARWord rest state)))+
        symbol.operator (atomNumber current observed (evaluateCARWord rest state)-
          evaluateCARWord rest (atomNumber current observed state)) := by rw [map_sub]; abel
      _ = (-(symbol.charge (sectorOrigin current observed)) : ℂ) •
          symbol.operator (evaluateCARWord rest state)+
        (-((rest.map SourceCARSymbol.charge).sum (sectorOrigin current observed)) : ℂ) •
          symbol.operator (evaluateCARWord rest state) := by
        rw [source_car_symbol_atom_charge,ih,map_smul]
      _ = _ := by
        simp only [List.map_cons,List.sum_cons,Finsupp.add_apply,Int.cast_add,
          neg_add,evaluateCARWord,LinearMap.comp_apply,add_smul]

theorem normal_car_configuration (current : NativeCurrent source)
    (after previous input : AtomConfiguration current) :
    normalCAROperator current after previous (configurationSlater current input) =
      if previous = input then configurationSlater current after else 0 := by
  classical
  by_cases same : previous = input
  · subst input
    rw [if_pos rfl]
    unfold normalCAROperator configurationSlater
    rw [LinearMap.comp_apply,annihilation_creation_modes current _ (configuration_modes_nodup current previous)]
  · rw [if_neg same]
    obtain ⟨mode,held,missing⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne previous input).mp same
    have heldList := (configuration_modes_mem current previous mode).mpr held
    have missingList : mode ∉ configurationModes current input :=
      fun member => missing ((configuration_modes_mem current input mode).mp member)
    have killed := annihilation_word_killed current mode (configurationModes current previous) heldList
      (creationModes current (configurationModes current input) 1)
      (annihilation_missing current mode _ missingList)
    unfold normalCAROperator configurationSlater
    rw [LinearMap.comp_apply,killed,map_zero]

def atomJointEmbedding (current : NativeCurrent source) :
    Matrix (AddressedBasisIndex current) (BasisIndex current) ℂ :=
  atomCoordinates current * sourceCoefficient current

def addressedCayley (current : NativeCurrent source) (time : ℝ) :
    Matrix (AddressedBasisIndex current) (AddressedBasisIndex current) ℂ :=
  1+atomJointEmbedding current *
    (CPS1ElectronicEvolution.step (jointFock current current.nodes) (time/2)-1) * atomReadbackMatrix current

theorem addressed_cayley_zero (current : NativeCurrent source) : addressedCayley current 0 = 1 := by
  simp only [addressedCayley,zero_div,CPS1ElectronicEvolution.zero_time,sub_self,Matrix.mul_zero,
    Matrix.zero_mul,add_zero]

theorem addressed_cayley_actual (current : NativeCurrent source) (time : ℝ) :
    addressedCayley current time * atomOccupation current = atomUpdatedOccupation current time := by
  rw [addressedCayley,Matrix.add_mul,Matrix.one_mul]
  simp only [Matrix.mul_assoc]
  change atomOccupation current+atomJointEmbedding current *
    ((CPS1ElectronicEvolution.step (jointFock current current.nodes) (time/2)-1)*
      atomReadback current (atomOccupation current)) = _
  rw [atom_readback_current,Matrix.sub_mul,Matrix.one_mul]
  change atomOccupation current+atomJointEmbedding current *
    (updatedCoordinates current time-coordinates current) = _
  rw [atomJointEmbedding,Matrix.mul_assoc]
  rw [atomUpdatedOccupation,updated_raw_increment,rawIncrement,Matrix.mul_add]
  rfl

def finiteNumberState (current : NativeCurrent source)
    (occupied : Matrix (AddressedBasisIndex current) (Electron source.nodes) ℂ) : AtomNumberSpace current :=
  exteriorPower.ιMulti ℂ (electronCount source.nodes) (fun slot mode => occupied mode slot)

def finiteNumberAction (current : NativeCurrent source) (time : ℝ) :
    AtomNumberSpace current →ₗ[ℂ] AtomNumberSpace current :=
  exteriorPower.map (electronCount source.nodes) (Matrix.toLin' (addressedCayley current time))

theorem finite_number_action_actual (current : NativeCurrent source) (time : ℝ) :
    finiteNumberAction current time (finiteNumberState current (atomOccupation current)) =
      finiteNumberState current (atomUpdatedOccupation current time) := by
  rw [finiteNumberAction,finiteNumberState,exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti ℂ (electronCount source.nodes))
  funext slot mode
  have value := congrArg (fun matrix => matrix mode slot) (addressed_cayley_actual current time)
  simpa only [Function.comp_def,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Matrix.mul_apply] using value

theorem finite_number_synthesis (current : NativeCurrent source)
    (occupied : Matrix (AddressedBasisIndex current) (Electron source.nodes) ℂ) :
    atomNumberSynthesis current (finiteNumberState current occupied) =
      CPS1ElectronicEvolution.slater (CPS1ElectronicEvolution.fields (addressedBasis current) occupied) := by
  rw [atomNumberSynthesis,finiteNumberState,LinearMap.comp_apply,exteriorPower.map_apply_ιMulti]
  change (exteriorPower.ιMulti ℂ (electronCount source.nodes)
    (fun slot => addressedSynthesis current (fun mode => occupied mode slot)) : SourceFermion) =
      (exteriorPower.ιMulti ℂ (electronCount source.nodes)
        (CPS1ElectronicEvolution.fields (addressedBasis current) occupied) : SourceFermion)
  congr 1
  apply congrArg (exteriorPower.ιMulti ℂ (electronCount source.nodes))
  funext slot
  exact addressed_synthesis_apply current _

def finitePhaseTransition (current : NativeCurrent source) (time : ℝ)
    (previous after : AtomConfiguration current) : ℂ :=
  (atomNumberBasis current).repr (finiteNumberAction current time (atomNumberBasis current previous)) after

structure FiniteCARMonomial (current : NativeCurrent source) where
  previous : AtomConfiguration current
  after : AtomConfiguration current
  coefficient : ℂ

def FiniteCARMonomial.operator {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    Module.End ℂ SourceFermion := term.coefficient • normalCAROperator current term.after term.previous

def finiteSourceCARWord (current : NativeCurrent source) : List (FiniteCARMonomial current) :=
  (Finset.univ : Finset (AtomConfiguration current × AtomConfiguration current)).toList.map
    (fun pair => ⟨pair.1,pair.2,finitePhaseTransition current raw.time pair.1 pair.2⟩)

theorem finite_phase_normal_order (current : NativeCurrent source) (state : AtomNumberSpace current) :
    ((finiteSourceCARWord current).map FiniteCARMonomial.operator).sum (atomNumberSynthesis current state) =
      atomNumberSynthesis current (finiteNumberAction current raw.time state) := by
  classical
  have onBasis (configuration : AtomConfiguration current) :
      ((finiteSourceCARWord current).map FiniteCARMonomial.operator).sum
          (atomNumberSynthesis current (atomNumberBasis current configuration)) =
        atomNumberSynthesis current (finiteNumberAction current raw.time (atomNumberBasis current configuration)) := by
    rw [atom_number_basis_physical]
    simp only [finiteSourceCARWord,List.map_map,Function.comp_def,FiniteCARMonomial.operator]
    rw [Finset.sum_map_toList]
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,normal_car_configuration]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp only [smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    have expansion := congrArg (atomNumberSynthesis current)
      ((atomNumberBasis current).sum_repr (finiteNumberAction current raw.time (atomNumberBasis current configuration)))
    simpa only [map_sum,map_smul,atom_number_basis_physical,finitePhaseTransition] using expansion
  have square : (((finiteSourceCARWord current).map FiniteCARMonomial.operator).sum).comp (atomNumberSynthesis current) =
      (atomNumberSynthesis current).comp (finiteNumberAction current raw.time) :=
    (atomNumberBasis current).ext onBasis
  exact LinearMap.congr_fun square state

theorem finite_car_actual_slater (current : NativeCurrent source) :
    ((finiteSourceCARWord current).map FiniteCARMonomial.operator).sum (actualSourceSlater current) =
      CPS1ElectronicEvolution.slater
        (CPS1ElectronicEvolution.fields (addressedBasis current) (atomUpdatedOccupation current raw.time)) := by
  have same : atomNumberSynthesis current (finiteNumberState current (atomOccupation current)) =
      actualSourceSlater current := by
    rw [finite_number_synthesis,atom_occupation_wave]
    rfl
  rw [← same,finite_phase_normal_order,finite_number_action_actual,finite_number_synthesis]

def configurationElectronNumber (current : NativeCurrent source) (configuration : AtomConfiguration current)
    (atom : AtomSector source) : Nat :=
  ((configurationModes current configuration).filter (fun mode => decide (mode.1 = atom))).length

def configurationCharge (current : NativeCurrent source) (configuration : AtomConfiguration current) : Charges cursor :=
  -((configurationModes current configuration).map
    (fun mode => Finsupp.single (sectorOrigin current mode.1) (1 : ℤ))).sum

def FiniteCARMonomial.chargeDelta {current : NativeCurrent source} (term : FiniteCARMonomial current) : Charges cursor :=
  configurationCharge current term.after-configurationCharge current term.previous

def FiniteCARMonomial.word {current : NativeCurrent source} (term : FiniteCARMonomial current) : List (SourceCARSymbol current) :=
  normalCARWord current term.after term.previous

theorem finite_monomial_ordered_word {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    term.operator = term.coefficient • evaluateCARWord term.word := by
  rw [FiniteCARMonomial.word,evaluate_normal_car_word]
  rfl

theorem finite_monomial_word_charge {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    (term.word.map SourceCARSymbol.charge).sum = term.chargeDelta := by
  unfold FiniteCARMonomial.word normalCARWord FiniteCARMonomial.chargeDelta configurationCharge
  have negSum (modes : List (AddressedBasisIndex current)) :
      (modes.map (fun mode => -Finsupp.single (sectorOrigin current mode.1) (1 : ℤ))).sum =
        -(modes.map (fun mode => Finsupp.single (sectorOrigin current mode.1) (1 : ℤ))).sum := by
    induction modes with
    | nil => simp only [List.map_nil,List.sum_nil,neg_zero]
    | cons mode rest ih => simp only [List.map_cons,List.sum_cons,ih,neg_add]
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,SourceCARSymbol.charge,
    List.map_reverse,List.sum_reverse,negSum]
  abel

theorem finite_monomial_atom_charge {current : NativeCurrent source} (term : FiniteCARMonomial current)
    (observed : AtomSector source) (state : SourceFermion) :
    atomNumber current observed (term.operator state)-term.operator (atomNumber current observed state) =
      (-(term.chargeDelta (sectorOrigin current observed)) : ℂ) • term.operator state := by
  rw [finite_monomial_ordered_word]
  simp only [LinearMap.smul_apply,map_smul,← smul_sub]
  rw [source_car_word_atom_charge,finite_monomial_word_charge]
  simp only [smul_smul,mul_comm]

theorem finite_configuration_total_charge (current : NativeCurrent source) (configuration : AtomConfiguration current) :
    totalCharge (configurationCharge current configuration) = -(electronCount source.nodes : ℤ) := by
  have counted (modes : List (AddressedBasisIndex current)) :
      totalCharge ((modes.map (fun mode => Finsupp.single (sectorOrigin current mode.1) (1 : ℤ))).sum) =
        (modes.length : ℤ) := by
    induction modes with
    | nil => simp only [List.map_nil,List.sum_nil,map_zero,List.length_nil,Nat.cast_zero]
    | cons mode rest ih =>
      rw [List.map_cons,List.sum_cons,map_add,ih]
      simp only [totalCharge,chargeWeight,Finsupp.linearCombination_single,one_smul,
        List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
  rw [configurationCharge,map_neg,counted,configuration_modes_length]

theorem finite_monomial_total_charge {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    totalCharge term.chargeDelta = 0 := by
  rw [FiniteCARMonomial.chargeDelta,map_sub,finite_configuration_total_charge,finite_configuration_total_charge,sub_self]

def FiniteCARMonomial.requests {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    ChargedSourceWord cursor :=
  ((configurationModes current term.previous).zip (configurationModes current term.after)).filterMap
    (fun pair => if pair.1.1 = pair.2.1 then none else
      some (.electron (sectorOrigin current pair.1.1) (sectorOrigin current pair.2.1)))

def electronRequestDelta : ChargedInstruction cursor → Charges cursor
  | .electron donor receiver => Finsupp.single donor 1-Finsupp.single receiver 1
  | .proton .. | .deprotonate .. => 0

theorem finite_monomial_request_charge {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    (term.requests.map electronRequestDelta).sum = term.chargeDelta := by
  classical
  have paired (previous after : List (AddressedBasisIndex current)) (sameLength : previous.length = after.length) :
      ((((previous.zip after).filterMap (fun pair => if pair.1.1 = pair.2.1 then none else
          some (ChargedInstruction.electron (sectorOrigin current pair.1.1) (sectorOrigin current pair.2.1)))).map
            electronRequestDelta).sum) =
        (previous.map (fun mode => Finsupp.single (sectorOrigin current mode.1) (1 : ℤ))).sum-
          (after.map (fun mode => Finsupp.single (sectorOrigin current mode.1) (1 : ℤ))).sum := by
    induction previous generalizing after with
    | nil =>
      cases after with
      | nil => simp only [List.zip_nil_left,List.filterMap_nil,List.map_nil,List.sum_nil,sub_self]
      | cons receiver after => simp only [List.length_nil,List.length_cons] at sameLength; omega
    | cons donor previous ih =>
      cases after with
      | nil => simp only [List.length_cons,List.length_nil] at sameLength; omega
      | cons receiver after =>
        have length : previous.length = after.length := Nat.succ.inj sameLength
        by_cases same : donor.1 = receiver.1
        · simp only [List.zip_cons_cons,List.filterMap_cons,if_pos same,List.map_cons,List.sum_cons]
          rw [ih after length,same]
          abel
        · simp only [List.zip_cons_cons,List.filterMap_cons,if_neg same,List.map_cons,List.sum_cons,electronRequestDelta]
          rw [ih after length]
          abel
  rw [FiniteCARMonomial.requests,paired _ _ ((configuration_modes_length current term.previous).trans
    (configuration_modes_length current term.after).symm)]
  unfold FiniteCARMonomial.chargeDelta configurationCharge
  abel

-- Every phase term carries its complete stock calculation; this does not select a history.
def FiniteCARMonomial.stock {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    SourceChargedRun source current := runChargedWord source current term.requests

def FiniteCARMonomial.phaseTerm {current : NativeCurrent source} (term : FiniteCARMonomial current) : ℂ :=
  (atomNumberBasis current).repr (finiteNumberState current (atomOccupation current)) term.previous*term.coefficient

theorem finite_monomial_source_vertices {current : NativeCurrent source} (term : FiniteCARMonomial current)
    (instruction : ChargedInstruction cursor) (held : instruction ∈ term.requests) :
    ∃ donor receiver, instruction = .electron donor receiver ∧ donor ∈ vertices source ∧ receiver ∈ vertices source := by
  classical
  obtain ⟨pair,_,generated⟩ := List.mem_filterMap.mp held
  split at generated
  · cases generated
  · cases generated
    refine ⟨_,_,rfl,?_,?_⟩
    · exact List.mem_map.mpr ⟨source.atoms.get pair.1.1,(source.atoms.get_mem pair.1.1),rfl⟩
    · exact List.mem_map.mpr ⟨source.atoms.get pair.2.1,(source.atoms.get_mem pair.2.1),rfl⟩

theorem finite_monomial_stock_whole {current : NativeCurrent source} (term : FiniteCARMonomial current) :
    term.stock.state.whole.1 = current ∧ term.stock.state.whole.1.occupied = current.occupied ∧
      term.stock.state.whole.1.remaining = current.remaining := ⟨rfl,rfl,rfl⟩

def finiteMaterialGrade? (source : Common before step raw) (current : NativeCurrent source)
    (term : FiniteCARMonomial current) : Option (NativeIncidenceTrace source current) := by
  classical
  exact match nativeIncidence? source current with
  | .error _ => none
  | .ok trace => if term.chargeDelta = trace.selection.token.delta then some trace else none

theorem finite_material_grade_commutes (source : Common before step raw) (current : NativeCurrent source)
    (term : FiniteCARMonomial current) (trace : NativeIncidenceTrace source current)
    (actual : finiteMaterialGrade? source current term = some trace) :
    nativeIncidence? source current = .ok trace ∧
      singIncidenceBoundary (trace.after.graph.incidence-trace.before.graph.incidence) = term.chargeDelta := by
  classical
  unfold finiteMaterialGrade? at actual
  cases made : nativeIncidence? source current with
  | error residual => simp only [made,reduceCtorEq] at actual
  | ok generated =>
    simp only [made] at actual
    by_cases same : term.chargeDelta = generated.selection.token.delta
    · rw [if_pos same] at actual
      have identified := Option.some.inj actual
      subst trace
      refine ⟨rfl, ?_⟩
      calc
        singIncidenceBoundary (generated.after.graph.incidence - generated.before.graph.incidence) =
            generated.after.graph.formalCharge - generated.before.graph.formalCharge :=
          native_incidence_valence_charge generated
        _ = generated.selection.token.delta := by
          rw [native_incidence_graph]
          simp only [applyChargedToken, add_sub_cancel_left]
        _ = term.chargeDelta := same.symm
    · rw [if_neg same] at actual
      cases actual

structure FiniteCARTrace (source : Common before step raw) (current : NativeCurrent source) where
  private mk ::
  word : List (FiniteCARMonomial current)
  wordActual : word = finiteSourceCARWord current
  slaterActual : (word.map FiniteCARMonomial.operator).sum (actualSourceSlater current) =
    CPS1ElectronicEvolution.slater
      (CPS1ElectronicEvolution.fields (addressedBasis current) (atomUpdatedOccupation current raw.time))
  phaseAt : Matrix (AddressedBasisIndex current) (Electron source.nodes) ℂ
  phaseActual : phaseAt = atomUpdatedOccupation current raw.time
  phaseGram : phaseAt.conjTranspose*phaseAt = 1
  materialGrades : List (Option (NativeIncidenceTrace source current))
  gradesActual : materialGrades = word.map (finiteMaterialGrade? source current)
  stockCalculations : List (SourceChargedRun source current)
  stockActual : stockCalculations = word.map FiniteCARMonomial.stock
  atomWard : ∀ term ∈ word, ∀ observed state,
    atomNumber current observed (term.operator state)-term.operator (atomNumber current observed state) =
      (-(term.chargeDelta (sectorOrigin current observed)) : ℂ) • term.operator state
  stockGrade : ∀ term ∈ word, (term.requests.map electronRequestDelta).sum = term.chargeDelta
  numberPreserved : ∀ term ∈ word, totalCharge term.chargeDelta = 0

def finiteCARTrace (source : Common before step raw) (current : NativeCurrent source) : FiniteCARTrace source current :=
  ⟨finiteSourceCARWord current,rfl,finite_car_actual_slater current,
    atomUpdatedOccupation current raw.time,rfl,atom_updated_gram current raw.time,
    (finiteSourceCARWord current).map (finiteMaterialGrade? source current),rfl,
    (finiteSourceCARWord current).map FiniteCARMonomial.stock,rfl,
    fun term _ observed state => finite_monomial_atom_charge term observed state,
    fun term _ => finite_monomial_request_charge term,fun term _ => finite_monomial_total_charge term⟩

theorem finite_car_complete_phase (source : Common before step raw) (current : NativeCurrent source) :
    (finiteCARTrace source current).word.length =
      Fintype.card (AtomConfiguration current)*Fintype.card (AtomConfiguration current) := by
  classical
  simp only [finiteCARTrace,finiteSourceCARWord,List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_prod]

theorem finite_car_stock_internal (source : Common before step raw) (current : NativeCurrent source) :
    (finiteCARTrace source current).stockCalculations =
      (finiteCARTrace source current).word.map (fun term => runChargedWord source current term.requests) := rfl

end
end CPS1MaterialIncidence
