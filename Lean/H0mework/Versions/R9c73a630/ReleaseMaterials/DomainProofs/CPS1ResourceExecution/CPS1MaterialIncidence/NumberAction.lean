import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CommonField
import Mathlib.LinearAlgebra.ExteriorPower.Basis

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

theorem raw_nuclear_star (current : NativeCurrent source) (i j : RawIndex current) (spin : Bool) (nuclear : Point) :
    star (rawNuclearIntegral current i j spin nuclear) = rawNuclearIntegral current j i spin nuclear := by
  unfold rawNuclearIntegral
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
  ring

theorem raw_pair_star (current : NativeCurrent source) (i j k l : RawIndex current) (spin secondSpin : Bool) :
    star (rawPairIntegral current i j k l spin secondSpin) = rawPairIntegral current j i l k spin secondSpin := by
  unfold rawPairIntegral
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
  ring

theorem raw_pair_swap (current : NativeCurrent source) (i j k l : RawIndex current) (spin secondSpin : Bool) :
    rawPairIntegral current i j k l spin secondSpin = rawPairIntegral current k l i j secondSpin spin := by
  unfold rawPairIntegral
  rw [← integral_prod_swap (fun point : Point × Point =>
    (SourceCoulomb.kernel (point.1-point.2) : ℂ)*
      star (rawValue current i 0 spin point.1)*rawValue current j 0 spin point.1*
      star (rawValue current k 0 secondSpin point.2)*rawValue current l 0 secondSpin point.2)]
  apply integral_congr_ae
  filter_upwards [] with point
  dsimp only [Prod.swap]
  rw [coulomb_kernel_sub_comm point.2 point.1]
  ring

theorem raw_core_hermitian (current : NativeCurrent source) (pose : List Body.Node) :
    (rawCore current pose).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have kineticStar :
      star (((1/(2*source.electronInertia) : ℝ) : ℂ)*∑ axis : Fin 3,
        inner ℂ (rawJet current j (Pi.single axis 1)) (rawJet current i (Pi.single axis 1))) =
      ((1/(2*source.electronInertia) : ℝ) : ℂ)*∑ axis : Fin 3,
        inner ℂ (rawJet current i (Pi.single axis 1)) (rawJet current j (Pi.single axis 1)) := by
    simp only [star_mul,star_sum,Complex.star_def,Complex.conj_ofReal]
    rw [mul_comm]
    apply congrArg (fun value : ℂ => ((1/(2*source.electronInertia) : ℝ) : ℂ)*value)
    exact Finset.sum_congr rfl (fun axis _ => inner_conj_symm _ _)
  have nuclearStar :
      star (((nucleusNodes pose).map (fun nuclear => -(nuclear.particle.charge : ℂ)*
        ∑ spin : Bool, rawNuclearIntegral current j i spin (Geometry.nucleusPosition nuclear))).sum) =
      ((nucleusNodes pose).map (fun nuclear => -(nuclear.particle.charge : ℂ)*
        ∑ spin : Bool, rawNuclearIntegral current i j spin (Geometry.nucleusPosition nuclear))).sum := by
    induction nucleusNodes pose with
    | nil => simp
    | cons nuclear rest ih =>
      simp only [List.map_cons,List.sum_cons,star_add,star_mul,star_neg,star_sum,raw_nuclear_star,ih]
      have chargeReal : star (nuclear.particle.charge : ℂ) = (nuclear.particle.charge : ℂ) := by simp
      rw [chargeReal]
      ring
  exact (show star (rawCore current pose j i) = rawCore current pose i j from by
    rw [rawCore,star_add,kineticStar,nuclearStar]
    rfl)

theorem raw_two_body_star (current : NativeCurrent source) (i j k l : RawIndex current) :
    star (rawTwoBody current i j k l) = rawTwoBody current k l i j := by
  simp only [rawTwoBody,star_sum,raw_pair_star]

theorem raw_two_body_swap (current : NativeCurrent source) (i j k l : RawIndex current) :
    rawTwoBody current i j k l = rawTwoBody current j i l k := by
  unfold rawTwoBody
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro spin _
  apply Finset.sum_congr rfl
  intro secondSpin _
  exact raw_pair_swap current _ _ _ _ _ _

theorem raw_fock_hermitian (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) :
    (rawFock current pose occupied).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i k
  have coreStar : star (rawCore current pose k i) = rawCore current pose i k :=
    (raw_core_hermitian current pose).apply i k
  have densityStar (j l : RawIndex current) : star (rawDensity current occupied l j) = rawDensity current occupied j l :=
    (Matrix.isHermitian_mul_conjTranspose_self occupied).apply j l
  simp only [rawFock,star_add,star_sum,star_mul,star_sub,coreStar,densityStar,raw_two_body_star]
  rw [Finset.sum_comm]
  apply congrArg (fun value : ℂ => rawCore current pose i k+value)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [raw_two_body_swap current j i k l]
  ring

def sourceCoefficient (current : NativeCurrent source) :=
  CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (rawField current)

def jointFock (current : NativeCurrent source) (pose : List Body.Node) :=
  (sourceCoefficient current).conjTranspose * rawFock current pose (rawOccupation current) * sourceCoefficient current

theorem joint_fock_hermitian (current : NativeCurrent source) (pose : List Body.Node) :
    (jointFock current pose).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul _ (raw_fock_hermitian current pose _)

def updatedCoordinates (current : NativeCurrent source) (time : ℝ) :=
  CPS1ElectronicEvolution.occupiedUpdate (jointFock current current.nodes) (time/2) (coordinates current)

def rawIncrement (current : NativeCurrent source) (next : Matrix (BasisIndex current) (Electron source.nodes) ℂ) :=
  rawOccupation current+sourceCoefficient current*(next-coordinates current)

theorem raw_increment_current (current : NativeCurrent source) :
    rawIncrement current (coordinates current) = rawOccupation current := by
  simp only [rawIncrement,sub_self,Matrix.mul_zero,add_zero]

theorem raw_increment_fields (current : NativeCurrent source)
    (next : Matrix (BasisIndex current) (Electron source.nodes) ℂ) :
    CPS1ElectronicEvolution.fields (rawField current) (rawIncrement current next) =
      CPS1ElectronicEvolution.fields (basis current) next := by
  funext slot
  simp only [CPS1ElectronicEvolution.fields,rawIncrement,Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  change CPS1ElectronicEvolution.fields (rawField current) (rawOccupation current) slot+
    CPS1ElectronicEvolution.fields (rawField current)
    (sourceCoefficient current*(next-coordinates current)) slot = _
  rw [raw_current_fields]
  rw [CPS1Deformation.fields_mul]
  have synthesized : CPS1ElectronicEvolution.fields (rawField current) (sourceCoefficient current) = basis current := by
    funext index
    exact (CPS1MolecularFrame.FiniteNormed.field_synthesis (rawField current) index).symm
  rw [synthesized,← current_coordinates current]
  simp only [CPS1ElectronicEvolution.fields,Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib]
  abel

theorem updated_gram (current : NativeCurrent source) (time : ℝ) :
    (updatedCoordinates current time).conjTranspose * updatedCoordinates current time = 1 :=
  (CPS1ElectronicEvolution.occupied_gram _ (joint_fock_hermitian current current.nodes) _ _).trans (coordinates_gram current)

theorem updated_zero (current : NativeCurrent source) :
    rawIncrement current (updatedCoordinates current 0) = rawOccupation current := by
  simp only [updatedCoordinates,zero_div,CPS1ElectronicEvolution.occupiedUpdate,
    CPS1ElectronicEvolution.zero_time,Matrix.one_mul,raw_increment_current]

def rawActionMatrix (current : NativeCurrent source) (time : ℝ) :=
  1+sourceCoefficient current*(CPS1ElectronicEvolution.step (jointFock current current.nodes) (time/2)-1)*
    CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)

def updatedRaw (current : NativeCurrent source) (time : ℝ) := rawActionMatrix current time*rawOccupation current

theorem updated_raw_increment (current : NativeCurrent source) (time : ℝ) :
    updatedRaw current time = rawIncrement current (updatedCoordinates current time) := by
  unfold updatedRaw rawActionMatrix rawIncrement
  simp only [Matrix.add_mul,Matrix.one_mul,Matrix.mul_assoc]
  rw [← coordinates,Matrix.sub_mul,Matrix.one_mul]
  rfl

theorem raw_action_zero (current : NativeCurrent source) : rawActionMatrix current 0 = 1 := by
  simp only [rawActionMatrix,zero_div,CPS1ElectronicEvolution.zero_time,sub_self,
    Matrix.mul_zero,Matrix.zero_mul,add_zero]

theorem updated_raw_zero (current : NativeCurrent source) : updatedRaw current 0 = rawOccupation current := by
  rw [updatedRaw,raw_action_zero,Matrix.one_mul]

theorem source_null_preserved (current : NativeCurrent source) (time : ℝ)
    (relation : Matrix (RawIndex current) (Electron source.nodes) ℂ)
    (null : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField current)*relation = 0) :
    rawActionMatrix current time*relation = relation := by
  simp only [rawActionMatrix,Matrix.add_mul,Matrix.one_mul,Matrix.mul_assoc,null,Matrix.mul_zero,add_zero]

abbrev CoordinateSpace (current : NativeCurrent source) := RawIndex current → ℂ
abbrev Config (current : NativeCurrent source) :=
  Set.powersetCard (RawIndex current) (electronCount source.nodes)

-- Integer modes retain the complete raw source labels. The GS quotient is
-- applied only to their physical field; it does not relabel a pivot as an atom.
noncomputable instance rawIndexLinearOrder (current : NativeCurrent source) : LinearOrder (RawIndex current) :=
  LinearOrder.lift' (Fintype.equivFin (RawIndex current)) (Fintype.equivFin (RawIndex current)).injective

def modeBasis (current : NativeCurrent source) : Module.Basis (RawIndex current) ℂ (CoordinateSpace current) :=
  Pi.basisFun ℂ _

def numberBasis (current : NativeCurrent source) :=
  letI := rawIndexLinearOrder current
  (modeBasis current).exteriorPower (electronCount source.nodes)

def occupiedColumns (current : NativeCurrent source)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) :
    Fin (electronCount source.nodes) → CoordinateSpace current := fun slot index => occupied index slot

def numberState (current : NativeCurrent source)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) :=
  exteriorPower.ιMulti ℂ (electronCount source.nodes) (occupiedColumns current occupied)

def numberRead (current : NativeCurrent source)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) : Config current → ℂ :=
  (numberBasis current).repr (numberState current occupied)

def occupation (current : NativeCurrent source) (configuration : Config current) (index : RawIndex current) : Nat :=
  if index ∈ configuration.val then 1 else 0

theorem occupation_integer (current : NativeCurrent source) (configuration : Config current) (index : RawIndex current) :
    occupation current configuration index = 0 ∨ occupation current configuration index = 1 := by
  unfold occupation
  split <;> simp

theorem configuration_number (current : NativeCurrent source) (configuration : Config current) :
    ∑ index, occupation current configuration index = electronCount source.nodes := by
  simp only [occupation]
  rw [Finset.sum_boole]
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter,Nat.cast_id] using Set.powersetCard.card_eq configuration

def occupationChange (current : NativeCurrent source) (before after : Config current) (index : RawIndex current) : ℤ :=
  (occupation current after index : ℤ)-(occupation current before index : ℤ)

theorem occupation_change_total (current : NativeCurrent source) (before after : Config current) :
    ∑ index, occupationChange current before after index = 0 := by
  simp only [occupationChange,Finset.sum_sub_distrib,← Nat.cast_sum,
    configuration_number,sub_self]

theorem occupation_change_integer (current : NativeCurrent source) (before after : Config current) (index : RawIndex current) :
    occupationChange current before after index = -1 ∨ occupationChange current before after index = 0 ∨
      occupationChange current before after index = 1 := by
  rcases occupation_integer current before index with old | old <;>
    rcases occupation_integer current after index with next | next <;>
    simp only [occupationChange,old,next] <;> norm_num

def numberAction (current : NativeCurrent source) (time : ℝ) :=
  exteriorPower.map (electronCount source.nodes)
    (Matrix.toLin' (rawActionMatrix current time))

theorem actual_number_action (current : NativeCurrent source) (time : ℝ) :
    numberAction current time (numberState current (rawOccupation current)) =
      numberState current (updatedRaw current time) := by
  rw [numberAction,numberState,exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti ℂ (electronCount source.nodes))
  funext slot index
  simp only [Function.comp_def,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,
    occupiedColumns,updatedRaw,Matrix.mul_apply]

theorem number_action_zero (current : NativeCurrent source) :
    numberAction current 0 (numberState current (rawOccupation current)) = numberState current (rawOccupation current) := by
  rw [actual_number_action,updated_raw_zero]

def phaseTransition (current : NativeCurrent source) (time : ℝ) (before after : Config current) : ℂ :=
  (numberBasis current).repr (numberAction current time (numberBasis current before)) after

theorem phase_transition_generated (current : NativeCurrent source) (time : ℝ) (configuration : Config current) :
    numberRead current (updatedRaw current time) configuration =
      ∑ previous ∈ ((numberBasis current).repr (numberState current (rawOccupation current))).support,
        numberRead current (rawOccupation current) previous * phaseTransition current time previous configuration := by
  rw [numberRead,← actual_number_action]
  have sourceExpansion := (numberBasis current).linearCombination_repr (numberState current (rawOccupation current))
  rw [Finsupp.linearCombination_apply,Finsupp.sum] at sourceExpansion
  conv_lhs => rw [← sourceExpansion]
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,phaseTransition,numberRead,smul_eq_mul]

def rawSynthesis (current : NativeCurrent source) : CoordinateSpace current →ₗ[ℂ] SpinSpace :=
  ∑ index, (LinearMap.proj index : CoordinateSpace current →ₗ[ℂ] ℂ).smulRight (rawField current index)

theorem raw_synthesis_apply (current : NativeCurrent source) (vector : CoordinateSpace current) :
    rawSynthesis current vector = ∑ index, vector index • rawField current index := by
  simp only [rawSynthesis,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply]

theorem physical_number_projection (current : NativeCurrent source)
    (occupied : Matrix (RawIndex current) (Electron source.nodes) ℂ) :
    exteriorPower.map (electronCount source.nodes) (rawSynthesis current) (numberState current occupied) =
      CPS1ElectronicEvolution.slater (CPS1ElectronicEvolution.fields (rawField current) occupied) := by
  rw [numberState,exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti ℂ (electronCount source.nodes))
  funext slot
  exact raw_synthesis_apply current _

theorem updated_number_state_nonzero (current : NativeCurrent source) (time : ℝ) :
    numberState current (updatedRaw current time) ≠ 0 := by
  have fieldEquation : CPS1ElectronicEvolution.fields (rawField current) (updatedRaw current time) =
      CPS1ElectronicEvolution.fields (basis current) (updatedCoordinates current time) := by
    rw [updated_raw_increment,raw_increment_fields]
  have orthogonal := CPS1ElectronicEvolution.occupied_fields (basis current) (basis_orthonormal current)
    (updatedCoordinates current time) (updated_gram current time)
  have normalized := CPS1ElectronicEvolution.slater_normalized _ orthogonal
  rw [← fieldEquation,← physical_number_projection] at normalized
  intro zero
  rw [zero,map_zero,map_zero] at normalized
  norm_num at normalized

theorem updated_number_support_nonempty (current : NativeCurrent source) (time : ℝ) :
    ∃ configuration : Config current, numberRead current (updatedRaw current time) configuration ≠ 0 := by
  by_contra absent
  apply updated_number_state_nonzero current time
  have zero : (numberBasis current).repr (numberState current (updatedRaw current time)) = 0 := by
    apply Finsupp.ext
    intro configuration
    change numberRead current (updatedRaw current time) configuration = 0
    by_contra nonzero
    exact absent ⟨configuration,nonzero⟩
  exact (numberBasis current).repr.injective (zero.trans ((numberBasis current).repr.map_zero).symm)

def phaseTerm (current : NativeCurrent source) (time : ℝ) (entry : Config current × Config current) : ℂ :=
  numberRead current (rawOccupation current) entry.1 * phaseTransition current time entry.1 entry.2

def phaseTrace (current : NativeCurrent source) (time : ℝ) : Finset (Config current × Config current) := by
  classical
  exact ((numberBasis current).repr (numberState current (rawOccupation current))).support.product Finset.univ |>.filter
    (fun entry => phaseTerm current time entry ≠ 0)

def sourceIntegerTrace (current : NativeCurrent source) (time : ℝ) :=
  (phaseTrace current time).toList.map (fun entry =>
    (entry.1,entry.2,phaseTerm current time entry,occupationChange current entry.1 entry.2))

theorem phase_trace_source (current : NativeCurrent source) (time : ℝ) (entry : Config current × Config current)
    (held : entry ∈ phaseTrace current time) :
    numberRead current (rawOccupation current) entry.1 ≠ 0 ∧
      phaseTransition current time entry.1 entry.2 ≠ 0 ∧
      ∑ index, occupationChange current entry.1 entry.2 index = 0 := by
  have nonzero := (Finset.mem_filter.mp held).2
  change numberRead current (rawOccupation current) entry.1*phaseTransition current time entry.1 entry.2 ≠ 0 at nonzero
  exact ⟨left_ne_zero_of_mul nonzero,right_ne_zero_of_mul nonzero,occupation_change_total current _ _⟩

theorem phase_trace_complete (current : NativeCurrent source) (time : ℝ) (configuration : Config current) :
    (∑ entry ∈ phaseTrace current time, if entry.2 = configuration then phaseTerm current time entry else 0) =
      numberRead current (updatedRaw current time) configuration := by
  classical
  unfold phaseTrace
  rw [Finset.sum_filter]
  have prune (entry : Config current × Config current) :
      (if phaseTerm current time entry ≠ 0 then
        if entry.2 = configuration then phaseTerm current time entry else 0 else 0) =
      if entry.2 = configuration then phaseTerm current time entry else 0 := by
    by_cases zero : phaseTerm current time entry = 0 <;> simp [zero]
  simp only [prune]
  have productSum := Finset.sum_product
    (((numberBasis current).repr (numberState current (rawOccupation current))).support)
    (Finset.univ : Finset (Config current))
    (fun entry : Config current × Config current => if entry.2 = configuration then phaseTerm current time entry else 0)
  simp only [Finset.product_eq_sprod]
  rw [productSum]
  simp only [phaseTerm,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact (phase_transition_generated current time configuration).symm

end
end CPS1MaterialIncidence
