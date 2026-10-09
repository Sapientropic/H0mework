import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.SourceWordStock

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

def SourceCARSymbol.mode {current : NativeCurrent source} :
    SourceCARSymbol current → AddressedBasisIndex current
  | .creating mode => mode
  | .annihilating mode => mode

def canonicalReducedOperator (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : Module.End ℂ SourceFermion :=
  evaluateCARWord (canonicalCARWord current previous after)

def canonicalNormalOperator (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : Module.End ℂ SourceFermion :=
  normalCAROperator current after previous

theorem canonical_reduced_operator_generated (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    canonicalReducedOperator current previous after =
      evaluateCARWord (canonicalCARWord current previous after) := rfl

theorem canonical_normal_operator_generated (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    canonicalNormalOperator current previous after = normalCAROperator current after previous := rfl

def addressedOccupationProjector (current : NativeCurrent source)
    (mode : AddressedBasisIndex current) : Module.End ℂ SourceFermion :=
  physicalPair (addressedBasis current mode) (addressedBasis current mode)

theorem addressed_occupation_projector_idem (current : NativeCurrent source)
    (mode : AddressedBasisIndex current) :
    (addressedOccupationProjector current mode).comp
      (addressedOccupationProjector current mode) = addressedOccupationProjector current mode := by
  apply LinearMap.ext
  intro state
  change physicalPair (addressedBasis current mode) (addressedBasis current mode)
      (physicalPair (addressedBasis current mode) (addressedBasis current mode) state) = _
  rw [physical_pair_square]
  have unitInner : inner ℂ (addressedBasis current mode) (addressedBasis current mode) = 1 := by
    simpa using (orthonormal_iff_ite.mp (addressed_basis_orthonormal current) mode mode)
  rw [unitInner,one_smul]
  rfl

def sharedOccupationProjector (current : NativeCurrent source)
    (previous after : AtomConfiguration current) (mode : AddressedBasisIndex current) :
    Module.End ℂ SourceFermion :=
  if mode ∈ previous.val ∩ after.val then addressedOccupationProjector current mode else 0

theorem shared_occupation_projector_idem (current : NativeCurrent source)
    (previous after : AtomConfiguration current) (mode : AddressedBasisIndex current) :
    (sharedOccupationProjector current previous after mode).comp
      (sharedOccupationProjector current previous after mode) =
      sharedOccupationProjector current previous after mode := by
  unfold sharedOccupationProjector
  split
  · exact addressed_occupation_projector_idem current mode
  · simp

theorem source_car_adjacent_swap {current : NativeCurrent source}
    (first second : SourceCARSymbol current)
    (different : first.mode ≠ second.mode) :
    evaluateCARWord [first,second] =
      -(evaluateCARWord [second,first]) := by
  cases first with
  | creating first =>
    cases second with
    | creating second =>
      apply LinearMap.ext
      intro state
      simp only [evaluateCARWord,LinearMap.comp_apply,SourceCARSymbol.operator]
      exact eq_neg_of_add_eq_zero_left
        (physical_creations_anticommute (addressedBasis current first)
          (addressedBasis current second) state)
    | annihilating second =>
      apply LinearMap.ext
      intro state
      simp only [evaluateCARWord,LinearMap.comp_apply,SourceCARSymbol.operator]
      have orthogonal : inner ℂ (addressedBasis current second)
          (addressedBasis current first) = 0 := by
        exact (orthonormal_iff_ite.mp (addressed_basis_orthonormal current) second first).trans
          (if_neg (Ne.symm different))
      have law := physical_annihilation_creation (addressedBasis current second)
        (addressedBasis current first) state
      rw [orthogonal,zero_smul] at law
      change physicalCreation (addressedBasis current first)
          (physicalAnnihilation (addressedBasis current second) state) =
        -physicalAnnihilation (addressedBasis current second)
          (physicalCreation (addressedBasis current first) state)
      exact eq_neg_of_add_eq_zero_right law
  | annihilating first =>
    cases second with
    | creating second =>
      apply LinearMap.ext
      intro state
      simp only [evaluateCARWord,LinearMap.comp_apply,SourceCARSymbol.operator]
      have orthogonal : inner ℂ (addressedBasis current first)
          (addressedBasis current second) = 0 := by
        exact (orthonormal_iff_ite.mp (addressed_basis_orthonormal current) first second).trans
          (if_neg different)
      have law := physical_annihilation_creation (addressedBasis current first)
        (addressedBasis current second) state
      rw [orthogonal,zero_smul] at law
      change physicalAnnihilation (addressedBasis current first)
          (physicalCreation (addressedBasis current second) state) =
        -physicalCreation (addressedBasis current second)
          (physicalAnnihilation (addressedBasis current first) state)
      exact eq_neg_of_add_eq_zero_left law
    | annihilating second =>
      apply LinearMap.ext
      intro state
      simp only [evaluateCARWord,LinearMap.comp_apply,SourceCARSymbol.operator]
      exact CliffordAlgebra.contractLeft_comm
        (innerSL ℂ (addressedBasis current first)).toLinearMap
        (innerSL ℂ (addressedBasis current second)).toLinearMap state

def carSwapSign (swaps : Nat) : ℂ := (-1 : ℂ) ^ swaps

theorem carSwapSign_pm_one (swaps : Nat) :
    carSwapSign swaps = 1 ∨ carSwapSign swaps = -1 := by
  unfold carSwapSign
  induction swaps with
  | zero => simp
  | succ swaps ih =>
      rcases ih with ih | ih <;> simp [pow_succ,ih]

inductive CARSwapChain {current : NativeCurrent source} :
    List (SourceCARSymbol current) → List (SourceCARSymbol current) → Nat → Prop
  | refl (word : List (SourceCARSymbol current)) : CARSwapChain word word 0
  | swap (pre : List (SourceCARSymbol current)) (first second : SourceCARSymbol current)
      (suffix : List (SourceCARSymbol current))
      (different : first.mode ≠ second.mode) :
      CARSwapChain (pre ++ [first,second] ++ suffix)
        (pre ++ [second,first] ++ suffix) 1
  | trans {first middle last : List (SourceCARSymbol current)} {left right : Nat} :
      CARSwapChain first middle left → CARSwapChain middle last right →
      CARSwapChain first last (left+right)

theorem car_swap_chain_perm {current : NativeCurrent source}
    {first last : List (SourceCARSymbol current)} {swaps : Nat}
    (chain : CARSwapChain first last swaps) : first.Perm last := by
  induction chain with
  | refl word => exact List.Perm.refl word
  | @swap pre first second suffix different =>
      have middle : (pre ++ [first,second]).Perm (pre ++ [second,first]) :=
        List.Perm.append (List.Perm.refl pre) (List.Perm.swap first second []).symm
      exact List.Perm.append middle (List.Perm.refl suffix)
  | trans chainFirst chainLast ihFirst ihLast =>
      exact ihFirst.trans ihLast

end
end CPS1MaterialIncidence
