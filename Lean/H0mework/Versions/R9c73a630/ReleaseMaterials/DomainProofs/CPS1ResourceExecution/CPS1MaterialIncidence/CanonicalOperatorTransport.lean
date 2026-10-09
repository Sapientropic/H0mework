import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CanonicalPairChain

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

def commonModes (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : List (AddressedBasisIndex current) :=
  (previous.val ∩ after.val).toList

def commonCARWord (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : List (SourceCARSymbol current) :=
  (commonModes current previous after).map SourceCARSymbol.creating ++
    (commonModes current previous after).reverse.map SourceCARSymbol.annihilating

def commonCAROperator (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : Module.End ℂ SourceFermion :=
  evaluateCARWord (commonCARWord current previous after)

def changedGroupedOperator (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : Module.End ℂ SourceFermion :=
  evaluateCARWord (pairGrouped (canonicalPairing current previous after))

def canonicalChangedOperator (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : Module.End ℂ SourceFermion :=
  canonicalReducedOperator current previous after

def normalOperatorResidual (current : NativeCurrent source)
    (previous after : AtomConfiguration current) : Module.End ℂ SourceFermion :=
  canonicalNormalOperator current previous after -
    (commonCAROperator current previous after).comp
      (changedGroupedOperator current previous after)

theorem canonical_changed_transport (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    ∃ swaps, changedGroupedOperator current previous after =
      carSwapSign swaps • canonicalChangedOperator current previous after := by
  obtain ⟨swaps,chain⟩ := canonical_pair_chain current previous after
  refine ⟨swaps,?_⟩
  unfold changedGroupedOperator canonicalChangedOperator
  rw [car_swap_chain_operator_transport chain]
  simp [canonicalReducedOperator]

theorem normal_operator_residual_decomposition (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    canonicalNormalOperator current previous after =
      (commonCAROperator current previous after).comp
        (changedGroupedOperator current previous after) +
      normalOperatorResidual current previous after := by
  unfold normalOperatorResidual
  abel

theorem common_carrier_empty (current : NativeCurrent source)
  (previous after : AtomConfiguration current)
    (empty : previous.val ∩ after.val = ∅) :
    commonCAROperator current previous after = LinearMap.id := by
  simp [commonCAROperator, commonCARWord, commonModes, empty, evaluateCARWord]

end
end CPS1MaterialIncidence
