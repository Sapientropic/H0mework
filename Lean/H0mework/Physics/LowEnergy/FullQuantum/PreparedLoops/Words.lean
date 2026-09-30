import H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Source

/-! Complete number-conserving Fock words are evaluated before reading the actual preparation. -/
set_option autoImplicit false
open scoped InnerProductSpace Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
open QuantizationCheck.Fermion Fermion StateGreen ClosedLoops CoframeResponse
open YangMills.FullPairing DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineHolonomicField
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

def fullWord (word : List Mother) : Module.End ℂ (Fock Quantum.Index) :=
  (word.map fun A => quantize (Quantum.operatorMatrix A)).prod

theorem fullWord_oneParticle (word : List Mother) (v : DiracExteriorMatterCarrier) :
    fullWord word (oneParticle (Quantum.coordinates v))=oneParticle (Quantum.coordinates (word.prod v)) := by
  induction word generalizing v with
  | nil => simp [fullWord]
  | cons A rest induction =>
    simp only [fullWord,List.map_cons,List.prod_cons,Module.End.mul_apply]
    change quantize (Quantum.operatorMatrix A) (fullWord rest (oneParticle (Quantum.coordinates v)))=_
    rw [induction,quantize_apply,source_matrix_oneParticle,Quantum.matrix_action]

theorem fullWord_read (point : BasePoint) (word : List Mother) :
    read (preparedVector point) (fullWord word)=
      inner ℂ (prepared point) (operator word.prod (prepared point)) := by
  change pairing (oneParticle (Quantum.coordinates (preparedMatter point)))
    (fullWord word (oneParticle (Quantum.coordinates (preparedMatter point))))=_
  rw [fullWord_oneParticle,pairing_oneParticle]
  change Quantum.coordinatePair (preparedMatter point) (word.prod (preparedMatter point))=_
  rw [Quantum.coordinatePair_full,← natural_inner,← operator_coordinates,preparedMatter_original]

theorem complete_word_expansion (point : BasePoint) (word : List (Mother × Mother))
    (generated : ∀ pair ∈ word, Expansion pair.1 pair.2) :
    read (preparedVector point) (fullWord (word.map Prod.fst))=
      read (preparedVector point) (fullWord (word.map Prod.snd)) := by
  rw [fullWord_read,fullWord_read]
  exact expansion_prepared point _ _ (Expansion.product word generated)

def weightedWord (C : StageNineHolonomicConfiguration) (atPoint : BasePoint) (word : List Mother) :
    Module.End ℂ (Fock Quantum.Index) := fullWord (boundaryWeight C atPoint::word)

theorem weightedWord_expansion (point : BasePoint) (C : StageNineHolonomicConfiguration) (atPoint : BasePoint)
    (word : List (Mother × Mother)) (generated : ∀ pair ∈ word, Expansion pair.1 pair.2) :
    read (preparedVector point) (weightedWord C atPoint (word.map Prod.fst))=
      read (preparedVector point) (weightedWord C atPoint (word.map Prod.snd)) := by
  simp only [weightedWord,fullWord_read,List.prod_cons]
  exact weighted_expansion point C atPoint _ _ (Expansion.product word generated)

theorem weightedWord_native (point : BasePoint) (C : StageNineHolonomicConfiguration) (atPoint : BasePoint)
    (word : List Mother) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1 (sourceWordMother (weightedWord C atPoint word))))=
      read (preparedVector point) (weightedWord C atPoint word) :=
  source_word_readback point _

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
