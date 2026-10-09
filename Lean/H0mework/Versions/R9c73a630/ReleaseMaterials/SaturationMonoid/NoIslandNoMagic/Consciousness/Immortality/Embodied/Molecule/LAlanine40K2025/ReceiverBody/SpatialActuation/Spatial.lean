import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel SourceFiniteData SourceCoulomb ContinuousGradient MeasureTheory
open UnifiedOrbitals
noncomputable section

def offsetQ (k : Fin 3) : ℚ := displacementQ*axisQ k
def offset : Point := fun k => (offsetQ k : ℝ)
def translatedTerm (term : Term) : Term :=
  { term with centre := fun k => term.centre k+offsetQ k }
def translatedTerms (i : Basis) : List Term := (sourceTerms i).map translatedTerm
def aoJet (i : Basis) (jet : MultiIndex) (x : Point) : ℝ :=
  orbital (translatedTerms i) jet x
def translatedAO (i : Basis) (x : Point) : ℝ := aoJet i zeroJet x
def nucleus (a : Fin 13) (k : Fin 3) : ℝ := generatedBody.frame.position a k

theorem primitive_translation (term : Term) (jet : MultiIndex) (x : Point) :
    value (translatedTerm term) jet x=value term jet (x-offset) := by
  have coordinate (k : Fin 3) : x k-((term.centre k+offsetQ k : ℚ) : ℝ)=(x-offset) k-term.centre k := by
    simp only [Rat.cast_add,Pi.sub_apply,offset]
    ring
  simp only [value,translatedTerm,coordinate]

theorem orbital_translation (terms : List Term) (jet : MultiIndex) (x : Point) :
    orbital (terms.map translatedTerm) jet x=orbital terms jet (x-offset) := by
  simp only [orbital,List.map_map,Function.comp_def,primitive_translation]

theorem ao_jet_translation (i : Basis) (jet : MultiIndex) (x : Point) :
    aoJet i jet x=orbital (sourceTerms i) jet (x-offset) :=
  orbital_translation (sourceTerms i) jet x

theorem ao_translation (i : Basis) (x : Point) : translatedAO i x=ao i (x-offset) :=
  ao_jet_translation i zeroJet x

theorem input_nucleus (a : Fin 13) (k : Fin 3) :
    input.body.frame.position a k=Attraction.Precise.nucleus a k := by
  apply Rat.cast_injective (α := ℝ)
  exact FiniteContinuation.position_at_source input input_admissible (a,k)

theorem nucleus_translation (a : Fin 13) :
    nucleus a=(fun k => (Attraction.Precise.nucleus a k : ℝ))+offset := by
  funext k
  simp only [nucleus,generated_position,input_nucleus,Rat.cast_add,Rat.cast_mul,
    Pi.add_apply,offset,offsetQ]

theorem translated_centres (i : Basis) : List.Forall (fun term =>
    ∃ a : Fin 13, term.centre=generatedBody.frame.position a) (translatedTerms i) := by
  rw [List.forall_iff_forall_mem]
  intro term member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨a,same⟩ := (List.forall_iff_forall_mem.mp (Attraction.Precise.all_term_centres_precise i)) original originalMember
  refine ⟨a,?_⟩
  funext k
  simp only [translatedTerm,generated_position,input_nucleus,offsetQ,same]

theorem centre_residual_preserved (term : Term) (a : Fin 13) (k : Fin 3) :
    (translatedTerm term).centre k-generatedBody.frame.position a k=
      term.centre k-input.body.frame.position a k := by
  simp only [translatedTerm,generated_position,offsetQ]
  ring

def overlap (i j : Basis) : ℝ := ∫ x : Point, translatedAO i x*translatedAO j x
def kinetic (i j : Basis) : ℝ := (1/2 : ℝ)*∑ k : Fin 3,
  ∫ x : Point, aoJet i (raise zeroJet k) x*aoJet j (raise zeroJet k) x

theorem overlap_translation (i j : Basis) : overlap i j=UnifiedOrbitals.overlap i j := by
  simp only [overlap,ao_translation,UnifiedOrbitals.overlap]
  exact integral_sub_right_eq_self (μ := (volume : Measure Point))
    (fun x : Point => ao i x*ao j x) offset

theorem kinetic_translation (i j : Basis) : kinetic i j=UnifiedOrbitals.kinetic i j := by
  unfold kinetic UnifiedOrbitals.kinetic UnifiedOrbitals.derivative
  simp only [ao_jet_translation]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact integral_sub_right_eq_self (μ := (volume : Measure Point))
    (fun x : Point => orbital (sourceTerms i) (raise zeroJet k) x*
      orbital (sourceTerms j) (raise zeroJet k) x) offset

def attraction (i j : Basis) : ℝ := ∑ a : Fin 13,
  -WholeBandBasin.Family.All.Nuclear.nuclearCharge a*
    ∫ x : Point, translatedAO i x*translatedAO j x*kernel (x-nucleus a)

theorem attraction_translation (i j : Basis) : attraction i j=Attraction.Precise.aoIntegral i j := by
  unfold attraction Attraction.Precise.aoIntegral
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have difference (x : Point) : x-nucleus a=(x-offset)-(fun k => (Attraction.Precise.nucleus a k : ℝ)) := by
    rw [nucleus_translation]
    abel
  simp only [ao_translation,difference]
  exact integral_sub_right_eq_self (μ := (volume : Measure Point))
    (fun x : Point => ao i x*ao j x*kernel (x-fun k => (Attraction.Precise.nucleus a k : ℝ))) offset

def repulsion (a b : Fin 13) : ℝ :=
  WholeBandBasin.Family.All.Nuclear.nuclearCharge a*WholeBandBasin.Family.All.Nuclear.nuclearCharge b*
    kernel (nucleus a-nucleus b)

theorem repulsion_translation (a b : Fin 13) :
    repulsion a b=WholeBandBasin.Family.All.Nuclear.PreciseTarget.nuclearRepulsion a b := by
  unfold repulsion WholeBandBasin.Family.All.Nuclear.PreciseTarget.nuclearRepulsion
  rw [nucleus_translation,nucleus_translation,add_sub_add_right_eq_sub]
  rfl

def electronRepulsion (i j k l : Basis) : ℝ := ∫ z : Point × Point,
  translatedAO i z.1*translatedAO j z.1*(translatedAO k z.2*translatedAO l z.2)*kernel (z.2-z.1)

theorem electron_repulsion_translation (i j k l : Basis) :
    electronRepulsion i j k l=UnifiedOrbitals.electronRepulsion i j k l := by
  have translated := integral_sub_right_eq_self (μ := (volume : Measure Point).prod volume)
    (fun z : Point × Point => ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*kernel (z.2-z.1)) (offset,offset)
  have difference (z : Point × Point) : (z.2-offset)-(z.1-offset)=z.2-z.1 := by abel
  simpa only [electronRepulsion,UnifiedOrbitals.electronRepulsion,ao_translation,
    Prod.fst_sub,Prod.snd_sub,difference,Measure.volume_eq_prod] using translated

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
