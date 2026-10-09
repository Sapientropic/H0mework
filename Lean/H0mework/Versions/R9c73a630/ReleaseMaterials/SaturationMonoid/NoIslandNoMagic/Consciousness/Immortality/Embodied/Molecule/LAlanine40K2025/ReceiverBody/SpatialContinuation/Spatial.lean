import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
open BasinRefinement SourceGaussianModel SourceFiniteData SourceCoulomb ContinuousGradient MeasureTheory
open UnifiedOrbitals
noncomputable section

def translationPoint (current : Material) : Point := fun k => (offset current k : ℝ)

theorem existing_offset (current : Material) (k : Fin 3) : SpatialActuation.offsetAt current.lab k=offset current k := by
  unfold SpatialActuation.offsetAt offset
  rw [congrArg (fun p => p 0 k) SpatialActuation.input_admissible.position]

theorem primitive_translation (current : Material) (term : Term) (jet : MultiIndex) (x : Point) :
    value (SpatialActuation.termAt current.lab term) jet x=value term jet (x-translationPoint current) := by
  have coordinate (k : Fin 3) :
      x k-((term.centre k+SpatialActuation.offsetAt current.lab k : ℚ) : ℝ)=
        (x-translationPoint current) k-term.centre k := by
    rw [existing_offset]
    simp only [Rat.cast_add,Pi.sub_apply,translationPoint]
    ring
  simp only [value,SpatialActuation.termAt,coordinate]

def aoJet (current : Material) (i : Basis) (jet : MultiIndex) (x : Point) : ℝ :=
  orbital (SpatialActuation.termsAt current.lab i) jet x

theorem ao_jet_translation (current : Material) (i : Basis) (jet : MultiIndex) (x : Point) :
    aoJet current i jet x=orbital (sourceTerms i) jet (x-translationPoint current) := by
  simp only [aoJet,SpatialActuation.termsAt,orbital,List.map_map,Function.comp_def,primitive_translation]

theorem ao_translation (current : Material) (i : Basis) (x : Point) :
    SpatialActuation.aoAt current.lab i x=ao i (x-translationPoint current) :=
  ao_jet_translation current i zeroJet x

theorem canonical_position (a : Fin 13) (k : Fin 3) :
    FiniteContinuation.sourceBody.frame.position a k=Attraction.Precise.nucleus a k :=
  (congrArg (fun p => p a k) SpatialActuation.input_admissible.position).symm.trans
    (SpatialActuation.input_nucleus a k)

theorem lab_position (current : Material) (valid : Admissible current) (a : Fin 13) (k : Fin 3) :
    current.lab.frame.position a k=Attraction.Precise.nucleus a k+offset current k := by
  have body := congrArg (fun p => p a k) valid.position
  change current.lab.frame.position a k-offset current k=FiniteContinuation.sourceBody.frame.position a k at body
  rw [canonical_position] at body
  linarith only [body]

def nucleus (current : Material) (a : Fin 13) (k : Fin 3) : ℝ := current.lab.frame.position a k

theorem nucleus_translation (current : Material) (valid : Admissible current) (a : Fin 13) :
    nucleus current a=(fun k => (Attraction.Precise.nucleus a k : ℝ))+translationPoint current := by
  funext k
  simp only [nucleus,lab_position current valid,Rat.cast_add,Pi.add_apply,translationPoint]

theorem actual_centres (current : Material) (valid : Admissible current) (i : Basis) :
    List.Forall (fun term => ∃ a : Fin 13, term.centre=current.lab.frame.position a)
      (SpatialActuation.termsAt current.lab i) := by
  rw [List.forall_iff_forall_mem]
  intro term member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨a,same⟩ := (List.forall_iff_forall_mem.mp (Attraction.Precise.all_term_centres_precise i)) original originalMember
  refine ⟨a,?_⟩
  funext k
  simp only [SpatialActuation.termAt,existing_offset,same,lab_position current valid]

theorem overlap_translation (current : Material) (i j : Basis) :
    (∫ x : Point, SpatialActuation.aoAt current.lab i x*SpatialActuation.aoAt current.lab j x)=
      UnifiedOrbitals.overlap i j := by
  simp only [ao_translation,UnifiedOrbitals.overlap]
  exact integral_sub_right_eq_self (μ := (volume : Measure Point)) (fun x : Point => ao i x*ao j x) (translationPoint current)

theorem kinetic_translation (current : Material) (i j : Basis) :
    (1/2 : ℝ)*(∑ k : Fin 3, ∫ x : Point, aoJet current i (raise zeroJet k) x*aoJet current j (raise zeroJet k) x)=
      UnifiedOrbitals.kinetic i j := by
  unfold UnifiedOrbitals.kinetic UnifiedOrbitals.derivative
  simp only [ao_jet_translation]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact integral_sub_right_eq_self (μ := (volume : Measure Point))
    (fun x : Point => orbital (sourceTerms i) (raise zeroJet k) x*orbital (sourceTerms j) (raise zeroJet k) x)
    (translationPoint current)

def attraction (current : Material) (i j : Basis) : ℝ := ∑ a : Fin 13,
  -WholeBandBasin.Family.All.Nuclear.nuclearCharge a*
    ∫ x : Point, SpatialActuation.aoAt current.lab i x*SpatialActuation.aoAt current.lab j x*kernel (x-nucleus current a)

theorem attraction_translation (current : Material) (valid : Admissible current) (i j : Basis) :
    attraction current i j=Attraction.Precise.aoIntegral i j := by
  unfold attraction Attraction.Precise.aoIntegral
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have difference (x : Point) : x-nucleus current a=
      (x-translationPoint current)-(fun k => (Attraction.Precise.nucleus a k : ℝ)) := by
    rw [nucleus_translation current valid]
    abel
  simp only [ao_translation,difference]
  exact integral_sub_right_eq_self (μ := (volume : Measure Point))
    (fun x : Point => ao i x*ao j x*kernel (x-fun k => (Attraction.Precise.nucleus a k : ℝ))) (translationPoint current)

def repulsion (current : Material) (a b : Fin 13) : ℝ :=
  WholeBandBasin.Family.All.Nuclear.nuclearCharge a*WholeBandBasin.Family.All.Nuclear.nuclearCharge b*
    kernel (nucleus current a-nucleus current b)

theorem repulsion_translation (current : Material) (valid : Admissible current) (a b : Fin 13) :
    repulsion current a b=WholeBandBasin.Family.All.Nuclear.PreciseTarget.nuclearRepulsion a b := by
  unfold repulsion WholeBandBasin.Family.All.Nuclear.PreciseTarget.nuclearRepulsion
  rw [nucleus_translation current valid,nucleus_translation current valid,add_sub_add_right_eq_sub]
  rfl

def electronRepulsion (current : Material) (i j k l : Basis) : ℝ := ∫ z : Point × Point,
  SpatialActuation.aoAt current.lab i z.1*SpatialActuation.aoAt current.lab j z.1*
    (SpatialActuation.aoAt current.lab k z.2*SpatialActuation.aoAt current.lab l z.2)*kernel (z.2-z.1)

theorem electron_repulsion_translation (current : Material) (i j k l : Basis) :
    electronRepulsion current i j k l=UnifiedOrbitals.electronRepulsion i j k l := by
  have translated := integral_sub_right_eq_self (μ := (volume : Measure Point).prod volume)
    (fun z : Point × Point => ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*kernel (z.2-z.1))
      (translationPoint current,translationPoint current)
  have difference (z : Point × Point) :
      (z.2-translationPoint current)-(z.1-translationPoint current)=z.2-z.1 := by abel
  simpa only [electronRepulsion,UnifiedOrbitals.electronRepulsion,ao_translation,
    Prod.fst_sub,Prod.snd_sub,difference,Measure.volume_eq_prod] using translated

theorem actual_gamma_translation (current : Material) (x y : Point) :
    SpatialActuation.gammaAt current.lab x y=
      SpatialActuation.originalKernel current.lab.realized (x-translationPoint current) (y-translationPoint current) := by
  simp only [SpatialActuation.gammaAt,SpatialActuation.originalKernel,ao_translation]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
