import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Classification
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material

open Program ProgrammeControl

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (family : OriginalItem law current word → List Port) (group : List Party)

def dependentTotal (location : Party × Good) : ℚ :=
  EffectFold.total (law.rawItems current word).attach
    (fun item => dependentAmount law current word family group item location)

def independentTotal (location : Party × Good) : ℚ :=
  EffectFold.total (law.rawItems current word).attach
    (fun item => independentAmount law current word family group item location)

def unresolvedTotal (location : Party × Good) : ℚ :=
  EffectFold.total (law.rawItems current word).attach
    (fun item => unresolvedAmount law current word family group item location)

theorem totals_nonnegative (location : Party × Good) :
    0 ≤ dependentTotal law current word family group location ∧
      0 ≤ independentTotal law current word family group location ∧
      0 ≤ unresolvedTotal law current word family group location := by
  refine ⟨EffectFold.total_nonnegative _ _ (fun item _ =>
    (acquisition_nonnegative law current word family group item location).1),
    EffectFold.total_nonnegative _ _ (fun item _ =>
    (acquisition_nonnegative law current word family group item location).2.1),
    EffectFold.total_nonnegative _ _ (fun item _ =>
    (acquisition_nonnegative law current word family group item location).2.2)⟩

private theorem partition_list (items : List (OriginalItem law current word)) (location : Party × Good) :
    EffectFold.total items (fun item => dependentAmount law current word family group item location) +
      EffectFold.total items (fun item => independentAmount law current word family group item location) +
      EffectFold.total items (fun item => unresolvedAmount law current word family group item location) =
      EffectFold.total items (fun item => Decoder.acquired law item.val location.1 location.2) := by
  induction items with
  | nil => simp [EffectFold.total]
  | cons item tail ih =>
      have head := acquisition_partition law current word family group item location
      simp only [EffectFold.total, List.map_cons, List.sum_cons] at ih ⊢
      linarith

theorem total_partition (location : Party × Good) :
    dependentTotal law current word family group location +
      independentTotal law current word family group location +
      unresolvedTotal law current word family group location =
        law.totalCredit (law.rawItems current word) location.1 location.2 := by
  have split := partition_list law current word family group (law.rawItems current word).attach location
  change _ = EffectFold.total (law.rawItems current word).attach
    (fun item => Decoder.acquired law item.val location.1 location.2) at split
  simp only [EffectFold.total] at split
  rw [List.attach_map_val
    (f := fun item => Decoder.acquired law item location.1 location.2)] at split
  exact split

def unresolvedOriginal (location : Party × Good)
    (positive : 0 < unresolvedTotal law current word family group location) :
    { item : OriginalItem law current word //
      0 < unresolvedAmount law current word family group item location } :=
  let found := EffectFold.firstPositive
    (fun item => unresolvedAmount law current word family group item location)
    (law.rawItems current word).attach positive
  ⟨found.val, found.property.2⟩

theorem positive_total_has_original_control (location : Party × Good)
    (positive : 0 < dependentTotal law current word family group location) :
    Nonempty (ControlUse law current word family) := by
  let found := EffectFold.firstPositive
    (fun item => dependentAmount law current word family group item location)
    (law.rawItems current word).attach positive
  obtain ⟨use, _same⟩ := positive_credit_returns_actual_control law current word family group
    found.val location found.property.2
  exact ⟨use⟩

theorem actual_material_balance (location : Party × Good) :
    (law.next current word).stock location.1 location.2 +
      total (law.rawItems current word) (fun item => Decoder.consumedFor law .necessity item location.1 location.2) +
      total (law.rawItems current word) (fun item => Decoder.consumedFor law .maintenance item location.1 location.2) +
      total (law.rawItems current word) (fun item => otherPaid law item location.1 location.2) =
    current.stock location.1 location.2 + dependentTotal law current word family group location +
      independentTotal law current word family group location + unresolvedTotal law current word family group location := by
  have balance := law.actual_next_material_balance current word location.1 location.2
  rw [← total_outflow_partition, ← total_partition law current word family group location] at balance
  simpa only [add_assoc] using balance

#print axioms actual_material_balance
#print axioms positive_total_has_original_control

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material
