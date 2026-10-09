import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.Raw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Clinical

structure Infusion where
  patient : String
  day : Nat
  totalRnaDose : ℚ
  deriving DecidableEq, Repr
def first : Infusion := ⟨Source.clinical.patient,Source.clinical.dose1Day,Source.clinical.dose1⟩
def second : Infusion :=
  ⟨first.patient,first.day+Source.clinical.doseInterval,Source.clinical.dose2⟩
def doses : List Infusion := [first,second]
def postFirstInterval : Nat × Nat := (first.day,second.day)
def followupDay : Nat := Source.clinical.weightDays[1]!
def finalMedication : ℚ := Source.clinical.secondTaper[1]!
def firstAttempt : List ℚ := Source.clinical.firstTaper

theorem original_same_patient_actual_redose :
    first.patient = "Musunuru2025/single-patient-expanded-access" ∧
    second.patient = first.patient ∧ first.day = 208 ∧ second.day = 230 ∧
    first.day < second.day ∧ first.totalRnaDose = 1/10 ∧ second.totalRnaDose = 3/10 ∧
    second.totalRnaDose = 3 * first.totalRnaDose ∧ followupDay = 256 ∧
    followupDay-first.day = 48 ∧ followupDay-second.day = 26 := by decide +kernel

theorem original_taper_rollback_and_later_change :
    firstAttempt = [101/10,81/10,101/10] ∧
    firstAttempt[0]! = firstAttempt[2]! ∧ firstAttempt[1]! < firstAttempt[2]! ∧
    Source.clinical.secondTaper = [101/10,5] ∧ finalMedication < firstAttempt[2]! ∧
    finalMedication / firstAttempt[2]! = 50/101 := by decide +kernel

theorem original_weight_and_interval :
    Source.clinical.weightDays = [207,256] ∧ Source.clinical.weights = [714/100,817/100] ∧
    Source.clinical.weightDays[0]! < first.day ∧
    Source.clinical.weights[1]! - Source.clinical.weights[0]! = 103/100 := by decide +kernel

theorem all_original_summaries_retained :
    Source.clinical.ammonia = [⟨23,14,48⟩,⟨9,9,19⟩,⟨13,9,28⟩] ∧
    Source.clinical.orotic = [⟨17/10,16/10,18/10⟩,⟨24/10,2,3⟩,⟨26/10,2,36/10⟩] ∧
    (Source.clinical.ammonia ++ Source.clinical.orotic).all
      (fun x => x.lower ≤ x.median && x.median ≤ x.upper) = true := by decide +kernel

theorem original_summary_response_is_not_monotone_ammonia :
    Source.clinical.ammonia[1]!.median < Source.clinical.ammonia[0]!.median ∧
    Source.clinical.ammonia[2]!.median < Source.clinical.ammonia[0]!.median ∧
    Source.clinical.ammonia[1]!.median < Source.clinical.ammonia[2]!.median ∧
    Source.clinical.orotic[0]!.median < Source.clinical.orotic[1]!.median ∧
    Source.clinical.orotic[1]!.median < Source.clinical.orotic[2]!.median := by decide +kernel

theorem original_measurement_units_and_missing_biopsy :
    Source.clinical.doseUnit = "mg total RNA per kg body mass" ∧
    Source.clinical.scavengerUnit = "ml per square meter per day" ∧
    Source.clinical.ammoniaUnit = "micromole per liter" ∧
    Source.clinical.oroticUnit = "millimole per mole creatinine" ∧
    Source.clinical.tissueStatement = "patient liver editing fraction was not measured; biopsy deferred" := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Clinical
