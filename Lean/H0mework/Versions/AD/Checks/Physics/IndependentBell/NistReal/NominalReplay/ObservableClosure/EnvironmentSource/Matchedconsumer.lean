import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.EnvironmentSource.Matchedsource

set_option autoImplicit false

namespace P23.EnvironmentSource.Matched.Consumer

open P23.GaussianWindow P23.EnvironmentSource.Sector.Consumer
noncomputable section

theorem raw_K_generated (s : RawKernel) (dA dB : EnvironmentPrim) (bg : BackgroundPrim)
    (ht : 0 < s.tV) (hA : 0 < dA.detector.TV) (hB : 0 < dB.detector.TV) :
    rawKA s dA dB bg = some (joint s dA dB bg / singleB s dB bg) ∧
      rawKB s dA dB bg = some (joint s dA dB bg / singleA s dA bg) := by
  have ha := (herald_A_iff s dA bg).mpr (Or.inr ⟨ht, hA⟩)
  have hb := (herald_B_iff s dB bg).mpr (Or.inr ⟨ht, hB⟩)
  simp only [rawKA, rawKB, if_pos ha, if_pos hb, and_self]

theorem actual_matched_calibration_consumer (s : RawKernel) (dA dB : EnvironmentPrim)
    (bg : BackgroundPrim) :
    fullBorn s (environmentJointNoClick dA dB 0 0) =
        1 / (1 + meanV s * (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV)) ∧
      noClickA s dA = 1 / (1 + meanV s * dA.detector.TV) ∧
      noClickB s dB = 1 / (1 + meanV s * dB.detector.TV) ∧
      singleA s dA bg = (bg.bA + meanV s * dA.detector.TV) / (1 + meanV s * dA.detector.TV) ∧
      singleB s dB bg = (bg.bB + meanV s * dB.detector.TV) / (1 + meanV s * dB.detector.TV) ∧
      (0 < singleA s dA bg ↔ 0 < bg.bA ∨ (0 < s.tV ∧ 0 < dA.detector.TV)) ∧
      (0 < singleB s dB bg ↔ 0 < bg.bB ∨ (0 < s.tV ∧ 0 < dB.detector.TV)) :=
  ⟨matched_mean_form s dA dB, localA_mean_form s dA, localB_mean_form s dB,
    singleA_form s dA bg, singleB_form s dB bg, herald_A_iff s dA bg, herald_B_iff s dB bg⟩

theorem generated_loss_inverse_consumer (s : RawKernel) (dA dB : EnvironmentPrim)
    (bg : BackgroundPrim) (ht : 0 < s.tV) :
    dA.detector.TV = (singleA s dA bg - bg.bA) / (meanV s * (1 - singleA s dA bg)) ∧
      dB.detector.TV = (singleB s dB bg - bg.bB) / (meanV s * (1 - singleB s dB bg)) :=
  ⟨lossA_inverse s dA bg ht, lossB_inverse s dB bg ht⟩

theorem actual_matched_rawK_cubic_consumer (s : RawKernel) (dA dB : EnvironmentPrim)
    (bg : BackgroundPrim) (ht : 0 < s.tV)
    (hA : 0 < dA.detector.TV) (hB : 0 < dB.detector.TV) :
    fullBorn s (environmentJointNoClick dA dB 0 0) =
        1 / (1 + meanV s * (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV)) ∧
      rawKA s dA dB bg = some (joint s dA dB bg / singleB s dB bg) ∧
      rawKB s dA dB bg = some (joint s dA dB bg / singleA s dA bg) ∧
      dA.detector.TV = (singleA s dA bg - bg.bA) / (meanV s * (1 - singleA s dA bg)) ∧
      dB.detector.TV = (singleB s dB bg - bg.bB) / (meanV s * (1 - singleB s dB bg)) ∧
      calibrationP (meanV s) bg.bA bg.bB (joint s dA dB bg / singleB s dB bg)
        (joint s dA dB bg / singleA s dA bg) (singleA s dA bg) = 0 :=
  ⟨matched_mean_form s dA dB, (raw_K_generated s dA dB bg ht hA hB).1,
    (raw_K_generated s dA dB bg ht hA hB).2,
    lossA_inverse s dA bg ht, lossB_inverse s dB bg ht,
    generated_cubic s dA dB bg ht hA hB⟩

end
end P23.EnvironmentSource.Matched.Consumer
