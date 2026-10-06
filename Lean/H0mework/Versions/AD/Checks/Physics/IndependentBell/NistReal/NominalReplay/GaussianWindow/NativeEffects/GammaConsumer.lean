import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.NativeEffects.Detectorgamma
import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.Consumer

set_option autoImplicit false

namespace P23.GaussianWindow.NativeEffects.Consumer

open Matrix
open scoped BigOperators ComplexOrder
noncomputable section

theorem actual_detector_all_sectors (d : DetectorPrim) (a : ℝ) :
    (ports d a)ᴴ * ports d a = 1 ∧
      ∀ n : ℕ,
        (occupation n)ᴴ * occupation n = 1 ∧
          gamma d a n =
            (wordTensor (noClickPorts d a) n * occupation n)ᴴ *
              (wordTensor (noClickPorts d a) n * occupation n) ∧
          (gamma d a n).PosSemidef ∧ (1 - gamma d a n).PosSemidef :=
  ⟨ports_gram d a, fun n =>
    ⟨occupation_isometry n, gamma_port_born d a n, gamma_bounds d a n⟩⟩

theorem source_native_tail (s : RawKernel) (dA dB : DetectorPrim) (a b : ℝ) (cutoff : ℕ) :
    (0 ≤ fullBorn s (aliceNoClick dA a) - prefixBorn s (aliceNoClick dA a) cutoff ∧
      fullBorn s (aliceNoClick dA a) - prefixBorn s (aliceNoClick dA a) cutoff ≤
        sourceTail s cutoff) ∧
      (0 ≤ fullBorn s (bobNoClick dB b) - prefixBorn s (bobNoClick dB b) cutoff ∧
        fullBorn s (bobNoClick dB b) - prefixBorn s (bobNoClick dB b) cutoff ≤
          sourceTail s cutoff) ∧
      (0 ≤ fullBorn s (jointNoClick dA dB a b) -
          prefixBorn s (jointNoClick dA dB a b) cutoff ∧
        fullBorn s (jointNoClick dA dB a b) - prefixBorn s (jointNoClick dA dB a b) cutoff ≤
          sourceTail s cutoff) :=
  ⟨born_truncation_budget s (aliceNoClick dA a) cutoff,
    born_truncation_budget s (bobNoClick dB b) cutoff,
    born_truncation_budget s (jointNoClick dA dB a b) cutoff⟩

theorem source_native_cutoff_six (s : RawKernel) (dA dB : DetectorPrim) (a b : ℝ) :
    (0 ≤ fullBorn s (aliceNoClick dA a) - prefixBorn s (aliceNoClick dA a) 6 ∧
      fullBorn s (aliceNoClick dA a) - prefixBorn s (aliceNoClick dA a) 6 ≤ sourceTail s 6) ∧
      (0 ≤ fullBorn s (bobNoClick dB b) - prefixBorn s (bobNoClick dB b) 6 ∧
        fullBorn s (bobNoClick dB b) - prefixBorn s (bobNoClick dB b) 6 ≤ sourceTail s 6) ∧
      (0 ≤ fullBorn s (jointNoClick dA dB a b) - prefixBorn s (jointNoClick dA dB a b) 6 ∧
        fullBorn s (jointNoClick dA dB a b) - prefixBorn s (jointNoClick dA dB a b) 6 ≤
          sourceTail s 6) :=
  P23.GaussianWindow.Consumer.three_no_click_cutoff_six s
    (aliceNoClick dA a) (bobNoClick dB b) (jointNoClick dA dB a b)

theorem source_native_joint_enclosure (s : RawKernel) (dA dB : DetectorPrim) (a b : ℝ)
    {lo hi : ℝ}
    (hlo : lo ≤ prefixBorn s (jointNoClick dA dB a b) 6)
    (hhi : prefixBorn s (jointNoClick dA dB a b) 6 ≤ hi) :
    lo ≤ fullBorn s (jointNoClick dA dB a b) ∧
      fullBorn s (jointNoClick dA dB a b) ≤ hi + sourceTail s 6 :=
  P23.GaussianWindow.Consumer.generated_no_click_enclosure s
    (jointNoClick dA dB a b) hlo hhi

end
end P23.GaussianWindow.NativeEffects.Consumer
