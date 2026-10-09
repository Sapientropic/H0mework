import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V012_012_048
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V012_048_081
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V012_081_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_12 (j : Basis) (ordered : (12 : Basis) ≤ j) :
    |aoIntegral (12 : Basis) j - (recordedAttraction (12 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (12 : Basis) = ⟨12,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(12 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(12 : Basis) ≤ (11 : Basis) by decide) ordered)
  · convert vcell12_12_error using 1; norm_num
  · convert vcell12_13_error using 1; norm_num
  · convert vcell12_14_error using 1; norm_num
  · convert vcell12_15_error using 1; norm_num
  · convert vcell12_16_error using 1; norm_num
  · convert vcell12_17_error using 1; norm_num
  · convert vcell12_18_error using 1; norm_num
  · convert vcell12_19_error using 1; norm_num
  · convert vcell12_20_error using 1; norm_num
  · convert vcell12_21_error using 1; norm_num
  · convert vcell12_22_error using 1; norm_num
  · convert vcell12_23_error using 1; norm_num
  · convert vcell12_24_error using 1; norm_num
  · convert vcell12_25_error using 1; norm_num
  · convert vcell12_26_error using 1; norm_num
  · convert vcell12_27_error using 1; norm_num
  · convert vcell12_28_error using 1; norm_num
  · convert vcell12_29_error using 1; norm_num
  · convert vcell12_30_error using 1; norm_num
  · convert vcell12_31_error using 1; norm_num
  · convert vcell12_32_error using 1; norm_num
  · convert vcell12_33_error using 1; norm_num
  · convert vcell12_34_error using 1; norm_num
  · convert vcell12_35_error using 1; norm_num
  · convert vcell12_36_error using 1; norm_num
  · convert vcell12_37_error using 1; norm_num
  · convert vcell12_38_error using 1; norm_num
  · convert vcell12_39_error using 1; norm_num
  · convert vcell12_40_error using 1; norm_num
  · convert vcell12_41_error using 1; norm_num
  · convert vcell12_42_error using 1; norm_num
  · convert vcell12_43_error using 1; norm_num
  · convert vcell12_44_error using 1; norm_num
  · convert vcell12_45_error using 1; norm_num
  · convert vcell12_46_error using 1; norm_num
  · convert vcell12_47_error using 1; norm_num
  · convert vcell12_48_error using 1; norm_num
  · convert vcell12_49_error using 1; norm_num
  · convert vcell12_50_error using 1; norm_num
  · convert vcell12_51_error using 1; norm_num
  · convert vcell12_52_error using 1; norm_num
  · convert vcell12_53_error using 1; norm_num
  · convert vcell12_54_error using 1; norm_num
  · convert vcell12_55_error using 1; norm_num
  · convert vcell12_56_error using 1; norm_num
  · convert vcell12_57_error using 1; norm_num
  · convert vcell12_58_error using 1; norm_num
  · convert vcell12_59_error using 1; norm_num
  · convert vcell12_60_error using 1; norm_num
  · convert vcell12_61_error using 1; norm_num
  · convert vcell12_62_error using 1; norm_num
  · convert vcell12_63_error using 1; norm_num
  · convert vcell12_64_error using 1; norm_num
  · convert vcell12_65_error using 1; norm_num
  · convert vcell12_66_error using 1; norm_num
  · convert vcell12_67_error using 1; norm_num
  · convert vcell12_68_error using 1; norm_num
  · convert vcell12_69_error using 1; norm_num
  · convert vcell12_70_error using 1; norm_num
  · convert vcell12_71_error using 1; norm_num
  · convert vcell12_72_error using 1; norm_num
  · convert vcell12_73_error using 1; norm_num
  · convert vcell12_74_error using 1; norm_num
  · convert vcell12_75_error using 1; norm_num
  · convert vcell12_76_error using 1; norm_num
  · convert vcell12_77_error using 1; norm_num
  · convert vcell12_78_error using 1; norm_num
  · convert vcell12_79_error using 1; norm_num
  · convert vcell12_80_error using 1; norm_num
  · convert vcell12_81_error using 1; norm_num
  · convert vcell12_82_error using 1; norm_num
  · convert vcell12_83_error using 1; norm_num
  · convert vcell12_84_error using 1; norm_num
  · convert vcell12_85_error using 1; norm_num
  · convert vcell12_86_error using 1; norm_num
  · convert vcell12_87_error using 1; norm_num
  · convert vcell12_88_error using 1; norm_num
  · convert vcell12_89_error using 1; norm_num
  · convert vcell12_90_error using 1; norm_num
  · convert vcell12_91_error using 1; norm_num
  · convert vcell12_92_error using 1; norm_num
  · convert vcell12_93_error using 1; norm_num
  · convert vcell12_94_error using 1; norm_num
  · convert vcell12_95_error using 1; norm_num
  · convert vcell12_96_error using 1; norm_num
  · convert vcell12_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
