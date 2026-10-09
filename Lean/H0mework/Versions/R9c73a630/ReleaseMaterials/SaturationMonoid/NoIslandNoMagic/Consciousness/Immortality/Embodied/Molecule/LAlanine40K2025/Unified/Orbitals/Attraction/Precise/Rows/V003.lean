import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_003_014
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_014_025
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_025_034
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_034_048
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_048_059
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_059_068
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_068_081
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_081_094
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V003_094_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_3 (j : Basis) (ordered : (3 : Basis) ≤ j) :
    |aoIntegral (3 : Basis) j - (recordedAttraction (3 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (3 : Basis) = ⟨3,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(3 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(3 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(3 : Basis) ≤ (2 : Basis) by decide) ordered)
  · convert vcell3_3_error using 1; norm_num
  · convert vcell3_4_error using 1; norm_num
  · convert vcell3_5_error using 1; norm_num
  · convert vcell3_6_error using 1; norm_num
  · convert vcell3_7_error using 1; norm_num
  · convert vcell3_8_error using 1; norm_num
  · convert vcell3_9_error using 1; norm_num
  · convert vcell3_10_error using 1; norm_num
  · convert vcell3_11_error using 1; norm_num
  · convert vcell3_12_error using 1; norm_num
  · convert vcell3_13_error using 1; norm_num
  · convert vcell3_14_error using 1; norm_num
  · convert vcell3_15_error using 1; norm_num
  · convert vcell3_16_error using 1; norm_num
  · convert vcell3_17_error using 1; norm_num
  · convert vcell3_18_error using 1; norm_num
  · convert vcell3_19_error using 1; norm_num
  · convert vcell3_20_error using 1; norm_num
  · convert vcell3_21_error using 1; norm_num
  · convert vcell3_22_error using 1; norm_num
  · convert vcell3_23_error using 1; norm_num
  · convert vcell3_24_error using 1; norm_num
  · convert vcell3_25_error using 1; norm_num
  · convert vcell3_26_error using 1; norm_num
  · convert vcell3_27_error using 1; norm_num
  · convert vcell3_28_error using 1; norm_num
  · convert vcell3_29_error using 1; norm_num
  · convert vcell3_30_error using 1; norm_num
  · convert vcell3_31_error using 1; norm_num
  · convert vcell3_32_error using 1; norm_num
  · convert vcell3_33_error using 1; norm_num
  · convert vcell3_34_error using 1; norm_num
  · convert vcell3_35_error using 1; norm_num
  · convert vcell3_36_error using 1; norm_num
  · convert vcell3_37_error using 1; norm_num
  · convert vcell3_38_error using 1; norm_num
  · convert vcell3_39_error using 1; norm_num
  · convert vcell3_40_error using 1; norm_num
  · convert vcell3_41_error using 1; norm_num
  · convert vcell3_42_error using 1; norm_num
  · convert vcell3_43_error using 1; norm_num
  · convert vcell3_44_error using 1; norm_num
  · convert vcell3_45_error using 1; norm_num
  · convert vcell3_46_error using 1; norm_num
  · convert vcell3_47_error using 1; norm_num
  · convert vcell3_48_error using 1; norm_num
  · convert vcell3_49_error using 1; norm_num
  · convert vcell3_50_error using 1; norm_num
  · convert vcell3_51_error using 1; norm_num
  · convert vcell3_52_error using 1; norm_num
  · convert vcell3_53_error using 1; norm_num
  · convert vcell3_54_error using 1; norm_num
  · convert vcell3_55_error using 1; norm_num
  · convert vcell3_56_error using 1; norm_num
  · convert vcell3_57_error using 1; norm_num
  · convert vcell3_58_error using 1; norm_num
  · convert vcell3_59_error using 1; norm_num
  · convert vcell3_60_error using 1; norm_num
  · convert vcell3_61_error using 1; norm_num
  · convert vcell3_62_error using 1; norm_num
  · convert vcell3_63_error using 1; norm_num
  · convert vcell3_64_error using 1; norm_num
  · convert vcell3_65_error using 1; norm_num
  · convert vcell3_66_error using 1; norm_num
  · convert vcell3_67_error using 1; norm_num
  · convert vcell3_68_error using 1; norm_num
  · convert vcell3_69_error using 1; norm_num
  · convert vcell3_70_error using 1; norm_num
  · convert vcell3_71_error using 1; norm_num
  · convert vcell3_72_error using 1; norm_num
  · convert vcell3_73_error using 1; norm_num
  · convert vcell3_74_error using 1; norm_num
  · convert vcell3_75_error using 1; norm_num
  · convert vcell3_76_error using 1; norm_num
  · convert vcell3_77_error using 1; norm_num
  · convert vcell3_78_error using 1; norm_num
  · convert vcell3_79_error using 1; norm_num
  · convert vcell3_80_error using 1; norm_num
  · convert vcell3_81_error using 1; norm_num
  · convert vcell3_82_error using 1; norm_num
  · convert vcell3_83_error using 1; norm_num
  · convert vcell3_84_error using 1; norm_num
  · convert vcell3_85_error using 1; norm_num
  · convert vcell3_86_error using 1; norm_num
  · convert vcell3_87_error using 1; norm_num
  · convert vcell3_88_error using 1; norm_num
  · convert vcell3_89_error using 1; norm_num
  · convert vcell3_90_error using 1; norm_num
  · convert vcell3_91_error using 1; norm_num
  · convert vcell3_92_error using 1; norm_num
  · convert vcell3_93_error using 1; norm_num
  · convert vcell3_94_error using 1; norm_num
  · convert vcell3_95_error using 1; norm_num
  · convert vcell3_96_error using 1; norm_num
  · convert vcell3_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
