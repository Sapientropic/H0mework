import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V008_008_045
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V008_045_079
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V008_079_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_8 (j : Basis) (ordered : (8 : Basis) ≤ j) :
    |aoIntegral (8 : Basis) j - (recordedAttraction (8 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (8 : Basis) = ⟨8,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(8 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(8 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(8 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(8 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(8 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(8 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(8 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(8 : Basis) ≤ (7 : Basis) by decide) ordered)
  · convert vcell8_8_error using 1; norm_num
  · convert vcell8_9_error using 1; norm_num
  · convert vcell8_10_error using 1; norm_num
  · convert vcell8_11_error using 1; norm_num
  · convert vcell8_12_error using 1; norm_num
  · convert vcell8_13_error using 1; norm_num
  · convert vcell8_14_error using 1; norm_num
  · convert vcell8_15_error using 1; norm_num
  · convert vcell8_16_error using 1; norm_num
  · convert vcell8_17_error using 1; norm_num
  · convert vcell8_18_error using 1; norm_num
  · convert vcell8_19_error using 1; norm_num
  · convert vcell8_20_error using 1; norm_num
  · convert vcell8_21_error using 1; norm_num
  · convert vcell8_22_error using 1; norm_num
  · convert vcell8_23_error using 1; norm_num
  · convert vcell8_24_error using 1; norm_num
  · convert vcell8_25_error using 1; norm_num
  · convert vcell8_26_error using 1; norm_num
  · convert vcell8_27_error using 1; norm_num
  · convert vcell8_28_error using 1; norm_num
  · convert vcell8_29_error using 1; norm_num
  · convert vcell8_30_error using 1; norm_num
  · convert vcell8_31_error using 1; norm_num
  · convert vcell8_32_error using 1; norm_num
  · convert vcell8_33_error using 1; norm_num
  · convert vcell8_34_error using 1; norm_num
  · convert vcell8_35_error using 1; norm_num
  · convert vcell8_36_error using 1; norm_num
  · convert vcell8_37_error using 1; norm_num
  · convert vcell8_38_error using 1; norm_num
  · convert vcell8_39_error using 1; norm_num
  · convert vcell8_40_error using 1; norm_num
  · convert vcell8_41_error using 1; norm_num
  · convert vcell8_42_error using 1; norm_num
  · convert vcell8_43_error using 1; norm_num
  · convert vcell8_44_error using 1; norm_num
  · convert vcell8_45_error using 1; norm_num
  · convert vcell8_46_error using 1; norm_num
  · convert vcell8_47_error using 1; norm_num
  · convert vcell8_48_error using 1; norm_num
  · convert vcell8_49_error using 1; norm_num
  · convert vcell8_50_error using 1; norm_num
  · convert vcell8_51_error using 1; norm_num
  · convert vcell8_52_error using 1; norm_num
  · convert vcell8_53_error using 1; norm_num
  · convert vcell8_54_error using 1; norm_num
  · convert vcell8_55_error using 1; norm_num
  · convert vcell8_56_error using 1; norm_num
  · convert vcell8_57_error using 1; norm_num
  · convert vcell8_58_error using 1; norm_num
  · convert vcell8_59_error using 1; norm_num
  · convert vcell8_60_error using 1; norm_num
  · convert vcell8_61_error using 1; norm_num
  · convert vcell8_62_error using 1; norm_num
  · convert vcell8_63_error using 1; norm_num
  · convert vcell8_64_error using 1; norm_num
  · convert vcell8_65_error using 1; norm_num
  · convert vcell8_66_error using 1; norm_num
  · convert vcell8_67_error using 1; norm_num
  · convert vcell8_68_error using 1; norm_num
  · convert vcell8_69_error using 1; norm_num
  · convert vcell8_70_error using 1; norm_num
  · convert vcell8_71_error using 1; norm_num
  · convert vcell8_72_error using 1; norm_num
  · convert vcell8_73_error using 1; norm_num
  · convert vcell8_74_error using 1; norm_num
  · convert vcell8_75_error using 1; norm_num
  · convert vcell8_76_error using 1; norm_num
  · convert vcell8_77_error using 1; norm_num
  · convert vcell8_78_error using 1; norm_num
  · convert vcell8_79_error using 1; norm_num
  · convert vcell8_80_error using 1; norm_num
  · convert vcell8_81_error using 1; norm_num
  · convert vcell8_82_error using 1; norm_num
  · convert vcell8_83_error using 1; norm_num
  · convert vcell8_84_error using 1; norm_num
  · convert vcell8_85_error using 1; norm_num
  · convert vcell8_86_error using 1; norm_num
  · convert vcell8_87_error using 1; norm_num
  · convert vcell8_88_error using 1; norm_num
  · convert vcell8_89_error using 1; norm_num
  · convert vcell8_90_error using 1; norm_num
  · convert vcell8_91_error using 1; norm_num
  · convert vcell8_92_error using 1; norm_num
  · convert vcell8_93_error using 1; norm_num
  · convert vcell8_94_error using 1; norm_num
  · convert vcell8_95_error using 1; norm_num
  · convert vcell8_96_error using 1; norm_num
  · convert vcell8_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
