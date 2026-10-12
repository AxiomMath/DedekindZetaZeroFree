module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexStandardIntertwinerGerm
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.AdelicRestrictedProductTopology
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Unramified.SphericalEulerNormalization
public import DedekindZetaZeroFree.LFunctions.Dedekind.ExceptionalEulerNormalizer

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPGlobalFiniteSIntertwiner

open IsDedekindDomain Filter
open scoped NumberField Topology TensorProduct Classical

variable (F : Type) [Field F] [NumberField F]

def residueSize (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  Ideal.absNorm v.asIdeal

def goodFactor (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  KPGlobalGoodEulerFactor.sphericalCoefficient (residueSize F v) 1 s

def enlargementFactor (S T : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  ∏ v ∈ T \ S, goodFactor F v s

abbrev normalizer
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ → ℂ :=
  GlobalZetaNormalizer.exceptionalNormalizer  F ζ hζ S

def residueNormalizer
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  (PositiveZetaResidue.exteriorResidue F S : ℂ) /
    (6 * GlobalZetaNormalizer.exteriorZeta  F ζ hζ S 2)

theorem residueNormalizer_pos
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (residueNormalizer F  ζ hζ S).im = 0 ∧
    0 < (residueNormalizer F  ζ hζ S).re := by
  obtain ⟨ε, hε, hd, hm, hg, heq, hzero, him, hre, hrest⟩ :=
    GlobalZetaNormalizer.positive_simple_exceptional_normalizer  F ζ hζ S
  exact ⟨by simpa [residueNormalizer, hzero] using him,
    by simpa [residueNormalizer, hzero] using hre⟩

section TensorFormulas

universe u v
variable (V : KPHilbert.Place F → Type u) (W : KPHilbert.Place F → Type v)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

end TensorFormulas

end DedekindZetaZeroFree.KPGlobalFiniteSIntertwiner

end
