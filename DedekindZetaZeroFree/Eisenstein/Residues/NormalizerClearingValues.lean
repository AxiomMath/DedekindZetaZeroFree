module

public import DedekindZetaZeroFree.Analysis.MeromorphicGermUniqueness
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Global.FiniteSetEnlargement

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open Filter

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue

theorem clearing_value_from_global_cofactor
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    {domain : Set ℂ} {m b a : ℂ → ℂ}
    (hm : MeromorphicOn m domain) (hb : MeromorphicOn b Set.univ)
    (hconnected : IsConnected domain)
    (hchamber : {s : ℂ | (1 : ℝ) / 3 < s.re} ⊆ domain)
    (hzero : (0 : ℂ) ∈ domain)
    (hbzero : ContinuousAt b 0) (hazero : ContinuousAt a 0)
    (hfactor : ∀ s, (1 : ℝ) / 3 < s.re →
      m s = KPGlobalFiniteSIntertwiner.normalizer F  ζ hζ E s * b s)
    (hclear : a =ᶠ[𝓝[≠] (0 : ℂ)] fun s => s * m s) :
    a 0 = KPGlobalFiniteSIntertwiner.residueNormalizer F  ζ hζ E * b 0 := by
  have hz := (GlobalZetaNormalizer.exterior_positive_simple_residue  F ζ hζ E).1
  have hshift (c : ℂ) : MeromorphicOn
      (fun s : ℂ => GlobalZetaNormalizer.exteriorZeta  F ζ hζ E (c + 6 * s))
      domain :=
    hz.comp_analyticOnNhd (by fun_prop) (fun _ _ => Set.mem_univ _)
  have hc : MeromorphicOn (KPGlobalFiniteSIntertwiner.normalizer F  ζ hζ E)
      domain := (hshift 1).div (hshift 2)
  have hmb := KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
    hm (hc.mul (fun s _ => hb s (Set.mem_univ s))) hconnected.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re) hchamber
    ⟨1, by norm_num⟩ (fun s hs => hfactor s hs) hzero
  obtain ⟨ε, hε, hden, hmero, han, hregular, hvalue, him, hpos, horder, hlimit⟩ :=
    GlobalZetaNormalizer.positive_simple_exceptional_normalizer  F ζ hζ E
  have he : a =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => (s * KPGlobalFiniteSIntertwiner.normalizer F  ζ hζ E s) * b s) := by
    filter_upwards [hclear, hmb] with s hcs hms
    simp only [hcs, hms, Pi.mul_apply, mul_assoc]
  have ht := hlimit.mul (hbzero.tendsto.mono_left nhdsWithin_le_nhds)
  exact tendsto_nhds_unique
    ((hazero.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (by simpa [KPGlobalFiniteSIntertwiner.residueNormalizer,
      KPGlobalFiniteSIntertwiner.normalizer] using ht)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue

end
