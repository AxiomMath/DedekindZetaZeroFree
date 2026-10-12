module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FiniteRootInsertionAndProductFamilies

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPLiteralScalarHCFiniteBorel
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCFiniteInsertion
open KPLiteralScalarHCFiniteRoot KPLiteralScalarHCFiniteProduct KPLiteralScalarHCFiniteOutside
open KPLiteralScalarHCCompactOrbit KPCplxCharacterHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
variable (S : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)

theorem canonical_borel_root_torus (b : S.borel.B) :
    ∃ u : q.adicCompletion F,
      b = S.borel.upperRoot (Multiplicative.ofAdd u) * S.borel.torus (S.borel.retract b) := by
  let c := b * (S.borel.torus (S.borel.retract b))⁻¹
  have hc : S.borel.retract c = 1 := by
    simp [c, map_mul, map_inv, S.borel.retract_torus]
  obtain ⟨u, hu⟩ := S.borel.borel_decomposition c
  rw [hc, map_one, one_mul] at hu
  refine ⟨Multiplicative.toAdd u, ?_⟩
  change b = S.borel.upperRoot u * S.borel.torus (S.borel.retract b)
  rw [← hu]
  dsimp only [c]
  group

theorem finiteInsertion_canonical_borel (b : S.borel.B) :
    ∃ u : q.adicCompletion F,
      (finiteInsertion F ζ hζ q b.val).val =
        KPGlobalTorusFunctionData.N F ζ hζ (finiteRootAdele F q u) *
          (finiteInsertion F ζ hζ q (S.borel.retract b).val).val := by
  obtain ⟨u, hu⟩ := canonical_borel_root_torus F ζ hζ q S b
  refine ⟨u, ?_⟩
  conv_lhs => rw [hu]
  change (finiteInsertion F ζ hζ q
    ((S.borel.upperRoot (Multiplicative.ofAdd u)).val * (S.borel.torus (S.borel.retract b)).val)).val = _
  rw [map_mul]
  change (finiteInsertion F ζ hζ q (S.borel.upperRoot (Multiplicative.ofAdd u))).val *
    (finiteInsertion F ζ hζ q (S.borel.torus (S.borel.retract b))).val = _
  rw [finiteInsertion_canonical_root, S.torus_full]

theorem canonical_borel_half_torus (b : S.borel.B) :
    KPLocalPrincipalSeries.deltaHalf S.borel b =
      KPLocalPrincipalSeries.deltaHalf S.borel (S.borel.torus (S.borel.retract b)) := by
  simp only [KPLocalPrincipalSeries.deltaHalf, S.borel.retract_torus]

variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)

variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

end DedekindZetaZeroFree.KPLiteralScalarHCFiniteBorel

end
