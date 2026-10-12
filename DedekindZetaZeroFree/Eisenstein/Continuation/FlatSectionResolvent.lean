module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarFlatSections
public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_scalar_continuation
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (B : JointRootAlignedSources R N) (v : R.A.UnitQuotient) :
    ∃ E : ℂ → Functions R,
      (∀ g, MeromorphicNFOn (fun s => E s g) KPContinuation.spectralDomain) ∧
      ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
        E s g = KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
          B.sources.K (B.sources.flat v) s g := by
  let ζ := R.A.zeta12
  let hζ := R.A.primitive_zeta12
  letI : T2Space (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨C, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨Haar, _, _, P, ⟨H⟩⟩ :=
    kp_ms_fixed_haar_disintegration F ζ hζ
      (Measure.haar : Measure (KPLiteralRaw.G F ζ hζ)) inferInstance
  exact literal_scalar_continuation F ζ hζ C Haar P H
    B.sources.K B.sources.iwasawa (B.sources.flat v)

end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end
