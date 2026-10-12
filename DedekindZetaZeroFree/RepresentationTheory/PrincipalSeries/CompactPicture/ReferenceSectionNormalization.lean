module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralScalarCanonicalReferenceComparison
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalGoodSphericalImage

section Local
variable {K : Type*} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
  {T : LocalHeisenbergData H D}

theorem fixed_section_eq_identity_scalar
    (B : LocalBorelData (K := K) (G := G) T) (P : Polarization T) (I : IwasawaData B)
    (h : UnramifiedCompactInducingData B P I)
    (f f₀ : sectionSpace B P .plus 0)
    (hf : f ∈ fixedSubmodule (IPlus B P) I.compact.toOpenSubgroup)
    (hf₀ : f₀ ∈ fixedSubmodule (IPlus B P) I.compact.toOpenSubgroup)
    (h₀ : (f₀.val 1).val 1 = 1) :
    f = (f.val 1).val 1 • f₀ := by
  let : AddCommGroup (sectionSpace B P .plus 0) := Module.addCommMonoidToAddCommGroup ℂ
  let U := fixedSubmodule (V := sectionSpace B P .plus 0)
    (IPlus B P) (I.compact.toOpenSubgroup : Subgroup G)
  obtain ⟨hfinite, hrank⟩ := plus_compact_fixed_line B P I h
  let : Module.Finite ℂ U := hfinite
  have hn : (⟨f₀, hf₀⟩ : U) ≠ 0 := by
    intro he
    have hz : (f₀.val 1).val 1 = 0 := congrArg (fun u : U => (u.val.val 1).val 1) he
    rw [h₀] at hz
    exact one_ne_zero hz
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hrank hn (⟨f, hf⟩ : U)
  have he : c • f₀ = f := congrArg Subtype.val hc
  have hs : c = (f.val 1).val 1 := by
    have hval := congrArg (fun u : sectionSpace B P .plus 0 => (u.val 1).val 1) he
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h₀, mul_one] using hval
  exact he.symm.trans (congrArg (fun c : ℂ => c • f₀) hs)

end Local

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

end DedekindZetaZeroFree.KPLiteralScalarCanonicalReferenceComparison

end
