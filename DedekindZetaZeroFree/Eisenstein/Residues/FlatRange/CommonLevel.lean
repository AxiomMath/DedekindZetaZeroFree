module

public import DedekindZetaZeroFree.Eisenstein.Residues.FlatRange.ActualSourceStage
public import DedekindZetaZeroFree.Eisenstein.Continuation.RegularSymmetriesAndUniformRightLevels
public import DedekindZetaZeroFree.Eisenstein.Residues.FlatRange.UniformFiniteLevels

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.ResidualFlatRange.Source.CommonLevel
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance levelTopGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance levelBorel (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K

local instance levelBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

private def meetLevel (U V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
  ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩

private lemma meetLevel_le (U V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ (meetLevel F ζ hζ U V) ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U ∧
    KPGlobalTorusFunctionData.globalLevel F ζ hζ (meetLevel F ζ hζ U V) ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ V := by
  constructor
  · exact Subgroup.map_mono (by dsimp only [meetLevel]; rw [OpenSubgroup.toSubgroup_inf]; exact inf_le_left)
  · exact Subgroup.map_mono (by dsimp only [meetLevel]; rw [OpenSubgroup.toSubgroup_inf]; exact inf_le_right)

private lemma flat_uniform_level_of_norm (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K)
    (hlevel : ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
          (KPLiteralChamber.literalIwasawa F ζ hζ K hK) (g * u.val) =
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
          (KPLiteralChamber.literalIwasawa F ζ hζ K hK) g) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ s g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
        f.val s (g * u) = f.val s g := by
  obtain ⟨U, hU⟩ := (f.property.1 0).1.2.2
  obtain ⟨V, hV⟩ := hlevel
  refine ⟨meetLevel F ζ hζ U V, ?_⟩
  intro s g u hu
  obtain ⟨hleU, hleV⟩ := meetLevel_le F ζ hζ U V
  rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f s (g*u),
    KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f s g,
    hV g ⟨u, hleV hu⟩, hU g u (hleU hu)]

private lemma source_uniform_level_of_sources (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (hlevel : ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
          (KPLiteralChamber.literalIwasawa F ζ hζ K hK) (g * u.val) =
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
          (KPLiteralChamber.literalIwasawa F ζ hζ K hK) g)
    (hconj : ∀ (C : Set (G F ζ hζ)), IsCompact C →
      ∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
        ∃ V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
          ∀ k ∈ C, ∀ u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V,
            k⁻¹ * u * k ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (μ : Measure K) (s : ℂ) (h : C(K, ℂ)) (g u : G F ζ hζ),
        u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
          source F ζ hζ K hK μ f a s h (g*u) = source F ζ hζ K hK μ f a s h g := by
  obtain ⟨U, hU⟩ := flat_uniform_level_of_norm F ζ hζ K hK f hlevel
  have hC : IsCompact ((fun k : G F ζ hζ => k * a) '' (K : Set (G F ζ hζ))) :=
    hK.1.image (continuous_id.mul continuous_const)
  obtain ⟨V, hV⟩ := hconj _ hC U
  obtain ⟨W, hW⟩ := hlevel
  refine ⟨meetLevel F ζ hζ V W, ?_⟩
  intro μ s h g u hu
  obtain ⟨hleV, hleW⟩ := meetLevel_le F ζ hζ V W
  have ha : alpha F ζ hζ K hK (g*u) = alpha F ζ hζ K hK g := by
    unfold alpha
    rw [hW g ⟨u, hleW hu⟩]
  simp only [source, ha]
  congr 1
  apply integral_congr_ae
  filter_upwards with k
  have hc : (k.val * a)⁻¹ * u * (k.val * a) ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    hV (k.val*a) ⟨k.val,k.property,rfl⟩ u (hleV hu)
  have he : (g * u) * k.val * a = (g * k.val * a) * ((k.val * a)⁻¹ * u * (k.val * a)) := by group
  rw [he, hU s (g*k.val*a) _ hc]

theorem source_uniform_level (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (μ : Measure K) (s : ℂ) (h : C(K, ℂ)) (g u : G F ζ hζ),
        u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
          source F ζ hζ K hK μ f a s h (g*u) = source F ζ hζ K hK μ f a s h g := by
  exact source_uniform_level_of_sources F ζ hζ K hK f a
    (KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level
      (KPLiteralChamber.literalIwasawa F ζ hζ K hK))
    (fun C hC U => compact_uniform_conjugated_finite_level F ζ hζ C hC U)

end DedekindZetaZeroFree.ResidualFlatRange.Source.CommonLevel

end
