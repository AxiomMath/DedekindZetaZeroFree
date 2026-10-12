module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormalizedFiniteCosetCovers
public import DedekindZetaZeroFree.Metaplectic.Weil.Polarization.UnipotentSubgroupTopology

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology NNReal
open Topology
namespace DedekindZetaZeroFree.KPSpatialSmoothing
open KPGlobalTorusFunctionData
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming inBorel → inBorel

 theorem actual_cover_of_torus_cosets
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (J0 : FiniteLevel F ζ hζ) (n : ℕ) (r : Fin n → E F ζ hζ)
    (hnormal : ∀ (k : D.K) (j : globalLevel F ζ hζ J0),
      k.val⁻¹ * j.val * k.val ∈ globalLevel F ζ hζ J0)
    (htorus : ∀ t : E F ζ hζ, ∃ (i : Fin n) (h : (P0 F ζ hζ).H)
      (j : (globalLevel F ζ hζ J0).comap (torus F ζ hζ).subtype),
      t = h.val * r i * j.val) :
    ∀ g : G F ζ hζ, ∃ (i : Fin n) (h : (P0 F ζ hζ).H) (x : Adeles F)
      (k : D.K) (j : globalLevel F ζ hζ J0),
      g = (((h.val.val * N F ζ hζ x) * (r i).val) * k.val) * j.val := by
  intro g
  obtain ⟨t, x, k, hg⟩ := D.decomposition g
  obtain ⟨i, h, j, ht⟩ := htorus t
  let jg : globalLevel F ζ hζ J0 := ⟨j.val.val, j.property⟩
  let j' : globalLevel F ζ hζ J0 :=
    ⟨k.val⁻¹ * jg.val * k.val, hnormal k jg⟩
  let u : E F ζ hζ := r i * j.val
  let y : Adeles F := (p F ζ hζ u : Adeles F) * x
  have hc : u.val * N F ζ hζ x * u.val⁻¹ = N F ζ hζ y :=
    ActualBorelRetraction.torus_conjugates_root F ζ hζ u x
  have hu : u.val * N F ζ hζ x = N F ζ hζ y * u.val := by
    rw [← hc]; group
  refine ⟨i, h, y, k, j', ?_⟩
  rw [hg, ht]
  change ((h.val.val * (r i).val * j.val.val) * N F ζ hζ x) * k.val =
    (((h.val.val * N F ζ hζ y) * (r i).val) * k.val) *
      (k.val⁻¹ * j.val.val * k.val)
  calc
    _ = (h.val.val * (u.val * N F ζ hζ x)) * k.val := by
      change ((h.val.val * (r i).val * j.val.val) * N F ζ hζ x) * k.val =
        (h.val.val * (((r i).val * j.val.val) * N F ζ hζ x)) * k.val
      group
    _ = (h.val.val * (N F ζ hζ y * u.val)) * k.val := by rw [hu]
    _ = _ := by
      change (h.val.val * (N F ζ hζ y * ((r i).val * j.val.val))) * k.val =
        (((h.val.val * N F ζ hζ y) * (r i).val) * k.val) *
          (k.val⁻¹ * j.val.val * k.val)
      group

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming finitePart_normal → finitePart_normal

 theorem compact_normalized_finite_core
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (J : FiniteLevel F ζ hζ) :
    ∃ J0 : FiniteLevel F ζ hζ,
      globalLevel F ζ hζ J0 ≤ globalLevel F ζ hζ J ∧
      ∀ (k : D.K) (j : globalLevel F ζ hζ J0),
        k.val⁻¹ * j.val * k.val ∈ globalLevel F ζ hζ J0 := by
  let := finitePart_normal F ζ hζ
  let : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  let L : Subgroup (finitePart F ζ hζ) :=
    ⨅ k : D.K, (J.toOpenSubgroup : Subgroup (finitePart F ζ hζ)).comap
      (MulAut.conjNormal k.val⁻¹).toMonoidHom
  let f : finitePart F ζ hζ × D.K → finitePart F ζ hζ :=
    fun p => MulAut.conjNormal p.2.val⁻¹ p.1
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    change Continuous (fun p : finitePart F ζ hζ × D.K =>
      p.2.val⁻¹ * p.1.val * (p.2.val⁻¹)⁻¹)
    fun_prop
  have ho : IsOpen (L : Set (finitePart F ζ hζ)) := by
    have he : (L : Set (finitePart F ζ hζ))ᶜ =
        Prod.fst '' (f ⁻¹' (J.toOpenSubgroup : Set (finitePart F ζ hζ))ᶜ) := by
      ext j
      change (¬ j ∈ L) ↔ _
      simp only [L, Subgroup.mem_iInf, Subgroup.mem_comap,
        Set.mem_image, Set.mem_preimage, Set.mem_compl_iff, Prod.exists]
      change (¬ ∀ k : D.K, f (j, k) ∈ J.toOpenSubgroup) ↔
        ∃ (a : finitePart F ζ hζ) (k : D.K),
          f (a, k) ∉ J.toOpenSubgroup ∧ a = j
      simp
    rw [← isClosed_compl_iff, he]
    exact isClosedMap_fst_of_compactSpace _ (J.toOpenSubgroup.isOpen.isClosed_compl.preimage hf)
  have hle : L ≤ (J.toOpenSubgroup : Subgroup (finitePart F ζ hζ)) := by
    intro j hj
    have h := (Subgroup.mem_iInf.mp hj) (1 : D.K)
    simpa using h
  let J0 : FiniteLevel F ζ hζ :=
    ⟨⟨L, ho⟩, J.isCompact.of_isClosed_subset (OpenSubgroup.isClosed ⟨L, ho⟩) hle⟩
  refine ⟨J0, Subgroup.map_mono hle, ?_⟩
  intro k j
  obtain ⟨a, ha, he⟩ := j.property
  change a.val = j.val at he
  let b : finitePart F ζ hζ := MulAut.conjNormal k.val⁻¹ a
  refine ⟨b, ?_, ?_⟩
  · apply Subgroup.mem_iInf.mpr
    intro l
    have h := (Subgroup.mem_iInf.mp ha) (k * l)
    change MulAut.conjNormal (k.val * l.val)⁻¹ a ∈ J.toOpenSubgroup at h
    change MulAut.conjNormal l.val⁻¹ b ∈ J.toOpenSubgroup
    convert h using 1
    apply Subtype.ext
    dsimp [b]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  · change k.val⁻¹ * a.val * (k.val⁻¹)⁻¹ = _
    rw [inv_inv, he]

end DedekindZetaZeroFree.KPSpatialSmoothing

end

section

noncomputable section
open scoped NumberField Classical Topology NNReal
open Topology
namespace DedekindZetaZeroFree.KPSpatialSmoothing
open KPGlobalTorusFunctionData
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming inBorel → inBorel

private theorem compact_parameter_multiplication
    {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace A] [CompactSpace A]
    (C : Subgroup G) (hC : IsClosed (C : Set G))
    (t : A → G) (ht : Continuous t) :
    IsProperMap (fun p : C × A => p.1.val * t p.2) := by
  let e : G × A ≃ₜ G × A :=
    { toFun := fun p => (p.1 * t p.2, p.2)
      invFun := fun p => (p.1 * (t p.2)⁻¹, p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      continuous_toFun := (continuous_fst.mul (ht.comp continuous_snd)).prodMk continuous_snd
      continuous_invFun := (continuous_fst.mul (ht.comp continuous_snd).inv).prodMk continuous_snd }
  have he : IsProperMap (fun p : C × A => (p.1.val, p.2)) :=
    hC.isProperMap_subtypeVal.prodMap isProperMap_id
  exact isProperMap_fst_of_compactSpace.comp (e.isProperMap.comp he)

private theorem finite_compact_multiplication
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (C K J : Subgroup G) (hC : IsClosed (C : Set G))
    (hK : IsCompact (K : Set G)) (hJ : IsCompact (J : Set G))
    (n : ℕ) (r : Fin n → G) :
    IsProperMap (fun p : Fin n × C × K × J =>
      p.2.1.val * r p.1 * p.2.2.1.val * p.2.2.2.val) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  let e : Fin n × C × K × J ≃ₜ C × (Fin n × K × J) :=
    { toFun := fun p => (p.2.1, p.1, p.2.2)
      invFun := fun p => (p.2.1, p.1, p.2.2)
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have ht : Continuous (fun p : Fin n × K × J => r p.1 * p.2.1.val * p.2.2.val) := by
    exact ((continuous_of_discreteTopology.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hp := (compact_parameter_multiplication C hC _ ht).comp e.isProperMap
  change IsProperMap (fun p : Fin n × C × K × J =>
    p.2.1.val * (r p.1 * p.2.2.1.val * p.2.2.2.val)) at hp
  simpa only [mul_assoc] using hp

private theorem actual_globalLevel_compact
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (J : FiniteLevel F ζ hζ) :
    IsCompact (globalLevel F ζ hζ J : Set (G F ζ hζ)) := by
  unfold globalLevel
  rw [Subgroup.coe_map]
  exact J.isCompact.image continuous_subtype_val

private theorem actual_multiplication_geometry
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (J0 : FiniteLevel F ζ hζ) (n : ℕ) (r : Fin n → E F ζ hζ)
    (hC : IsClosed (actualC F ζ hζ : Set (G F ζ hζ)))
    (hcover : ∀ g : G F ζ hζ, ∃ (i : Fin n) (h : (P0 F ζ hζ).H) (x : Adeles F)
      (k : D.K) (j : globalLevel F ζ hζ J0),
      g = (((h.val.val * N F ζ hζ x) * (r i).val) * k.val) * j.val) :
    IsProperMap (fun p : Fin n × actualC F ζ hζ × D.K × globalLevel F ζ hζ J0 =>
      p.2.1.val * (r p.1).val * p.2.2.1.val * p.2.2.2.val) ∧
    IsQuotientMap (fun p : Fin n × actualC F ζ hζ × D.K × globalLevel F ζ hζ J0 =>
      p.2.1.val * (r p.1).val * p.2.2.1.val * p.2.2.2.val) := by
  have hJ := actual_globalLevel_compact F ζ hζ J0
  have hp := finite_compact_multiplication (actualC F ζ hζ) D.K
    (globalLevel F ζ hζ J0) hC D.compact hJ n (fun i => (r i).val)
  refine ⟨hp, hp.isClosedMap.isQuotientMap hp.continuous ?_⟩
  intro g
  obtain ⟨i, h, x, k, j, he⟩ := hcover g
  let c : actualC F ζ hζ :=
    ⟨h.val.val * N F ζ hζ x, (mem_actualC_iff F ζ hζ _).mpr ⟨h, x, rfl⟩⟩
  exact ⟨(i, c, k, j), he.symm⟩

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming finitePart_normal → finitePart_normal

theorem actual_covariant_finite_cover
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (J : FiniteLevel F ζ hζ) :
    ∃ (J0 : FiniteLevel F ζ hζ) (n : ℕ) (r : Fin n → E F ζ hζ),
      globalLevel F ζ hζ J0 ≤ globalLevel F ζ hζ J ∧
      (∀ (k : D.K) (j : globalLevel F ζ hζ J0),
        k.val⁻¹ * j.val * k.val ∈ globalLevel F ζ hζ J0) ∧
      (∀ g : G F ζ hζ, ∃ (i : Fin n) (h : (P0 F ζ hζ).H) (x : Adeles F)
        (k : D.K) (j : globalLevel F ζ hζ J0),
        g = (((h.val.val * N F ζ hζ x) * (r i).val) * k.val) * j.val) ∧
      IsClosed (actualC F ζ hζ : Set (G F ζ hζ)) ∧
      Continuous (actualChi F ζ hζ) ∧
      IsProperMap (fun p : Fin n × actualC F ζ hζ × D.K × globalLevel F ζ hζ J0 =>
        p.2.1.val * (r p.1).val * p.2.2.1.val * p.2.2.2.val) ∧
      IsQuotientMap (fun p : Fin n × actualC F ζ hζ × D.K × globalLevel F ζ hζ J0 =>
        p.2.1.val * (r p.1).val * p.2.2.1.val * p.2.2.2.val) := by
  obtain ⟨J0, n, r, hle, hnormal, htorus⟩ :=
    actual_normalized_torus_finite_cover F ζ hζ D J
  have hcover := actual_cover_of_torus_cosets F ζ hζ D J0 n r hnormal htorus
  obtain ⟨hC, hchi⟩ := actual_HN_closed_character_continuous F ζ hζ
  obtain ⟨hp, hq⟩ := actual_multiplication_geometry F ζ hζ D J0 n r hC hcover
  exact ⟨J0, n, r, hle, hnormal, hcover, hC, hchi, hp, hq⟩

end DedekindZetaZeroFree.KPSpatialSmoothing

end
end
