module

public import DedekindZetaZeroFree.Adeles.Lattices.AdditiveFundamentalDomain
public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ChamberCosetBounds
public import DedekindZetaZeroFree.Analysis.IsolatedSpectralProjections
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HolomorphicKTypeGeneration

@[expose] public section

section

noncomputable section
open scoped Classical NumberField NNReal Topology Pointwise

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps

private theorem invariant_level {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N K : Subgroup G) [N.Normal]
    (hK : IsCompact (K : Set G))
    (hb : ∀ W : Set N, W ∈ nhds 1 → ∃ U : CompactOpenLevel N,
      (U.toOpenSubgroup : Set N) ⊆ W) :
    ∃ U : CompactOpenLevel N, K ≤ Subgroup.normalizer (U.toOpenSubgroup.toSubgroup.map N.subtype) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨U₀, _⟩ := hb Set.univ (by simp)
  let c (k : K) : N →* N :=
    { toFun := fun n => ⟨k.val * n.val * k.val⁻¹, Subgroup.Normal.conj_mem inferInstance n.val n.property k.val⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; dsimp; group }
  let U : Subgroup N := ⨅ k : K, U₀.toOpenSubgroup.toSubgroup.comap (c k)
  have hUc : Continuous (fun p : K × N => c p.1 p.2) := by
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst).inv |>.subtype_mk _
  have hopen : IsOpen (U : Set N) := by
    have he : (U : Set N) = (Prod.snd '' ((fun p : K × N => c p.1 p.2) ⁻¹'
        (U₀.toOpenSubgroup : Set N)ᶜ))ᶜ := by
      ext n
      simp [U, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_image]
    rw [he]
    exact (isClosedMap_snd_of_compactSpace _
      (U₀.toOpenSubgroup.isOpen.isClosed_compl.preimage hUc)).isOpen_compl
  have hsub : U ≤ U₀.toOpenSubgroup.toSubgroup := by
    intro n hn
    have h := Subgroup.mem_iInf.mp hn (1 : K)
    simpa [c] using h
  have hcompact : IsCompact (U : Set N) :=
    U₀.isCompact.of_isClosed_subset (OpenSubgroup.isClosed ⟨U, hopen⟩) hsub
  refine ⟨⟨⟨U, hopen⟩, hcompact⟩, ?_⟩
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    obtain ⟨a, ha, rfl⟩ := hn
    refine ⟨⟨k * a.val * k⁻¹, Subgroup.Normal.conj_mem inferInstance a.val a.property k⟩, ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro l
    have h := Subgroup.mem_iInf.mp ha (l * ⟨k,hk⟩)
    change (c l ⟨k * a.val * k⁻¹, _⟩) ∈ U₀.toOpenSubgroup
    change (c (l * ⟨k,hk⟩) a) ∈ U₀.toOpenSubgroup at h
    convert h using 1
    apply Subtype.ext
    dsimp [c]
    group
  · intro hn
    obtain ⟨a, ha, he⟩ := hn
    change a.val = k * n * k⁻¹ at he
    have hna : n = k⁻¹ * a.val * k := by rw [he]; group
    refine ⟨⟨n, ?_⟩, ?_, rfl⟩
    · rw [hna]; simpa using Subgroup.Normal.conj_mem inferInstance a.val a.property k⁻¹
    · apply Subgroup.mem_iInf.mpr
      intro l
      have h := Subgroup.mem_iInf.mp ha (l * ⟨k⁻¹, K.inv_mem hk⟩)
      change (c l ⟨n, _⟩) ∈ U₀.toOpenSubgroup
      change (c (l * ⟨k⁻¹, K.inv_mem hk⟩) a) ∈ U₀.toOpenSubgroup at h
      convert h using 1
      apply Subtype.ext
      dsimp [c]
      rw [hna]
      group

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
open KPGlobalTorusBorelNormTwistTransport
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

 def raw (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ) :
    IwasawaData F ζ hζ := ⟨D.K, D.compact, D.decomposition, D.overlap⟩

private theorem norm_compact_supergroup
    (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ)
    (L : Subgroup (G F ζ hζ)) (hL : IsCompact (L : Set (G F ζ hζ))) (hKL : D.K ≤ L)
    (l : L) : iwasawaNorm F ζ hζ (raw D) l.val = 1 := by
  let f : G F ζ hζ → ℝ := fun g => ((iwasawaNorm F ζ hζ (raw D) g : ℝ≥0) : ℝ)
  have hc : Continuous f := fullCusp_iwasawaNorm_continuous F ζ hζ D
  have hp : ∀ g, 0 < f g := fun g => by
    exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero (iwasawaNorm F ζ hζ (raw D) g))
  obtain ⟨m, hm, hmax⟩ := hL.exists_isMaxOn ⟨1,L.one_mem⟩ hc.continuousOn
  have hB : ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F),
      t.val * KPGlobalTorusFunctionData.N F ζ hζ x ∈ L →
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1 := by
    intro t x hb
    let b := t.val * KPGlobalTorusFunctionData.N F ζ hζ x
    have hmul : ∀ g, f (b * g) =
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) * f g := by
      intro g
      dsimp [f,b]
      rw [iwasawaNorm_borel_mul F ζ hζ (raw D) t x g, Units.val_mul, NNReal.coe_mul]
    have h₁ : f (b * m) ≤ f m := hmax (L.mul_mem hb hm)
    rw [hmul] at h₁
    have h₂ : f (b⁻¹ * m) ≤ f m := hmax (L.mul_mem (L.inv_mem hb) hm)
    have h₃ := hmul (b⁻¹ * m)
    rw [mul_inv_cancel_left] at h₃
    have he : (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) = 1 := by
      have hd : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
        exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t))
      have hmpos := hp m
      nlinarith
    apply Units.ext
    exact NNReal.coe_injective he
  obtain ⟨t,x,k,he⟩ := D.decomposition l.val
  have hb : t.val * KPGlobalTorusFunctionData.N F ζ hζ x ∈ L := by
    have hh : t.val * KPGlobalTorusFunctionData.N F ζ hζ x = l.val * k.val⁻¹ := by rw [he]; group
    rw [hh]
    exact L.mul_mem l.property (L.inv_mem (hKL k.property))
  rw [he, iwasawaNorm_formula F ζ hζ (raw D) t x k]
  exact hB t x hb

theorem exists_iwasawaNorm_right_level
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ) :
    ∃ U : KPMsRationalCompactCrossPairing.Level F ζ hζ,
      ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (g * u.val) =
          KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g := by
  let N := KPGlobalTorusFunctionData.finitePart F ζ hζ
  have hn : N.Normal := by
    dsimp [N]
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
    exact ActualFiniteFactor.finiteSubgroup_normal F ζ hζ
  letI := hn
  obtain ⟨U, hU⟩ := invariant_level N D.K D.compact
    (KPGlobalTorusFiniteStagesCofinality.finitePart_compactOpen_basis F ζ hζ)
  let L := D.K ⊔ KPGlobalTorusFunctionData.globalLevel F ζ hζ U
  have hL : IsCompact (L : Set (G F ζ hζ)) := by
    dsimp [L]
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D.K
      (KPGlobalTorusFunctionData.globalLevel F ζ hζ U) hU]
    exact D.compact.mul (globalLevel_isCompact F ζ hζ U)
  refine ⟨U, ?_⟩
  intro g u
  obtain ⟨t,x,k,rfl⟩ := D.decomposition g
  change iwasawaNorm F ζ hζ (raw D)
    (((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) * u.val) =
    iwasawaNorm F ζ hζ (raw D) ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val)
  rw [mul_assoc, iwasawaNorm_borel_mul F ζ hζ (raw D) t x,
    iwasawaNorm_formula F ζ hζ (raw D) t x k]
  have hku : k.val * u.val ∈ L := L.mul_mem
    ((show D.K ≤ L from le_sup_left) k.property)
    ((show KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤ L from le_sup_right) u.property)
  rw [norm_compact_supergroup D L hL le_sup_left ⟨_,hku⟩, mul_one]

end DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps

end

end
