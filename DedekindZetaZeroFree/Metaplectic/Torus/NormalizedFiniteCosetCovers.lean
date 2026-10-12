module

public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal Topology
namespace DedekindZetaZeroFree.KPSpatialSmoothing
open KPGlobalTorusFunctionData KPGlobalTorusFiniteStagesCofinality

open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming finitePart_normal → finitePart_normal
private theorem normalized_shrink
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ) (J : FiniteLevel F ζ hζ) :
    ∃ J0 : FiniteLevel F ζ hζ,
      globalLevel F ζ hζ J0 ≤ globalLevel F ζ hζ J ∧
      ∀ (k : D.K) (j : globalLevel F ζ hζ J0),
        k.val⁻¹ * j.val * k.val ∈ globalLevel F ζ hζ J0 := by
  letI := finitePart_normal F ζ hζ
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  let conj (k : D.K) : finitePart F ζ hζ →* finitePart F ζ hζ :=
    { toFun := fun u => ⟨k.val⁻¹ * u.val * k.val,
        Subgroup.Normal.conj_mem inferInstance u.val u.property k.val⁻¹ |> (by simpa using ·)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intros; apply Subtype.ext; change _ = _; simp [mul_assoc] }
  let V : Subgroup (finitePart F ζ hζ) :=
    ⨅ k : D.K, J.toOpenSubgroup.toSubgroup.comap (conj k)
  have hV (u : finitePart F ζ hζ) : u ∈ V ↔ ∀ k : D.K, conj k u ∈ J.toOpenSubgroup := by
    simp [V]
  have hn : ∀ᶠ u in nhds (1 : finitePart F ζ hζ), ∀ k : D.K, conj k u ∈ J.toOpenSubgroup := by
    have ht : ∀ᶠ u in nhds (1 : finitePart F ζ hζ), ∀ k ∈ (Set.univ : Set D.K), conj k u ∈ J.toOpenSubgroup := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro k _
      have hc : Continuous (fun p : finitePart F ζ hζ × D.K => conj p.2 p.1) := by
        apply Continuous.subtype_mk
        change Continuous (fun p : finitePart F ζ hζ × D.K => p.2.val⁻¹ * p.1.val * p.2.val)
        fun_prop
      exact hc.continuousAt.eventually (J.toOpenSubgroup.isOpen.mem_nhds (by change conj k 1 ∈ J.toOpenSubgroup; rw [map_one]; exact J.toOpenSubgroup.one_mem))
    simpa using ht
  have hVo : IsOpen (V : Set (finitePart F ζ hζ)) := by
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    change ∀ᶠ u in nhds (1 : finitePart F ζ hζ), u ∈ V
    simpa only [hV] using hn
  have hVJ : V ≤ J.toOpenSubgroup.toSubgroup := by
    intro u hu
    simpa [conj] using (hV u).mp hu 1
  let J0 : FiniteLevel F ζ hζ := ⟨⟨V, hVo⟩,
    J.isCompact.of_isClosed_subset (V.isClosed_of_isOpen hVo) hVJ⟩
  refine ⟨J0, Subgroup.map_mono hVJ, ?_⟩
  intro k j
  obtain ⟨u, hu, he⟩ := j.property
  change u.val = j.val at he
  rw [← he]
  refine ⟨conj k u, ?_, ?_⟩
  · apply (hV _).mpr
    intro l
    have ht := (hV u).mp hu (k * l)
    convert ht using 1
    apply Subtype.ext
    change l.val⁻¹ * (k.val⁻¹ * u.val * k.val) * l.val =
      (k.val * l.val)⁻¹ * u.val * (k.val * l.val)
    group
  · rfl
private theorem torus_cover
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (J : FiniteLevel F ζ hζ) :
    ∃ (n : ℕ) (r : Fin n → E F ζ hζ),
      ∀ t : E F ζ hζ, ∃ (i : Fin n) (h : (P0 F ζ hζ).H)
        (u : (globalLevel F ζ hζ J).comap (E F ζ hζ).subtype),
        t = h.val * r i * u.val := by
  let π := finiteTorusClassProjection F ζ hζ
  let pD := KPGlobalProductPolarizationCharacter.pD F ζ hζ
  let f : finiteTorusForClassLifts F ζ hζ →* finitePart F ζ hζ :=
    { toFun := fun t => ⟨t.val.val, t.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let V := J.toOpenSubgroup.toSubgroup.comap f
  have hVo : IsOpen (V : Set (finiteTorusForClassLifts F ζ hζ)) :=
    J.toOpenSubgroup.isOpen.preimage hf
  let K := V.map π
  have hKo : IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)) := by
    exact finiteTorusClassProjection_open_of_surjective F ζ hζ
      (finiteTorusClassProjection_surjective F ζ hζ) _ hVo
  let A := KPGlobalPrincipalCubicLagrangian.A F
  let M := A ⊔ K
  have hMo : IsOpen (M : Set (KPGlobalCubicIdelePairing.D F)) :=
    Subgroup.isOpen_mono le_sup_right hKo
  letI : CompactSpace (KPGlobalCubicIdelePairing.D F ⧸ A) :=
    KPGlobalPrincipalCubicLagrangian.principal_cocompact F ζ hζ
  let q := QuotientGroup.map A M (MonoidHom.id _) le_sup_left
  have hqc : Continuous q := by
    apply (QuotientGroup.isQuotientMap_mk A).continuous_iff.mpr
    exact QuotientGroup.continuous_mk
  have hqs : Function.Surjective q := by
    exact QuotientGroup.map_surjective_of_surjective A M (MonoidHom.id _)
      (QuotientGroup.mk'_surjective M) le_sup_left
  letI : CompactSpace (KPGlobalCubicIdelePairing.D F ⧸ M) := hqs.compactSpace hqc
  letI : DiscreteTopology (KPGlobalCubicIdelePairing.D F ⧸ M) :=
    QuotientGroup.discreteTopology hMo
  letI : Finite (KPGlobalCubicIdelePairing.D F ⧸ M) := finite_of_compact_of_discrete
  letI : Fintype (KPGlobalCubicIdelePairing.D F ⧸ M) := Fintype.ofFinite _
  let e := Fintype.equivFin (KPGlobalCubicIdelePairing.D F ⧸ M)
  let rep (x : KPGlobalCubicIdelePairing.D F ⧸ M) :=
    (QuotientGroup.mk'_surjective M x).choose
  let rr (i : Fin (Fintype.card (KPGlobalCubicIdelePairing.D F ⧸ M))) :=
    (finiteTorusClassProjection_surjective F ζ hζ (rep (e.symm i))).choose
  have hr (i) : π (rr i) = rep (e.symm i) :=
    (finiteTorusClassProjection_surjective F ζ hζ (rep (e.symm i))).choose_spec
  have hH : (P0 F ζ hζ).H = KPGlobalCenterRationalCharacter.R F ζ hζ := by
    have he := congrArg KPGlobalTorusFunctionData.Polarization.H
      (KPMsRationalCompactCrossPairing.actual_weyl_fibre F ζ hζ 0)
    exact he
  refine ⟨_, fun i => (rr i).val, ?_⟩
  intro t
  let i := e (QuotientGroup.mk' M (pD t))
  have hi : QuotientGroup.mk' M (π (rr i)) = QuotientGroup.mk' M (pD t) := by
    rw [hr]
    exact (QuotientGroup.mk'_surjective M (e.symm i)).choose_spec |>.trans (by simp [i])
  have hm : pD t / π (rr i) ∈ M := QuotientGroup.eq_iff_div_mem.mp hi.symm
  obtain ⟨a, ha, d, hd, had⟩ := Subgroup.mem_sup.mp hm
  obtain ⟨u, hu, hud⟩ := hd
  let uu : (globalLevel F ζ hζ J).comap (E F ζ hζ).subtype :=
    ⟨u.val, ⟨f u, hu, rfl⟩⟩
  let h := t * uu.val⁻¹ * (rr i).val⁻¹
  have hh : h ∈ KPGlobalCenterRationalCharacter.R F ζ hζ := by
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage]
    change pD h ∈ A
    have hp : pD h = a := by
      change pD (t * u.val⁻¹ * (rr i).val⁻¹) = a
      simp only [map_mul, map_inv]
      change pD t * (π u)⁻¹ * (π (rr i))⁻¹ = a
      rw [hud]
      have ht : pD t = (a * d) * π (rr i) := by
        rw [had]; simp [div_eq_mul_inv, mul_assoc]
      rw [ht]
      calc
        a * d * π (rr i) * d⁻¹ * (π (rr i))⁻¹ =
            a * (d * π (rr i) * d⁻¹ * (π (rr i))⁻¹) := by group
        _ = a := by rw [mul_comm d (π (rr i))]; simp [mul_assoc]
    rw [hp]
    exact ha
  refine ⟨i, ⟨h, hH.symm ▸ hh⟩, uu, ?_⟩
  change t = (t * uu.val⁻¹ * (rr i).val⁻¹) * (rr i).val * uu.val
  group

theorem actual_normalized_torus_finite_cover
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (J : FiniteLevel F ζ hζ) :
    ∃ (J0 : FiniteLevel F ζ hζ) (n : ℕ) (r : Fin n → E F ζ hζ),
      globalLevel F ζ hζ J0 ≤ globalLevel F ζ hζ J ∧
      (∀ (k : D.K) (j : globalLevel F ζ hζ J0),
        k.val⁻¹ * j.val * k.val ∈ globalLevel F ζ hζ J0) ∧
      (∀ t : E F ζ hζ, ∃ (i : Fin n) (h : (P0 F ζ hζ).H)
        (u : (globalLevel F ζ hζ J0).comap (E F ζ hζ).subtype),
        t = h.val * r i * u.val) := by
  obtain ⟨J0, hJ, hnorm⟩ := normalized_shrink F ζ hζ D J
  obtain ⟨n, r, hcover⟩ := torus_cover F ζ hζ J0
  exact ⟨J0, n, r, hJ, hnorm, hcover⟩

end DedekindZetaZeroFree.KPSpatialSmoothing

end
