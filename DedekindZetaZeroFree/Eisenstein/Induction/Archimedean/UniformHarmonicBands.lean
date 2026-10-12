module

public import DedekindZetaZeroFree.Eisenstein.Induction.Archimedean.CompactTranslateReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding.UniformCompactSeparation

open NumberField

 theorem su2_fixes (u : KPCplxCharacterHaar.ComplexSU2) :
    KPArch.action (KPCplxCharacterHaar.complexSU2Embedding u) (0, 0) = (0, 0) := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp u.property).1
  have hb := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hu
  have hz := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hu
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp u.property).2
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply, ite_true, show (0 : Fin 2) ≠ 1 by decide, ite_false] at hb hz
  have hn : ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 1 := by
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using congrArg Complex.re hb
  have hn' : ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 +
      ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 = 1 := by simpa [add_comm] using hn
  ext
  · simpa [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KPCplxCharacterHaar.complexSU2Embedding, hn', add_comm] using hz
  · simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KPCplxCharacterHaar.complexSU2Embedding, hn', hd]

 def compactTuple (F : Type) [Field F] [NumberField F]
    (u : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) :
    KPContSectorArchSphericalFibers.KInfinity F :=
  ⟨fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w)), by
    rw [KPContSectorArchSphericalFibers.KInfinity, Subgroup.mem_comap,
      MulAction.mem_stabilizer_iff]
    funext i
    change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding
      (u (KPCusp.complexPlace F i))) • ((0, 0) : KPArch.H3) = (0, 0)
    rw [Matrix.ProjGenLinGroup.mk_smul KPArch.scalar_action]
    exact su2_fixes _⟩

private theorem section_mk_eq (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (a b : KPCplxCharacterHaar.ComplexGL2)
    (h : Matrix.ProjGenLinGroup.mk a = Matrix.ProjGenLinGroup.mk b) : f a = f b := by
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  rw [← hz]
  rw [← Matrix.GeneralLinearGroup.scalar_commute]
  exact (KPCplxPrincipalSeriesCharts.central_invariance s f z a).symm

private theorem kfinite_pi (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (hf : KPContHolomorphicKGeneration.IsKFinite s f)
    (u : KPCplxPrincipalSeriesCharts.compactSubgroup) :
    KPContHolomorphicKGeneration.IsKFinite s (KPCplxPrincipalSeriesCharts.pi s u f) := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ
    (Set.range (fun k : KPCplxPrincipalSeriesCharts.compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f))) := hf
  change FiniteDimensional ℂ (Submodule.span ℂ
    (Set.range (fun k : KPCplxPrincipalSeriesCharts.compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k (KPCplxPrincipalSeriesCharts.pi s u f))))
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ
    (Set.range (fun k : KPCplxPrincipalSeriesCharts.compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f)))
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  dsimp only
  rw [← KPCplxPrincipalSeriesCharts.pi_mul]
  exact Submodule.subset_span ⟨k * u, rfl⟩

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))

 def singleCompact (w : InfinitePlace F) (x : KPCplxCharacterHaar.ComplexSU2) :
    KPContSectorArchSphericalFibers.KInfinity F :=
  compactTuple F (Function.update (fun _ => 1) w x)

 def slotRestriction (w : InfinitePlace F) :
    (KPContSectorArchSphericalFibers.KInfinity F → ℂ) →ₗ[ℂ]
      (KPCplxCharacterHaar.ComplexSU2 → ℂ) where
  toFun h x := h (singleCompact F w x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem slot_generator_native (w : InfinitePlace F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (u : KPContSectorArchSphericalFibers.KInfinity F) :
    ∃ f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter,
      KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter f ∧
      ∀ x, f (KPCplxCharacterHaar.complexSU2Embedding x) = t.val.val
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (singleCompact F w x * u).val * c.val) := by
  obtain ⟨f, hf, he⟩ := actual_one_slot_source_principal_series F ζ hζ t w u c
  obtain ⟨r, hr⟩ := KPContinuation.ArchCompact.KInfinity_has_su2 F ζ hζ u
  let uw : KPCplxPrincipalSeriesCharts.compactSubgroup := ⟨u.val w, ⟨r w, hr w⟩⟩
  refine ⟨KPCplxPrincipalSeriesCharts.pi _ uw f, kfinite_pi _ f hf uw, ?_⟩
  intro x
  dsimp only [uw]
  rw [← hr w, KPCplxPrincipalSeriesCharts.pi_mk]
  change f (KPCplxCharacterHaar.complexSU2Embedding x * KPCplxCharacterHaar.complexSU2Embedding (r w)) = _
  rw [he]
  apply congrArg (fun a => t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val))
  funext v
  by_cases hv : v = w
  · subst v
    simp [singleCompact, compactTuple, map_mul, hr]
  · simp [singleCompact, compactTuple, hv]

 abbrev nativeBand (N : ℕ) := (Finset.range (N + 1)).sup
  (KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter)

private theorem nativeBand_mono {N M : ℕ} (h : N ≤ M) : nativeBand N ≤ nativeBand M :=
  Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right h 1))

private theorem kfinite_in_band
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter f) :
    ∃ N, f ∈ nativeBand N := by
  obtain ⟨I, a, ha, he⟩ := RepresentationTheory.KPContHolomorphicKGenerationProve.kFinite_finite_harmonic_decomposition _ f hf
  refine ⟨I.sup id, ?_⟩
  rw [← he]
  apply Submodule.sum_mem
  intro i hi
  exact (Finset.le_sup (f := KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter)
    (show i ∈ Finset.range (I.sup id + 1) from Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))) (ha i hi)

 def coordinateSpace (w : InfinitePlace F) : Submodule ℂ (KPCplxCharacterHaar.ComplexSU2 → ℂ) :=
  (actualCompactTranslateSpace F ζ hζ t).map (slotRestriction F w)

private theorem coordinateSpace_finite (w : InfinitePlace F) :
    FiniteDimensional ℂ (coordinateSpace F ζ hζ t w) := by
  letI := actualCompactTranslateSpace_finiteDimensional F ζ hζ t
  exact inferInstanceAs (FiniteDimensional ℂ ((actualCompactTranslateSpace F ζ hζ t).map (slotRestriction F w)))

private theorem coordinateSpace_uniform_band (w : InfinitePlace F) :
    ∃ N, coordinateSpace F ζ hζ t w ≤
      (nativeBand N).map (KPCplxIntertwinerEigenvalues.compactRestriction _) := by
  let R := KPCplxIntertwinerEigenvalues.compactRestriction KPCplxPrincipalSeriesCharts.positiveParameter
  let g := fun p : KPGlobalTorusFunctionData.finitePart F ζ hζ × KPContSectorArchSphericalFibers.KInfinity F =>
    fun x : KPCplxCharacterHaar.ComplexSU2 => t.val.val
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (singleCompact F w x * p.2).val * p.1.val)
  have hT : coordinateSpace F ζ hζ t w = Submodule.span ℂ (Set.range g) := by
    unfold coordinateSpace actualCompactTranslateSpace
    rw [Submodule.map_span]
    congr 1
    ext f
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨_, ⟨p, rfl⟩, rfl⟩
  letI := coordinateSpace_finite F ζ hζ t w
  have hfg : (Submodule.span ℂ (Set.range g)).FG := by
    rw [← hT]
    exact Module.Finite.iff_fg.mp inferInstance
  obtain ⟨s, hs, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  have hn : ∀ b : s, ∃ N, b.val ∈ (nativeBand N).map R := by
    intro b
    obtain ⟨⟨c, u⟩, hp⟩ := hs b.property
    obtain ⟨f, hf, hfe⟩ := slot_generator_native F ζ hζ t w c u
    obtain ⟨N, hN⟩ := kfinite_in_band f hf
    refine ⟨N, Submodule.mem_map.mpr ⟨f, hN, ?_⟩⟩
    rw [← hp]
    exact funext hfe
  choose N hN using hn
  refine ⟨s.attach.sup N, ?_⟩
  rw [hT, he]
  apply Submodule.span_le.mpr
  intro b hb
  exact Submodule.map_mono (nativeBand_mono (Finset.le_sup (Finset.mem_attach s ⟨b, hb⟩))) (hN ⟨b, hb⟩)

private theorem all_slices_coordinate (h : actualCompactTranslateSpace F ζ hζ t)
    (w : InfinitePlace F) (a : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) :
    (fun x => h.val (compactTuple F (Function.update a w x))) ∈ coordinateSpace F ζ hζ t w := by
  let b := compactTuple F (Function.update a w 1)
  have hm := actualCompactTranslateSpace_right_invariant F ζ hζ t h b
  refine Submodule.mem_map.mpr ⟨fun k => h.val (k * b), hm, ?_⟩
  funext x
  apply congrArg h.val
  apply Subtype.ext
  funext v
  by_cases hv : v = w <;> simp [singleCompact, b, compactTuple, hv]

private theorem coordinate_interpolation (w : InfinitePlace F) (N : ℕ)
    (hN : coordinateSpace F ζ hζ t w ≤ (nativeBand N).map (KPCplxIntertwinerEigenvalues.compactRestriction _)) :
    ∃ (n : ℕ) (x : Fin n → KPCplxCharacterHaar.ComplexSU2) (b : Fin n → nativeBand N),
      ∀ (h : coordinateSpace F ζ hζ t w) (y : KPCplxCharacterHaar.ComplexSU2),
        h.val y = ∑ i, h.val (x i) * (b i).val (KPCplxCharacterHaar.complexSU2Embedding y) := by
  let S := coordinateSpace F ζ hζ t w
  letI : FiniteDimensional ℂ S := coordinateSpace_finite F ζ hζ t w
  obtain ⟨n, m, x, A, b, hb⟩ := finite_evaluation_reconstruction S
  have hc : ∀ i : Fin m, (∑ j, A j i • (b j).val) ∈ S := by
    intro i
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (b j).property)
  have he : ∀ i : Fin m, ∃ f : nativeBand N,
      KPCplxIntertwinerEigenvalues.compactRestriction _ f.val = ∑ j, A j i • (b j).val := by
    intro i
    obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp (hN (hc i))
    exact ⟨⟨f, hf⟩, he⟩
  choose f hf using he
  refine ⟨m, x, f, ?_⟩
  intro h y
  rw [hb]
  have hy (i : Fin m) := congrFun (hf i) y
  simp only [KPCplxIntertwinerEigenvalues.compactRestriction, LinearMap.coe_mk,
    AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hy
  simp_rw [hy, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

 def partialProducts {ι X : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (E : ∀ i, V i →ₗ[ℂ] (X → ℂ)) (s : Finset ι) : Submodule ℂ ((ι → X) → ℂ) :=
  Submodule.span ℂ (Set.range (fun v : ∀ i, V i => fun a => ∏ i ∈ s, E i (v i) (a i)))

private theorem partialProducts_mul {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (E : ∀ i, V i →ₗ[ℂ] (X → ℂ)) (s : Finset ι) (w : ι) (hw : w ∉ s)
    (v : V w) (q : (ι → X) → ℂ) (hq : q ∈ partialProducts V E s) :
    (fun a => E w v (a w) * q a) ∈ partialProducts V E (insert w s) := by
  refine Submodule.span_induction (p := fun q _ => (fun a => E w v (a w) * q a) ∈ partialProducts V E (insert w s)) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨b, rfl⟩
    apply Submodule.subset_span
    refine ⟨Function.update b w v, ?_⟩
    funext a
    dsimp only
    rw [Finset.prod_insert hw]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hw)]
  · simpa only [Pi.zero_def, mul_zero] using (Submodule.zero_mem (partialProducts V E (insert w s)))
  · intro f g hf hg hf' hg'
    simpa only [Pi.add_def, mul_add] using Submodule.add_mem _ hf' hg'
  · intro c f hf hf'
    simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using Submodule.smul_mem _ c hf'

private theorem tensor_interpolation {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (E : ∀ i, V i →ₗ[ℂ] (X → ℂ)) (n : ι → ℕ)
    (x : ∀ i, Fin (n i) → X) (b : ∀ i, Fin (n i) → V i)
    (s : Finset ι) (f : (ι → X) → ℂ) (a₀ : ι → X)
    (hf : ∀ w ∈ s, ∀ a, f a = ∑ j, f (Function.update a w (x w j)) * E w (b w j) (a w))
    (hd : ∀ a, f a = f (fun i => if i ∈ s then a i else a₀ i)) :
    f ∈ partialProducts V E s := by
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have he : f = fun _ => f a₀ := by funext a; simpa using hd a
    rw [he]
    have h1 : (fun _ : ι → X => (1 : ℂ)) ∈ partialProducts V E ∅ :=
      Submodule.subset_span ⟨fun _ => 0, by simp⟩
    simpa only [Pi.smul_def, smul_eq_mul, mul_one] using Submodule.smul_mem _ (f a₀) h1
  | @insert w s hw ih =>
    have hqi : ∀ j : Fin (n w), (fun a => f (Function.update a w (x w j))) ∈ partialProducts V E s := by
      intro j
      apply ih
      · intro v hv a
        have hne : v ≠ w := ne_of_mem_of_not_mem hv hw
        have hh := hf v (Finset.mem_insert_of_mem hv) (Function.update a w (x w j))
        simpa only [Function.update_of_ne hne, Function.update_comm hne] using hh
      · intro a
        have hh := hd (Function.update a w (x w j))
        have hh' := hd (Function.update (fun i => if i ∈ s then a i else a₀ i) w (x w j))
        rw [hh, hh']
        congr 1
        funext i
        by_cases hi : i = w
        · subst i; simp
        · by_cases his : i ∈ s <;> simp [hi, his]
    have he : f = ∑ j, (fun a => E w (b w j) (a w) * f (Function.update a w (x w j))) := by
      funext a
      simpa only [Finset.sum_apply, mul_comm] using hf w (Finset.mem_insert_self w s) a
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => partialProducts_mul V E s w hw (b w j) _ (hqi j))

theorem actual_compact_translate_space_mem_uniform_native_bands
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ N : NumberField.InfinitePlace F → ℕ,
      actualCompactTranslateSpace F ζ hζ t ≤
        Submodule.span ℂ (Set.range (fun f :
          (w : NumberField.InfinitePlace F) →
            ↥((Finset.range (N w + 1)).sup
              (KPCplxIntertwinerEigenvalues.harmonicKType
                KPCplxPrincipalSeriesCharts.positiveParameter)) =>
          fun k : KPContSectorArchSphericalFibers.KInfinity F =>
            ∏ w, (f w).val ((k.val w).out))) := by
  classical
  have hn := fun w => coordinateSpace_uniform_band F ζ hζ t w
  choose N hN using hn
  have hc := fun w => coordinate_interpolation F ζ hζ t w (N w) (hN w)
  choose n x b hb using hc
  let V : InfinitePlace F → Type := fun w => ↥(nativeBand (N w))
  let E := fun w : InfinitePlace F =>
    (KPCplxIntertwinerEigenvalues.compactRestriction KPCplxPrincipalSeriesCharts.positiveParameter).domRestrict (nativeBand (N w))
  have hprod (h : actualCompactTranslateSpace F ζ hζ t) :
      (fun a => h.val (compactTuple F a)) ∈ partialProducts V E Finset.univ := by
    apply tensor_interpolation V E n x b Finset.univ _ (fun _ => 1)
    · intro w hw a
      have hm := all_slices_coordinate F ζ hζ t h w a
      have hi := hb w ⟨_, hm⟩ (a w)
      change h.val (compactTuple F a) = ∑ j,
        h.val (compactTuple F (Function.update a w (x w j))) *
          (b w j).val (KPCplxCharacterHaar.complexSU2Embedding (a w))
      simpa only [Function.update_eq_self] using hi
    · intro a
      simp only [Finset.mem_univ, ite_true]
  choose r hr using KPContinuation.ArchCompact.KInfinity_has_su2 F ζ hζ
  let L : ((InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) → ℂ) →ₗ[ℂ]
      (KPContSectorArchSphericalFibers.KInfinity F → ℂ) :=
    { toFun := fun f k => f (r k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨N, ?_⟩
  intro h hh
  have hL : (partialProducts V E Finset.univ).map L ≤
      Submodule.span ℂ (Set.range (fun f : ∀ w : InfinitePlace F, nativeBand (N w) =>
        fun k : KPContSectorArchSphericalFibers.KInfinity F => ∏ w, (f w).val ((k.val w).out))) := by
    unfold partialProducts
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨f, ?_⟩
    funext k
    apply Finset.prod_congr rfl
    intro w _
    apply section_mk_eq
    exact (Quotient.out_eq (k.val w)).trans (hr k w).symm
  apply hL
  refine Submodule.mem_map.mpr ⟨fun a => h (compactTuple F a), hprod ⟨h, hh⟩, ?_⟩
  funext k
  apply congrArg h
  apply Subtype.ext
  funext w
  exact hr k w

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding.UniformCompactSeparation

end
