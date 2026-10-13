module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FiniteEulerCorrections

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowHeckeBridge

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

theorem isOpen_re_gt (r : ℝ) : IsOpen {z : ℂ | r < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem eqOn_halfPlane_of_eq_right {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re}) (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ z : ℂ, 1 < z.re → f z = g z) :
    ∀ z : ℂ, 0 < z.re → f z = g z := by
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : f =ᶠ[nhds (2 : ℂ)] g := by
    refine Filter.eventually_of_mem ((isOpen_re_gt 1).mem_nhds ?_) (fun z hz => h z hz)
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected h2 hev
  exact fun z hz => this hz

theorem entire_eq_of_eq_right {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ z : ℂ, 1 < z.re → f z = g z) : f = g := by
  have hev : f =ᶠ[nhds (2 : ℂ)] g := by
    refine Filter.eventually_of_mem ((isOpen_re_gt 1).mem_nhds ?_) (fun z hz => h z hz)
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have := hf'.eqOn_of_preconnected_of_eventuallyEq hg' isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  exact funext fun z => this (Set.mem_univ z)

theorem tendsto_boundary_of_eq {g L : ℂ → ℂ} (hg : Continuous g)
    (hL : ∀ s : ℂ, 0 < s.re → g s = L s) (t : ℝ) :
    Filter.Tendsto (fun x : ℝ => L ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  have hc : Filter.Tendsto (fun x : ℝ => g ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
    ((hg.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)).tendsto
      0).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hL _ (by simpa using hx)

section Primitive

variable {F : Type} [Field F] [NumberField F]

def hecke (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) :
    NonprincipalRayHeckeData F ν.conductor ν.character :=
  nonprincipalRayHeckeData F (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
    ν.conductor ν.conductor_ne_zero ν.character ν.primitive hν

theorem hecke_analyticOn (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) :
    AnalyticOnNhd ℂ (hecke A ν hν).L {z : ℂ | 0 < z.re} :=
  (hecke A ν hν).L_holo.analyticOnNhd (isOpen_re_gt 0)

theorem hecke_eq_idealLSeries (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) (s : ℂ) (hs : 1 < s.re) :
    (hecke A ν hν).L s = Detector.idealLSeries F ν.character s := by
  rw [← ((hecke A ν hν).series s hs).tsum_eq]
  unfold Detector.idealLSeries
  refine tsum_congr fun I => ?_
  by_cases h : I = ⊥
  · subst h
    simp [(ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
  · simp [h]

theorem eq_hecke_of_analyticOn (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) :
    ∀ s : ℂ, 0 < s.re → g s = (hecke A ν hν).L s :=
  eqOn_halfPlane_of_eq_right hg (hecke_analyticOn A ν hν)
    (fun s hs => (h s hs).trans (hecke_eq_idealLSeries A ν hν s hs).symm)

theorem entire_eq_hecke (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) :
    ∀ s : ℂ, 0 < s.re → g s = (hecke A ν hν).L s :=
  eq_hecke_of_analyticOn A ν hν (fun z _ => hg.analyticAt z) h

theorem entire_unique (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    {g g' : ℂ → ℂ} (hg : Differentiable ℂ g) (hg' : Differentiable ℂ g')
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s)
    (h' : ∀ s : ℂ, 1 < s.re → g' s = Detector.idealLSeries F ν.character s) : g = g' :=
  entire_eq_of_eq_right hg hg' fun s hs => (h s hs).trans (h' s hs).symm

theorem hecke_exists_entire (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 0 < s.re → g s = (hecke A ν hν).L s := by
  have hF := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  exact ⟨nonprincipalHeckeEntireContinuation F ν.conductor ν.character (hecke A ν hν),
    nonprincipalHeckeEntireContinuation_differentiable F hF ν.conductor ν.conductor_ne_zero
      ν.character (hecke A ν hν),
    fun s hs => nonprincipalHeckeEntireContinuation_eq F hF ν.conductor ν.conductor_ne_zero
      ν.character (hecke A ν hν) s hs⟩

theorem mask_differentiable (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) (E : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hE : E.Finite) :
    Differentiable ℂ
      (Detector.finiteEulerDeletionMask F E (fun v => ν.character v.asIdeal)) := by
  obtain ⟨h, -, -⟩ := Detector.deleted_primitive_L_continuation F ν E hE {s : ℂ | 0 < s.re}
    (hecke A ν hν).L (hecke_analyticOn A ν hν).meromorphicOn (hecke A ν hν).series
  exact h

theorem mask_ne_zero (ν : Detector.PrimitiveFrequencyCharacter F)
    (E : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : E.Finite) (s : ℂ)
    (hs : 0 < s.re) :
    Detector.finiteEulerDeletionMask F E (fun v => ν.character v.asIdeal) s ≠ 0 := by
  letI := hE.fintype
  rw [Detector.finiteEulerDeletionMask, finprod_eq_prod_of_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact (Detector.finite_euler_local_factor_nonzero F s.re hs p.val
    (ν.character p.val.asIdeal) s
    (RayUnitary.ray_character_norm_le_one F ν.conductor ν.conductor_ne_zero
      ν.character p.val.asIdeal) le_rfl).2.2

theorem deleted_tsum_eq_mask_mul (A : SArithmeticData F)
    (ν : Detector.PrimitiveFrequencyCharacter F) (hν : ¬ ν.character.IsPrincipal)
    (E : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : E.Finite) (s : ℂ)
    (hs : 1 < s.re) :
    ∑' I : Ideal (𝓞 F), Detector.deletedPrimitiveIdealCoefficient F ν E I *
        (Ideal.absNorm I : ℂ) ^ (-s) =
      Detector.finiteEulerDeletionMask F E (fun v => ν.character v.asIdeal) s *
        (hecke A ν hν).L s := by
  obtain ⟨-, -, hBs⟩ := Detector.deleted_primitive_L_continuation F ν E hE {s : ℂ | 0 < s.re}
    (hecke A ν hν).L (hecke_analyticOn A ν hν).meromorphicOn (hecke A ν hν).series
  rw [(hBs s hs).tsum_eq, mul_comm]

theorem eq_mask_mul_of_analyticOn (A : SArithmeticData F)
    (ν : Detector.PrimitiveFrequencyCharacter F) (hν : ¬ ν.character.IsPrincipal)
    (E : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : E.Finite) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ s : ℂ, 1 < s.re → g s = ∑' I : Ideal (𝓞 F),
      Detector.deletedPrimitiveIdealCoefficient F ν E I * (Ideal.absNorm I : ℂ) ^ (-s)) :
    ∀ s : ℂ, 0 < s.re → g s =
      Detector.finiteEulerDeletionMask F E (fun v => ν.character v.asIdeal) s *
        (hecke A ν hν).L s := by
  have hm : AnalyticOnNhd ℂ
      (fun s => Detector.finiteEulerDeletionMask F E (fun v => ν.character v.asIdeal) s *
        (hecke A ν hν).L s) {z : ℂ | 0 < z.re} := by
    intro z hz
    exact ((mask_differentiable A ν hν E hE).analyticAt z).mul (hecke_analyticOn A ν hν z hz)
  exact eqOn_halfPlane_of_eq_right hg hm
    (fun s hs => (h s hs).trans (deleted_tsum_eq_mask_mul A ν hν E hE s hs))

end Primitive

section Rows

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem omega_eq_minus (u : D.Row) : D.omega u = (D.inducers u).minus := rfl

abbrev deletionSet (u : D.Row) :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  FrequencyCharacterMasks.frequencyMask u.toFrequency

theorem deletionSet_eq (u : D.Row) :
    deletionSet D u = FrequencyCharacterMasks.frequencyMask u.toFrequency := rfl

theorem deletionSet_finite (u : D.Row) : (deletionSet D u).Finite := by
  rw [deletionSet_eq, FrequencyCharacterMasks.frequencyMask_eq_principal_support]
  exact D.recipe.A.Sf.finite_toSet.union
    (Detector.exterior_frequency_support_finite_norm_pos F _ D.recipe.A.Sf.finite_toSet
      u.u u.toFrequency.generates.1).1

theorem frequency_ideal_eq (u : D.Row) :
    u.toFrequency.ideal = DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u := by
  apply D.recipe.A.exteriorIdealEquiv.injective
  apply Subtype.ext
  rw [D.recipe.A.exteriorIdealEquiv_apply, D.recipe.A.exteriorIdealEquiv_apply]
  exact u.toFrequency.generates.2.symm.trans
    (PrincipalProbeConstruction.Inputs.rowIdeal_generates D.recipe.A u.u u.u_ne_zero).2

theorem deletionSet_subset_rowPrimesWithS (u : D.Row) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hv : v ∈ deletionSet D u) : v.asIdeal ∈ EulerDeletion.rowPrimesWithS D u := by
  have hv' : v ∈ (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ∪
      {w | u.toFrequency.ideal.val ≤ w.asIdeal} := hv
  rcases hv' with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_coe.mp h, rfl⟩)
  · have h' : (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val ≤ v.asIdeal := by
      have h2 : u.toFrequency.ideal.val ≤ v.asIdeal := h
      rwa [frequency_ideal_eq D u] at h2
    refine Finset.mem_union_left _ ?_
    unfold EulerDeletion.rowPrimes
    rw [Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).property.1]
    exact ⟨v.isPrime, h'⟩

private theorem rowPrimesWithS_ne_top (u : D.Row) (p : Ideal (𝓞 F))
    (hp : p ∈ EulerDeletion.rowPrimesWithS D u) : p ≠ ⊤ := by
  unfold EulerDeletion.rowPrimesWithS at hp
  rcases Finset.mem_union.mp hp with h | h
  · unfold EulerDeletion.rowPrimes at h
    rw [Multiset.mem_toFinset] at h
    exact Ideal.IsPrime.ne_top (Ideal.isPrime_of_prime
      (UniqueFactorizationMonoid.prime_of_normalized_factor p h))
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h
    exact v.isPrime.ne_top

private theorem one_le_inv_one_sub_rpow (I : Ideal (𝓞 F)) (hI : I ≠ ⊤) (σ : ℝ) (hσ : 0 < σ) :
    1 ≤ (1 - (Ideal.absNorm I : ℝ) ^ (-σ))⁻¹ := by
  have hne : Ideal.absNorm I ≠ 1 := fun h => hI (Ideal.absNorm_eq_one_iff.mp h)
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h0 | hpos
  · rw [h0]
    simp [Real.zero_rpow (neg_ne_zero.mpr hσ.ne')]
  · have h2 : 1 < (Ideal.absNorm I : ℝ) := by
      have h1 : 1 ≤ Ideal.absNorm I := hpos
      exact_mod_cast lt_of_le_of_ne h1 (Ne.symm hne)
    have h3 : (Ideal.absNorm I : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg h2 (neg_neg_of_pos hσ)
    have h4 : 0 ≤ (Ideal.absNorm I : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact (one_le_inv₀ (by linarith)).mpr (by linarith)

private theorem prod_subtype_le_prod (E : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) [Fintype E]
    (hE : E.Finite) (P : Finset (Ideal (𝓞 F))) (hP : ∀ v ∈ E, v.asIdeal ∈ P)
    (g : Ideal (𝓞 F) → ℝ) (hg1 : ∀ I ∈ P, 1 ≤ g I) :
    ∏ v : E, g v.1.asIdeal ≤ ∏ p ∈ P, g p := by
  classical
  have hinj : Set.InjOn (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (hE.toFinset : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :=
    fun v _ w _ h => IsDedekindDomain.HeightOneSpectrum.ext h
  have hsub : hE.toFinset.image (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.asIdeal) ⊆ P := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact hP v (hE.mem_toFinset.mp hv)
  calc ∏ v : E, g v.1.asIdeal = ∏ v ∈ hE.toFinset, g v.asIdeal :=
        (Finset.prod_subtype hE.toFinset (fun x => hE.mem_toFinset) (fun x => g x.asIdeal)).symm
    _ = ∏ p ∈ hE.toFinset.image (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.asIdeal), g p :=
        (Finset.prod_image hinj).symm
    _ ≤ ∏ p ∈ P, g p :=
        Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun p hp => by linarith [hg1 p (hsub hp)])
          (fun p hp _ => hg1 p hp)

private theorem local_factor_upper (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (a s : ℂ) (σ : ℝ) (hσ : 0 < σ)
    (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖1 - a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤ 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  have hv : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hb : ‖a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (lt_trans zero_lt_one hv)),
      Complex.neg_re]
    calc
      ‖a‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by positivity) _)
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le hv.le (neg_le_neg hs)
  calc ‖1 - a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by rw [norm_one]; linarith

theorem mask_norm_le (u : D.Row) (ν : Detector.PrimitiveFrequencyCharacter F)
    (σs : ℝ) (hσs : 0 < σs) (s : ℂ) (hs : σs ≤ s.re) :
    ‖Detector.finiteEulerDeletionMask F (deletionSet D u) (fun v => ν.character v.asIdeal) s‖ ≤
      ∏ p ∈ EulerDeletion.rowPrimesWithS D u, (1 + (Ideal.absNorm p : ℝ) ^ (-σs)) ∧
    ‖(Detector.finiteEulerDeletionMask F (deletionSet D u)
        (fun v => ν.character v.asIdeal) s)⁻¹‖ ≤
      ∏ p ∈ EulerDeletion.rowPrimesWithS D u, (1 - (Ideal.absNorm p : ℝ) ^ (-σs))⁻¹ := by
  have hfin := deletionSet_finite D u
  letI := hfin.fintype
  have hP : ∀ v ∈ deletionSet D u, v.asIdeal ∈ EulerDeletion.rowPrimesWithS D u :=
    fun v hv => deletionSet_subset_rowPrimesWithS D u v hv
  have hbd : ∀ v : deletionSet D u,
      0 < 1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σs) ∧
        1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σs) ≤
          ‖Detector.finiteEulerLocalFactor F v.1 (ν.character v.1.asIdeal) s‖ := fun v =>
    ⟨(Detector.finite_euler_local_factor_nonzero F σs hσs v.1 (ν.character v.1.asIdeal) s
      (RayUnitary.ray_character_norm_le_one F ν.conductor ν.conductor_ne_zero ν.character
        v.1.asIdeal) hs).1,
     (Detector.finite_euler_local_factor_nonzero F σs hσs v.1 (ν.character v.1.asIdeal) s
      (RayUnitary.ray_character_norm_le_one F ν.conductor ν.conductor_ne_zero ν.character
        v.1.asIdeal) hs).2.1⟩
  have hinv : ∀ v : deletionSet D u,
      ‖(Detector.finiteEulerLocalFactor F v.1 (ν.character v.1.asIdeal) s)⁻¹‖ ≤
        (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σs))⁻¹ := fun v => by
    rw [norm_inv]
    exact inv_anti₀ (hbd v).1 (hbd v).2
  rw [Detector.finiteEulerDeletionMask, finprod_eq_prod_of_fintype]
  constructor
  · rw [norm_prod]
    refine le_trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun v _ => local_factor_upper v.1 _ s σs hσs
        (RayUnitary.ray_character_norm_le_one F ν.conductor ν.conductor_ne_zero ν.character
          v.1.asIdeal) hs)) ?_
    exact prod_subtype_le_prod (deletionSet D u) hfin (EulerDeletion.rowPrimesWithS D u) hP
      (fun I => 1 + (Ideal.absNorm I : ℝ) ^ (-σs))
      (fun I _ => le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · conv_lhs => rw [← Finset.prod_inv_distrib]
    rw [norm_prod]
    refine le_trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ => hinv v)) ?_
    exact prod_subtype_le_prod (deletionSet D u) hfin (EulerDeletion.rowPrimesWithS D u) hP
      (fun I => (1 - (Ideal.absNorm I : ℝ) ^ (-σs))⁻¹)
      (fun I hI => one_le_inv_one_sub_rpow I (rowPrimesWithS_ne_top D u I hI) σs hσs)

theorem principal_of_cofinite_one [NumberField.IsTotallyComplex F]
    (ν : Detector.PrimitiveFrequencyCharacter F)
    (h : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ν.character v.asIdeal = 1) : ν.character.IsPrincipal := by
  let ψ : Detector.PrimitiveFrequencyCharacter F :=
    ⟨⊤, top_ne_bot, GlobalZetaNormalizer.principalCharacter F,
      GlobalZetaNormalizer.principalCharacter_primitive F⟩
  have hν : ν = ψ :=
    PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.primitive_inducers_eq_of_cofinite_prime_values
      ν ψ (by
        filter_upwards [h] with v hv
        rw [hv]
        exact ((GlobalZetaNormalizer.principalCharacter_principal F) v.asIdeal v.ne_bot
          (by simp)).symm)
  rw [hν]
  exact GlobalZetaNormalizer.principalCharacter_principal F

theorem minus_isPrincipal_iff_plus (hη : D.recipe.target.IsPrincipal) (u : D.Row) :
    (D.inducers u).minus.character.IsPrincipal ↔ (D.inducers u).plus.character.IsPrincipal := by
  classical
  letI : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  have cop : ∀ m : Ideal (𝓞 F), m ≠ ⊥ →
      ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.asIdeal ⊔ m = ⊤ := by
    intro m hm
    apply Filter.eventually_cofinite.mpr
    apply (Ideal.finite_factors hm).subset
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    apply Ideal.dvd_iff_le.mpr
    have hvmax : v.asIdeal.IsMaximal := v.isMaximal
    exact (hvmax.eq_of_le hv (show v.asIdeal ≤ v.asIdeal ⊔ m from le_sup_left)).symm ▸
      (show m ≤ v.asIdeal ⊔ m from le_sup_right)
  have hc := cop (D.recipe.A.modulus * (D.inducers u).plus.conductor *
        (D.inducers u).minus.conductor)
        (mul_ne_zero (mul_ne_zero D.recipe.A.modulus_ne_zero
          (D.inducers u).plus.conductor_ne_zero) (D.inducers u).minus.conductor_ne_zero)
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      v.asIdeal ⊔ (D.recipe.A.modulus * (D.inducers u).plus.conductor *
        (D.inducers u).minus.conductor) = ⊤ →
      ((D.inducers u).minus.character v.asIdeal = 1 ↔
        (D.inducers u).plus.character v.asIdeal = 1) := by
    intro v hv
    have hv' : IsCoprime v.asIdeal (D.recipe.A.modulus * (D.inducers u).plus.conductor *
        (D.inducers u).minus.conductor) := Ideal.isCoprime_iff_sup_eq.mpr hv
    have h1 : v.asIdeal ⊔ D.recipe.A.modulus = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp (hv'.of_mul_right_left.of_mul_right_left)
    have htw := (D.inducers u).twist v.asIdeal v.ne_bot hv
    have hη1 : D.recipe.target v.asIdeal = 1 := hη v.asIdeal v.ne_bot h1
    rw [hη1, one_mul] at htw
    rw [htw]
    constructor
    · intro h
      have := congrArg star h
      simpa using this
    · intro h
      rw [h]; simp
  constructor
  · intro hm
    refine principal_of_cofinite_one _ ?_
    filter_upwards [hc] with v hv
    have hv' : IsCoprime v.asIdeal (D.recipe.A.modulus * (D.inducers u).plus.conductor *
        (D.inducers u).minus.conductor) := Ideal.isCoprime_iff_sup_eq.mpr hv
    have h2 : v.asIdeal ⊔ (D.inducers u).minus.conductor = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp hv'.of_mul_right_right
    exact (key v hv).mp (hm v.asIdeal v.ne_bot h2)
  · intro hp
    refine principal_of_cofinite_one _ ?_
    filter_upwards [hc] with v hv
    have hv' : IsCoprime v.asIdeal (D.recipe.A.modulus * (D.inducers u).plus.conductor *
        (D.inducers u).minus.conductor) := Ideal.isCoprime_iff_sup_eq.mpr hv
    have h2 : v.asIdeal ⊔ (D.inducers u).plus.conductor = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp hv'.of_mul_right_left.of_mul_right_right
    exact (key v hv).mpr (hp v.asIdeal v.ne_bot h2)

theorem conductor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, 1 ≤ D.q u →
      (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ) ≤ C * D.q u) ∧
      (1 + (Ideal.absNorm (D.inducers u).minus.conductor : ℝ) ≤ C * D.q u) := by
  classical
  letI : IsPrincipalIdealRing D.recipe.A.R :=
    D.recipe.A.principalIdealRing_of_classGroup_subsingleton D.recipe.classKilled
  letI : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) := by
    intro v hv
    by_contra h
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six D.recipe.A v h)
  obtain ⟨Vr, e, he, hSnorm⟩ :=
    PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.actual_detector_frequency_representatives
      D.recipe
  obtain ⟨η0, hη0S, _, htarget⟩ :=
    PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.target_primitive_inducer
      D.recipe
  have cop : ∀ m : Ideal (𝓞 F), m ≠ ⊥ →
      ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.asIdeal ⊔ m = ⊤ := by
    intro m hm
    apply Filter.eventually_cofinite.mpr
    apply (Ideal.finite_factors hm).subset
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    apply Ideal.dvd_iff_le.mpr
    have hvmax : v.asIdeal.IsMaximal := v.isMaximal
    exact (hvmax.eq_of_le hv (show v.asIdeal ≤ v.asIdeal ⊔ m from le_sup_left)).symm ▸
      (show m ≤ v.asIdeal ⊔ m from le_sup_right)

  let f : D.Row → PrincipalMellinComparison.Frequency D.recipe :=
    fun r => ⟨⟨r.u, r.isRep.choose⟩, r.isRep.choose_spec⟩
  have hinj : ∀ r r' : D.Row, e (f r) = e (f r') → r = r' := by
    intro r r' h
    apply FixedData.Row.u_injective
    exact congrArg (fun x : PrincipalMellinComparison.Frequency D.recipe =>
      (x.val.val : D.recipe.A.R)) (e.injective h)
  obtain ⟨K0⟩ := Detector.kummer_frequency_family_exists F D.recipe.A.zeta12
    D.recipe.A.primitive_zeta12 D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix Vr
  let K : Detector.KummerFrequencyFamily F D.recipe.A.zeta12 D.recipe.σ
      (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) Vr :=
    { numerator := fun w =>
        if h : ∃ r : D.Row, e (f r) = w then (D.inducers h.choose).plus else K0.numerator w
      kummer := by
        intro w
        by_cases h : ∃ r : D.Row, e (f r) = w
        · have hk := (D.inducers h.choose).kummer
          have hw : w.val = Units.mk0 ((h.choose.u : D.recipe.A.R) : F)
              (by exact_mod_cast h.choose.generates.1) := by
            have hw0 : w.val = (e (f h.choose)).val := congrArg Subtype.val h.choose_spec.symm
            rw [hw0, he]
            exact Units.ext rfl
          show Detector.IsKummerFrequencyCharacter F D.recipe.A.zeta12 D.recipe.σ _ w.val
            (if h : ∃ r : D.Row, e (f r) = w then (D.inducers h.choose).plus
              else K0.numerator w)
          rw [dif_pos h, hw]
          exact hk
        · show Detector.IsKummerFrequencyCharacter F D.recipe.A.zeta12 D.recipe.σ _ w.val
            (if h : ∃ r : D.Row, e (f r) = w then (D.inducers h.choose).plus
              else K0.numerator w)
          rw [dif_neg h]
          exact K0.kummer w }
  have hKnum : ∀ r : D.Row, K.numerator (e (f r)) = (D.inducers r).plus := by
    intro r
    have h : ∃ r' : D.Row, e (f r') = e (f r) := ⟨r, rfl⟩
    show (if h : ∃ r' : D.Row, e (f r') = e (f r) then (D.inducers h.choose).plus
      else K0.numerator (e (f r))) = _
    rw [dif_pos h, hinj _ _ h.choose_spec]
  obtain ⟨T⟩ := Detector.twisted_frequency_family_exists F D.recipe.A.zeta12
    D.recipe.A.primitive_zeta12 D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix Vr K η0
  have hω : ∀ r : D.Row, D.omega r = T.denominator (e (f r)) := by
    intro r
    apply PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.primitive_inducers_eq_of_cofinite_prime_values
    filter_upwards [cop (D.recipe.A.modulus * (D.inducers r).plus.conductor *
        (D.inducers r).minus.conductor)
        (mul_ne_zero (mul_ne_zero D.recipe.A.modulus_ne_zero
          (D.inducers r).plus.conductor_ne_zero) (D.inducers r).minus.conductor_ne_zero),
      cop (η0.conductor * (K.numerator (e (f r))).conductor * (T.denominator (e (f r))).conductor)
        (mul_ne_zero (mul_ne_zero η0.conductor_ne_zero
          (K.numerator (e (f r))).conductor_ne_zero) (T.denominator (e (f r))).conductor_ne_zero),
      cop (D.recipe.A.modulus * η0.conductor)
        (mul_ne_zero D.recipe.A.modulus_ne_zero η0.conductor_ne_zero)] with v h1 h2 h3
    have twist1 := (D.inducers r).twist v.asIdeal v.ne_bot h1
    have twist2 := T.induces (e (f r)) v.asIdeal v.ne_bot h2
    have ht := htarget v.asIdeal v.ne_bot h3
    rw [twist2, hKnum r, ht]
    exact twist1

  obtain ⟨Cn, hCn, hnum⟩ :=
    Detector.frequency_numerator_conductor_bound F D.recipe.A.zeta12
      D.recipe.A.primitive_zeta12 D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix
  obtain ⟨Cd, hCd, hcond⟩ :=
    Detector.frequency_denominator_conductor_bound F D.recipe.A.zeta12
      D.recipe.A.primitive_zeta12 D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix η0 hη0S
  refine ⟨1 + Cn + Cd, by positivity, fun r hq => ?_⟩
  have hsn : (Detector.frequencySNorm F
      (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) Vr (e (f r)) : ℝ) =
      D.q r := hSnorm (f r)
  have h1 := hnum Vr K (e (f r))
  rw [hKnum r] at h1
  have h2 := hcond Vr K T (e (f r))
  rw [← hω r] at h2
  have hq0 : 0 ≤ D.q r := by linarith
  have h3 : (Ideal.absNorm (D.inducers r).plus.conductor : ℝ) ≤ Cn * D.q r := by
    have := h1.1.trans h1.2
    rwa [hsn] at this
  have h4 : (Ideal.absNorm (D.omega r).conductor : ℝ) ≤ Cd * D.q r := by
    rwa [hsn] at h2
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg hCn.le hq0, mul_nonneg hCd.le hq0]
  · show 1 + (Ideal.absNorm (D.omega r).conductor : ℝ) ≤ _
    nlinarith [mul_nonneg hCn.le hq0, mul_nonneg hCd.le hq0]

abbrev heckePlus (u : D.Row) (hnp : ¬ (D.inducers u).plus.character.IsPrincipal) :
    NonprincipalRayHeckeData F (D.inducers u).plus.conductor (D.inducers u).plus.character :=
  hecke D.recipe.A (D.inducers u).plus hnp

abbrev heckeOmega (u : D.Row) (hnp : ¬ (D.omega u).character.IsPrincipal) :
    NonprincipalRayHeckeData F (D.omega u).conductor (D.omega u).character :=
  hecke D.recipe.A (D.omega u) hnp

theorem Lpsi_eq_mask_mul (u : D.Row) (hnp : ¬ (D.inducers u).plus.character.IsPrincipal)
    (s : ℂ) (hs : 1 < s.re) :
    D.Lpsi u s =
      Detector.finiteEulerDeletionMask F (deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) s * (heckePlus D u hnp).L s := by
  rw [← deleted_tsum_eq_mask_mul D.recipe.A (D.inducers u).plus hnp (deletionSet D u)
    (deletionSet_finite D u) s hs]
  have hL : D.Lpsi u s = ∑' I : Ideal (𝓞 F),
      MaskedHeckeMeromorphic.coefficient u.toFrequency MaskedHeckeMeromorphic.Row.plus I *
        (Ideal.absNorm I : ℂ) ^ (-s) := by
    exact (D.Lpsi_eq_raw u s hs).trans rfl
  rw [hL]
  refine tsum_congr fun I => ?_
  simp only [MaskedHeckeMeromorphic.coefficient]
  have h := (D.inducers u).plus_mask I
  exact congrArg (· * ((Ideal.absNorm I : ℂ) ^ (-s))) h

theorem Llam_eq_mask_mul (u : D.Row) (hnp : ¬ (D.omega u).character.IsPrincipal)
    (s : ℂ) (hs : 1 < s.re) :
    D.Llam u s =
      Detector.finiteEulerDeletionMask F (deletionSet D u)
        (fun v => (D.omega u).character v.asIdeal) s * (heckeOmega D u hnp).L s := by
  rw [← deleted_tsum_eq_mask_mul D.recipe.A (D.omega u) hnp (deletionSet D u)
    (deletionSet_finite D u) s hs]
  have hL : D.Llam u s = ∑' I : Ideal (𝓞 F),
      MaskedHeckeMeromorphic.coefficient u.toFrequency MaskedHeckeMeromorphic.Row.minus I *
        (Ideal.absNorm I : ℂ) ^ (-s) := by
    exact (D.Llam_eq_raw u s hs).trans rfl
  rw [hL]
  refine tsum_congr fun I => ?_
  simp only [MaskedHeckeMeromorphic.coefficient]
  have h := (D.inducers u).minus_mask I
  exact congrArg (· * ((Ideal.absNorm I : ℂ) ^ (-s))) h

theorem eq_mask_mul_Lpsi (u : D.Row) (hnp : ¬ (D.inducers u).plus.character.IsPrincipal)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) :
    ∀ s : ℂ, 0 < s.re → g s =
      Detector.finiteEulerDeletionMask F (deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) s * (heckePlus D u hnp).L s := by
  refine eqOn_halfPlane_of_eq_right hg ?_ (fun s hs => (h s hs).trans (Lpsi_eq_mask_mul D u hnp s hs))
  intro z hz
  exact ((mask_differentiable D.recipe.A _ hnp _ (deletionSet_finite D u)).analyticAt z).mul
    (hecke_analyticOn D.recipe.A _ hnp z hz)

theorem entire_eq_mask_mul_Lpsi (u : D.Row)
    (hnp : ¬ (D.inducers u).plus.character.IsPrincipal)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h : ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) :
    ∀ s : ℂ, 0 < s.re → g s =
      Detector.finiteEulerDeletionMask F (deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) s * (heckePlus D u hnp).L s :=
  eq_mask_mul_Lpsi D u hnp (fun z _ => hg.analyticAt z) h

theorem entire_Lpsi_unique (u : D.Row) {g g' : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg' : Differentiable ℂ g') (h : ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s)
    (h' : ∀ s : ℂ, 1 < s.re → g' s = D.Lpsi u s) : g = g' :=
  entire_eq_of_eq_right hg hg' fun s hs => (h s hs).trans (h' s hs).symm

theorem entire_eq_heckeOmega (u : D.Row) (hnp : ¬ (D.omega u).character.IsPrincipal)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s) :
    ∀ s : ℂ, 0 < s.re → g s = (heckeOmega D u hnp).L s :=
  entire_eq_hecke D.recipe.A (D.omega u) hnp hg h

theorem entire_omega_unique (u : D.Row) {g g' : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg' : Differentiable ℂ g')
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s)
    (h' : ∀ s : ℂ, 1 < s.re → g' s = Detector.idealLSeries F (D.omega u).character s) :
    g = g' :=
  entire_unique D.recipe.A (D.omega u) hg hg' h h'

end Rows

end

end DedekindZetaZeroFree.Quantitative.RowHeckeBridge
