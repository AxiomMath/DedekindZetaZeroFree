module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.DenominatorExistence

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.AllIdealSieveTransfer31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open scoped Classical BigOperators

section Copied

open DedekindZetaZeroFree.Detector IsDedekindDomain

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem primitive_sieve_finset_transfer_of_property
    (F : Type) [Field F] [NumberField F]
    (C Ccond N X ε : ℝ)
    (P : PrimitiveFrequencyCharacter F → Prop)
    (hbound : ∀ (n : ℕ) (ω : Fin n → PrimitiveFrequencyCharacter F),
      Pairwise (fun i j => ¬ samePrimitiveFrequencyCharacter F (ω i) (ω j)) →
      (∀ i, (Ideal.absNorm (ω i).conductor : ℝ) ≤ Ccond * X) →
      (∀ i, P (ω i)) →
      ∀ c : NonzeroIdeal F →₀ ℂ,
        (∀ I ∈ c.support, (Ideal.absNorm I.val : ℝ) ≤ N) →
        (∑ i, ‖∑ I ∈ c.support, c I * (ω i).character I.val‖ ^ 2) ≤
          C * (N + X ^ (2 : ℕ)) * (N * X) ^ ε * ∑ I ∈ c.support, ‖c I‖ ^ 2)
    {α : Type} (J : Finset α) (ω : α → PrimitiveFrequencyCharacter F)
    (hdist : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      ¬ samePrimitiveFrequencyCharacter F (ω i) (ω j))
    (hcond : ∀ i ∈ J, (Ideal.absNorm (ω i).conductor : ℝ) ≤ Ccond * X)
    (hP : ∀ i ∈ J, P (ω i))
    (B : Finset (Ideal (𝓞 F)))
    (hB : ∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (b : Ideal (𝓞 F) → ℂ) :
    (∑ i ∈ J, ‖∑ I ∈ B, b I * (ω i).character I‖ ^ 2) ≤
      C * (N + X ^ (2 : ℕ)) * (N * X) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  classical
  let D : Finset (NonzeroIdeal F) := B.attach.image (fun I => (⟨I.val, (hB I.val I.property).1⟩ : NonzeroIdeal F))
  have hD (I : NonzeroIdeal F) : I ∈ D ↔ I.val ∈ B := by
    simp only [D, Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨I, rfl⟩
      exact I.property
    · intro hI
      exact ⟨⟨I.val, hI⟩, Subtype.ext rfl⟩
  let c : NonzeroIdeal F →₀ ℂ := Finsupp.onFinset D
    (fun I => if I ∈ D then b I.val else 0) (by
      intro I hI
      by_contra hn
      simp [hn] at hI)
  have hc : c.support ⊆ D := Finsupp.support_onFinset_subset
  have hcval (I : NonzeroIdeal F) (hI : I ∈ D) : c I = b I.val := by
    simp [c, hI]
  have sumD {M : Type} [AddCommMonoid M] (f : Ideal (𝓞 F) → M) :
      (∑ I ∈ D, f I.val) = ∑ I ∈ B, f I := by
    dsimp only [D]
    rw [Finset.sum_image]
    · exact Finset.sum_attach B f
    · intro I hI K hK h
      exact Subtype.ext (congrArg (fun I : NonzeroIdeal F => I.val) h)
  have sumChar (χ : PrimitiveFrequencyCharacter F) :
      (∑ I ∈ c.support, c I * χ.character I.val) =
        ∑ I ∈ B, b I * χ.character I := by
    calc
      _ = ∑ I ∈ D, c I * χ.character I.val := by
        apply Finset.sum_subset hc
        intro I hI hn
        rw [Finsupp.notMem_support_iff.mp hn, zero_mul]
      _ = ∑ I ∈ D, b I.val * χ.character I.val :=
        Finset.sum_congr rfl (fun I hI => by rw [hcval I hI])
      _ = _ := sumD (fun I => b I * χ.character I)
  have sumEnergy : (∑ I ∈ c.support, ‖c I‖ ^ 2) = ∑ I ∈ B, ‖b I‖ ^ 2 := by
    calc
      _ = ∑ I ∈ D, ‖c I‖ ^ 2 := by
        apply Finset.sum_subset hc
        intro I hI hn
        simp [Finsupp.notMem_support_iff.mp hn]
      _ = ∑ I ∈ D, ‖b I.val‖ ^ 2 :=
        Finset.sum_congr rfl (fun I hI => by rw [hcval I hI])
      _ = _ := sumD (fun I => ‖b I‖ ^ 2)
  let e := (Fintype.equivFin J).symm
  have h := hbound (Fintype.card J) (fun i => ω (e i).val)
    (fun i j hij => hdist _ (e i).property _ (e j).property
      (fun hh => hij (e.injective (Subtype.ext hh))))
    (fun i => hcond _ (e i).property) (fun i => hP _ (e i).property) c
    (fun I hI => (hB I.val ((hD I).mp (hc hI))).2)
  simp only [sumChar, sumEnergy] at h
  rw [e.sum_comp (fun i : J => ‖∑ I ∈ B, b I * (ω i.val).character I‖ ^ 2)] at h
  rw [Finset.sum_coe_sort J (fun i => ‖∑ I ∈ B, b I * (ω i).character I‖ ^ 2)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem unrestricted_balanced_section
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) [IsPrincipalIdealRing A.R] :
    ∃ K_bal : Set A.G, IsCompact K_bal ∧
      Nonempty (A.BalancedIdealSection ⊤ K_bal) := by
  classical
  obtain ⟨K, hK, hcover⟩ := A.exists_compact_balanced_cover
  let K_bal : Set A.G := Subtype.val '' K
  have hcompact : IsCompact K_bal := hK.image continuous_subtype_val
  have hex : ∀ I : A.Exterior, ∃ (r : A.R) (a : Fˣ),
      A.Generates I r ∧ (a : F) = (r : F) ∧
      A.diagonal a / A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I) ∈ K_bal := by
    intro I
    let J := A.extendIdeal I
    let r := Submodule.IsPrincipal.generator J
    have hspan : Ideal.span {r} = J := Submodule.IsPrincipal.span_singleton_generator J
    have hr : r ≠ 0 := by
      intro h
      have hJ : J = ⊥ := by rw [← hspan, h]; simp
      have hJ0 : J ≠ ⊥ := A.extendIdeal_ne_zero I
      exact hJ0 hJ
    let a := Units.mk0 (r : F) (by exact_mod_cast hr)
    have ha : (a : F) = (r : F) := rfl
    have hg : A.Generates I r := ⟨hr, hspan⟩
    let y : A.G1 := ⟨A.diagonal a /
      A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I),
        A.normalized_generator_mem_G1 I r hg a ha⟩
    obtain ⟨γ, hγ⟩ := hcover y
    have hΓ : (γ.val : A.G) ∈ A.Gamma := γ.property
    obtain ⟨v, hv, hvγ⟩ := hΓ
    obtain ⟨u, hu, huv⟩ := hv
    let ε : A.U := ⟨u, hu⟩
    let r' : A.R := r * (A.unitEquiv ε ^ 6 : A.Rˣ)
    let a' : Fˣ := a * u ^ 6
    have ha' : (a' : F) = (r' : F) := by
      simp [a', r', ha, SArithmeticData.unitEquiv, ε]
    have hr' : A.Generates I r' := by
      refine ⟨mul_ne_zero hr (Units.ne_zero _), ?_⟩
      rw [Ideal.span_singleton_mul_right_unit (Units.isUnit _) r]
      exact hspan
    refine ⟨r', a', hr', ha', ?_⟩
    refine ⟨γ.val * y, hγ, ?_⟩
    change (γ.val : A.G) * (y : A.G) = _
    rw [← hvγ, ← huv]
    simp only [y, a', map_mul, map_pow, powMonoidHom_apply, div_eq_mul_inv]
    ac_rfl
  choose r a hr ha hb using hex
  refine ⟨K_bal, hcompact, ⟨{
    generator := r
    fieldUnit := a
    generates := hr
    fieldUnit_coe := ha
    allowed := ?_
    balanced := hb}⟩⟩
  intro I
  trivial

end Copied

variable {F : Type} [Field F] [NumberField F]

theorem all_ideal_sieve_transfer_of_dyadic
    (A : SArithmeticData F) (c0 : ℝ) (hc0 : 0 < c0)
    (L : Set (Detector.FixedSResidue.FullLocalCharacters A)) (hL : L.Finite)
    (hDyadic : ∀ σ ∈ L, Detector.HasExteriorDyadicConductorSieve F A σ c0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ {α : Type} (J : Finset α) (ω : α → Detector.PrimitiveFrequencyCharacter F),
          (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
            ¬ Detector.samePrimitiveFrequencyCharacter F (ω i) (ω j)) →
          (∀ i ∈ J, (Ideal.absNorm (ω i).conductor : ℝ) ≤ c0 * U) →
          (∀ i ∈ J, ∃ σ ∈ L, Detector.HasFixedFullSLocalTuple F A (ω i) σ) →
          ∀ (B : Finset (Ideal (𝓞 F))),
            (∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
            ∀ b : Ideal (𝓞 F) → ℂ,
              (∑ i ∈ J, ‖∑ I ∈ B, b I * (ω i).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    Detector.detector_logarithmic_sieve_gluing_epsilon F A c0 hc0 L hL hDyadic ε hε
  refine ⟨C, hC, ?_⟩
  intro U N hU hN α J ω hdist hcond hP B hB b
  exact primitive_sieve_finset_transfer_of_property F C c0 N U ε
    (fun ω => ∃ σ ∈ L, Detector.HasFixedFullSLocalTuple F A ω σ)
    (fun n ω hω' hcondω htype c hc => hbound N U hN hU n ω hω' htype hcondω c hc)
    J ω hdist hcond hP B hB b

theorem all_ideal_sieve_transfer
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (c0 : ℝ) (hc0 : 0 < c0)
    (L : Set (Detector.FixedSResidue.FullLocalCharacters R.A)) (hL : L.Finite)
    (hOrder : ∀ σ ∈ L, Detector.FixedSResidue.HasFiniteOrder R.A σ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ {α : Type} (J : Finset α) (ω : α → Detector.PrimitiveFrequencyCharacter F),
          (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
            ¬ Detector.samePrimitiveFrequencyCharacter F (ω i) (ω j)) →
          (∀ i ∈ J, (Ideal.absNorm (ω i).conductor : ℝ) ≤ c0 * U) →
          (∀ i ∈ J, ∃ σ ∈ L, Detector.HasFixedFullSLocalTuple F R.A (ω i) σ) →
          ∀ (B : Finset (Ideal (𝓞 F))),
            (∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
            ∀ b : Ideal (𝓞 F) → ℂ,
              (∑ i ∈ J, ‖∑ I ∈ B, b I * (ω i).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  classical
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  obtain ⟨K_bal, hK, ⟨s⟩⟩ := unrestricted_balanced_section F R.A
  exact all_ideal_sieve_transfer_of_dyadic R.A c0 hc0 L hL
    (fun σ hσ => Detector.hasExteriorDyadicConductorSieve_of_balancedSection F R.A ⊤ K_bal hK s σ
      (hOrder σ hσ) c0 hc0) ε hε

theorem all_ideal_sieve_transfer_frequency
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (c : ℝ) (hc : 0 < c)
    (L : Set (Detector.FixedSResidue.FullLocalCharacters R.A)) (hL : L.Finite)
    (hOrder : ∀ σ ∈ L, Detector.FixedSResidue.HasFiniteOrder R.A σ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ (ω : Frequency R → Detector.PrimitiveFrequencyCharacter F),
          (∀ u v : Frequency R,
            Detector.samePrimitiveFrequencyCharacter F (ω u) (ω v) → u = v) →
          (∀ u : Frequency R, (Ideal.absNorm (ω u).conductor : ℝ) ≤ c * frequencyNorm R u) →
          (∀ u : Frequency R, ∃ σ ∈ L, Detector.HasFixedFullSLocalTuple F R.A (ω u) σ) →
          ∀ (J : Finset (Frequency R)), (∀ u ∈ J, frequencyNorm R u < 2 * U) →
          ∀ (B : Finset (Ideal (𝓞 F))),
            (∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
            ∀ b : Ideal (𝓞 F) → ℂ,
              (∑ u ∈ J, ‖∑ I ∈ B, b I * (ω u).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := all_ideal_sieve_transfer R (2 * c) (by positivity) L hL hOrder ε hε
  refine ⟨C, hC, ?_⟩
  intro U N hU hN ω hinj hcond hP J hJ B hB b
  refine h U N hU hN J ω ?_ ?_ (fun u _ => hP u) B hB b
  · intro i _ j _ hij hsame
    exact hij (hinj i j hsame)
  · intro u hu
    calc (Ideal.absNorm (ω u).conductor : ℝ) ≤ c * frequencyNorm R u := hcond u
      _ ≤ c * (2 * U) := mul_le_mul_of_nonneg_left (hJ u hu).le hc.le
      _ = 2 * c * U := by ring

end

end DedekindZetaZeroFree.Quantitative.AllIdealSieveTransfer31
