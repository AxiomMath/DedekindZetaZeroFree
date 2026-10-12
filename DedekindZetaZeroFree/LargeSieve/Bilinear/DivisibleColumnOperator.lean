module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEnvelopes

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.DivisiblePrefix
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma column_admissible (C : Context Q) {u : Ideal (𝓞 F)}
    (hu : u ∈ C.columns) : u ∈ Sieve.idealAdmissibleFinset F c (2 * C.N / norm C.d) :=
  (Finset.mem_filter.mp hu).1

private lemma homogeneous_domination {ι : Type*} (E H : (ι → ℂ) → ℝ)
    (hE : ∀ x, 0 ≤ E x)
    (hEs : ∀ x (t : ℝ), E (fun i => (t : ℂ) * x i) = t ^ 2 * E x)
    (hHs : ∀ x (t : ℝ), H (fun i => (t : ℂ) * x i) = t ^ 2 * H x)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, H x ≤ C * E x) (x : ι → ℂ) :
    H x ≤ sSup ({0} ∪ {y : ℝ | ∃ z, E z ≤ 1 ∧ y = H z}) * E x := by
  let S : Set ℝ := {0} ∪ {y : ℝ | ∃ z, E z ≤ 1 ∧ y = H z}
  have hS : BddAbove S := by
    refine ⟨C, ?_⟩
    rintro y (hy | ⟨z, hz, rfl⟩)
    · have : y = 0 := hy
      subst y
      exact hC
    · exact (hbound z).trans (mul_le_of_le_one_right hC hz)
  by_cases he : E x = 0
  · simpa [he] using hbound x
  have hepos : 0 < E x := lt_of_le_of_ne (hE x) (Ne.symm he)
  let t : ℝ := (Real.sqrt (E x))⁻¹
  have ht : t ^ 2 * E x = 1 := by
    dsimp [t]
    rw [inv_pow, Real.sq_sqrt (hE x), inv_mul_cancel₀ he]
  have hm : H (fun i => (t : ℂ) * x i) ≤ sSup S := by
    apply le_csSup hS
    exact Or.inr ⟨_, (hEs x t).trans_le (by rw [ht]), rfl⟩
  have hm' := mul_le_mul_of_nonneg_right hm (hE x)
  rw [hHs] at hm'
  simpa only [mul_assoc, ht, mul_left_comm, mul_one] using hm'
private lemma finite_form_bound {ι ρ : Type*} (S : Finset ι) (R : Finset ρ)
    (H : ι → ρ → ℂ) (z : ι → ℂ) :
    (∑ a ∈ R, ‖∑ b ∈ S, z b * H b a‖ ^ 2) ≤
      sSup ({0} ∪ {y : ℝ | ∃ w : ι → ℂ,
        (∑ b ∈ S, ‖w b‖ ^ 2) ≤ 1 ∧
          y = ∑ a ∈ R, ‖∑ b ∈ S, w b * H b a‖ ^ 2}) *
        ∑ b ∈ S, ‖z b‖ ^ 2 := by
  apply homogeneous_domination
    (fun w => ∑ b ∈ S, ‖w b‖ ^ 2)
    (fun w => ∑ a ∈ R, ‖∑ b ∈ S, w b * H b a‖ ^ 2)
    (by intro w; positivity)
    (by intro w t; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, Finset.mul_sum])
    (by
      intro w t
      simp only [mul_assoc, ← Finset.mul_sum, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      )
    (∑ a ∈ R, ∑ b ∈ S, ‖H b a‖ ^ 2) (by positivity)
  intro w
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  calc
    _ ≤ (∑ b ∈ S, ‖w b * H b a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ = (∑ b ∈ S, ‖w b‖ * ‖H b a‖) ^ 2 := by simp only [norm_mul]
    _ ≤ (∑ b ∈ S, ‖w b‖ ^ 2) * ∑ b ∈ S, ‖H b a‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq S _ _
    _ = _ := mul_comm _ _

private lemma restricted_prefix_bound (B X : ℝ) (R S : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ Sieve.idealAdmissibleFinset F c (2 * B))
    (hS : S ⊆ Sieve.idealAdmissibleFinset F c (2 * X))
    (z : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ R, ‖∑ b ∈ S, z b * (Q.χ b) a‖ ^ 2) ≤
      ErrorRectangles.U Q B X * ∑ b ∈ S, ‖z b‖ ^ 2 := by
  let w : Ideal (𝓞 F) → ℂ := fun b => if b ∈ S then z b else 0
  have hs : ∀ a, (∑ b ∈ Sieve.idealAdmissibleFinset F c (2 * X),
      w b * (Q.χ b) a) = ∑ b ∈ S, z b * (Q.χ b) a := by
    intro a
    simp only [w, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have he : (∑ b ∈ Sieve.idealAdmissibleFinset F c (2 * X), ‖w b‖ ^ 2) =
      ∑ b ∈ S, ‖z b‖ ^ 2 := by
    simp only [w, apply_ite (fun x : ℂ => ‖x‖ ^ 2), norm_zero,
      zero_pow (by decide : 2 ≠ 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  calc
    _ ≤ ∑ a ∈ Sieve.idealAdmissibleFinset F c (2 * B),
        ‖∑ b ∈ Sieve.idealAdmissibleFinset F c (2 * X), w b * (Q.χ b) a‖ ^ 2 := by
      simp only [hs]
      exact Finset.sum_le_sum_of_subset_of_nonneg hR (by intros; positivity)
    _ ≤ _ := by
      simpa only [he, ErrorRectangles.U] using
        (finite_form_bound (Sieve.idealAdmissibleFinset F c (2 * X))
          (Sieve.idealAdmissibleFinset F c (2 * B)) (fun b a => (Q.χ b) a) w)

private lemma phase_norm (g h : Q.G) : ‖Q.C g h‖ = 1 := by
  have hh := congrArg (fun z : ℂ => ‖z‖) (Q.C_sq g h)
  rw [norm_pow, norm_one] at hh
  nlinarith [norm_nonneg (Q.C g h)]

private lemma transport_prefix_bound
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c)
    (B X : ℝ) (f : Ideal (𝓞 F))
    (R T : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ Sieve.idealAdmissibleFinset F c (2 * B))
    (hT : T ⊆ Sieve.idealAdmissibleFinset F c (2 * X))
    (hft : ∀ t ∈ T, Squarefree (f * t) ∧ (f * t) ⊔ c = ⊤)
    (w : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ R, ‖∑ t ∈ T, w t * (Q.χ (f*t)) a‖ ^ 2) ≤
      (Nat.card Q.G : ℝ)^2 * ErrorRectangles.U Q B X * ∑ t ∈ T, ‖w t‖ ^ 2 := by
  classical
  letI : Fintype Q.G := Fintype.ofFinite Q.G
  let I := (Finset.univ : Finset Unit)
  let J := (Finset.univ : Finset (Q.G × Q.G))
  let RB := fun _ : Unit => R
  let VB := fun h : Q.G × Q.G => T.filter (fun t => (Q.cls t, Q.cls (f*t)) = h)
  have hr := (DedekindZetaZeroFree.LargeSieve.algebra_normalized_reciprocity F c Q D.bad D.bad_ne_bot
    D.original_dvd_bad (fun a ha haq => ⟨D.index_dvd_conductor a ha haq,
      D.conductor_dvd_index_bad a ha haq⟩)).2.1
  have hloc : ∀ g ∈ I, ∀ h ∈ J, ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ RB g, ‖∑ t ∈ VB h, z t * (Q.χ (f*t)) a‖ ^ 2) ≤
        ErrorRectangles.U Q B X * ∑ t ∈ VB h, ‖z t‖ ^ 2 := by
    intro g hg h hh z
    have hsubV : VB h ⊆ T := Finset.filter_subset _ _
    let p := fun a => (Q.χ a) f * Q.C h.2 (Q.cls a) * Q.C h.1 (Q.cls a)
    have hp : ∀ a ∈ R, ‖p a‖ ≤ 1 := by
      intro a ha
      have hm := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (hR ha)
      simpa [p, norm_mul, phase_norm] using quadraticFamily_norm_le_one Q hm.1 hm.2.1 f
    have heq : ∀ a ∈ R, ∀ t ∈ VB h,
        (Q.χ (f*t)) a = (Q.χ t) a * p a := by
      intro a ha t ht
      have ham := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (hR ha)
      have htm := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (hT (hsubV ht))
      have hdm := hft t (hsubV ht)
      have hc := (Finset.mem_filter.mp ht).2
      have hc1 : Q.cls t = h.1 := congrArg Prod.fst hc
      have hc2 : Q.cls (f*t) = h.2 := congrArg Prod.snd hc
      have h1 := hr (f*t) a hdm.1 (by simpa only [core] using hdm.2) ham.1 (by simpa only [core] using ham.2.1)
      have h2 := hr t a htm.1 (by simpa only [core] using htm.2.1) ham.1 (by simpa only [core] using ham.2.1)
      have h3 : (Q.χ a) t = (Q.χ t) a * Q.C (Q.cls t) (Q.cls a) := by
        rw [h2, mul_assoc, ← pow_two, Q.C_sq, mul_one]
      rw [h1, (Q.χ a).map_mul', h3, hc1, hc2]
      dsimp [p]
      ring
    have hbound := restricted_prefix_bound (Q := Q) B X R (VB h) hR
      (hsubV.trans hT) z
    dsimp [RB]
    calc
      _ = ∑ a ∈ R, ‖(∑ t ∈ VB h, z t * (Q.χ t) a) * p a‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        congr 2
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t ht
        rw [heq a ha t ht, mul_assoc]
      _ ≤ ∑ a ∈ R, ‖∑ t ∈ VB h, z t * (Q.χ t) a‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_mul, mul_pow]
        exact mul_le_of_le_one_right (sq_nonneg _)
          (by have hh := hp a ha; nlinarith [norm_nonneg (p a)])
      _ ≤ _ := hbound
  have hh := Sieve.SplitPrefixEnvelope.finite_partition_quadratic_bound I J R T RB VB
    (by ext a; simp [I, RB]) (by ext t; simp [J, VB])
    (by intro i hi j hj hij; exact False.elim (hij (Subsingleton.elim i j)))
    (by
      intro i hi j hj hij
      apply Finset.disjoint_left.mpr
      intro t hti htj
      exact hij (((Finset.mem_filter.mp hti).2).symm.trans (Finset.mem_filter.mp htj).2))
    (fun t a => (Q.χ (f*t)) a) (ErrorRectangles.U Q B X)
    (Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩) hloc w
  simp only [I, J, Finset.card_univ, Fintype.card_unit, Nat.cast_one,
    one_mul, Fintype.card_prod, Fintype.card_eq_nat_card, Nat.cast_mul] at hh
  have hunit : Nat.card Unit = 1 := by simp
  simpa only [hunit, Nat.cast_one, one_mul, pow_two, Nat.card_prod, Nat.cast_mul] using hh

theorem realized_divisible_column_U
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ C : Context Q, C.D = D → 1 ≤ C.N →
      ∀ (B P : ℝ), 1 ≤ B → 1 ≤ P →
      ∀ (f : Ideal (𝓞 F)), f ≠ ⊥ → Squarefree f → f ⊔ c = ⊤ → P ≤ norm f →
      ∀ (R V : Finset (Ideal (𝓞 F))),
        R ⊆ Sieve.idealAdmissibleFinset F c (2 * B) → V ⊆ C.columns →
      ∀ (r v z : Ideal (𝓞 F) → ℂ),
        (∀ a ∈ R, ‖r a‖ ≤ 1) → (∀ u ∈ V, ‖v u‖ ≤ 1) →
        (∑ a ∈ R, ‖∑ u ∈ V,
          if f ∣ u then r a * (z u * (Q.χ u) a) * v u else 0‖ ^ 2) ≤
          A * ErrorRectangles.U Q B (C.N / (norm C.d * P)) *
            ∑ u ∈ V, if f ∣ u then ‖z u‖ ^ 2 else 0 := by
  refine ⟨(Nat.card Q.G : ℝ)^2 + 1, (by nlinarith [sq_nonneg (Nat.card Q.G : ℝ)]), ?_⟩
  intro C hCD hN B P hB hP f hf0 hfsf hfc hPf R V hR hV r v z hr hv
  let X : ℝ := C.N / (norm C.d * P)
  let T := (Sieve.idealAdmissibleFinset F c (2 * X)).filter (fun t => f*t ∈ V)
  have hinj : Function.Injective (fun t : Ideal (𝓞 F) => f*t) := by
    intro t v h
    exact mul_left_cancel₀ hf0 h
  have hT : T ⊆ Sieve.idealAdmissibleFinset F c (2 * X) := Finset.filter_subset _ _
  have hftV : ∀ t ∈ T, f*t ∈ V := fun t ht => (Finset.mem_filter.mp ht).2
  have hft : ∀ t ∈ T, Squarefree (f*t) ∧ (f*t) ⊔ c = ⊤ := by
    intro t ht
    have hm := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
      (column_admissible C (hV (hftV t ht)))
    exact ⟨hm.1, hm.2.1⟩
  have honto : ∀ u ∈ V.filter (fun u => f ∣ u), ∃ t ∈ T, f*t = u := by
    intro u hu
    obtain ⟨huV, hud⟩ := Finset.mem_filter.mp hu
    have huC := hV huV
    have hu0 := ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
      (column_admissible C huC)).1.ne_zero
    obtain ⟨t, ht⟩ := hud
    have htdiv : t ∣ u := by rw [ht]; exact dvd_mul_left _ _
    obtain ⟨husf, huc, hunorm⟩ := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
      (column_admissible C huC)
    have htsf : Squarefree t := husf.squarefree_of_dvd htdiv
    have htc : t ⊔ c = ⊤ :=
      eq_top_iff.mpr (huc ▸ sup_le_sup_right (Ideal.dvd_iff_le.mp htdiv) c)
    have hdpos : 0 < norm C.d := by
      dsimp [ExplicitTerms.norm]
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.hd0)
    have htpos : 0 ≤ norm t := Nat.cast_nonneg _
    have hprod : norm u = norm f * norm t := by simp [ht, ExplicitTerms.norm, map_mul]
    have htnorm : norm t ≤ 2 * C.N / (norm C.d * P) := by
      apply (le_div_iff₀ (mul_pos hdpos (lt_of_lt_of_le zero_lt_one hP))).mpr
      have hu' := (le_div_iff₀ hdpos).mp hunorm
      change norm u * norm C.d ≤ 2 * C.N at hu'
      calc
        norm t * (norm C.d * P) = (P * norm t) * norm C.d := by ring
        _ ≤ (norm f * norm t) * norm C.d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPf htpos) (le_of_lt hdpos)
        _ ≤ 2 * C.N := by rwa [← hprod]
    have htp : t ∈ Sieve.idealAdmissibleFinset F c (2 * X) := by
      apply (Sieve.mem_idealAdmissibleFinset _ _ _ _).mpr
      refine ⟨htsf, htc, ?_⟩
      change norm t ≤ _
      convert htnorm using 1 <;> dsimp [X] <;> ring
    exact ⟨t, Finset.mem_filter.mpr ⟨htp, ht ▸ huV⟩, ht.symm⟩
  have hreindex : ∀ h : Ideal (𝓞 F) → ℂ,
      (∑ u ∈ V, if f ∣ u then h u else 0) = ∑ t ∈ T, h (f*t) := by
    intro h
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_bij (fun t ht => f*t)
    · intro t ht
      exact Finset.mem_filter.mpr ⟨hftV t ht, dvd_mul_right f t⟩
    · intro t ht v hv he
      exact hinj he
    · intro u hu
      obtain ⟨t, ht, he⟩ := honto u hu
      exact ⟨t, ht, he⟩
    · intros; rfl
  let w : Ideal (𝓞 F) → ℂ := fun t => z (f*t) * v (f*t)
  have henergy : (∑ t ∈ T, ‖w t‖ ^ 2) ≤
      ∑ u ∈ V, if f ∣ u then ‖z u‖ ^ 2 else 0 := by
    calc
      _ ≤ ∑ t ∈ T, ‖z (f*t)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        dsimp [w]
        rw [norm_mul, mul_pow]
        exact mul_le_of_le_one_right (sq_nonneg _)
          (by have hh := hv (f*t) (hftV t ht); nlinarith [norm_nonneg (v (f*t))])
      _ = ∑ u ∈ V.filter (fun u => f ∣ u), ‖z u‖ ^ 2 := by
        apply Finset.sum_bij (fun t ht => f*t)
        · intro t ht
          exact Finset.mem_filter.mpr ⟨hftV t ht, dvd_mul_right f t⟩
        · intro t ht v hv he
          exact hinj he
        · intro u hu
          obtain ⟨t, ht, he⟩ := honto u hu
          exact ⟨t, ht, he⟩
        · intros; rfl
      _ = _ := Finset.sum_filter _ _
  have hrow : (∑ a ∈ R, ‖∑ u ∈ V,
      if f ∣ u then r a * (z u * (Q.χ u) a) * v u else 0‖ ^ 2) ≤
      ∑ a ∈ R, ‖∑ t ∈ T, w t * (Q.χ (f*t)) a‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro a ha
    rw [hreindex]
    have he : (∑ t ∈ T, r a * (z (f*t) * (Q.χ (f*t)) a) * v (f*t)) =
        r a * ∑ t ∈ T, w t * (Q.χ (f*t)) a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp [w]
      ring
    rw [he, norm_mul, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _)
      (by have hh := hr a ha; nlinarith [norm_nonneg (r a)])
  have hU : 0 ≤ ErrorRectangles.U Q B X := Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩
  calc
    _ ≤ _ := hrow
    _ ≤ (Nat.card Q.G : ℝ)^2 * ErrorRectangles.U Q B X * ∑ t ∈ T, ‖w t‖ ^ 2 :=
      transport_prefix_bound D core B X f R T hR hT hft w
    _ ≤ (Nat.card Q.G : ℝ)^2 * ErrorRectangles.U Q B X * (∑ u ∈ V, if f ∣ u then ‖z u‖ ^ 2 else 0) :=
      mul_le_mul_of_nonneg_left henergy (mul_nonneg (sq_nonneg _) hU)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : (Nat.card Q.G : ℝ)^2 ≤ (Nat.card Q.G : ℝ)^2 + 1) hU) (by positivity)

end DedekindZetaZeroFree.LargeSieve.Bilinear.DivisiblePrefix

end
