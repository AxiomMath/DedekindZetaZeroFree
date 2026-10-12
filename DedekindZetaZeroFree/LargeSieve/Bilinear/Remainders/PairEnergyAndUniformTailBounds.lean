module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterLift
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Remainders.GeometricBudgetsAndRowRatios

@[expose] public section

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/
noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly
open ExplicitTerms

theorem cutoff_pair_decay
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ C : Context Q, C.D = D → C.W = W →
        1 ≤ C.M → 1 ≤ C.N →
        C.N ^ 2 / C.M * Real.rpow (C.M * C.N) ε ≤ C.K →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ∀ (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p),
          p ∈ C.pairs →
          ‖primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2
            (C.primitive p hp)‖ ≤ B * Real.rpow (C.M * C.N) (-2) := by
  by_cases hW : Sieve.SieveWeight W
  · by_cases hF : NumberField.IsTotallyComplex F
    · obtain ⟨A, δ, CW, hA, hδ, _, hδA, horder, hCW, hsmall, hlarge⟩ :=
        TransformTail.chooseOrder hF W hW ε 2 hε (by norm_num)
      obtain ⟨T, hT, hagg⟩ := TransformTail.aggregate c D.original_ne_bot A hA
      let B := T * CW * Real.rpow (4 * (Ideal.absNorm c : ℝ)) ((A : ℝ) - 1)
      have hB : 0 ≤ B := by dsimp [B]; positivity
      refine ⟨2 * B, by positivity, ?_⟩
      intro C hCD hCW' hM hN hK hd1 hdN p hp hpair
      have hM0 : 0 < C.M := by linarith
      have hN0 : 0 < C.N := by linarith
      have hd0 : 0 < norm C.d := by linarith
      have hK0 : 0 < C.K := (mul_pos (div_pos (pow_pos hN0 2) hM0)
        (Real.rpow_pos_of_pos (mul_pos hM0 hN0) ε)).trans_le hK
      have hcols := (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1)
      have hshell : ∀ u ∈ C.columns,
          u ∈ Sieve.paperShell F ⊤ (C.N / (Ideal.absNorm C.d : ℝ)) := by
        intro u hu
        obtain ⟨huad, hus, _⟩ := Finset.mem_filter.mp hu
        have huN := (Sieve.mem_idealAdmissibleFinset F c _ u).mp huad
        have hduN := (Sieve.mem_paperShell F c C.N _).mp hus
        apply (Sieve.mem_paperShell F ⊤ _ u).mpr
        refine ⟨huN.1, by simp, ?_, ?_⟩
        · apply (div_lt_iff₀ hd0).mpr
          change C.N < (Ideal.absNorm u : ℝ) * (Ideal.absNorm C.d : ℝ)
          simpa only [map_mul, Nat.cast_mul,
            mul_comm (Ideal.absNorm C.d : ℝ) (Ideal.absNorm u : ℝ)] using hduN.2.2.1
        · simpa only [ExplicitTerms.norm, mul_div_assoc] using huN.2.2
      let L : Finset (Ideal (𝓞 F)) := {p.1, p.2}
      have hL : L ⊆ Sieve.paperShell F ⊤ (C.N / (Ideal.absNorm C.d : ℝ)) := by
        intro u hu
        simp only [L, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hshell _ hcols.1
        · exact hshell _ hcols.2
      let θ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun u v =>
        if u = p.1 ∧ v = p.2 then 1 else 0
      let η : ∀ u v : Ideal (𝓞 F),
          DedekindZetaZeroFree.RayClassCharacter F (u * v) := fun u v =>
        if h : C.ValidPair (u, v) then C.primitive (u, v) h
        else Sieve.Initial.liftCharacter (by simp [Ideal.dvd_iff_le]) (principalCharacter F)
      have hθ : ∀ u ∈ L, ∀ v ∈ L, ‖θ u v‖ ≤ 1 := by
        intro u _ v _
        dsimp [θ]
        split_ifs <;> norm_num
      obtain ⟨_, hmajor, hblock⟩ := hagg W δ CW hδ hδA hCW.le hsmall hlarge
        C.M C.N C.K hM hN hK0 C.d C.hd0 hd1 hdN L hL (fun _ => 1) θ hθ η
      have hc0 : 0 < (Ideal.absNorm c : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.original_ne_bot)
      have habsorb := TransformTail.absorb (Ideal.absNorm c : ℝ) ε 2 T CW
        hc0 hε hT hCW.le A hA horder C.M C.N C.K (norm C.d) hM hN hd1 hK
      have henergy : (∑ u ∈ L, ‖(1 : ℂ)‖ ^ 2) ≤ (2 : ℝ) := by
        have hc : L.card ≤ 2 := (Finset.card_insert_le p.1 {p.2}).trans (by simp)
        simpa only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
          using (show (L.card : ℝ) ≤ 2 by exact_mod_cast hc)
      have hnonneg : 0 ≤ (∑ u ∈ L, ‖(1 : ℂ)‖ ^ 2) := by positivity
      have hbound := hblock.trans (hmajor.trans
        (mul_le_mul_of_nonneg_right habsorb hnonneg))
      have heq : TransformTail.blockTail c C.d W C.M C.K L (fun _ => 1) θ η =
          primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2 (C.primitive p hp) := by
        have hηp : η p.1 p.2 = C.primitive p hp := by simp [η, hp]
        have hneq : p.1 ≠ p.2 := by
          intro he
          have htop : p.2 = ⊤ := by simpa only [he, sup_idem] using hp.huv
          exact hp.offDiagonal (by simp [he, htop])
        calc
          _ = TransformTail.mobiusTail c C.d W C.M C.K p.1 p.2 (η p.1 p.2) := by
            simp [TransformTail.blockTail, θ, L, hneq, Ne.symm hneq]
          _ = _ := by rw [hηp, hCW']; rfl
      rw [heq] at hbound
      calc
        _ ≤ B * Real.rpow (C.M * C.N) (-2) * (∑ u ∈ L, ‖(1 : ℂ)‖ ^ 2) := hbound
        _ ≤ B * Real.rpow (C.M * C.N) (-2) * 2 :=
          mul_le_mul_of_nonneg_left henergy (mul_nonneg hB
            (Real.rpow_nonneg (mul_pos hM0 hN0).le _))
        _ = _ := by ring
    · refine ⟨0, le_rfl, ?_⟩
      intro C _ _
      exact (hF C.hF).elim
  · refine ⟨0, le_rfl, ?_⟩
    intro C _ hCW
    exact (hW (hCW ▸ C.hW)).elim

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly
open ExplicitTerms

 theorem column_energy_le {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) :
    (∑ u ∈ C.columns, ‖C.lam (C.d * u)‖ ^ 2) ≤ Sieve.energy F c C.N C.lam := by
  have hinj : Set.InjOn (fun u => C.d * u) (C.columns : Set (Ideal (𝓞 F))) := by
    intro u hu v hv h
    exact mul_left_cancel₀ C.hd0 h
  have heq := Finset.sum_image (f := fun b => ‖C.lam b‖ ^ 2) hinj
  rw [← heq]
  unfold Sieve.energy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hu).2.1
  · intro b hb hnot
    positivity

 theorem pair_coefficient_sum_le {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) :
    (∑ p ∈ C.pairs, ‖C.coefficient p‖) ≤
      (C.columns.card : ℝ) * Sieve.energy F c C.N C.lam := by
  calc
    (∑ p ∈ C.pairs, ‖C.coefficient p‖) ≤
        ∑ p ∈ C.columns ×ˢ C.columns, ‖C.coefficient p‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro p hp hn; exact norm_nonneg _
    _ = (∑ u ∈ C.columns, ‖C.lam (C.d * u)‖) ^ 2 := by
      rw [Finset.sum_product]
      simp only [Context.coefficient, norm_mul, norm_star]
      rw [← Finset.sum_mul_sum, pow_two]
    _ ≤ (C.columns.card : ℝ) * (∑ u ∈ C.columns, ‖C.lam (C.d * u)‖ ^ 2) :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (C.columns.card : ℝ) * Sieve.energy F c C.N C.lam :=
      mul_le_mul_of_nonneg_left (column_energy_le C) (Nat.cast_nonneg _)

theorem finite_pair_energy_bound (F : Type) [Field F] [NumberField F] :
    ∃ H : ℝ, 0 < H ∧
      ∀ {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
        (C : Context Q), 1 ≤ C.N → 1 ≤ norm C.d →
        (∑ p ∈ C.pairs, ‖C.coefficient p‖) ≤
          H * C.N * Sieve.energy F c C.N C.lam := by
  obtain ⟨H, hH, _, hcount⟩ := exists_ideal_count_bound_finset F
  refine ⟨2 * H, by linarith, ?_⟩
  intro c Q C hN hd
  have hbound : (C.columns.card : ℝ) ≤ H * (2 * C.N) := by
    apply hcount (2 * C.N) (by linarith) C.columns
    intro u hu
    have hnorm : (Ideal.absNorm u : ℝ) ≤ 2 * C.N / norm C.d :=
      ((Sieve.mem_idealAdmissibleFinset F c _ u).mp (Finset.mem_filter.mp hu).1).2.2
    exact hnorm.trans ((div_le_iff₀ (by linarith : 0 < norm C.d)).mpr (by nlinarith))
  have henergy : 0 ≤ Sieve.energy F c C.N C.lam := by
    unfold Sieve.energy; positivity
  exact (pair_coefficient_sum_le C).trans
    ((mul_le_mul_of_nonneg_right hbound henergy).trans_eq (by ring))
end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailAux

lemma cutoff_inner_bound (F : Type*) [Field F] [NumberField F]
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℝ → ℂ) (P : ℝ), 0 ≤ P →
      (∀ x : ℝ, 0 < x → ‖k x‖ ≤ P * Real.rpow x (-p)) →
      ∀ (T L : ℝ) (d : Ideal (𝓞 F)), 0 < T → 1 ≤ L → d ≠ ⊥ →
        ‖(T / (Ideal.absNorm d : ℝ) : ℂ) *
          ∑' b : Ideal (𝓞 F), ReflectedTails.dualCutoffSummand F k T L d b‖ ≤
          C * P * Real.rpow (L * T / (Ideal.absNorm d : ℝ)) (1-p) := by
  obtain ⟨C, hC, hbound⟩ := PoissonTruncation.exists_scaled_ideal_series_tail_bound F p hp
  refine ⟨C, hC, ?_⟩
  intro k P hP hk T L d hT hL hd
  have hnd : 0 < (Ideal.absNorm d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd)
  have hu : 0 < T / (Ideal.absNorm d : ℝ) := div_pos hT hnd
  have hb := (hbound P hP k hk _ hu).2.2.2 L hL
  have heq (b : Ideal (𝓞 F)) : ReflectedTails.dualCutoffSummand F k T L d b =
      if b ≠ ⊥ ∧ L < (Ideal.absNorm b : ℝ)
        then k ((T / (Ideal.absNorm d : ℝ)) * (Ideal.absNorm b : ℝ)) else 0 := by
    unfold ReflectedTails.dualCutoffSummand
    split_ifs <;> congr 1 <;> ring
  have hsum : Summable (fun b : Ideal (𝓞 F) =>
      ‖ReflectedTails.dualCutoffSummand F k T L d b‖) := by
    simpa only [heq, apply_ite norm, norm_zero] using hb.1
  have hi : ‖∑' b : Ideal (𝓞 F), ReflectedTails.dualCutoffSummand F k T L d b‖ ≤
      C * P * Real.rpow (T / (Ideal.absNorm d : ℝ)) (-p) * Real.rpow L (1-p) := by
    refine (norm_tsum_le_tsum_norm hsum).trans ?_
    simpa only [heq, apply_ite norm, norm_zero, Real.rpow_eq_pow] using hb.2.2.1
  rw [norm_mul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  refine (mul_le_mul_of_nonneg_left hi hu.le).trans_eq ?_
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  simp only [Real.rpow_eq_pow] at *
  rw [show L * T / (Ideal.absNorm d : ℝ) = L * (T / (Ideal.absNorm d : ℝ)) by ring,
    Real.mul_rpow hL0.le hu.le]
  have he : (T / (Ideal.absNorm d : ℝ)) * (T / (Ideal.absNorm d : ℝ)) ^ (-p) =
      (T / (Ideal.absNorm d : ℝ)) ^ (1-p) := by
    nth_rewrite 1 [← Real.rpow_one (T / (Ideal.absNorm d : ℝ))]
    rw [← Real.rpow_add hu]
    congr 1 <;> ring
  calc
    _ = C * P * L ^ (1-p) *
        ((T / (Ideal.absNorm d : ℝ)) * (T / (Ideal.absNorm d : ℝ)) ^ (-p)) := by ring
    _ = _ := by rw [he]; ring

theorem primal_tail_all_scale (F : Type*) [Field F] [NumberField F]
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℝ → ℂ) (P : ℝ), 0 ≤ P →
      (∀ x : ℝ, 0 < x → ‖g x‖ ≤ P * Real.rpow x (-p)) →
      ∀ (T Z : ℝ), 0 < T → 0 < Z →
      ∀ (D : Finset (Ideal (𝓞 F))), (∀ d ∈ D, d ≠ ⊥ ∧ Z < (Ideal.absNorm d : ℝ)) →
      ∀ (a : Ideal (𝓞 F) → ℂ), (∀ d ∈ D, ‖a d‖ ≤ 1) →
        ‖ReflectedTails.primalTail F g T D a‖ ≤
          C * P * (D.card : ℝ) * Real.rpow (Z / T) (-p) := by
  obtain ⟨C, hC, hb⟩ := PoissonTruncation.exists_scaled_ideal_series_tail_bound F p hp
  refine ⟨C, hC, ?_⟩
  intro g P hP hg T Z hT hZ D hD a ha
  have hterm : ∀ d ∈ D, ‖a d * ∑' b, ReflectedTails.primalSummand F g T d b‖ ≤
      C * P * Real.rpow (Z / T) (-p) := by
    intro d hd
    have hn : 0 < (Ideal.absNorm d : ℝ) := hZ.trans (hD d hd).2
    have hu : 0 < (Ideal.absNorm d : ℝ) / T := div_pos hn hT
    have hs := hb P hP g hg _ hu
    have heq (b : Ideal (𝓞 F)) : ReflectedTails.primalSummand F g T d b =
        if b = ⊥ then 0 else g (((Ideal.absNorm d : ℝ) / T) * (Ideal.absNorm b : ℝ)) := by
      unfold ReflectedTails.primalSummand
      split_ifs <;> congr 1 <;> ring
    have hsum : Summable (fun b : Ideal (𝓞 F) => ‖ReflectedTails.primalSummand F g T d b‖) := by
      simpa only [heq] using hs.1
    have hi : ‖∑' b, ReflectedTails.primalSummand F g T d b‖ ≤
        C * P * Real.rpow ((Ideal.absNorm d : ℝ) / T) (-p) := by
      refine (norm_tsum_le_tsum_norm hsum).trans ?_
      simpa only [heq, Real.rpow_eq_pow] using hs.2.2.1
    have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hZ hT)
      (div_le_div_of_nonneg_right (hD d hd).2.le hT.le) (show -p ≤ 0 by linarith)
    calc
      _ = ‖a d‖ * ‖∑' b, ReflectedTails.primalSummand F g T d b‖ := norm_mul _ _
      _ ≤ 1 * (C * P * Real.rpow ((Ideal.absNorm d : ℝ) / T) (-p)) :=
        mul_le_mul (ha d hd) hi (norm_nonneg _) zero_le_one
      _ ≤ C * P * Real.rpow (Z / T) (-p) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hP)
  calc
    _ ≤ ∑ d ∈ D, ‖a d * ∑' b, ReflectedTails.primalSummand F g T d b‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ D, C * P * Real.rpow (Z / T) (-p) := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem small_dual_tail_all_scale (F : Type*) [Field F] [NumberField F]
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℝ → ℂ) (P : ℝ), 0 ≤ P →
      (∀ x : ℝ, 0 < x → ‖k x‖ ≤ P * Real.rpow x (-p)) →
      ∀ (T Y : ℝ), 0 < T → 0 < Y →
      ∀ (D : Finset (Ideal (𝓞 F))), (∀ d ∈ D, d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ Y) →
      ∀ (a : Ideal (𝓞 F) → ℂ), (∀ d ∈ D, ‖a d‖ ≤ 1) →
        ‖ReflectedTails.smallDualTail F k T D a‖ ≤
          C * P * (D.card : ℝ) * Real.rpow (T / Y) (1-p) := by
  obtain ⟨C, hC, hb⟩ := PoissonTruncation.exists_scaled_ideal_series_tail_bound F p hp
  refine ⟨C, hC, ?_⟩
  intro k P hP hk T Y hT hY D hD a ha
  have hterm : ∀ d ∈ D, ‖a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
      ∑' b, ReflectedTails.dualSummand F k T d b‖ ≤
      C * P * Real.rpow (T / Y) (1-p) := by
    intro d hd
    have hn : 0 < (Ideal.absNorm d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hD d hd).1)
    have hu : 0 < T / (Ideal.absNorm d : ℝ) := div_pos hT hn
    have hs := hb P hP k hk _ hu
    have heq (b : Ideal (𝓞 F)) : ReflectedTails.dualSummand F k T d b =
        if b = ⊥ then 0 else k ((T / (Ideal.absNorm d : ℝ)) * (Ideal.absNorm b : ℝ)) := by
      unfold ReflectedTails.dualSummand
      split_ifs <;> congr 1 <;> ring
    have hsum : Summable (fun b : Ideal (𝓞 F) => ‖ReflectedTails.dualSummand F k T d b‖) := by
      simpa only [heq] using hs.1
    have hi : ‖∑' b, ReflectedTails.dualSummand F k T d b‖ ≤
        C * P * Real.rpow (T / (Ideal.absNorm d : ℝ)) (-p) := by
      refine (norm_tsum_le_tsum_norm hsum).trans ?_
      simpa only [heq, Real.rpow_eq_pow] using hs.2.2.1
    have hip : ‖(T / (Ideal.absNorm d : ℝ) : ℂ) *
        ∑' b, ReflectedTails.dualSummand F k T d b‖ ≤
        C * P * Real.rpow (T / (Ideal.absNorm d : ℝ)) (1-p) := by
      rw [norm_mul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
      refine (mul_le_mul_of_nonneg_left hi hu.le).trans_eq ?_
      simp only [Real.rpow_eq_pow]
      have he : (T / (Ideal.absNorm d : ℝ)) * (T / (Ideal.absNorm d : ℝ)) ^ (-p) =
          (T / (Ideal.absNorm d : ℝ)) ^ (1-p) := by
        nth_rewrite 1 [← Real.rpow_one (T / (Ideal.absNorm d : ℝ))]
        rw [← Real.rpow_add hu]
        congr 1 <;> ring
      calc
        _ = C * P * ((T / (Ideal.absNorm d : ℝ)) * (T / (Ideal.absNorm d : ℝ)) ^ (-p)) := by ring
        _ = _ := by rw [he]
    have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hT hY)
      (div_le_div_of_nonneg_left hT.le hn (hD d hd).2) (show 1-p ≤ 0 by linarith)
    calc
      _ = ‖a d‖ * ‖(T / (Ideal.absNorm d : ℝ) : ℂ) *
          ∑' b, ReflectedTails.dualSummand F k T d b‖ := by rw [mul_assoc, norm_mul]
      _ ≤ 1 * (C * P * Real.rpow (T / (Ideal.absNorm d : ℝ)) (1-p)) :=
        mul_le_mul (ha d hd) hip (norm_nonneg _) zero_le_one
      _ ≤ C * P * Real.rpow (T / Y) (1-p) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hP)
  calc
    _ ≤ ∑ d ∈ D, ‖a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
        ∑' b, ReflectedTails.dualSummand F k T d b‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ D, C * P * Real.rpow (T / Y) (1-p) := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem dual_cutoff_tail_all_scale (F : Type*) [Field F] [NumberField F]
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℝ → ℂ) (P : ℝ), 0 ≤ P →
      (∀ x : ℝ, 0 < x → ‖k x‖ ≤ P * Real.rpow x (-p)) →
      ∀ (T Z L : ℝ), 0 < T → 0 < Z → 1 ≤ L →
      ∀ (D : Finset (Ideal (𝓞 F))), (∀ d ∈ D, d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ Z) →
      ∀ (a : Ideal (𝓞 F) → ℂ), (∀ d ∈ D, ‖a d‖ ≤ 1) →
        ‖ReflectedTails.dualCutoffTail F k T L D a‖ ≤
          C * P * (D.card : ℝ) * Real.rpow (L * T / Z) (1-p) := by
  obtain ⟨C, hC, hb⟩ := cutoff_inner_bound F p hp
  refine ⟨C, hC, ?_⟩
  intro k P hP hk T Z L hT hZ hL D hD a ha
  have hterm : ∀ d ∈ D, ‖a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
      ∑' b, ReflectedTails.dualCutoffSummand F k T L d b‖ ≤
      C * P * Real.rpow (L * T / Z) (1-p) := by
    intro d hd
    have hn : 0 < (Ideal.absNorm d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hD d hd).1)
    have hbase : L * T / Z ≤ L * T / (Ideal.absNorm d : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hn (hD d hd).2
    have hpow := Real.rpow_le_rpow_of_nonpos (div_pos (by positivity) hZ) hbase
      (show 1-p ≤ 0 by linarith)
    calc
      _ = ‖a d‖ * ‖(T / (Ideal.absNorm d : ℝ) : ℂ) *
          ∑' b, ReflectedTails.dualCutoffSummand F k T L d b‖ := by rw [mul_assoc, norm_mul]
      _ ≤ 1 * (C * P * Real.rpow (L * T / (Ideal.absNorm d : ℝ)) (1-p)) :=
        mul_le_mul (ha d hd) (hb k P hP hk T L d hT hL (hD d hd).1)
          (norm_nonneg _) zero_le_one
      _ ≤ C * P * Real.rpow (L * T / Z) (1-p) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hP)
  calc
    _ ≤ ∑ d ∈ D, ‖a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
        ∑' b, ReflectedTails.dualCutoffSummand F k T L d b‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ D, C * P * Real.rpow (L * T / Z) (1-p) := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailAux

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailAux
open ExplicitTerms

private lemma global_power_of_two_ended (f : ℝ → ℂ) (P p : ℝ) (hp : 0 < p)
    (n : ℕ) (hn : p ≤ (n : ℝ))
    (hsmall : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖f x‖ ≤ P * Real.rpow x (-p))
    (hlarge : ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ P * Real.rpow x (-(n : ℝ)))
    (hP : 0 ≤ P) : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ P * Real.rpow x (-p) := by
  intro x hx
  rcases le_or_gt x 1 with hx1 | hx1
  · exact hsmall x hx hx1
  · exact (hlarge x hx1.le).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1.le (neg_le_neg hn)) hP)

private lemma field_global_power (D : ℝ) (r : ℕ) (f : ℝ → ℂ) (hD : 0 < D)
    (hr : 1 ≤ r) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (p : ℝ) (hp : 0 < p) : ∃ P : ℝ, 0 < P ∧ ∀ x : ℝ, 0 < x →
      ‖DedekindZetaZeroFree.LargeSieve.fieldTransform D r f x‖ ≤ P * Real.rpow x (-p) := by
  obtain ⟨P, hP, hs, hl⟩ := DedekindZetaZeroFree.LargeSieve.fieldTransform_euler_two_ended_bound
    D r f hD hr hf hc 0 ⌈p⌉₊ p hp
  refine ⟨P, hP, global_power_of_two_ended _ P p hp ⌈p⌉₊ (Nat.le_ceil p) ?_ ?_ hP.le⟩
  · simpa using hs
  · simpa using hl

private lemma reflected_global_power (D : ℝ) (r : ℕ) (f : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hf : ContDiff ℝ ∞ f)
    (hsupp : Function.support f ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b)
    (p : ℝ) (hp : 0 < p) : ∃ P : ℝ, 0 < P ∧ ∀ x : ℝ, 0 < x →
      ‖DedekindZetaZeroFree.LargeSieve.SquareSecondPass.reflectedTransform D r f x‖ ≤ P * Real.rpow x (-p) := by
  obtain ⟨P, hP, hs, hl⟩ := DedekindZetaZeroFree.LargeSieve.reflectedSquareTransform_euler_two_ended_bound
    D r f a b hD hr hf hsupp ha hab 0 ⌈p⌉₊ p hp
  refine ⟨P, hP, global_power_of_two_ended _ P p hp ⌈p⌉₊ (Nat.le_ceil p) ?_ ?_ hP.le⟩
  · simpa using hs
  · simpa using hl

private lemma compact_sq (h : ℝ → ℂ) (hc : HasCompactSupport h) :
    HasCompactSupport (fun t : ℝ => h (t ^ 2)) := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℝ) |>.mp hc.isBounded
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(|r| + 1)) (|r| + 1)) isCompact_Icc
  intro t ht
  have hmem : t ^ 2 ∈ tsupport h := subset_tsupport h ht
  have hbound : |t ^ 2| ≤ r := by
    have := hr hmem
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  have : t ^ 2 ≤ |r| := le_trans (le_abs_self _) (hbound.trans (le_abs_self _))
  constructor <;> nlinarith [sq_nonneg (t + (|r| + 1)),
    sq_nonneg (t - (|r| + 1)), abs_nonneg r]

private lemma square_power (x p : ℝ) (hx : 0 < x) :
    Real.rpow (x ^ 2) (-(p / 2)) = Real.rpow x (-p) := by
  have h : Real.rpow x 2 = x ^ (2 : ℕ) := Real.rpow_two x
  rw [← h]
  have h2 : Real.rpow x (2 * (-(p/2))) =
      Real.rpow (Real.rpow x 2) (-(p/2)) := Real.rpow_mul hx.le 2 (-(p/2))
  rw [← h2]
  congr 1
  ring

theorem kernel_power_certificates
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (W : ℝ → ℝ) (p : ℝ) (hp : 1 < p) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ C : Context Q, C.W = W →
      ∀ x : ℝ, 0 < x →
        ‖C.source (x ^ 2)‖ ≤ P * Real.rpow x (-p) ∧
        ‖C.originalKernel x‖ ≤ P * Real.rpow x (-p) ∧
        ‖SquareSecondPass.weight (principalDiscriminant F) (principalComplexPlaces F)
          C.source x‖ ≤ P * Real.rpow x (-p) ∧
        ‖C.reflectedKernel x‖ ≤ P * Real.rpow x (-p) := by
  by_cases hW : Sieve.SieveWeight W
  · by_cases hF : NumberField.IsTotallyComplex F
    · let f : ℝ → ℂ := fun x => W x
      have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hW.smooth
      have hsupp : Function.support f ⊆ Set.Icc (1/2 : ℝ) (5/2) := by
        intro x hx
        by_contra hn
        exact hx (by simp [f, hW.zero_outside x hn])
      have hfc : HasCompactSupport f :=
        HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
      have hD := principalDiscriminant_pos F
      have hr := principalComplexPlaces_pos F hF
      have hp0 : 0 < p := by linarith
      obtain ⟨P₁, hP₁⟩ := isBounded_iff_forall_norm_le.mp
        (hfc.isCompact_range hf.continuous).isBounded
      have hP₁0 : 0 ≤ P₁ := (norm_nonneg (f 0)).trans (hP₁ _ (Set.mem_range_self 0))
      let P₀ := P₁ * Real.rpow 2 p
      have hP₀0 : 0 ≤ P₀ := by dsimp [P₀]; positivity
      have hsquare : ∀ x : ℝ, 0 < x → ‖f (x ^ 2)‖ ≤ P₀ * Real.rpow x (-p) := by
        intro x hx
        by_cases hx2 : x ≤ 2
        · have hneg : Real.rpow x (-p) = (Real.rpow x p)⁻¹ := Real.rpow_neg hx.le p
          have hdiv : Real.rpow (2 / x) p = Real.rpow 2 p / Real.rpow x p :=
            Real.div_rpow (by norm_num) hx.le p
          have hpow : 1 ≤ Real.rpow 2 p * Real.rpow x (-p) := by
            rw [hneg, ← div_eq_mul_inv, ← hdiv]
            exact Real.one_le_rpow ((one_le_div hx).mpr hx2) hp0.le
          exact (hP₁ _ (Set.mem_range_self _)).trans (by
            calc
              P₁ = P₁ * 1 := (mul_one _).symm
              _ ≤ P₁ * (Real.rpow 2 p * Real.rpow x (-p)) :=
                mul_le_mul_of_nonneg_left hpow hP₁0
              _ = P₀ * Real.rpow x (-p) := by dsimp [P₀]; ring)
        · have hn : x ^ 2 ∉ Set.Icc (1/2 : ℝ) (5/2) := by
            intro h
            have := h.2
            have : 2 < x := lt_of_not_ge hx2
            nlinarith
          rw [show f (x ^ 2) = 0 by simp [f, hW.zero_outside _ hn], norm_zero]
          exact mul_nonneg hP₀0 (Real.rpow_nonneg hx.le _)
      obtain ⟨P₂, hP₂, hb₂⟩ := field_global_power _ _ (fun x => f (x ^ 2)) hD hr
        (hf.comp (contDiff_id.pow 2)) (compact_sq f hfc) p hp0
      obtain ⟨P₃, hP₃, hb₃⟩ := field_global_power _ _ f hD hr hf hfc (p/2) (by positivity)
      obtain ⟨P₄, hP₄, hb₄⟩ := reflected_global_power _ _ f (1/2) (5/2) hD hr hf hsupp
        (by norm_num) (by norm_num) p hp0
      let P := P₀ + P₂ + P₃ + P₄
      have hP : 0 ≤ P := by dsimp [P]; positivity
      refine ⟨P, hP, ?_⟩
      intro C hCW x hx
      have hsource : C.source = f := by funext t; simp [Context.source, f, hCW]
      have he₀ : P₀ ≤ P := by dsimp [P]; linarith
      have he₂ : P₂ ≤ P := by dsimp [P]; linarith
      have he₃ : P₃ ≤ P := by dsimp [P]; linarith
      have he₄ : P₄ ≤ P := by dsimp [P]; linarith
      have hpow0 := Real.rpow_nonneg hx.le (-p)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hsource]
        exact (hsquare x hx).trans (mul_le_mul_of_nonneg_right he₀ hpow0)
      · change ‖fieldTransform _ _ (fun t => C.source (t ^ 2)) x‖ ≤ _
        rw [hsource]
        exact (hb₂ x hx).trans (mul_le_mul_of_nonneg_right he₂ hpow0)
      · rw [hsource]
        have hb := hb₃ (x ^ 2) (sq_pos_of_pos hx)
        rw [square_power x p hx] at hb
        exact hb.trans (mul_le_mul_of_nonneg_right he₃ hpow0)
      · change ‖SquareSecondPass.reflectedTransform _ _ C.source x‖ ≤ _
        rw [hsource]
        exact (hb₄ x hx).trans (mul_le_mul_of_nonneg_right he₄ hpow0)
    · refine ⟨0, le_rfl, ?_⟩
      intro C _
      exact (hF C.hF).elim
  · refine ⟨0, le_rfl, ?_⟩
    intro C hCW
    exact (hW (hCW ▸ C.hW)).elim
end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailAux

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

open ExplicitTerms

def localBlockKernel {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (B : ℝ) (unit : Bool := false) : ℂ :=
  (∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        (C.primitive p hp) a *
          C.reflectedRemainder (p.1 * p.2)
            (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1) -
    ∑ a ∈ C.originalRows B unit,
      (C.primitive p hp) a *
        C.originalRemainder (c * C.d * (p.1 * p.2))
          (Real.sqrt (C.M / norm a)) (C.Y2 B) (C.Z2 B) C.L2

def localTailMajorant {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) : ℝ :=
  ‖localBlockKernel C p hp 1 true‖ +
    ∑ B ∈ dyadicScales C, ‖localBlockKernel C p hp B‖

private lemma mu_norm {F : Type} [Field F] [NumberField F] (j : Ideal (𝓞 F)) :
    ‖(UniqueFactorizationMonoid.moebius j : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree j
  · rw [Squarefree.moebius_eq h]
    push_cast
    rw [norm_pow]
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

private lemma three_tail_bound {F : Type} [Field F] [NumberField F]
    (a : ℝ) (ha : 1 < a) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (g k : ℝ → ℂ) (P : ℝ), 0 ≤ P →
      (∀ x, 0 < x → ‖g x‖ ≤ P * Real.rpow x (-a)) →
      (∀ x, 0 < x → ‖k x‖ ≤ P * Real.rpow x (-a)) →
      ∀ (j : Ideal (𝓞 F)), j ≠ ⊥ →
      ∀ (T Y Z L : ℝ), 0 < T → 0 < Y → 0 < Z → 1 ≤ L →
      ‖ReflectedTails.primalTail F g T ((idealDivisors j).filter (fun f => Z < norm f))
          (fun f => (UniqueFactorizationMonoid.moebius f : ℂ)) +
        ReflectedTails.smallDualTail F k T ((idealDivisors j).filter (fun f => norm f ≤ Y))
          (fun f => (UniqueFactorizationMonoid.moebius f : ℂ)) +
        ReflectedTails.dualCutoffTail F k T L
          ((idealDivisors j).filter (fun f => Y < norm f ∧ norm f ≤ Z))
          (fun f => (UniqueFactorizationMonoid.moebius f : ℂ))‖ ≤
      H * P * ((idealDivisors j).card : ℝ) * LocalTailAux.tailBudget a T Y Z L := by
  obtain ⟨Cg, hCg, hg⟩ := LocalTailAux.primal_tail_all_scale F a ha
  obtain ⟨Ck, hCk, hk⟩ := LocalTailAux.small_dual_tail_all_scale F a ha
  obtain ⟨Cl, hCl, hl⟩ := LocalTailAux.dual_cutoff_tail_all_scale F a ha
  refine ⟨Cg + Ck + Cl, by positivity, ?_⟩
  intro g k P hP hgp hkp j hj T Y Z L hT hY hZ hL
  have hgb := hg g P hP hgp T Z hT hZ ((idealDivisors j).filter (fun f => Z < norm f)) (fun f hf =>
    ⟨ne_bot_of_mem_idealDivisors (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩)
    _ (fun f _ => mu_norm f)
  have hkb := hk k P hP hkp T Y hT hY ((idealDivisors j).filter (fun f => norm f ≤ Y)) (fun f hf =>
    ⟨ne_bot_of_mem_idealDivisors (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩)
    _ (fun f _ => mu_norm f)
  have hlb := hl k P hP hkp T Z L hT hZ hL ((idealDivisors j).filter (fun f => Y < norm f ∧ norm f ≤ Z)) (fun f hf =>
    ⟨ne_bot_of_mem_idealDivisors (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2.2⟩)
    _ (fun f _ => mu_norm f)
  have hcard (s : Ideal (𝓞 F) → Prop) [DecidablePred s] :
      (((idealDivisors j).filter s).card : ℝ) ≤ ((idealDivisors j).card : ℝ) := by
    exact_mod_cast Finset.card_filter_le (idealDivisors j) s
  have hbud : ∀ x : ℝ, 0 < x → ∀ q : ℝ, 0 ≤ Real.rpow x q :=
    fun x hx q => Real.rpow_nonneg hx.le q
  have hg' := hgb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hcard _) (mul_nonneg hCg hP))
    (hbud (Z/T) (div_pos hZ hT) (-a)))
  have hk' := hkb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hcard _) (mul_nonneg hCk hP))
    (hbud (T/Y) (div_pos hT hY) (1-a)))
  have hl' := hlb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hcard _) (mul_nonneg hCl hP))
    (hbud (L*T/Z) (div_pos (mul_pos (zero_lt_one.trans_le hL) hT) hZ) (1-a)))
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hg' hk') hl').trans ?_)
  unfold LocalTailAux.tailBudget
  have h1 := hbud (Z/T) (div_pos hZ hT) (-a)
  have h2 := hbud (T/Y) (div_pos hT hY) (1-a)
  have h3 := hbud (L*T/Z) (div_pos (mul_pos (zero_lt_one.trans_le hL) hT) hZ) (1-a)
  have hm : 0 ≤ P * ((idealDivisors j).card : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hCg hm) h2, mul_nonneg (mul_nonneg hCg hm) h3,
    mul_nonneg (mul_nonneg hCk hm) h1, mul_nonneg (mul_nonneg hCk hm) h3,
    mul_nonneg (mul_nonneg hCl hm) h1, mul_nonneg (mul_nonneg hCl hm) h2]

private lemma norm_pos {F : Type} [Field F] [NumberField F] {j : Ideal (𝓞 F)}
    (hj : j ≠ ⊥) : 0 < norm j := by
  unfold ExplicitTerms.norm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hj)

private lemma original_row_pos {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (B : ℝ) (unit : Bool) {r : Ideal (𝓞 F)}
    (hr : r ∈ C.originalRows B unit) : 0 < norm r := by
  cases unit
  · have hs := ((Sieve.mem_paperShell F (c * C.d) B r).mp (Finset.mem_filter.mp hr).1).1
    exact norm_pos hs.ne_zero
  · have he : r = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp hr).1
    simp [he, ExplicitTerms.norm]

private lemma reflected_row_pos {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (B : ℝ) (unit : Bool) {r : Ideal (𝓞 F)}
    (hr : r ∈ C.reflectedRows B unit) : 0 < norm r := by
  obtain ⟨tr, ht, rfl⟩ := Finset.mem_image.mp hr
  exact norm_pos (Finset.mem_filter.mp ht).2.2.2

private lemma thresholds_pos {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ)
    (B : ℝ) (hB : 0 < B) :
    (0 < C.Y2 B ∧ 0 < C.Z2 B ∧ 1 ≤ C.L2) ∧
    ∀ e ∈ C.mobiusDivisors, 0 < C.Y1 B e ∧ 0 < C.Z1 B e := by
  have hd := norm_pos C.hd0
  have hM0 : 0 < C.M := zero_lt_one.trans_le hM
  have hN0 : 0 < C.N := zero_lt_one.trans_le hN
  have hMN : 1 ≤ C.M * C.N := one_le_mul_of_one_le_of_one_le hM hN
  have hL : 1 ≤ C.L2 := by
    have hp := Real.one_le_rpow hMN (show 0 ≤ 2 * C.δ by positivity)
    unfold Context.L2 Context.L1
    simp only [Real.rpow_eq_pow]
    linarith
  refine ⟨⟨?_, ?_, hL⟩, ?_⟩
  · unfold Context.Y2
    simp only [Real.rpow_eq_pow]
    positivity
  · unfold Context.Z2
    simp only [Real.rpow_eq_pow]
    positivity
  · intro e he
    have he0 := norm_pos (ne_bot_of_mem_idealDivisors he)
    constructor
    · unfold Context.Y1
      simp only [Real.rpow_eq_pow]
      positivity
    · unfold Context.Z1
      simp only [Real.rpow_eq_pow]
      positivity

private lemma local_block_budget {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (W : ℝ → ℝ) (a : ℝ) (ha : 1 < a) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ C : Context Q, C.W = W →
      1 ≤ C.M → 1 ≤ C.N → 0 < C.δ →
      ∀ (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
        (B : ℝ) (unit : Bool), 0 < B →
        ‖localBlockKernel C p hp B unit‖ ≤ J * LocalTailAux.blockBudget C a p hp B unit := by
  obtain ⟨H, hH, ht⟩ := three_tail_bound (F := F) a ha
  obtain ⟨P, hP, hcert⟩ := LocalTailAux.kernel_power_certificates (Q := Q) W a ha
  refine ⟨H * P, mul_nonneg hH hP, ?_⟩
  intro C hW hM hN hδ p hp B unit hB
  have hthr := thresholds_pos C hM hN hδ B hB
  have hpc : p.1 * p.2 ≠ ⊥ := mul_ne_zero hp.hu0 hp.hv0
  have hc0 : c ≠ ⊥ := C.D.original_ne_bot
  have hj : (c * C.d) * (p.1 * p.2) ≠ ⊥ := mul_ne_zero (mul_ne_zero hc0 C.hd0) hpc
  have horig (r : Ideal (𝓞 F)) (hr : r ∈ C.originalRows B unit) :
      ‖C.originalRemainder ((c * C.d) * (p.1 * p.2)) (Real.sqrt (C.M / norm r))
        (C.Y2 B) (C.Z2 B) C.L2‖ ≤
      H * P * ((idealDivisors ((c * C.d) * (p.1 * p.2))).card : ℝ) *
        LocalTailAux.tailBudget a (Real.sqrt (C.M / norm r)) (C.Y2 B) (C.Z2 B) C.L2 := by
    exact ht _ _ P hP (fun x hx => (hcert C hW x hx).1)
      (fun x hx => (hcert C hW x hx).2.1) _ hj _ _ _ _
      (Real.sqrt_pos.mpr (div_pos (zero_lt_one.trans_le hM) (original_row_pos C B unit hr)))
      hthr.1.1 hthr.1.2.1 hthr.1.2.2
  have href (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
      (r : Ideal (𝓞 F)) (hr : r ∈ C.reflectedRows B unit) :
      ‖C.reflectedRemainder (p.1 * p.2) (Real.sqrt (C.dualScale e p / norm r))
        (C.Y1 B e) (C.Z1 B e) C.L1‖ ≤
      H * P * ((idealDivisors (p.1 * p.2)).card : ℝ) *
        LocalTailAux.tailBudget a (Real.sqrt (C.dualScale e p / norm r)) (C.Y1 B e) (C.Z1 B e) C.L1 := by
    have hs : 0 < C.dualScale e p := by
      unfold Context.dualScale
      exact div_pos (mul_pos (norm_pos (ne_bot_of_mem_idealDivisors he)) (norm_pos hpc))
        (zero_lt_one.trans_le hM)
    have h := ht _ _ P hP (fun x hx => (hcert C hW x hx).2.2.1)
      (fun x hx => (hcert C hW x hx).2.2.2) _ hpc _ _ _ _
      (Real.sqrt_pos.mpr (div_pos hs (reflected_row_pos C B unit hr)))
      (hthr.2 e he).1 (hthr.2 e he).2 hthr.1.2.2
    convert h using 1 <;> simp only [Context.reflectedRemainder, ReflectedCoprimeTruncation.remainder,
      ReflectedTails.dualCutoffTail, ReflectedTails.dualCutoffSummand, Context.reflectedKernel,
      ExplicitTerms.norm, Complex.ofReal_div, Complex.ofReal_natCast, Context.L2]
    rfl
  have hchar (r : Ideal (𝓞 F)) : ‖C.primitive p hp r‖ ≤ 1 := RayOperations.norm_le_one _ _
  have hrbound :
      ‖∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
        ∑ r ∈ C.reflectedRows B unit, C.primitive p hp r *
          C.reflectedRemainder (p.1*p.2) (Real.sqrt (C.dualScale e p / norm r))
            (C.Y1 B e) (C.Z1 B e) C.L1‖ ≤
      H * P * (∑ e ∈ C.mobiusDivisors, ‖C.prefactor e p hp‖ *
        ∑ r ∈ C.reflectedRows B unit, ((idealDivisors (p.1*p.2)).card : ℝ) *
          LocalTailAux.tailBudget a (Real.sqrt (C.dualScale e p / norm r))
            (C.Y1 B e) (C.Z1 B e) C.L1) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he => ?_)
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [norm_mul]
    have hb := mul_le_mul (hchar r) (href e he r hr) (norm_nonneg _) zero_le_one
    simp only [one_mul] at hb
    have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (C.prefactor e p hp))
    convert hh using 1 <;> ring
  have hobound :
      ‖∑ r ∈ C.originalRows B unit, C.primitive p hp r *
        C.originalRemainder ((c*C.d)*(p.1*p.2)) (Real.sqrt (C.M / norm r))
          (C.Y2 B) (C.Z2 B) C.L2‖ ≤
      H * P * (∑ r ∈ C.originalRows B unit,
        ((idealDivisors ((c*C.d)*(p.1*p.2))).card : ℝ) *
          LocalTailAux.tailBudget a (Real.sqrt (C.M / norm r)) (C.Y2 B) (C.Z2 B) C.L2) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    rw [norm_mul]
    have hh := mul_le_mul (hchar r) (horig r hr) (norm_nonneg _) zero_le_one
    simpa only [one_mul, mul_assoc] using hh
  exact (norm_sub_le _ _).trans ((add_le_add hrbound hobound).trans_eq (by
    unfold LocalTailAux.blockBudget
    ring))

theorem uniform_local_tail_pair
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (hδε : δ ≤ ε / 100) :
    ∃ B, 0 ≤ B ∧
      ∀ C : Context Q, C.D = D → C.W = W → C.δ = δ →
        1 ≤ C.M → 1 ≤ C.N →
        max 1 (C.N ^ 2 / C.M * Real.rpow (C.M * C.N) ε) ≤ C.K →
        C.K ≤ C.M * Real.rpow (C.M * C.N) (-ε) →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ∀ (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p),
          p ∈ C.pairs → localTailMajorant C p hp ≤ B * Real.rpow (C.M * C.N) (-2) := by
  let a : ℝ := 1 + (12 + 4 * δ) / δ
  have ha : 1 < a := by
    dsimp [a]
    have : 0 < (12 + 4 * δ) / δ := div_pos (by positivity) hδ
    linarith
  have hexp : 10 + 4 * δ - δ * (a-1) = -2 := by
    dsimp [a]
    field_simp
    <;> ring
  obtain ⟨J, hJ, hblock⟩ := local_block_budget (Q := Q) W a ha
  obtain ⟨G, hG, hgeom⟩ := LocalTailAux.geometric_pair_budget D ε hε δ hδ hδε a ha
  refine ⟨J * G, mul_nonneg hJ hG, ?_⟩
  intro C hD hW heδ hM hN hKlo hKhi hd1 hd2 p hp hpair
  have hcδ : 0 < C.δ := by rw [heδ]; exact hδ
  have hmajor : localTailMajorant C p hp ≤ J * LocalTailAux.pairBudget C a p hp := by
    unfold localTailMajorant LocalTailAux.pairBudget
    rw [mul_add, Finset.mul_sum]
    refine add_le_add (hblock C hW hM hN hcδ p hp 1 true (by norm_num))
      (Finset.sum_le_sum fun B hB => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
    exact hblock C hW hM hN hcδ p hp _ false (pow_pos (by norm_num) _)
  have hg := hgeom C hD heδ hM hN hKlo hKhi hd1 hd2 p hp hpair
  rw [hexp] at hg
  exact hmajor.trans ((mul_le_mul_of_nonneg_left hg hJ).trans_eq (by ring))

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

open ExplicitTerms

section FiniteAlgebra
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private theorem R_pairSum (C : Context Q) (B : ℝ) (unit : Bool) :
    R C B unit = C.pairSum (fun p hp => C.coefficient p * localBlockKernel C p hp B unit) := by
  unfold R Context.pairSum localBlockKernel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp [mul_sub]

private theorem pairSum_norm_le (C : Context Q)
    (f : (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ) :
    ‖C.pairSum f‖ ≤ ∑ p ∈ C.pairs, if hp : C.ValidPair p then ‖f p hp‖ else 0 := by
  unfold Context.pairSum
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

private theorem R_norm_le (C : Context Q) (B : ℝ) (unit : Bool) :
    ‖R C B unit‖ ≤ ∑ p ∈ C.pairs,
      if hp : C.ValidPair p then
        ‖C.coefficient p‖ * ‖localBlockKernel C p hp B unit‖ else 0 := by
  rw [R_pairSum]
  simpa only [norm_mul] using pairSum_norm_le C
    (fun p hp => C.coefficient p * localBlockKernel C p hp B unit)

private theorem total_norm_le (C : Context Q) :
    ‖totalRemainder C‖ ≤ ∑ p ∈ C.pairs,
      if hp : C.ValidPair p then ‖C.coefficient p‖ *
        (‖primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2
            (C.primitive p hp)‖ + localTailMajorant C p hp) else 0 := by
  have hcut := pairSum_norm_le C (fun p hp => C.coefficient p *
    primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2 (C.primitive p hp))
  simp only [norm_mul] at hcut
  have hloc := R_norm_le C 1 true
  have hsum := Finset.sum_le_sum (fun B (_ : B ∈ dyadicScales C) => R_norm_le C B false)
  unfold totalRemainder
  calc
    ‖cutoffRemainder C + R C 1 true + ∑ B ∈ dyadicScales C, R C B‖ ≤
      ‖cutoffRemainder C‖ + ‖R C 1 true‖ + ∑ B ∈ dyadicScales C, ‖R C B‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_sum_le _ _))
    _ ≤ _ := add_le_add (add_le_add hcut hloc) hsum
    _ = _ := by
      rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hv : C.ValidPair p
      · simp only [dif_pos hv, localTailMajorant, mul_add, Finset.mul_sum, add_assoc]
      · simp only [dif_neg hv, Finset.sum_const_zero, add_zero]

end FiniteAlgebra

theorem uniform_remainder_small_delta
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (hδε : δ ≤ ε / 100) :
    ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D → C.W = W → C.δ = δ →
        1 ≤ C.M → 1 ≤ C.N →
        max 1 (C.N ^ 2 / C.M * Real.rpow (C.M * C.N) ε) ≤ C.K →
        C.K ≤ C.M * Real.rpow (C.M * C.N) (-ε) →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ‖totalRemainder C‖ ≤ A * Sieve.energy F c C.N C.lam := by
  obtain ⟨Bc, hBc, hcut⟩ := cutoff_pair_decay D W ε hε
  obtain ⟨Bl, hBl, hloc⟩ := uniform_local_tail_pair D W ε hε δ hδ hδε
  obtain ⟨H, hH, hpair⟩ := finite_pair_energy_bound F
  let A := (Bc + Bl) * H + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro C hD hW hdelta hM hN hK hKup hd hdN
  have hKlo : C.N ^ 2 / C.M * Real.rpow (C.M * C.N) ε ≤ C.K :=
    (le_max_right _ _).trans hK
  have hS : 1 ≤ C.M * C.N := one_le_mul_of_one_le_of_one_le hM hN
  have hSpos : 0 < C.M * C.N := by linarith
  have hSN : C.N ≤ C.M * C.N := by nlinarith
  have hpower : Real.rpow (C.M * C.N) (-2) * C.N ≤ 1 := by
    have hpow : Real.rpow (C.M * C.N) (-2) = ((C.M * C.N) ^ 2)⁻¹ :=
      (Real.rpow_neg hSpos.le (2 : ℝ)).trans
        (congrArg Inv.inv (Real.rpow_two (C.M * C.N)))
    rw [hpow]
    apply (inv_mul_le_iff₀ (pow_pos hSpos 2)).mpr
    nlinarith
  have henergy : 0 ≤ Sieve.energy F c C.N C.lam := by
    unfold Sieve.energy; positivity
  have hB : 0 ≤ Bc + Bl := add_nonneg hBc hBl
  have hpow0 : 0 ≤ Real.rpow (C.M * C.N) (-2) := Real.rpow_nonneg hSpos.le _
  calc
    ‖totalRemainder C‖ ≤ ∑ p ∈ C.pairs,
        if hp : C.ValidPair p then ‖C.coefficient p‖ *
          (‖primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2
              (C.primitive p hp)‖ + localTailMajorant C p hp) else 0 := total_norm_le C
    _ ≤ ∑ p ∈ C.pairs, ‖C.coefficient p‖ *
        ((Bc + Bl) * Real.rpow (C.M * C.N) (-2)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hv : C.ValidPair p := (Finset.mem_filter.mp hp).2
      rw [dif_pos hv]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [add_mul] using add_le_add
        (hcut C hD hW hM hN hKlo hd hdN p hv hp)
        (hloc C hD hW hdelta hM hN hK hKup hd hdN p hv hp)
    _ = ((Bc + Bl) * Real.rpow (C.M * C.N) (-2)) *
        (∑ p ∈ C.pairs, ‖C.coefficient p‖) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
    _ ≤ ((Bc + Bl) * Real.rpow (C.M * C.N) (-2)) *
        (H * C.N * Sieve.energy F c C.N C.lam) :=
      mul_le_mul_of_nonneg_left (hpair C hN hd) (mul_nonneg hB hpow0)
    _ = ((Bc + Bl) * H * Sieve.energy F c C.N C.lam) *
        (Real.rpow (C.M * C.N) (-2) * C.N) := by ring
    _ ≤ ((Bc + Bl) * H * Sieve.energy F c C.N C.lam) * 1 :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ ≤ A * Sieve.energy F c C.N C.lam := by
      dsimp [A]; nlinarith

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end
