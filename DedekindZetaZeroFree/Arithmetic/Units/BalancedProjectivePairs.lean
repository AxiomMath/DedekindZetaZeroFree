module

public import DedekindZetaZeroFree.Eisenstein.Induction.PGLAdelicRowHeight

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPChamberUnitBalancedPairs

open NumberField NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

variable (F : Type) [Field F] [NumberField F]

theorem archimedean_balance :
    ∃ C : ℝ, 0 < C ∧ ∀ a : InfinitePlace F → ℝ,
      (∀ v, 0 < a v) → ∃ u : (RingOfIntegers F)ˣ,
        ∀ v, v (u : RingOfIntegers F) * a v ≤
          C * (∏ w, a w ^ w.mult) ^ (1 / (Module.finrank ℚ F : ℝ)) := by
  classical
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (isBounded_normLeOne F)
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro a ha
  let x := mixedSpaceOfRealSpace a
  have hxv (v : InfinitePlace F) : normAtPlace v x = a v :=
    normAtPlace_mixedSpaceOfRealSpace (ha v).le
  have hx : 0 < mixedEmbedding.norm x := by
    rw [mixedEmbedding.norm_apply]
    exact Finset.prod_pos fun v _ => pow_pos (by rw [hxv]; exact ha v) _
  let t : ℝ := (mixedEmbedding.norm x) ^ (1 / (Module.finrank ℚ F : ℝ))
  have ht : 0 < t := Real.rpow_pos_of_pos hx _
  have htp : t ^ Module.finrank ℚ F = mixedEmbedding.norm x := by
    dsimp [t]
    rw [one_div]
    exact Real.rpow_inv_natCast_pow hx.le (show Module.finrank ℚ F ≠ 0 from (Module.finrank_pos (R := ℚ) (M := F)).ne')
  have hy : mixedEmbedding.norm (t⁻¹ • x) = 1 := by
    rw [mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr ht), inv_pow, htp,
      inv_mul_cancel₀ hx.ne']
  obtain ⟨u, hu⟩ := exists_unit_smul_mem (hy ▸ one_ne_zero)
  refine ⟨u, ?_⟩
  have humem : u • (t⁻¹ • x) ∈ normLeOne F :=
    mem_normLeOne.mpr ⟨hu, by rw [norm_unit_smul, hy]⟩
  intro v
  have hvle : normAtPlace v (u • (t⁻¹ • x)) ≤ max C 1 := by
    apply le_trans _ ((hC _ humem).trans (le_max_left _ _))
    rw [norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w => normAtPlace w (u • (t⁻¹ • x))) (Finset.mem_univ v)
  rw [unitSMul_smul, map_mul, normAtPlace_apply, normAtPlace_smul,
    abs_of_pos (inv_pos.mpr ht), hxv] at hvle
  have hv := (mul_le_mul_of_nonneg_left hvle ht.le)
  have eqt : t = (∏ w, a w ^ w.mult) ^ (1 / (Module.finrank ℚ F : ℝ)) := by
    simp only [t, mixedEmbedding.norm_apply, hxv]
  rw [← eqt]
  convert hv using 1 <;> field_simp <;> ring

private theorem row_isup (v : AbsoluteValue F ℝ) (r : Fin 2 → F) :
    (⨆ i, v (r i)) = max (v (r 0)) (v (r 1)) := by
  apply eq_of_forall_ge_iff
  intro x
  simp [ciSup_le_iff (show BddAbove (Set.range (fun i => v (r i))) from Set.finite_range _ |>.bddAbove), Fin.forall_fin_two]

theorem row_archimedean_product (r : Fin 2 → RingOfIntegers F)
    (hr : (fun i => (r i : F)) ≠ 0) :
    (∏ v : InfinitePlace F, (max (v (r 0 : F)) (v (r 1 : F))) ^ v.mult) =
      (Ideal.span (Set.range r)).absNorm *
        Projectivization.mulHeight (Projectivization.mk F (fun i => (r i : F)) hr) := by
  classical
  have hr' : r ≠ 0 := by intro h; apply hr; ext i; simp [h]
  have hN := absNorm_mul_finprod_finitePlace_eq_one hr'
  rw [Projectivization.mulHeight_mk, NumberField.mulHeight_eq hr, ← mul_assoc,
    mul_comm ((Ideal.span (Set.range r)).absNorm : ℝ)]
  have hisup (v : InfinitePlace F) : (⨆ i, v (r i : F)) = max (v (r 0 : F)) (v (r 1 : F)) := row_isup F v.val _
  simp_rw [hisup]
  rw [mul_assoc, hN, mul_one]

theorem exists_unit_balanced_row :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : Fin 2 → RingOfIntegers F)
      (hr : (fun i => (r i : F)) ≠ 0),
      ∃ u : (RingOfIntegers F)ˣ, ∀ σ : F →+* ℂ,
        max ‖σ (((u : RingOfIntegers F) * r 0 : RingOfIntegers F) : F)‖
            ‖σ (((u : RingOfIntegers F) * r 1 : RingOfIntegers F) : F)‖ ≤
          C * ((Ideal.span (Set.range r)).absNorm *
            Projectivization.mulHeight (Projectivization.mk F (fun i => (r i : F)) hr)) ^
              (1 / (Module.finrank ℚ F : ℝ)) := by
  classical
  obtain ⟨C, hC, hb⟩ := archimedean_balance F
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hp (v : InfinitePlace F) : 0 < max (v (r 0 : F)) (v (r 1 : F)) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hr
    have hi' : 0 < v (r i : F) := (v.pos_iff).mpr hi
    have he : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases he with rfl | rfl
    · exact hi'.trans_le (le_max_left _ _)
    · exact hi'.trans_le (le_max_right _ _)
  obtain ⟨u, hu⟩ := hb (fun v => max (v (r 0 : F)) (v (r 1 : F))) hp
  refine ⟨u, ?_⟩
  intro σ
  have hv := hu (InfinitePlace.mk σ)
  rw [row_archimedean_product F r hr] at hv
  change ‖σ (u : RingOfIntegers F)‖ * max ‖σ (r 0 : F)‖ ‖σ (r 1 : F)‖ ≤ _ at hv
  simpa [map_mul, norm_mul, ← mul_max_of_nonneg _ _ (norm_nonneg (σ (u : RingOfIntegers F))),
    RingOfIntegers.coe_eq_algebraMap] using hv

theorem integral_representative (ℓ : KPChamberHeight.Line F) :
    ∃ (r : Fin 2 → RingOfIntegers F) (hr : (fun i => (r i : F)) ≠ 0),
      Projectivization.mk F (fun i => (r i : F)) hr = ℓ := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (RingOfIntegers F)) ℓ.rep
  choose r h using hb
  have hb0 : (b : RingOfIntegers F) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.prop
  have hbF : ((b : RingOfIntegers F) : F) ≠ 0 := by exact_mod_cast hb0
  have he : (fun i => (r i : F)) = ((b : RingOfIntegers F) : F) • ℓ.rep := by
    ext i; simpa [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap] using h i
  have hr : (fun i => (r i : F)) ≠ 0 := by
    rw [he]; exact smul_ne_zero hbF ℓ.rep_nonzero
  refine ⟨r, hr, ?_⟩
  rw [← ℓ.mk_rep, Projectivization.mk_eq_mk_iff']
  exact ⟨((b : RingOfIntegers F) : F), he.symm⟩

private theorem span_mul_range (a : RingOfIntegers F) (r : Fin 2 → RingOfIntegers F) :
    Ideal.span {a} * Ideal.span (Set.range r) = Ideal.span (Set.range (fun i => a * r i)) := by
  rw [Ideal.span_mul_span]
  congr 1
  ext z
  simp only [Set.mem_mul, Set.mem_singleton_iff, Set.mem_range, exists_eq_left]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨r i, ⟨i, rfl⟩, rfl⟩

theorem ideal_representative
    (J : ClassGroup (RingOfIntegers F) → (Ideal (RingOfIntegers F))⁰)
    (hJ : ∀ j, ClassGroup.mk0 (J j) = j)
    (ℓ : KPChamberHeight.Line F) :
    ∃ (j : ClassGroup (RingOfIntegers F)) (r : Fin 2 → RingOfIntegers F)
      (hr : (fun i => (r i : F)) ≠ 0),
      Projectivization.mk F (fun i => (r i : F)) hr = ℓ ∧
        Ideal.span (Set.range r) = (J j : Ideal (RingOfIntegers F)) := by
  classical
  obtain ⟨r, hr, hℓ⟩ := integral_representative F ℓ
  have hI : Ideal.span (Set.range r) ≠ ⊥ := by
    intro h
    apply hr
    ext i
    have hi := Ideal.mem_span_range_self (f := r) (x := i)
    rw [h, Ideal.mem_bot] at hi
    simp [hi]
  let I : (Ideal (RingOfIntegers F))⁰ :=
    ⟨Ideal.span (Set.range r), mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let j := ClassGroup.mk0 I
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp (hJ j).symm
  have hm (i : Fin 2) : x * r i ∈ Ideal.span {y} * (J j : Ideal (RingOfIntegers F)) := by
    rw [← hxy]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (Ideal.mem_span_range_self (f := r))
  have hd (i : Fin 2) : y ∣ x * r i := by
    apply Ideal.mem_span_singleton.mp
    exact (Ideal.mul_le_left : Ideal.span {y} * (J j : Ideal (RingOfIntegers F)) ≤ _) (hm i)
  choose s hs using hd
  have he : (fun i => y * s i : Fin 2 → RingOfIntegers F) = (fun i => x * r i) := funext fun i => (hs i).symm
  have hspan : Ideal.span (Set.range s) = (J j : Ideal (RingOfIntegers F)) := by
    have he' : Ideal.span {y} * Ideal.span (Set.range s) =
        Ideal.span {y} * (J j : Ideal (RingOfIntegers F)) := by
      rw [span_mul_range F, he, ← span_mul_range F]
      exact hxy
    exact mul_left_cancel₀ (by simpa [Ideal.span_singleton_eq_bot] using hy) he'
  have hxF : (x : F) ≠ 0 := by exact_mod_cast hx
  have hyF : (y : F) ≠ 0 := by exact_mod_cast hy
  have heF : (fun i => (s i : F)) = ((x : F) / (y : F)) • (fun i => (r i : F)) := by
    ext i
    have hh : (y : F) * (s i : F) = (x : F) * (r i : F) := by exact_mod_cast congrFun he i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    simpa [mul_comm] using hh
  have hs0 : (fun i => (s i : F)) ≠ 0 := by
    rw [heF]; exact smul_ne_zero (div_ne_zero hxF hyF) hr
  refine ⟨j, s, hs0, ?_, hspan⟩
  rw [← hℓ, Projectivization.mk_eq_mk_iff']
  exact ⟨(x : F) / (y : F), heF.symm⟩

theorem exists_unit_balanced_pair
    (J : ClassGroup (RingOfIntegers F) → (Ideal (RingOfIntegers F))⁰)
    (hJ : ∀ j, ClassGroup.mk0 (J j) = j) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ (B : ℝ), 1 ≤ B → ∀ ℓ : KPChamberHeight.Line F,
        Projectivization.mulHeight ℓ ≤ B →
        ∃ (j : ClassGroup (RingOfIntegers F))
          (r : Fin 2 → RingOfIntegers F)
          (hr : (fun i => (r i : F)) ≠ 0),
          Projectivization.mk F (fun i => (r i : F)) hr = ℓ ∧
          Ideal.span (Set.range r) = (J j : Ideal (RingOfIntegers F)) ∧
          ∀ σ : F →+* ℂ,
            max ‖σ (r 0 : F)‖ ‖σ (r 1 : F)‖ ≤
              C_F * B ^ (1 / (Module.finrank ℚ F : ℝ)) := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_unit_balanced_row F
  let N : ℝ := 1 + ∑ j, ((J j : Ideal (RingOfIntegers F)).absNorm : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    positivity
  let e : ℝ := 1 / (Module.finrank ℚ F : ℝ)
  have he : 0 ≤ e := by dsimp [e]; positivity
  refine ⟨C * N ^ e, mul_pos hC (Real.rpow_pos_of_pos hN _), ?_⟩
  intro B hB ℓ hH
  obtain ⟨j, r, hr, hℓ, hJr⟩ := ideal_representative F J hJ ℓ
  obtain ⟨u, hu⟩ := hb r hr
  let s : Fin 2 → RingOfIntegers F := fun i => (u : RingOfIntegers F) * r i
  have huF : ((u : RingOfIntegers F) : F) ≠ 0 := by
    exact_mod_cast u.ne_zero
  have hs : (fun i => (s i : F)) = ((u : RingOfIntegers F) : F) • (fun i => (r i : F)) := by
    ext i
    simp [s, Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap]
  have hs0 : (fun i => (s i : F)) ≠ 0 := by
    rw [hs]
    exact smul_ne_zero huF hr
  refine ⟨j, s, hs0, ?_, ?_, ?_⟩
  · rw [← hℓ, Projectivization.mk_eq_mk_iff']
    exact ⟨((u : RingOfIntegers F) : F), hs.symm⟩
  · rw [show s = (fun i => (u : RingOfIntegers F) * r i) from rfl,
      ← span_mul_range F, Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.top_mul, hJr]
  · intro σ
    have hNj : ((J j : Ideal (RingOfIntegers F)).absNorm : ℝ) ≤ N := by
      have hsum := Finset.single_le_sum
        (fun k (_ : k ∈ (Finset.univ : Finset (ClassGroup (RingOfIntegers F)))) =>
          (show 0 ≤ ((J k : Ideal (RingOfIntegers F)).absNorm : ℝ) by positivity))
        (Finset.mem_univ j)
      exact hsum.trans (by dsimp [N]; linarith)
    have hH0 : 0 ≤ Projectivization.mulHeight ℓ :=
      (Projectivization.mulHeight_pos ℓ).le
    have hn0 : 0 ≤ ((J j : Ideal (RingOfIntegers F)).absNorm : ℝ) := by positivity
    have hbound : ((J j : Ideal (RingOfIntegers F)).absNorm : ℝ) *
        Projectivization.mulHeight ℓ ≤ N * B :=
      mul_le_mul hNj hH hH0 hN.le
    have hv := hu σ
    rw [hJr, hℓ] at hv
    refine hv.trans ?_
    change C * (((J j : Ideal (RingOfIntegers F)).absNorm : ℝ) *
      Projectivization.mulHeight ℓ) ^ e ≤ (C * N ^ e) * B ^ e
    rw [mul_assoc, ← Real.mul_rpow hN.le (by linarith)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hn0 hH0) hbound he) hC.le

end DedekindZetaZeroFree.KPChamberUnitBalancedPairs

end
