module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.StandardIntegralAndLevelContinuation

@[expose] public section

section
noncomputable section

namespace DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps.Augmentation

open ValuativeRel KPLocalPrincipalSeries KPRankOneShellContinuation KPRankOneRootParameter

private theorem chamber_evaluation_infinite
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ε : Sign) :
    {u : ℂˣ | ∃ s : ℂ, convergenceHalfPlane ε s ∧ evaluationUnit K ε s = u}.Infinite := by
  let a : ℕ → ℝ := fun n => if ε = .plus then (n : ℝ) else -(n : ℝ) - 1
  have ha : Function.Injective a := by
    intro m n h
    dsimp [a] at h
    cases ε <;> simp only [if_true, if_false, reduceCtorEq] at h
    · exact_mod_cast h
    · have : (m : ℝ) = (n : ℝ) := by linarith
      exact_mod_cast this
  have hl : Real.log (residueCardinality K : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast Finite.one_lt_card (α := 𝓀[K])
  have hn (x : ℝ) : ‖(evaluationUnit K ε (x : ℂ) : ℂ)‖ =
      Real.exp ((if ε = .plus then -x else x) * Real.log (residueCardinality K : ℝ)) := by
    cases ε with
    | plus =>
      change ‖r K (x : ℂ)‖ = _
      simp only [r, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
        Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero, if_true]
    | minus =>
      change ‖(r K (x : ℂ))⁻¹‖ = _
      simp only [r, norm_inv, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
        Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero,
        ← Real.exp_neg, neg_mul, neg_neg, reduceCtorEq, if_false]
  have hinj : Function.Injective (fun n => evaluationUnit K ε (a n : ℂ)) := by
    intro m n h
    apply ha
    have he := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) h
    rw [hn, hn] at he
    have he' := (mul_left_inj' hl).mp (Real.exp_injective he)
    cases ε <;> simpa using he'
  apply (Set.infinite_range_of_injective hinj).mono
  rintro u ⟨n, rfl⟩
  refine ⟨(a n : ℂ), ?_, rfl⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  cases ε <;> simp only [a, convergenceHalfPlane, if_true, if_false,
    reduceCtorEq, Complex.ofReal_re] <;> linarith

 def scalarLaurent (Q : ℤ →₀ ℂ) : LaurentPolynomial ℂ :=
  Q.sum (fun n c => LaurentPolynomial.C c * LaurentPolynomial.T n)

private theorem scalarLaurent_coeff (Q : ℤ →₀ ℂ) (n : ℤ) :
    (scalarLaurent Q).coeff n = Q n := by
  classical
  simp only [scalarLaurent, ← LaurentPolynomial.single_eq_C_mul_T,
    Finsupp.sum, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply,
    AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    simp [hbn]
  · intro hn
    simp [Finsupp.notMem_support_iff.mp hn]

private theorem scalarLaurent_eval (Q : ℤ →₀ ℂ) (u : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) u (scalarLaurent Q) =
      Q.sum (fun n c => (u : ℂ) ^ n * c) := by
  classical
  simp only [scalarLaurent, Finsupp.sum, map_sum,
    LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, Units.val_zpow_eq_zpow_val]
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _

theorem scalar_laurent_chamber_unique
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ε : Sign) (Q R : ℤ →₀ ℂ)
    (hQR : ∀ s : ℂ, convergenceHalfPlane ε s →
      Q.sum (fun n c => (evaluationUnit K ε s : ℂ) ^ n * c) =
        R.sum (fun n c => (evaluationUnit K ε s : ℂ) ^ n * c)) :
    Q = R := by
  let p : LaurentPolynomial ℂ := scalarLaurent Q - scalarLaurent R
  have hp : ∀ u ∈ {u : ℂˣ | ∃ s : ℂ,
      convergenceHalfPlane ε s ∧ evaluationUnit K ε s = u},
      LaurentPolynomial.eval₂ (RingHom.id ℂ) u p = 0 := by
    rintro u ⟨s, hs, rfl⟩
    simp only [p, map_sub, sub_eq_zero]
    simpa only [scalarLaurent_eval] using hQR s hs
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
  have hroots : {x : ℂ | f.eval x = (0 : Polynomial ℂ).eval x}.Infinite := by
    apply ((chamber_evaluation_infinite K ε).image
      (f := fun u : ℂˣ => (u : ℂ)) Units.val_injective.injOn).mono
    rintro x ⟨u, hu, rfl⟩
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ) u) hf
    simp only [map_mul, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
      hp u hu, zero_mul, Polynomial.eval_zero] at he ⊢
    exact he
  have hz := Polynomial.eq_of_infinite_eval_eq f 0 hroots
  rw [hz, map_zero] at hf
  have hpzero : p = 0 :=
    (IsUnit.mul_left_inj (LaurentPolynomial.isUnit_T (R := ℂ) (n : ℤ))).mp
      (by simpa using hf.symm)
  have hpoly : scalarLaurent Q = scalarLaurent R := sub_eq_zero.mp hpzero
  apply Finsupp.ext
  intro n
  have he := congrArg (fun L : LaurentPolynomial ℂ => L.coeff n) hpoly
  simpa only [scalarLaurent_coeff] using he

end DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps.Augmentation

end

end
