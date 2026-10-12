module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CompactCharacterRightDerivatives

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.Casimir

open scoped Matrix.Norms.L2Operator

noncomputable def chebPair : ℕ → (ℂ → ℂ) × (ℂ → ℂ)
  | 0 => (fun _ => 1, fun _ => 1)
  | n + 1 =>
    (fun z => z * (chebPair n).2 z - (chebPair n).1 z,
     fun z => (z * (chebPair n).2 z - (chebPair n).1 z) - (chebPair n).2 z)

noncomputable def chebR (n : ℕ) : ℂ → ℂ := (chebPair n).1

noncomputable def chebR' (n : ℕ) : ℂ → ℂ := (chebPair n).2

@[simp] theorem chebPair_zero : chebPair 0 = (fun _ => 1, fun _ => 1) := rfl

@[simp] theorem chebPair_succ (n : ℕ) :
    chebPair (n + 1) =
      (fun z => z * (chebPair n).2 z - (chebPair n).1 z,
       fun z => (z * (chebPair n).2 z - (chebPair n).1 z) - (chebPair n).2 z) :=
  rfl

@[simp] theorem chebR_zero : chebR 0 = fun _ => 1 := rfl

@[simp] theorem chebR'_zero : chebR' 0 = fun _ => 1 := rfl

theorem chebR_succ (n : ℕ) :
    chebR (n + 1) = fun z => z * chebR' n z - chebR n z := rfl

theorem chebR'_succ (n : ℕ) :
    chebR' (n + 1) = fun z => chebR (n + 1) z - chebR' n z := rfl

theorem rawSymmetricPowerTrace_even (g : RawU2) (n : ℕ) :
    rawSymmetricPowerTrace (2 * n) g =
      (Matrix.det g.val) ^ n * chebR n ((Matrix.trace g.val) ^ 2 / Matrix.det g.val) ∧
    rawSymmetricPowerTrace (2 * n + 1) g =
      (Matrix.det g.val) ^ n * Matrix.trace g.val *
        chebR' n ((Matrix.trace g.val) ^ 2 / Matrix.det g.val) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [rawSymmetricPowerTrace]
    · simp [rawSymmetricPowerTrace]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hdet : Matrix.det g.val ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero (Unitary.toUnits g)
    have he : rawSymmetricPowerTrace (2 * (n + 1)) g =
        (Matrix.det g.val) ^ (n + 1) *
          chebR (n + 1) ((Matrix.trace g.val) ^ 2 / Matrix.det g.val) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, rawSymmetricPowerTrace, h1, h0,
        chebR_succ]
      field_simp
      ring
    refine ⟨he, ?_⟩
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring,
      show 2 * n + 3 = (2 * n + 1) + 2 by ring, rawSymmetricPowerTrace,
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring, he, h1, chebR'_succ, chebR_succ]
    field_simp
    ring

theorem rawRankOneCharacter_eq_chebR (n : ℕ) (g : RawU2) :
    rawRankOneCharacter n g =
      chebR n ((Matrix.trace g.val) ^ 2 / Matrix.det g.val) := by
  have hdet : Matrix.det g.val ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero (Unitary.toUnits g)
  rw [rawRankOneCharacter, (rawSymmetricPowerTrace_even g n).1]
  field_simp

theorem traceless_anticommutator (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : Matrix.trace M = 0) (hN : Matrix.trace N = 0) :
    M * N + N * M = (Matrix.trace (M * N)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hm : M 1 1 = -M 0 0 := by
    rw [Matrix.trace_fin_two] at hM
    linear_combination hM
  have hn : N 1 1 = -N 0 0 := by
    rw [Matrix.trace_fin_two] at hN
    linear_combination hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, hm, hn, Matrix.one_apply] <;> ring

theorem skew_trace_mul_real (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : star M = -M) (hN : star N = -N) :
    Matrix.trace (M * N) = ((Matrix.trace (M * N)).re : ℂ) := by
  have hs : star (Matrix.trace (M * N)) = Matrix.trace (M * N) := by
    rw [← Matrix.trace_conjTranspose]
    change Matrix.trace (star (M * N)) = _
    rw [star_mul, hM, hN, neg_mul_neg, Matrix.trace_mul_comm]
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im hs
    change -(Matrix.trace (M * N)).im = (Matrix.trace (M * N)).im at hi
    simp only [Complex.ofReal_im]
    linarith

theorem orthonormal_traceless_square (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : star M = -M) (htrace : Matrix.trace M = 0)
    (hnorm : -(Matrix.trace (M * M)).re = 1) :
    M * M = (- (1 / 2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have ht : Matrix.trace (M * M) = -1 := by
    rw [skew_trace_mul_real M M hskew hskew]
    have hr : (Matrix.trace (M * M)).re = -1 := by linarith
    simp [hr]
  have h := traceless_anticommutator M M htrace htrace
  rw [ht] at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  linear_combination (1/2 : ℂ) * hij

noncomputable def rankOneSecondDerivative {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (n : ℕ) (b : Fin d × Fin 3) (u : RawU2) : ℂ :=
  deriv (fun t : ℝ => deriv (fun s : ℝ =>
    star (rawRankOneCharacter n (u * basisExp B hskew b t * basisExp B hskew b s))) 0) 0

theorem characterSecondDerivative_factor {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (ℓ : RawHarmonicType d) (b : Fin d × Fin 3) (g : Fin d → RawU2) :
    characterSecondDerivative B hskew ℓ b g =
      rankOneSecondDerivative B hskew (ℓ b.1) b (g b.1) *
        ∏ j ∈ Finset.univ.erase b.1, star (rawRankOneCharacter (ℓ j) (g j)) := by
  classical
  have hfactor (t s : ℝ) :
      star (rawCharacter ℓ (g * basisLift B hskew b t * basisLift B hskew b s)) =
        star (rawRankOneCharacter (ℓ b.1)
          (g b.1 * basisExp B hskew b t * basisExp B hskew b s)) *
          ∏ j ∈ Finset.univ.erase b.1, star (rawRankOneCharacter (ℓ j) (g j)) := by
    simp only [rawCharacter, star_prod]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b.1)]
    congr 1
    · simp [basisLift]
    · apply Finset.prod_congr rfl
      intro j hj
      have hj' : j ≠ b.1 := (Finset.mem_erase.mp hj).1
      simp [basisLift, hj']
  simp only [characterSecondDerivative, hfactor, deriv_mul_const_field,
    rankOneSecondDerivative]

@[simp] theorem rawRankOneCharacter_zero (u : RawU2) :
    rawRankOneCharacter 0 u = 1 := by
  simp [rawRankOneCharacter, rawSymmetricPowerTrace]

@[simp] theorem rankOneSecondDerivative_zero {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (b : Fin d × Fin 3) (u : RawU2) :
    rankOneSecondDerivative B hskew 0 b u = 0 := by
  simp [rankOneSecondDerivative]

open scoped Matrix.Norms.Operator in
theorem basisExp_hasDerivAt_entry {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (b : Fin d × Fin 3) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s : ℝ => (basisExp B hskew b s).val i j)
      (((basisExp B hskew b t).val * B b.1 b.2) i j) t := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) (B b.1 b.2) (t : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    (f := fun t : ℝ => (t : ℂ)) t Complex.ofRealCLM.hasDerivAt
  have hi := (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt t h
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t hi
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_restrictScalars, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at hj
  change HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • B b.1 b.2) i j)
    (((ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ
        (NormedSpace.exp ((t : ℂ) • B b.1 b.2) * B b.1 b.2))) 1) i j) t at hj
  simpa [basisExp] using hj

@[simp] theorem basisExp_zero {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (b : Fin d × Fin 3) : basisExp B hskew b 0 = 1 := by
  apply Subtype.ext
  simp [basisExp]

theorem trace_basisExp_hasDerivAt {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (b : Fin d × Fin 3) (g : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Matrix.trace (g * (basisExp B hskew b s).val))
      (Matrix.trace (g * (basisExp B hskew b t).val * B b.1 b.2)) t := by
  have hentry (i j : Fin 2) :
      HasDerivAt (fun s : ℝ => (g * (basisExp B hskew b s).val) i j)
        ((g * (basisExp B hskew b t).val * B b.1 b.2) i j) t := by
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
        (basisExp_hasDerivAt_entry B hskew b t k j).const_mul (g i k)) using 1
    · rfl
    · rw [Matrix.mul_assoc]
      rfl
  simpa [Matrix.trace] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hentry i i)

theorem basisExp_det_eq_one {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (htrace : ∀ j a, Matrix.trace (B j a) = 0)
    (b : Fin d × Fin 3) (t : ℝ) :
    Matrix.det (basisExp B hskew b t).val = 1 := by
  have hD (s : ℝ) :
      HasDerivAt (fun r : ℝ => Matrix.det (basisExp B hskew b r).val) 0 s := by
    have h := ((basisExp_hasDerivAt_entry B hskew b s 0 0).mul
      (basisExp_hasDerivAt_entry B hskew b s 1 1)).sub
      ((basisExp_hasDerivAt_entry B hskew b s 0 1).mul
        (basisExp_hasDerivAt_entry B hskew b s 1 0))
    have ht := htrace b.1 b.2
    rw [Matrix.trace_fin_two] at ht
    convert h using 1
    · funext r
      exact Matrix.det_fin_two _
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      have ht' := congrArg (fun z : ℂ => -Matrix.det (basisExp B hskew b s).val * z) ht
      simp only [Matrix.det_fin_two] at ht'
      linear_combination ht'
  have hc := is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt)
    (fun s => (hD s).deriv) t 0
  simpa using hc

theorem orthonormal_trace_contraction
    (B : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ a, star (B a) = -B a)
    (htrace : ∀ a, Matrix.trace (B a) = 0)
    (horth : ∀ a b, -(Matrix.trace (B a * B b)).re = if a = b then 1 else 0)
    (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a, Matrix.trace (M * B a) * Matrix.trace (N * B a)) =
      -Matrix.trace (M * N) + (1 / 2 : ℂ) * Matrix.trace M * Matrix.trace N := by
  classical
  have hb (a : Fin 3) : B a 1 1 = -B a 0 0 := by
    have h := htrace a
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  have ht (a b : Fin 3) : Matrix.trace (B a * B b) = if a = b then -1 else 0 := by
    rw [skew_trace_mul_real _ _ (hskew a) (hskew b)]
    have h := horth a b
    split_ifs with hab
    · simp only [if_pos hab] at h
      have h' : (Matrix.trace (B a * B b)).re = -1 := by linarith
      simp [h']
    · simp only [if_neg hab] at h
      have h' : (Matrix.trace (B a * B b)).re = 0 := by linarith
      simp [h']
  let C : Matrix (Fin 3) (Fin 3) ℂ := fun a i => ![B a 0 0, B a 0 1, B a 1 0] i
  let D : Matrix (Fin 3) (Fin 3) ℂ := fun i a => ![-2 * B a 0 0, -B a 1 0, -B a 0 1] i
  have hCD : C * D = 1 := by
    ext a b
    have h := ht a b
    simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hb] at h
    change (C * D) a b = _
    rw [Matrix.mul_apply]
    simp only [Fin.sum_univ_three]
    simp [C, D, Matrix.one_apply]
    split_ifs at h ⊢ <;> linear_combination -h
  have hDC : D * C = 1 := mul_eq_one_comm.mp hCD
  have h (i j : Fin 3) := congrFun (congrFun hDC i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at h
  have h00 := h 0 0
  have h01 := h 0 1
  have h02 := h 0 2
  have h11 := h 1 1
  have h12 := h 1 2
  have h21 := h 2 1
  simp [C, D, Matrix.one_apply] at h00 h01 h02 h11 h12 h21
  simp only [Fin.sum_univ_three, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hb]
  linear_combination
    -(M 0 0 - M 1 1) * (N 0 0 - N 1 1) / 2 * h00 -
    ((M 0 0 - M 1 1) * N 1 0 + (N 0 0 - N 1 1) * M 1 0) / 2 * h01 -
    ((M 0 0 - M 1 1) * N 0 1 + (N 0 0 - N 1 1) * M 0 1) / 2 * h02 -
    (M 0 1 * N 1 0 + M 1 0 * N 0 1) * h11 -
    M 0 1 * N 0 1 * h12 - M 1 0 * N 1 0 * h21

theorem polynomial_hasDerivAt_complex_curve (p : Polynomial ℂ)
    {f : ℝ → ℂ} {v : ℂ} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => Polynomial.eval (f s) p)
      (Polynomial.eval (f t) p.derivative * v) t := by
  have h := ((p.hasDerivAt (f t)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hf
  simpa [Function.comp_def, mul_comm] using h

theorem polynomial_mixed_derivative (p : Polynomial ℂ)
    (f : ℝ → ℝ → ℂ) (v : ℝ → ℂ) (w : ℂ)
    (hs : ∀ t, HasDerivAt (f t) (v t) 0)
    (ht : HasDerivAt (fun t => f t 0) (v 0) 0)
    (hv : HasDerivAt v w 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => Polynomial.eval (f t s) p) 0) 0 =
      Polynomial.eval (f 0 0) p.derivative.derivative * (v 0)^2 +
        Polynomial.eval (f 0 0) p.derivative * w := by
  have heq : (fun t : ℝ => deriv (fun s : ℝ => Polynomial.eval (f t s) p) 0) =
      fun t => Polynomial.eval (f t 0) p.derivative * v t := by
    funext t
    exact (polynomial_hasDerivAt_complex_curve p (hs t)).deriv
  rw [heq]
  have h := (polynomial_hasDerivAt_complex_curve p.derivative ht).mul hv
  convert h.deriv using 1 <;> ring

theorem trace_basisExp_mul_hasDerivAt {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (b : Fin d × Fin 3) (g A : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Matrix.trace (g * (basisExp B hskew b s).val * A))
      (Matrix.trace (g * (basisExp B hskew b t).val * B b.1 b.2 * A)) t := by
  have heq (s : ℝ) : Matrix.trace (g * (basisExp B hskew b s).val * A) =
      Matrix.trace ((A * g) * (basisExp B hskew b s).val) := by
    rw [Matrix.trace_mul_comm _ A, ← Matrix.mul_assoc]
  simp_rw [heq]
  convert trace_basisExp_hasDerivAt B hskew b (A * g) t using 1
  rw [Matrix.trace_mul_comm _ A]
  simp only [Matrix.mul_assoc]

theorem polynomial_trace_invariant_mixed_derivative {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (htrace : ∀ j a, Matrix.trace (B j a) = 0)
    (horth : ∀ j a b, -(Matrix.trace (B j a * B j b)).re = if a = b then 1 else 0)
    (b : Fin d × Fin 3) (g : RawU2) (p : Polynomial ℂ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      Polynomial.eval ((Matrix.trace
        (g * basisExp B hskew b t * basisExp B hskew b s).val)^2 /
        Matrix.det (g * basisExp B hskew b t * basisExp B hskew b s).val) p) 0) 0 =
      Polynomial.eval ((Matrix.trace g.val)^2 / Matrix.det g.val) p.derivative.derivative *
        (2 * Matrix.trace g.val * Matrix.trace (g.val * B b.1 b.2) / Matrix.det g.val)^2 +
      Polynomial.eval ((Matrix.trace g.val)^2 / Matrix.det g.val) p.derivative *
        ((2 * (Matrix.trace (g.val * B b.1 b.2))^2 - (Matrix.trace g.val)^2) /
          Matrix.det g.val) := by
  simp only [Submonoid.coe_mul, Matrix.det_mul, basisExp_det_eq_one B hskew htrace, mul_one]
  let f (t s : ℝ) := (Matrix.trace
    (g.val * (basisExp B hskew b t).val * (basisExp B hskew b s).val))^2 / Matrix.det g.val
  let v (t : ℝ) := 2 * Matrix.trace (g.val * (basisExp B hskew b t).val) *
    Matrix.trace (g.val * (basisExp B hskew b t).val * B b.1 b.2) / Matrix.det g.val
  have hs (t : ℝ) : HasDerivAt (f t) (v t) 0 := by
    have h := ((trace_basisExp_hasDerivAt B hskew b
      (g.val * (basisExp B hskew b t).val) 0).pow 2).div_const (Matrix.det g.val)
    simpa [f, v, mul_assoc] using h
  have ht : HasDerivAt (fun t => f t 0) (v 0) 0 := by
    have h := ((trace_basisExp_hasDerivAt B hskew b g.val 0).pow 2).div_const (Matrix.det g.val)
    simpa [f, v, mul_assoc] using h
  have hv : HasDerivAt v
      ((2 * (Matrix.trace (g.val * B b.1 b.2))^2 - (Matrix.trace g.val)^2) / Matrix.det g.val) 0 := by
    have h := (((trace_basisExp_hasDerivAt B hskew b g.val 0).const_mul 2).mul
      (trace_basisExp_mul_hasDerivAt B hskew b g.val (B b.1 b.2) 0)).div_const (Matrix.det g.val)
    have hsq := orthonormal_traceless_square (B b.1 b.2)
      (hskew b.1 b.2) (htrace b.1 b.2) (by simpa using horth b.1 b.2 b.2)
    simp only [basisExp_zero, Submonoid.coe_one, Matrix.mul_one] at h
    rw [Matrix.mul_assoc, hsq] at h
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul] at h
    convert h using 1 <;> ring
  simpa [f, v] using polynomial_mixed_derivative p f v _ hs ht hv

theorem orthonormal_trace_square_sum
    (B : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ a, star (B a) = -B a)
    (htrace : ∀ a, Matrix.trace (B a) = 0)
    (horth : ∀ a b, -(Matrix.trace (B a * B b)).re = if a = b then 1 else 0)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a, (Matrix.trace (g * B a))^2) =
      2 * Matrix.det g - (Matrix.trace g)^2 / 2 := by
  have h := orthonormal_trace_contraction B hskew htrace horth g g
  simp only [← pow_two (Matrix.trace _)] at h
  rw [h]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem polynomial_trace_invariant_casimir {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (htrace : ∀ j a, Matrix.trace (B j a) = 0)
    (horth : ∀ j a b, -(Matrix.trace (B j a * B j b)).re = if a = b then 1 else 0)
    (j : Fin d) (g : RawU2) (p : Polynomial ℂ) :
    (∑ a : Fin 3, deriv (fun t : ℝ => deriv (fun s : ℝ =>
      Polynomial.eval ((Matrix.trace
        (g * basisExp B hskew (j,a) t * basisExp B hskew (j,a) s).val)^2 /
        Matrix.det (g * basisExp B hskew (j,a) t * basisExp B hskew (j,a) s).val) p) 0) 0) =
      2 * ((Matrix.trace g.val)^2 / Matrix.det g.val) *
        (4 - (Matrix.trace g.val)^2 / Matrix.det g.val) *
        Polynomial.eval ((Matrix.trace g.val)^2 / Matrix.det g.val) p.derivative.derivative -
      4 * ((Matrix.trace g.val)^2 / Matrix.det g.val - 1) *
        Polynomial.eval ((Matrix.trace g.val)^2 / Matrix.det g.val) p.derivative := by
  have hsum := orthonormal_trace_square_sum (B j) (hskew j) (htrace j) (horth j) g.val
  have hd : Matrix.det g.val ≠ 0 := (Matrix.UnitaryGroup.det_isUnit g).ne_zero
  simp_rw [polynomial_trace_invariant_mixed_derivative B hskew htrace horth]
  have hv (a : Fin 3) :
      (2 * Matrix.trace g.val * Matrix.trace (g.val * B j a) / Matrix.det g.val)^2 =
        (2 * Matrix.trace g.val / Matrix.det g.val)^2 *
          (Matrix.trace (g.val * B j a))^2 := by ring
  simp_rw [hv]
  have hw : (∑ a : Fin 3,
      (2 * (Matrix.trace (g.val * B j a))^2 - (Matrix.trace g.val)^2) /
        Matrix.det g.val) =
      (2 * (2 * Matrix.det g.val - (Matrix.trace g.val)^2 / 2) -
        3 * (Matrix.trace g.val)^2) / Matrix.det g.val := by
    rw [← Finset.sum_div]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hsum]
  field_simp
  ring

open Polynomial

noncomputable def casimirPolyPair : ℕ → Polynomial ℂ × Polynomial ℂ
| 0 => (1,1)
| n+1 => (X * (casimirPolyPair n).2 - (casimirPolyPair n).1,
  (X * (casimirPolyPair n).2 - (casimirPolyPair n).1) - (casimirPolyPair n).2)
noncomputable def casimirP (n : ℕ) := (casimirPolyPair n).1
noncomputable def casimirQ (n : ℕ) := (casimirPolyPair n).2

@[simp] theorem casimirP_zero : casimirP 0 = 1 := rfl

@[simp] theorem casimirQ_zero : casimirQ 0 = 1 := rfl

theorem casimirP_succ (n : ℕ) : casimirP (n+1) = X * casimirQ n - casimirP n := rfl
theorem casimirQ_succ (n : ℕ) : casimirQ (n+1) = (X - 1) * casimirQ n - casimirP n := by
  simp only [casimirQ, casimirPolyPair, casimirP]; ring
theorem casimirPoly_eval (n : ℕ) (z : ℂ) :
  (casimirP n).eval z = chebR n z ∧ (casimirQ n).eval z = chebR' n z := by
  induction n with
  | zero => simp
  | succ n ih => simp [casimirP_succ, casimirQ_succ, chebR_succ, chebR'_succ, ih]; ring
theorem casimirPoly_first (n : ℕ) :
  (X - 4) * (casimirP n).derivative = C (2*(n:ℂ)+1) * casimirQ n - C ((n:ℂ)+1) * casimirP n ∧
  X * (X - 4) * (casimirQ n).derivative = (C (n:ℂ)*X+2) * casimirQ n - C (2*((n:ℂ)+1)) * casimirP n := by
  induction n with
  | zero => simp [Polynomial.C_ofNat]
  | succ n ih =>
    obtain ⟨hp,hq⟩ := ih
    simp only [map_add, map_mul, map_one, map_ofNat] at hp hq
    simp only [casimirP_succ, casimirQ_succ, derivative_sub, derivative_mul, derivative_X,
      derivative_one, sub_zero, one_mul, Nat.cast_add, Nat.cast_one, map_add, map_mul,
      map_one, map_ofNat]
    constructor
    · linear_combination -hp + hq
    · linear_combination -X*hp + (X-1)*hq
theorem casimirPoly_equation (n : ℕ) :
  X * (X-4) * (casimirP n).derivative.derivative + 2*(X-1)*(casimirP n).derivative =
    C ((n:ℂ)*((n:ℂ)+1)) * casimirP n := by
  obtain ⟨hp,hq⟩ := casimirPoly_first n
  have hdp := congrArg Polynomial.derivative hp
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_ofNat, sub_zero,
    derivative_C, derivative_one, zero_add, add_zero, zero_mul, one_mul, map_add, map_mul, map_one, C_ofNat] at hdp hp hq ⊢
  have h : (X-4) * (X*(X-4)*(casimirP n).derivative.derivative +
      2*(X-1)*(casimirP n).derivative) =
      (X-4) * ((C (n:ℂ) * (C (n:ℂ)+1)) * casimirP n) := by
    linear_combination X*(X-4)*hdp + (2*C (n:ℂ)+1)*hq - (C (n:ℂ)*X+2)*hp
  exact mul_left_cancel₀ (by intro he; have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) he; simp at hc) h
theorem casimirPoly_eval_equation (n : ℕ) (z : ℂ) :
    2*z*(4-z)*(casimirP n).derivative.derivative.eval z -
      4*(z-1)*(casimirP n).derivative.eval z =
      -(2*(n:ℂ)*((n:ℂ)+1)) * chebR n z := by
  have h := congrArg (Polynomial.eval z) (casimirPoly_equation n)
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_ofNat, eval_C, eval_one] at h
  rw [← (casimirPoly_eval n z).1]
  linear_combination -2*h

theorem rankOneSecondDerivative_sum {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (htrace : ∀ j a, Matrix.trace (B j a) = 0)
    (horth : ∀ j a b, -(Matrix.trace (B j a * B j b)).re = if a = b then 1 else 0)
    (n : ℕ) (j : Fin d) (u : RawU2) :
    (∑ a : Fin 3, rankOneSecondDerivative B hskew n (j,a) u) =
      -(2*(n:ℂ)*((n:ℂ)+1)) * star (rawRankOneCharacter n u) := by
  simp only [rankOneSecondDerivative, rawRankOneCharacter_eq_chebR,
    ← (casimirPoly_eval n _).1, deriv.star, ← star_sum]
  rw [polynomial_trace_invariant_casimir B hskew htrace horth,
    casimirPoly_eval_equation]
  simp [(casimirPoly_eval n _).1]

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.Casimir
