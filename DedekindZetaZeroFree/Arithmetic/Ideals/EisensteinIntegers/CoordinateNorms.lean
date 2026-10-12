module

public import DedekindZetaZeroFree.Arithmetic.Ideals.EisensteinIntegers.PrimaryIdealDomain

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

noncomputable def coordBasis (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3) :
    Module.Basis (Fin 2) ℤ (R E) :=
  hω.integralPowerBasis.basis.reindex (finCongr (by simp; decide))
private theorem coordBasis_apply (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3) (i : Fin 2) :
    coordBasis E ω hω i = η E ω hω ^ (i : ℕ) := by
  simp [coordBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

theorem existsUnique_int_coordinates (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (x : R E) :
    ∃! ab : ℤ × ℤ, x = (ab.1 : R E) + (ab.2 : R E) * η E ω hω := by
  let B := coordBasis E ω hω
  have h0 : B 0 = 1 := by simp [B, coordBasis_apply]
  have h1 : B 1 = η E ω hω := by simp [B, coordBasis_apply]
  have rep (a b : ℤ) : B.repr ((a : R E) + (b : R E) * η E ω hω) =
      Finsupp.single 0 a + Finsupp.single 1 b := by
    rw [show (a : R E) + (b : R E) * η E ω hω = a • B 0 + b • B 1 by
      simp [h0, h1, zsmul_eq_mul]]
    rw [map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
    simp
  refine ⟨(B.repr x 0, B.repr x 1), ?_, ?_⟩
  · have h := B.sum_repr x
    simpa [Fin.sum_univ_two, h0, h1, zsmul_eq_mul] using h.symm
  · rintro ⟨a,b⟩ hab
    apply Prod.ext
    · have h := congrArg (fun y => B.repr y 0) hab
      simpa [rep] using h.symm
    · have h := congrArg (fun y => B.repr y 1) hab
      simpa [rep] using h.symm

theorem eta_sq_add_eta_add_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3) :
    η E ω hω ^ 2 + η E ω hω + 1 = 0 := by
  have h := IsCyclotomicExtension.Rat.Three.eta_sq hω
  simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] at h
  linear_combination h

theorem norm_int_coordinates (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (a b : ℤ) :
    Algebra.norm ℤ ((a : R E) + (b : R E) * η E ω hω) =
      a ^ 2 - a * b + b ^ 2 := by
  let B := coordBasis E ω hω
  have h0 : B 0 = 1 := by simp [B, coordBasis_apply]
  have h1 : B 1 = η E ω hω := by simp [B, coordBasis_apply]
  have rep (c d : ℤ) : B.repr ((c : R E) + (d : R E) * η E ω hω) =
      Finsupp.single 0 c + Finsupp.single 1 d := by
    rw [show (c : R E) + (d : R E) * η E ω hω = c • B 0 + d • B 1 by
      simp [h0, h1, zsmul_eq_mul]]
    rw [map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
    simp
  have hm : ((a : R E) + (b : R E) * η E ω hω) * η E ω hω =
      ((-b : ℤ) : R E) + ((a-b : ℤ) : R E) * η E ω hω := by
    push_cast
    have h := eta_sq_add_eta_add_one E ω hω
    linear_combination (b : R E) * h
  rw [Algebra.norm_eq_matrix_det B]
  have mat : Algebra.leftMulMatrix B ((a : R E) + (b : R E) * η E ω hω) =
      !![a, -b; b, a-b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num only [Algebra.leftMulMatrix_eq_repr_mul, Fin.zero_eta, Fin.mk_one] <;>
      simp only [h0, h1, mul_one, hm, rep] <;> simp
  rw [mat, Matrix.det_fin_two]
  simp
  ring

theorem normSq_int_coordinates (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (ι : E →+* ℂ) (a b : ℤ) :
    Complex.normSq (ιR E ι ((a : R E) + (b : R E) * η E ω hω)) =
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
  let z := ιR E ι (η E ω hω)
  have hp : z ^ 3 = 1 := by
    have hh := congrArg (ιR E ι) hω.toInteger_cube_eq_one
    simpa only [map_pow, map_one] using hh
  have hn : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_pow_eq_one hp (by decide)]
    norm_num
  have he : z ^ 2 + z + 1 = 0 := by
    have hh := congrArg (ιR E ι) (eta_sq_add_eta_add_one E ω hω)
    simpa only [map_add, map_pow, map_one, map_zero] using hh
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  have hn' : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hn
  have him : z.im ≠ 0 := by
    intro h
    rw [h] at hr
    nlinarith [sq_nonneg (z.re + 1 / 2)]
  have hre : 2 * z.re + 1 = 0 := by
    have hh : z.im * (2 * z.re + 1) = 0 := by nlinarith [hi]
    exact (mul_eq_zero.mp hh).resolve_left him
  simp only [map_add, map_mul, map_intCast]
  change Complex.normSq ((a : ℂ) + (b : ℂ) * z) = _
  push_cast
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, mul_zero, sub_zero, zero_add]
  nlinarith [sq_nonneg ((b : ℝ) * z.im)]

theorem absNorm_span_eq_normSq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ι : E →+* ℂ) (x : R E) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) = Complex.normSq (ιR E ι x) := by
  let ω := IsCyclotomicExtension.zeta 3 ℚ E
  have hω : IsPrimitiveRoot ω 3 := IsCyclotomicExtension.zeta_spec 3 ℚ E
  obtain ⟨⟨a,b⟩, hx, _⟩ := existsUnique_int_coordinates E ω hω x
  rw [hx, Ideal.absNorm_span_singleton, norm_int_coordinates, normSq_int_coordinates]
  have hn : (0 : ℝ) ≤ ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
    rw [← normSq_int_coordinates E ω hω ι a b]
    exact Complex.normSq_nonneg _
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hn]

end DedekindZetaZeroFree.Eisenstein
