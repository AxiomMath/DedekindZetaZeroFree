module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

section
open MeasureTheory
open scoped NNReal
open scoped BigOperators ComplexConjugate ContDiff
noncomputable section
set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.GramCoefficients
abbrev LocalGL := Matrix.GeneralLinearGroup (Fin 2) ℂ

def normalizedGram (B : LocalGL) (p q : Fin 2) : ℂ :=
  (∑ j : Fin 2, B p j * conj (B q j)) / (‖((Matrix.GeneralLinearGroup.det B : ℂˣ) : ℂ)‖ : ℂ)

lemma normalizedGram_scalar (c : ℂˣ) (B : LocalGL) (p q : Fin 2) :
    normalizedGram (Matrix.GeneralLinearGroup.scalar (Fin 2) c * B) p q =
      normalizedGram B p q := by
  have hentry (i j : Fin 2) :
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c * B) i j = (c : ℂ) * B i j := by
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : ℂˣ) : ℂ) = (c : ℂ) ^ 2 := by
    change (Matrix.GeneralLinearGroup.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) ℂ).det = _
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar]
  unfold normalizedGram
  simp only [hentry, map_mul, Units.val_mul, hdet, norm_mul, norm_pow,
    Complex.ofReal_mul, Complex.ofReal_pow]
  have hn : (‖(c : ℂ)‖ : ℂ) ^ 2 = (c : ℂ) * conj (c : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hn]
  have hsum : (∑ j : Fin 2, (c : ℂ) * B p j * (conj (c : ℂ) * conj (B q j))) =
      ((c : ℂ) * conj (c : ℂ)) * ∑ j : Fin 2, B p j * conj (B q j) := by
    simp only [Fin.sum_univ_two]
    ring
  rw [hsum]
  field_simp

lemma gram_tensor_average_smooth {X ι : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (Q : X → ι → Fin 2 → Fin 2 → ℂ) (h : X → ℂ)
    (hQ : ∀ (w : ι) (p q : Fin 2), Continuous (fun x => Q x w p q))
    (hh : Continuous h) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun A : ι → Fin 2 → ℂ =>
        ∫ x, h x * ∏ w : ι, ∑ r : Fin 2 × Fin 2,
          (A w r.1 * conj (A w r.2)) * Q x w r.1 r.2 ∂μ) := by
  classical
  have hc : ∀ r : ι → Fin 2 × Fin 2, Integrable
      (fun x => h x * ∏ w : ι, Q x w (r w).1 (r w).2) μ := by
    intro r
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact hh.mul (continuous_finsetProd _ (fun w _ => hQ w (r w).1 (r w).2))
  have he (A : ι → Fin 2 → ℂ) :
      (∫ x, h x * ∏ w : ι, ∑ r : Fin 2 × Fin 2,
        (A w r.1 * conj (A w r.2)) * Q x w r.1 r.2 ∂μ) =
      ∑ r : ι → Fin 2 × Fin 2, (∏ w : ι, A w (r w).1 * conj (A w (r w).2)) *
        (∫ x, h x * ∏ w : ι, Q x w (r w).1 (r w).2 ∂μ) := by
    calc
      _ = ∫ x, ∑ r : ι → Fin 2 × Fin 2,
          (∏ w : ι, A w (r w).1 * conj (A w (r w).2)) *
          (h x * ∏ w : ι, Q x w (r w).1 (r w).2) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Fintype.prod_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.prod_mul_distrib]
        ring
      _ = _ := by
        rw [integral_finsetSum _ (fun r _ => (hc r).const_mul _)]
        simp_rw [integral_const_mul]
  simp_rw [he]
  apply ContDiff.sum
  intro r _
  apply ContDiff.mul _ contDiff_const
  apply contDiff_prod
  intro w _
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun A : ι → Fin 2 → ℂ => A w (r w).1) :=
    (contDiff_apply ℝ ℂ (r w).1).comp (contDiff_apply ℝ (Fin 2 → ℂ) w)
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun A : ι → Fin 2 → ℂ => A w (r w).2) :=
    (contDiff_apply ℝ ℂ (r w).2).comp (contDiff_apply ℝ (Fin 2 → ℂ) w)
  exact hp.mul (Complex.conjCLE.contDiff.comp hq)

lemma gram_tensor_real_average_smooth {X ι : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (Q : X → ι → Fin 2 → Fin 2 → ℂ) (h : X → ℝ)
    (hQ : ∀ (w : ι) (p q : Fin 2), Continuous (fun x => Q x w p q))
    (hh : Continuous h) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun A : ι → Fin 2 → ℂ =>
        ∫ x, h x * (∏ w : ι, ∑ r : Fin 2 × Fin 2,
          (A w r.1 * conj (A w r.2)) * Q x w r.1 r.2).re ∂μ) := by
  have hi (A : ι → Fin 2 → ℂ) : Integrable
      (fun x => (h x : ℂ) * ∏ w : ι, ∑ r : Fin 2 × Fin 2,
        (A w r.1 * conj (A w r.2)) * Q x w r.1 r.2) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply (Complex.continuous_ofReal.comp hh).mul
    exact continuous_finsetProd _ (fun w _ => continuous_finsetSum _ (fun r _ =>
      continuous_const.mul (hQ w r.1 r.2)))
  have he (A : ι → Fin 2 → ℂ) :
      (∫ x, h x * (∏ w : ι, ∑ r : Fin 2 × Fin 2,
        (A w r.1 * conj (A w r.2)) * Q x w r.1 r.2).re ∂μ) =
      Complex.reCLM (∫ x, (h x : ℂ) * ∏ w : ι, ∑ r : Fin 2 × Fin 2,
        (A w r.1 * conj (A w r.2)) * Q x w r.1 r.2 ∂μ) := by
    rw [← Complex.reCLM.integral_comp_comm (hi A)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Complex.reCLM_apply]
  simp_rw [he]
  exact Complex.reCLM.contDiff.comp (gram_tensor_average_smooth μ Q
    (fun x => (h x : ℂ)) hQ (Complex.continuous_ofReal.comp hh))

lemma normalized_average_log_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (q H : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : ∀ z ∈ U, 0 < q z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (he : ∀ z ∈ U, H z = (q z).rpow (-(1 : ℝ) / 2) * c) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Real.log (q z)) U := by
  have hpos : ∀ z ∈ U, 0 < H z := by
    intro z hz
    rw [he z hz]
    exact mul_pos (Real.rpow_pos_of_pos (hq z hz) _) hc
  have hl : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (-2 : ℝ) * (Real.log (H z) - Real.log c)) U :=
    contDiffOn_const.mul ((hH.log (fun z hz => ne_of_gt (hpos z hz))).sub contDiffOn_const)
  apply hl.congr
  intro z hz
  rw [he z hz]
  change Real.log (q z) = -2 * (Real.log ((q z) ^ (-(1 : ℝ) / 2) * c) - Real.log c)
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (hq z hz) _))
    (ne_of_gt hc), Real.log_rpow (hq z hz)]
  ring

lemma gram_divided_tensor_average_smooth
    {X ι E : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (Q : X → ι → Fin 2 → Fin 2 → ℂ) (h : X → ℝ)
    (hQ : ∀ (w : ι) (p q : Fin 2), Continuous (fun x => Q x w p q))
    (hh : Continuous h) (U : Set E) (A : E → ι → Fin 2 → ℂ)
    (d : E → ℝ) (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U)
    (hd : ContDiffOn ℝ (⊤ : ℕ∞) d U) (hd0 : ∀ z ∈ U, d z ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (∫ x, h x * (∏ w : ι, ∑ r : Fin 2 × Fin 2,
        (A z w r.1 * conj (A z w r.2)) * Q x w r.1 r.2).re ∂μ) / d z) U := by
  exact ((gram_tensor_real_average_smooth μ Q h hQ hh).comp_contDiffOn hA).div hd hd0

lemma normalizedGram_continuous (p q : Fin 2) :
    Continuous (fun B : LocalGL => normalizedGram B p q) := by
  have hent (i j : Fin 2) : Continuous (fun B : LocalGL => B i j) := by
    exact (continuous_apply j).comp ((continuous_apply i).comp
      (show Continuous (fun B : LocalGL => (B : Matrix (Fin 2) (Fin 2) ℂ)) from Units.continuous_val))
  have hd : Continuous (fun B : LocalGL =>
      (‖((Matrix.GeneralLinearGroup.det B : ℂˣ) : ℂ)‖ : ℂ)) := by
    change Continuous (fun B : LocalGL => (‖(B : Matrix (Fin 2) (Fin 2) ℂ).det‖ : ℂ))
    simp only [Matrix.det_fin_two]
    exact Complex.continuous_ofReal.comp
      ((((hent 0 0).mul (hent 1 1)).sub ((hent 0 1).mul (hent 1 0))).norm)
  exact (continuous_finsetSum _ (fun j _ => (hent p j).mul
    (Complex.continuous_conj.comp (hent q j)))).div hd (fun B => by
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero B)))

lemma normalizedGram_eq_of_pgl_eq (A B : LocalGL)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) (p q : Fin 2) :
    normalizedGram A p q = normalizedGram B p q := by
  obtain ⟨c, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hcomm : A * Matrix.GeneralLinearGroup.scalar (Fin 2) c =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c * A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  rw [hcomm, normalizedGram_scalar]

noncomputable def projectiveGram (p q : Fin 2) (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) : ℂ :=
  normalizedGram (Classical.choose (Matrix.ProjGenLinGroup.mk_surjective g)) p q

lemma projectiveGram_mk (p q : Fin 2) (B : LocalGL) :
    projectiveGram p q (Matrix.ProjGenLinGroup.mk B) = normalizedGram B p q := by
  apply normalizedGram_eq_of_pgl_eq
  exact Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective _)

lemma projectiveGram_continuous (p q : Fin 2) :
    letI : TopologicalSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
      inferInstanceAs (TopologicalSpace (LocalGL ⧸ Subgroup.center LocalGL))
    Continuous (projectiveGram p q) := by
  letI : TopologicalSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
    inferInstanceAs (TopologicalSpace (LocalGL ⧸ Subgroup.center LocalGL))
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center LocalGL)).continuous_iff.mpr
  change Continuous (fun B : LocalGL => projectiveGram p q (Matrix.ProjGenLinGroup.mk B))
  simp_rw [projectiveGram_mk]
  exact normalizedGram_continuous p q

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.GramCoefficients

end

end

section

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ProjectiveAverage

open GramCoefficients

lemma normalizedGram_mul (A B : LocalGL) (p q : Fin 2) :
    normalizedGram (A * B) p q =
      (∑ r : Fin 2 × Fin 2,
        (A p r.1 * conj (A q r.2)) * normalizedGram B r.1 r.2) /
          (‖((Matrix.GeneralLinearGroup.det A : ℂˣ) : ℂ)‖ : ℂ) := by
  simp only [normalizedGram, map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type, map_add, map_mul]
  field_simp
  <;> ring

def projectiveRowWeight (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) : ℝ :=
  (projectiveGram 1 1 g).re

lemma projectiveRowWeight_mk (B : LocalGL) :
    projectiveRowWeight (Matrix.ProjGenLinGroup.mk B) =
      (‖B 1 0‖ ^ 2 + ‖B 1 1‖ ^ 2) /
        ‖((Matrix.GeneralLinearGroup.det B : ℂˣ) : ℂ)‖ := by
  simp only [projectiveRowWeight, projectiveGram_mk, normalizedGram, Fin.sum_univ_two,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
    ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]

@[simp] lemma projectiveRowWeight_one :
    projectiveRowWeight (1 : Matrix.ProjGenLinGroup (Fin 2) ℂ) = 1 := by
  rw [← map_one (Matrix.ProjGenLinGroup.mk : LocalGL →* _), projectiveRowWeight_mk]
  norm_num

lemma projectiveRowWeight_coe (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
    (projectiveRowWeight g : ℂ) = projectiveGram 1 1 g := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  simp only [projectiveRowWeight_mk, projectiveGram_mk, normalizedGram, Fin.sum_univ_two,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_add,
    ← Complex.ofReal_div]

lemma projective_row_sum (A : LocalGL) (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
    (∑ r : Fin 2 × Fin 2,
      (A 1 r.1 * conj (A 1 r.2)) * projectiveGram r.1 r.2 g) =
        (projectiveRowWeight (Matrix.ProjGenLinGroup.mk A * g) *
          ‖((Matrix.GeneralLinearGroup.det A : ℂˣ) : ℂ)‖ : ℝ) := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hd : (‖((Matrix.GeneralLinearGroup.det A : ℂˣ) : ℂ)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero A))
  have he := projectiveRowWeight_coe (Matrix.ProjGenLinGroup.mk (A * B))
  rw [projectiveGram_mk, normalizedGram_mul] at he
  rw [← map_mul]
  simp only [projectiveGram_mk, Complex.ofReal_mul]
  exact ((eq_div_iff hd).mp he).symm

lemma projective_tensor_formula {ι : Type*} [Fintype ι]
    (A : ι → LocalGL) (B : ι → Matrix.ProjGenLinGroup (Fin 2) ℂ) :
    (∏ w : ι, projectiveRowWeight (Matrix.ProjGenLinGroup.mk (A w) * B w)) =
      (∏ w : ι, ∑ r : Fin 2 × Fin 2,
        (A w 1 r.1 * conj (A w 1 r.2)) * projectiveGram r.1 r.2 (B w)).re /
        (∏ w : ι, ‖((Matrix.GeneralLinearGroup.det (A w) : ℂˣ) : ℂ)‖) := by
  simp_rw [projective_row_sum]
  rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib]
  exact (mul_div_cancel_right₀ _ (Finset.prod_ne_zero_iff.mpr (fun w _ =>
    norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero (A w))))).symm

lemma projective_compact_average_smooth
    {X ι E : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (B : X → ι → Matrix.ProjGenLinGroup (Fin 2) ℂ) (h : X → ℝ)
    (hB : letI : TopologicalSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
        inferInstanceAs (TopologicalSpace (LocalGL ⧸ Subgroup.center LocalGL))
      ∀ w, Continuous (fun x => B x w)) (hh : Continuous h)
    (U : Set E) (A : E → ι → LocalGL)
    (hA : ∀ w p q, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A z w p q) U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∫ x, h x * ∏ w : ι,
        projectiveRowWeight (Matrix.ProjGenLinGroup.mk (A z w) * B x w) ∂μ) U := by
  letI : TopologicalSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
    inferInstanceAs (TopologicalSpace (LocalGL ⧸ Subgroup.center LocalGL))
  have hd (w : ι) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ‖((Matrix.GeneralLinearGroup.det (A z w) : ℂˣ) : ℂ)‖) U := by
    have he : (fun z => ((Matrix.GeneralLinearGroup.det (A z w) : ℂˣ) : ℂ)) =
        (fun z => A z w 0 0 * A z w 1 1 - A z w 0 1 * A z w 1 0) := by
      funext z
      exact Matrix.det_fin_two _
    apply ContDiffOn.norm (𝕜 := ℂ) _ (fun z _ => Matrix.GeneralLinearGroup.det_ne_zero (A z w))
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((Matrix.GeneralLinearGroup.det (A z w) : ℂˣ) : ℂ)) U
    rw [he]
    exact ((hA w 0 0).mul (hA w 1 1)).sub ((hA w 0 1).mul (hA w 1 0))
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z w q => A z w 1 q) U :=
    contDiffOn_pi.mpr (fun w => contDiffOn_pi.mpr (fun q => hA w 1 q))
  have hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∏ w : ι, ‖((Matrix.GeneralLinearGroup.det (A z w) : ℂˣ) : ℂ)‖) U :=
    contDiffOn_prod (fun w _ => hd w)
  have hp0 : ∀ z ∈ U,
      (∏ w : ι, ‖((Matrix.GeneralLinearGroup.det (A z w) : ℂˣ) : ℂ)‖) ≠ 0 := by
    intro z _
    exact Finset.prod_ne_zero_iff.mpr (fun w _ =>
      norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero (A z w)))
  have hs := gram_divided_tensor_average_smooth μ
    (fun x w p q => projectiveGram p q (B x w)) h
    (fun w p q => (projectiveGram_continuous p q).comp (hB w)) hh
    U (fun z w q => A z w 1 q)
    (fun z => ∏ w : ι, ‖((Matrix.GeneralLinearGroup.det (A z w) : ℂˣ) : ℂ)‖)
    hb hp hp0
  apply hs.congr
  intro z _
  simp_rw [projective_tensor_formula]
  simp_rw [← mul_div_assoc]
  exact integral_div _ _

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ProjectiveAverage

end

end
