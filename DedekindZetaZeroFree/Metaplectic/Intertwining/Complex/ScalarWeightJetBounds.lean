module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Complex.NormalizedRowJetBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped ContDiff Matrix.Norms.Elementwise

lemma scalar_bottomRowNormSq_pos (g : ComplexGL2) : 0 < bottomRowNormSq g := by
  have hn : 0 ≤ bottomRowNormSq g := by unfold bottomRowNormSq; positivity
  by_contra hp
  have hz : bottomRowNormSq g = 0 := le_antisymm (le_of_not_gt hp) hn
  have h0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    apply norm_eq_zero.mp
    have : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 = 0 := by
      unfold bottomRowNormSq at hz
      nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖]
    nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)]
  have h1 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
    apply norm_eq_zero.mp
    have : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 0 := by
      unfold bottomRowNormSq at hz
      nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖]
    nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)]
  exact Matrix.GeneralLinearGroup.det_ne_zero g (by simp [Matrix.det_fin_two, h0, h1])

private lemma scalar_entry_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {g : E → ComplexGL2}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (i j : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ) i j) U := by
  exact (contDiff_apply ℝ ℂ j).contDiffOn.comp
    ((contDiff_apply ℝ (Fin 2 → ℂ) i).contDiffOn.comp hg (Set.mapsTo_univ _ _))
    (Set.mapsTo_univ _ _)

lemma scalar_ratio_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {g : E → ComplexGL2}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ)) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v => ratio (g v)) U := by
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ).det) U := by
    simp only [Matrix.det_fin_two]
    exact ((scalar_entry_contDiffOn hg 0 0).mul (scalar_entry_contDiffOn hg 1 1)).sub
      ((scalar_entry_contDiffOn hg 0 1).mul (scalar_entry_contDiffOn hg 1 0))
  have hnorm := hdet.norm ℂ (fun v _ => Matrix.GeneralLinearGroup.det_ne_zero (g v))
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => bottomRowNormSq (g v)) U :=
    ((scalar_entry_contDiffOn hg 1 0).norm_sq ℂ).add ((scalar_entry_contDiffOn hg 1 1).norm_sq ℂ)
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun v => ‖((Matrix.GeneralLinearGroup.det (g v) : ℂˣ) : ℂ)‖ /
      bottomRowNormSq (g v)) U
  exact hnorm.div hb (fun v _ => (scalar_bottomRowNormSq_pos (g v)).ne')

lemma scalar_log_ratio_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {g : E → ComplexGL2}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ)) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v => Real.log (ratio (g v))) U := by
  exact (scalar_ratio_contDiffOn hg).log
    (fun v _ => (div_pos (norm_pos_iff.mpr (Units.ne_zero _))
      (scalar_bottomRowNormSq_pos (g v))).ne')

lemma scalar_weight_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (s x : ℂ) {U : Set E} {g : E → ComplexGL2}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ)) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v =>
      (2 * (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) ^ m *
      Complex.exp (((4 / 3 : ℂ) + 2 * s) *
        (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ))) U := by
  have hprod : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v => (weyl * upperUnipotent x * g v : Matrix (Fin 2) (Fin 2) ℂ)) U := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun v =>
      (weyl * upperUnipotent x : Matrix (Fin 2) (Fin 2) ℂ) * (g v : Matrix (Fin 2) (Fin 2) ℂ)) U
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    apply ContDiffOn.sum
    intro k _
    exact contDiffOn_const.mul (scalar_entry_contDiffOn hg k j)
  have hl := scalar_log_ratio_contDiffOn (g := fun v => weyl * upperUnipotent x * g v) hprod
  have hc : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v => (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hl
  exact (contDiffOn_const.mul hc).pow m |>.mul ((contDiffOn_const.mul hc).cexp)

namespace ScalarCompactification

open Set

noncomputable def rowSquare {n : ℕ} (g : (Fin n → ℝ) → ComplexGL2)
    (p : (Fin 2 → ℂ) × (Fin n → ℝ)) : ℝ :=
  ‖SourceJets.actedRow g p 0‖ ^ 2 + ‖SourceJets.actedRow g p 1‖ ^ 2

lemma rowSquare_pos {n : ℕ} (g : (Fin n → ℝ) → ComplexGL2)
    (r : Fin 2 → ℂ) (u : Fin n → ℝ) (hr : r ≠ 0) : 0 < rowSquare g (r,u) := by
  have hrow : Matrix.vecMul r (g u : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
    intro h
    apply hr
    apply Matrix.vecMul_injective_of_isUnit (g u).isUnit
    simpa using h
  have hn : 0 ≤ rowSquare g (r,u) := by unfold rowSquare; positivity
  by_contra hp
  have hz : rowSquare g (r,u) = 0 := le_antisymm (le_of_not_gt hp) hn
  apply hrow
  have h0 : SourceJets.actedRow g (r,u) 0 = 0 := by
    apply norm_eq_zero.mp
    unfold rowSquare at hz
    nlinarith [sq_nonneg ‖SourceJets.actedRow g (r,u) 1‖,
      norm_nonneg (SourceJets.actedRow g (r,u) 0)]
  have h1 : SourceJets.actedRow g (r,u) 1 = 0 := by
    apply norm_eq_zero.mp
    unfold rowSquare at hz
    nlinarith [sq_nonneg ‖SourceJets.actedRow g (r,u) 0‖,
      norm_nonneg (SourceJets.actedRow g (r,u) 1)]
  ext i
  fin_cases i
  · simpa [Matrix.vecMul, dotProduct, SourceJets.actedRow] using h0
  · simpa [Matrix.vecMul, dotProduct, SourceJets.actedRow] using h1

noncomputable def logRatio {n : ℕ} (g : (Fin n → ℝ) → ComplexGL2)
    (p : (Fin 2 → ℂ) × (Fin n → ℝ)) : ℝ :=
  Real.log (‖(g p.2 : Matrix (Fin 2) (Fin 2) ℂ).det‖ / rowSquare g p)

lemma logRatio_contDiffOn {n : ℕ} (U : Set (Fin n → ℝ))
    (g : (Fin n → ℝ) → ComplexGL2)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (g u : Matrix (Fin 2) (Fin 2) ℂ)) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (logRatio g) (({r | r ≠ 0}) ×ˢ U) := by
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u => (g u : Matrix (Fin 2) (Fin 2) ℂ).det) U := by
    simp only [Matrix.det_fin_two]
    exact ((scalar_entry_contDiffOn hg 0 0).mul (scalar_entry_contDiffOn hg 1 1)).sub
      ((scalar_entry_contDiffOn hg 0 1).mul (scalar_entry_contDiffOn hg 1 0))
  have hd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin 2 → ℂ) × (Fin n → ℝ) => ‖(g p.2 : Matrix (Fin 2) (Fin 2) ℂ).det‖)
      (({r | r ≠ 0}) ×ˢ U) :=
    (hdet.norm ℂ (fun u _ => Matrix.GeneralLinearGroup.det_ne_zero (g u))).comp
      contDiff_snd.contDiffOn (fun _ hp => hp.2)
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (rowSquare g) (({r | r ≠ 0}) ×ˢ U) :=
    (((SourceJets.actedRow_contDiffOn U g hg 0).norm_sq ℂ).add
      ((SourceJets.actedRow_contDiffOn U g hg 1).norm_sq ℂ)).mono
        (prod_mono (subset_univ _) (Subset.refl _))
  exact (hd.div hb (fun p hp => (rowSquare_pos g p.1 p.2 hp.1).ne')).log
    (fun p hp => (div_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero (g p.2)))
      (rowSquare_pos g p.1 p.2 hp.1)).ne')

def unitRows : Set (Fin 2 → ℂ) := {r | ‖r 0‖ ^ 2 + ‖r 1‖ ^ 2 = 1}

lemma unitRows_compact : IsCompact unitRows := by
  have hc : IsClosed unitRows := isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : Fin 2 → ℂ) 1).of_isClosed_subset hc
  intro r hr
  simp only [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  change ‖r 0‖ ^ 2 + ‖r 1‖ ^ 2 = 1 at hr
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith [norm_nonneg (r 0), norm_nonneg (r 1),
    sq_nonneg ‖r 0‖, sq_nonneg ‖r 1‖]

lemma unitRows_ne_zero {r : Fin 2 → ℂ} (hr : r ∈ unitRows) : r ≠ 0 := by
  intro he
  simp [unitRows, he] at hr

lemma slice_jets_contDiffAt {P E V : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W : Set (P × E)) (hW : IsOpen W) (f : P × E → V)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W) (q : ℕ) (p : P × E) (hp : p ∈ W) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : P × E =>
      iteratedFDeriv ℝ q (fun u => f (p.1,u)) p.2) p := by
  induction q generalizing p with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p
        (hf.contDiffAt (hW.mem_nhds hp))
  | succ q ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : P × E =>
        fderiv ℝ (iteratedFDeriv ℝ q (fun u => f (p.1,u))) p.2) p := by
      exact ((ih (p.1,p.2) hp).comp (p,p.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
        (m := (⊤ : ℕ∞)) contDiffAt_snd (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q+1) => E) V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p hd

abbrev Params := (ℂ × ℝ × ℝ) × (Fin 2 → ℂ)

noncomputable def weight {n : ℕ} (m : ℕ) (g : (Fin n → ℝ) → ComplexGL2)
    (p : Params × (Fin n → ℝ)) : ℂ :=
  (2 * ((p.1.1.2.1 : ℂ) * (logRatio g (p.1.2,p.2) : ℂ) - (p.1.1.2.2 : ℂ))) ^ m *
    Complex.exp (((4 / 3 : ℂ) + 2 * p.1.1.1) * (logRatio g (p.1.2,p.2) : ℂ))

def domain {n : ℕ} (U : Set (Fin n → ℝ)) : Set (Params × (Fin n → ℝ)) :=
  {p | p.1.2 ≠ 0} ∩ (univ ×ˢ U)

lemma domain_open {n : ℕ} (U : Set (Fin n → ℝ)) (hU : IsOpen U) : IsOpen (domain U) :=
  (isOpen_ne.preimage (by fun_prop)).inter (isOpen_univ.prod hU)

lemma weight_contDiffOn {n : ℕ} (m : ℕ) (U : Set (Fin n → ℝ))
    (g : (Fin n → ℝ) → ComplexGL2)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (g u : Matrix (Fin 2) (Fin 2) ℂ)) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (weight m g) (domain U) := by
  have hl : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : Params × (Fin n → ℝ) => (logRatio g (p.1.2,p.2) : ℂ)) (domain U) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (logRatio_contDiffOn U g hg)).comp
      (contDiff_fst.snd.prodMk contDiff_snd).contDiffOn (fun _ hp => ⟨hp.1,hp.2.2⟩)
  unfold weight
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : Params × (Fin n → ℝ) => (p.1.1.2.1 : ℂ)) (domain U) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (by fun_prop)
  have hz : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : Params × (Fin n → ℝ) => (p.1.1.2.2 : ℂ)) (domain U) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (by fun_prop)
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : Params × (Fin n → ℝ) => p.1.1.1) (domain U) := by fun_prop
  exact ((contDiffOn_const.mul ((hb.mul hl).sub hz)).pow m).mul
    (((contDiffOn_const.add (contDiffOn_const.mul hs)).mul hl).cexp)

lemma compact_weight_jets {n : ℕ} (j m : ℕ)
    (U K : Set (Fin n → ℝ)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g : (Fin n → ℝ) → ComplexGL2)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (g u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s : ℂ) (b z : ℝ) (r : Fin 2 → ℂ),
      ‖s‖ ≤ R → b ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 1 → r ∈ unitRows →
      ∀ q ≤ j, ∀ u ∈ K,
        ‖iteratedFDeriv ℝ q (fun v => weight m g (((s,b,z),r),v)) u‖ ≤ A := by
  let T : Set Params := ((Metric.closedBall (0 : ℂ) R ×ˢ Icc (0 : ℝ) 1 ×ˢ
    Icc (0 : ℝ) 1) ×ˢ unitRows)
  have hT : IsCompact T :=
    ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_Icc.prod isCompact_Icc)).prod unitRows_compact
  have hsub : T ×ˢ K ⊆ domain U := by
    intro p hp
    exact ⟨unitRows_ne_zero hp.1.2, ⟨mem_univ _,hKU hp.2⟩⟩
  have hc (q : ℕ) : ContinuousOn (fun p : Params × (Fin n → ℝ) =>
      ‖iteratedFDeriv ℝ q (fun v => weight m g (p.1,v)) p.2‖) (T ×ˢ K) := by
    intro p hp
    exact ((slice_jets_contDiffAt (domain U) (domain_open U hU) (weight m g)
      (weight_contDiffOn m U g hg) q p (hsub hp)).continuousAt.norm).continuousWithinAt
  have hb : BddAbove (⋃ q ∈ Finset.range (j+1),
      (fun p : Params × (Fin n → ℝ) =>
        ‖iteratedFDeriv ℝ q (fun v => weight m g (p.1,v)) p.2‖) '' (T ×ˢ K)) :=
    (Finset.finite_toSet _).bddAbove_biUnion.mpr (fun q _ => (hT.prod hK).bddAbove_image (hc q))
  obtain ⟨A,hA⟩ := hb
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro s b z r hs hb hz hr q hq u hu
  apply le_trans (hA ?_) (le_max_left _ _)
  refine mem_iUnion₂.mpr ⟨q, Finset.mem_range.mpr (by omega), ?_⟩
  refine ⟨(((s,b,z),r),u), ⟨⟨⟨?_,hb,hz⟩,hr⟩,hu⟩,rfl⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using hs

noncomputable def normalizedRow (x : ℂ) : Fin 2 → ℂ :=
  ((Real.sqrt (1 + ‖x‖ ^ 2) : ℂ)⁻¹) • ![1,x]

lemma normalizedRow_mem (x : ℂ) : normalizedRow x ∈ unitRows := by
  have ht : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hd : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr ht
  have hd2 := Real.sq_sqrt ht.le
  change ‖normalizedRow x 0‖ ^ 2 + ‖normalizedRow x 1‖ ^ 2 = 1
  simp only [normalizedRow, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  field_simp
  nlinarith

lemma normalizedRow_log {n : ℕ} (g : (Fin n → ℝ) → ComplexGL2)
    (x : ℂ) (u : Fin n → ℝ) :
    Real.log (ratio (weyl * upperUnipotent x * g u)) =
      logRatio g (normalizedRow x,u) - Real.log (1 + ‖x‖ ^ 2) := by
  have ht : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hd : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr ht
  have hd2 := Real.sq_sqrt ht.le
  have he (i : Fin 2) : SourceJets.actedRow g (normalizedRow x,u) i =
      ((Real.sqrt (1 + ‖x‖ ^ 2) : ℂ)⁻¹) *
        (weyl * upperUnipotent x * g u : Matrix (Fin 2) (Fin 2) ℂ) 1 i := by
    simp [SourceJets.actedRow, normalizedRow, weyl, upperUnipotent,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hb : rowSquare g (normalizedRow x,u) =
      bottomRowNormSq (weyl * upperUnipotent x * g u) / (1 + ‖x‖ ^ 2) := by
    unfold rowSquare bottomRowNormSq
    rw [he 0, he 1]
    simp only [norm_mul, norm_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
      mul_pow, inv_pow, div_pow, Matrix.GeneralLinearGroup.coe_mul, hd2]
    ring
  have hdet : ‖((Matrix.GeneralLinearGroup.det (weyl * upperUnipotent x * g u) : ℂˣ) : ℂ)‖ =
      ‖(g u : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
    change ‖(weyl * upperUnipotent x * g u : Matrix (Fin 2) (Fin 2) ℂ).det‖ = _
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul]
    have hw : (weyl : Matrix (Fin 2) (Fin 2) ℂ).det = -1 := by
      simp [weyl, Matrix.det_fin_two]
    have hx : (upperUnipotent x : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      simp [upperUnipotent, Matrix.det_fin_two]
    rw [hw, hx]
    simp
  have hbp := scalar_bottomRowNormSq_pos (weyl * upperUnipotent x * g u)
  have hdp := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero (g u))
  unfold logRatio ratio
  rw [hdet, hb]
  rw [Real.log_div hdp.ne' (div_pos hbp ht).ne', Real.log_div hbp.ne' ht.ne',
    Real.log_div hdp.ne' hbp.ne']
  ring

lemma weight_factorization {n : ℕ} (m : ℕ) (g : (Fin n → ℝ) → ComplexGL2)
    (s x : ℂ) (u : Fin n → ℝ) :
    (2 * (Real.log (ratio (weyl * upperUnipotent x * g u)) : ℂ)) ^ m *
      Complex.exp (((4 / 3 : ℂ) + 2 * s) *
        (Real.log (ratio (weyl * upperUnipotent x * g u)) : ℂ)) =
    ((1 + Real.log (1 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ m *
      Complex.exp (-((4 / 3 : ℂ) + 2 * s) * (Real.log (1 + ‖x‖ ^ 2) : ℂ)) *
        weight m g (((s, (1 + Real.log (1 + ‖x‖ ^ 2))⁻¹,
          Real.log (1 + ‖x‖ ^ 2) / (1 + Real.log (1 + ‖x‖ ^ 2))), normalizedRow x),u) := by
  have ht : 0 ≤ Real.log (1 + ‖x‖ ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg ‖x‖])
  have hL : (1 + Real.log (1 + ‖x‖ ^ 2) : ℝ) ≠ 0 := by positivity
  have hLc : ((1 + Real.log (1 + ‖x‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [normalizedRow_log]
  unfold weight
  simp only [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_div]
  have hpoly : 2 * ((logRatio g (normalizedRow x,u) : ℂ) -
      (Real.log (1 + ‖x‖ ^ 2) : ℂ)) =
      ((1 + Real.log (1 + ‖x‖ ^ 2) : ℝ) : ℂ) *
        (2 * (((1 + Real.log (1 + ‖x‖ ^ 2) : ℝ) : ℂ)⁻¹ *
          (logRatio g (normalizedRow x,u) : ℂ) -
          (Real.log (1 + ‖x‖ ^ 2) : ℂ) / ((1 + Real.log (1 + ‖x‖ ^ 2) : ℝ) : ℂ))) := by
    field_simp
  rw [hpoly, mul_pow]
  rw [show ((4 / 3 : ℂ) + 2 * s) * ((logRatio g (normalizedRow x,u) : ℂ) -
      (Real.log (1 + ‖x‖ ^ 2) : ℂ)) =
      -((4 / 3 : ℂ) + 2 * s) * (Real.log (1 + ‖x‖ ^ 2) : ℂ) +
      ((4 / 3 : ℂ) + 2 * s) * (logRatio g (normalizedRow x,u) : ℂ) by ring,
    Complex.exp_add]
  ring

lemma factor_norm (m : ℕ) (s x : ℂ) :
    ‖((1 + Real.log (1 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ m *
      Complex.exp (-((4 / 3 : ℂ) + 2 * s) * (Real.log (1 + ‖x‖ ^ 2) : ℂ))‖ =
      (1 + Real.log (1 + ‖x‖ ^ 2)) ^ m * envelope (4 / 3 + 2 * s.re) x := by
  have ht : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hlog : 0 ≤ Real.log (1 + ‖x‖ ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg ‖x‖])
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Complex.norm_exp]
  unfold envelope
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos ht]
  congr 2
  simp
  ring

end ScalarCompactification

theorem compact_scalar_weight_jets (n j m : ℕ)
    (U K : Set (Fin n → ℝ)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g : (Fin n → ℝ) → ComplexGL2)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s x : ℂ), ‖s‖ ≤ R →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun v =>
        (2 * (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) ^ m *
          Complex.exp (((4 / 3 : ℂ) + 2 * s) *
            (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ))) U ∧
      ∀ q ≤ j, ∀ u ∈ K,
        ‖iteratedFDeriv ℝ q (fun v =>
          (2 * (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) ^ m *
            Complex.exp (((4 / 3 : ℂ) + 2 * s) *
              (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ))) u‖ ≤
        A * (1 + Real.log (1 + ‖x‖ ^ 2)) ^ m * envelope (4 / 3 + 2 * s.re) x := by
  obtain ⟨A,hA,hbound⟩ := ScalarCompactification.compact_weight_jets j m U K hU hK hKU g hg R
  refine ⟨A,hA,?_⟩
  intro s x hs
  refine ⟨scalar_weight_contDiffOn m s x hg,?_⟩
  intro q hq u hu
  let t : ℝ := Real.log (1 + ‖x‖ ^ 2)
  have ht : 0 ≤ t := Real.log_nonneg (by nlinarith [sq_nonneg ‖x‖])
  have hL : 0 < 1 + t := by positivity
  have hb : (1+t)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hL.le, inv_le_one_of_one_le₀ (by linarith)⟩
  have hz : t / (1+t) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht hL.le, (div_le_one hL).mpr (by linarith)⟩
  let p : ScalarCompactification.Params :=
    ((s,(1+t)⁻¹,t/(1+t)),ScalarCompactification.normalizedRow x)
  let f : (Fin n → ℝ) → ℂ := fun v => ScalarCompactification.weight m g (p,v)
  let c : ℂ := ((1+t : ℝ) : ℂ)^m *
    Complex.exp (-((4/3 : ℂ) + 2*s) * (t : ℂ))
  have hp : (p,u) ∈ ScalarCompactification.domain U :=
    ⟨ScalarCompactification.unitRows_ne_zero (ScalarCompactification.normalizedRow_mem x),
      ⟨Set.mem_univ _,hKU hu⟩⟩
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) f u :=
    ((ScalarCompactification.weight_contDiffOn m U g hg).contDiffAt
      ((ScalarCompactification.domain_open U hU).mem_nhds hp)).comp u
      (contDiffAt_const.prodMk contDiffAt_id)
  have he : (fun v =>
      (2 * (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) ^ m *
        Complex.exp (((4 / 3 : ℂ) + 2 * s) *
          (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ))) = c • f := by
    funext v
    exact ScalarCompactification.weight_factorization m g s x v
  rw [he, iteratedFDeriv_const_smul_apply (hf.of_le (by simp)), norm_smul]
  have hbf : ‖iteratedFDeriv ℝ q f u‖ ≤ A :=
    hbound s ((1+t)⁻¹) (t/(1+t)) (ScalarCompactification.normalizedRow x)
      hs hb hz (ScalarCompactification.normalizedRow_mem x) q hq u hu
  apply (mul_le_mul_of_nonneg_left hbf (norm_nonneg c)).trans_eq
  rw [show ‖c‖ = (1+t)^m * envelope (4/3+2*s.re) x from
    ScalarCompactification.factor_norm m s x]
  dsimp [t]
  ring

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted
