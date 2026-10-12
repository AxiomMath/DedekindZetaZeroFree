module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.CompactProjectorWords

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open scoped Matrix

theorem native_harmonic_finite_words
    (ℓ : ℕ) (f : PrincipalSeries positiveParameter)
    (hf : f ∈ KPCplxIntertwinerEigenvalues.harmonicKType positiveParameter ℓ) :
    ∃ n : ℕ, ∃ w : Fin n → KPContHolomorphicKGeneration.RealLieWord,
      ∃ c : Fin n → ℂ, ∀ a : ComplexGL2,
        f a = ∑ j, c j * KPContHolomorphicKGeneration.complexSphericalWord (w j) 0 a := by
  classical
  obtain ⟨D, hD⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (RepresentationTheory.KPContHolomorphicKGenerationProve.harmonic_mem_raw_spherical_span ℓ f hf)
  let e := D.support.equivFin.symm
  refine ⟨D.support.card, fun j => (e j).val, fun j => D (e j).val, ?_⟩
  intro a
  have he := congrFun hD a
  change (∑ w ∈ D.support, D w •
    RepresentationTheory.KPContHolomorphicKGenerationProve.rawWord w
      (sphericalSection positiveParameter : ComplexGL2 → ℂ)) a = f a at he
  rw [← he]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort D.support]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  have hword : ∀ w : KPContHolomorphicKGeneration.RealLieWord,
      (KPContHolomorphicKGeneration.rightWord positiveParameter w
        (sphericalSection positiveParameter) : ComplexGL2 → ℂ) =
      RepresentationTheory.KPContHolomorphicKGenerationProve.rawWord w
        (sphericalSection positiveParameter : ComplexGL2 → ℂ) := by
    intro w
    have hall : ∀ (h : PrincipalSeries positiveParameter),
        (KPContHolomorphicKGeneration.rightWord positiveParameter w h : ComplexGL2 → ℂ) =
        RepresentationTheory.KPContHolomorphicKGenerationProve.rawWord w (h : ComplexGL2 → ℂ) := by
      induction w with
      | nil => intro h; rfl
      | cons X w ih =>
        intro h
        change KPContHolomorphicKGeneration.rightLieFunction X
          (KPContHolomorphicKGeneration.rightWord positiveParameter w h : ComplexGL2 → ℂ) = _
        rw [ih h]
        rfl
    exact hall _
  rw [KPContHolomorphicKGeneration.complexSphericalWord_zero]
  exact congrArg (fun h : ComplexGL2 → ℂ => D (e j).val * h a) (hword (e j).val).symm

section PolynomialWords
open scoped ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

 abbrev WordMat := KPContHolomorphicKGeneration.Mat
 def wordDomain : Set WordMat := {g | g.det ≠ 0}
private theorem wordDomain_open : IsOpen wordDomain := by
  have hc : Continuous (fun g : WordMat => g.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  exact isOpen_ne_fun hc continuous_const
 def wordPhase (g : WordMat) : ℂ :=
  (Real.log (‖g.det‖ / (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2)) : ℂ)
 def wordExponent : Polynomial ℂ :=
  Polynomial.C (1 + 2 * (positiveParameter : ℂ)) + Polynomial.C 2 * Polynomial.X
private theorem word_row_pos (g : WordMat) (hg : g ∈ wordDomain) :
    0 < ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 := by
  by_contra h
  push Not at h
  have h10 : g 1 0 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (g 1 0), norm_nonneg (g 1 1)])
  have h11 : g 1 1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (g 1 0), norm_nonneg (g 1 1)])
  exact hg (by rw [Matrix.det_fin_two, h10, h11]; ring)
private theorem wordPhase_smooth : ContDiffOn ℝ ∞ wordPhase wordDomain := by
  have hd : ContDiff ℝ ∞ (fun g : WordMat => g.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  have hr : ContDiff ℝ ∞ (fun g : WordMat => ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) := by
    apply ContDiff.add
    · exact (by fun_prop : ContDiff ℝ ∞ (fun g : WordMat => g 1 0)).norm_sq (𝕜 := ℂ)
    · exact (by fun_prop : ContDiff ℝ ∞ (fun g : WordMat => g 1 1)).norm_sq (𝕜 := ℂ)
  have hl := ((hd.contDiffOn.norm ℂ (fun g hg => hg)).div hr.contDiffOn
    (fun g hg => ne_of_gt (word_row_pos g hg))).log
    (fun g hg => ne_of_gt (div_pos (norm_pos_iff.mpr hg) (word_row_pos g hg)))
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hl
 def wordDirection (X : WordMat) (h : WordMat → ℂ) (g : WordMat) : ℂ :=
  fderiv ℝ h g (g * X)
private theorem wordDirection_smooth (X : WordMat) {h : WordMat → ℂ}
    (hh : ContDiffOn ℝ ∞ h wordDomain) :
    ContDiffOn ℝ ∞ (wordDirection X h) wordDomain := by
  apply (hh.fderiv_of_isOpen wordDomain_open (m := ∞) (by simp)).clm_apply
  have hv : ContDiff ℝ ∞ (fun g : WordMat => g * X) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    fun_prop
  exact hv.contDiffOn
 def wordAtom (p : Polynomial ℂ) (h : WordMat → ℂ) (s : ℂ) (g : WordMat) : ℂ :=
  Complex.exp (wordExponent.eval s * wordPhase g) * p.eval s * h g
 inductive PolynomialSeparated : (ℂ → WordMat → ℂ) → Prop
  | atom (p : Polynomial ℂ) (h : WordMat → ℂ) (hh : ContDiffOn ℝ ∞ h wordDomain) :
      PolynomialSeparated (wordAtom p h)
  | add {f g} : PolynomialSeparated f → PolynomialSeparated g →
      PolynomialSeparated (fun s a => f s a + g s a)
private theorem polynomialSeparated_smooth {H} (hH : PolynomialSeparated H) (s : ℂ) :
    ContDiffOn ℝ ∞ (H s) wordDomain := by
  induction hH with
  | atom p h hh =>
    exact ((contDiffOn_const.mul wordPhase_smooth).cexp.mul contDiffOn_const).mul hh
  | add hf hg ihf ihg => exact ihf.add ihg
private theorem polynomialSeparated_derivative {H} (hH : PolynomialSeparated H) (X : WordMat) :
    ∃ H', PolynomialSeparated H' ∧ ∀ s g, g ∈ wordDomain →
      H' s g = wordDirection X (H s) g := by
  induction hH with
  | atom p h hh =>
    refine ⟨fun s g => wordAtom (p * wordExponent)
      (fun g => h g * wordDirection X wordPhase g) s g + wordAtom p (wordDirection X h) s g,
      PolynomialSeparated.add (PolynomialSeparated.atom _ _ (hh.mul (wordDirection_smooth X wordPhase_smooth)))
        (PolynomialSeparated.atom _ _ (wordDirection_smooth X hh)), ?_⟩
    intro s g hg
    have hp := (wordPhase_smooth.contDiffAt (wordDomain_open.mem_nhds hg)).differentiableAt (by simp)
    have hd := (hh.contDiffAt (wordDomain_open.mem_nhds hg)).differentiableAt (by simp)
    have he := (((hp.hasFDerivAt.const_mul (wordExponent.eval s)).cexp).mul_const (p.eval s)).mul hd.hasFDerivAt
    change _ = fderiv ℝ (((fun a => Complex.exp (wordExponent.eval s * wordPhase a) * p.eval s) * h)) g (g * X)
    rw [he.fderiv]
    simp [wordAtom, Polynomial.eval_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, wordDirection]
    ring
  | @add H G hf hG ihf ihg =>
    obtain ⟨H', hH', eH⟩ := ihf
    obtain ⟨G', hG', eG⟩ := ihg
    refine ⟨fun s g => H' s g + G' s g, PolynomialSeparated.add hH' hG', ?_⟩
    intro s g hg
    change H' s g + G' s g = wordDirection X (fun a => H s a + G s a) g
    rw [eH s g hg, eG s g hg]
    have hdH := ((polynomialSeparated_smooth hf s).contDiffAt (wordDomain_open.mem_nhds hg)).differentiableAt (by simp)
    have hdG := ((polynomialSeparated_smooth hG s).contDiffAt (wordDomain_open.mem_nhds hg)).differentiableAt (by simp)
    simp only [wordDirection, fderiv_fun_add hdH hdG, ContinuousLinearMap.add_apply]

private theorem polynomialSeparated_finite {H} (hH : PolynomialSeparated H) :
    ∃ (n : ℕ) (p : Fin n → Polynomial ℂ) (h : Fin n → WordMat → ℂ),
      (∀ j, ContDiffOn ℝ ∞ (h j) wordDomain) ∧
      ∀ s g, H s g = Complex.exp (wordExponent.eval s * wordPhase g) *
        ∑ j, (p j).eval s * h j g := by
  induction hH with
  | atom p h hh =>
    exact ⟨1, fun _ => p, fun _ => h, fun _ => hh, by
      intro s g
      simp [Fin.sum_univ_one, wordAtom, mul_assoc]⟩
  | @add H G hf hg ihf ihg =>
    obtain ⟨n, p, h, hh, he⟩ := ihf
    obtain ⟨m, q, k, hk, ke⟩ := ihg
    refine ⟨n + m, Fin.append p q, Fin.append h k, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hh i
      · simpa using hk i
    · intro s g
      change H s g + G s g = _
      rw [he, ke, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, mul_add]

private theorem polynomial_word_separated (w : KPContHolomorphicKGeneration.RealLieWord) :
    ∃ H, PolynomialSeparated H ∧ ∀ s a,
      KPContHolomorphicKGeneration.complexSphericalWord w s a = H s (a : WordMat) := by
  induction w with
  | nil =>
    refine ⟨wordAtom 1 (fun _ => 1), PolynomialSeparated.atom _ _ contDiffOn_const, ?_⟩
    intro s a
    simp only [KPContHolomorphicKGeneration.complexSphericalWord, List.foldr_nil,
      KPContHolomorphicKGeneration.complexSpherical, wordAtom, wordExponent,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_one, mul_one, wordPhase, bottomRowNormSq]
    congr 1
    congr 1
    ring
  | cons X w ih =>
    obtain ⟨H, hH, he⟩ := ih
    obtain ⟨H', hH', hd⟩ := polynomialSeparated_derivative hH X
    refine ⟨H', hH', ?_⟩
    intro s a
    have heq : matrixFunction (KPContHolomorphicKGeneration.complexSphericalWord w s) =ᶠ[nhds (a : WordMat)] H s := by
      filter_upwards [wordDomain_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero a)] with g hg
      unfold matrixFunction
      change g.det ≠ 0 at hg
      rw [dif_pos hg]
      exact he s (Matrix.GeneralLinearGroup.mkOfDetNeZero g hg)
    change fderiv ℝ (matrixFunction (KPContHolomorphicKGeneration.complexSphericalWord w s))
      (a : WordMat) ((a : WordMat) * X) = _
    rw [heq.fderiv_eq]
    exact (hd s (a : WordMat) (Matrix.GeneralLinearGroup.det_ne_zero a)).symm

theorem sphericalWord_polynomial_smooth_factors
    (w : KPContHolomorphicKGeneration.RealLieWord) :
    ∃ (n : ℕ) (p : Fin n → Polynomial ℂ)
      (h : Fin n → KPContHolomorphicKGeneration.Mat → ℂ),
      (∀ j, ContDiffOn ℝ ∞ (h j) {g | g.det ≠ 0}) ∧
      ∀ (s : ℂ) (a : ComplexGL2),
        KPContHolomorphicKGeneration.complexSphericalWord w s a =
          KPContHolomorphicKGeneration.complexSpherical s a *
            ∑ j, (p j).eval s * h j (a : KPContHolomorphicKGeneration.Mat) := by
  obtain ⟨H, hH, he⟩ := polynomial_word_separated w
  obtain ⟨n, p, h, hh, hrep⟩ := polynomialSeparated_finite hH
  refine ⟨n, p, h, hh, ?_⟩
  intro s a
  rw [he, hrep]
  have heq : Complex.exp (wordExponent.eval s * wordPhase (a : WordMat)) =
      KPContHolomorphicKGeneration.complexSpherical s a := by
    simp only [wordExponent, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X,
      KPContHolomorphicKGeneration.complexSpherical, wordPhase, bottomRowNormSq]
    congr 1
    congr 1
    ring
  rw [heq]

end PolynomialWords

private theorem entire_det {m : ℕ} (A : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun s => A s i j) Set.univ) :
    AnalyticOnNhd ℂ (fun s => (A s).det) Set.univ := by
  simp only [Matrix.det_apply']
  apply Finset.analyticOnNhd_fun_sum
  intro σ hσ
  exact analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ (fun i hi => hA (σ i) i))

private theorem entire_adjugate {m : ℕ} (A : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun s => A s i j) Set.univ) (i j : Fin m) :
    AnalyticOnNhd ℂ (fun s => (A s).adjugate i j) Set.univ := by
  simp only [Matrix.adjugate_apply]
  apply entire_det
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_apply]
    exact analyticOnNhd_const
  · simpa [Matrix.updateRow_apply, ha] using hA a b

theorem normalized_adjugate_clearing {m : ℕ}
    (A : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun s => A s i j) Set.univ)
    (h0 : (A 0).det ≠ 0) (v : Fin m → ℂ) :
    ∃ (q : ℂ → ℂ) (b : Fin m → ℂ → ℂ),
      AnalyticOnNhd ℂ q Set.univ ∧ q 0 = 1 ∧
      (∀ j, AnalyticOnNhd ℂ (b j) Set.univ) ∧
      ∀ s i, ∑ j, A s i j * b j s = q s * v i := by
  classical
  let d := (A 0).det
  let q := fun s => (A s).det / d
  let b := fun j s => ((A s).adjugate *ᵥ v) j / d
  refine ⟨q, b, (entire_det A hA).div_const, div_self h0, ?_, ?_⟩
  · intro j
    exact (Finset.analyticOnNhd_fun_sum _ (fun k hk =>
      (entire_adjugate A hA j k).mul analyticOnNhd_const)).div_const
  · intro s i
    have h := congrArg (fun w : Fin m → ℂ => w i)
      (show A s *ᵥ ((A s).adjugate *ᵥ v) = (A s).det • v by
        rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
          Matrix.one_mulVec])
    change (∑ j, A s i j * (((A s).adjugate *ᵥ v) j / d)) =
      ((A s).det / d) * v i
    calc
      _ = (∑ j, A s i j * ((A s).adjugate *ᵥ v) j) / d := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        exact (mul_div_assoc _ _ _).symm
      _ = ((A s).det * v i) / d := congrArg (fun z : ℂ => z / d) h
      _ = _ := by ring

section HarmonicClearingAssembly
open KPCplxIntertwinerEigenvalues KPCplxHarmonicExtraction MeasureTheory
open scoped Matrix ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

 abbrev HS (ℓ : ℕ) := harmonicKType positiveParameter ℓ
 def cProj (μ : Measure ComplexSU2) (hp : IsProbabilityMeasure μ) (ℓ : ℕ)
    (h : PrincipalSeries positiveParameter) : PrincipalSeries positiveParameter :=
  (characterAverage_section_exists positiveParameter μ hp ℓ h).choose
private theorem cProj_eval (μ : Measure ComplexSU2) (hp : IsProbabilityMeasure μ) (ℓ : ℕ)
    (h : PrincipalSeries positiveParameter) (g : ComplexGL2) :
    cProj μ hp ℓ h g = characterAverage positiveParameter μ ℓ h g :=
  (characterAverage_section_exists positiveParameter μ hp ℓ h).choose_spec g
private theorem cProj_mem (μ : Measure ComplexSU2) (hhaar : μ.IsHaarMeasure)
    (hp : IsProbabilityMeasure μ) (ℓ : ℕ) (h : PrincipalSeries positiveParameter) :
    cProj μ hp ℓ h ∈ HS ℓ := by
  obtain ⟨p,hp',he⟩ := characterAverage_compact_polynomial positiveParameter μ hhaar hp ℓ h
  refine ⟨p,hp',?_⟩
  ext k
  exact (he k).trans (cProj_eval μ hp ℓ h (complexSU2Embedding k)).symm
private theorem cProj_self_compact (μ : Measure ComplexSU2) (hhaar : μ.IsHaarMeasure)
    (hp : IsProbabilityMeasure μ) (ℓ : ℕ) (h : PrincipalSeries positiveParameter)
    (hh : h ∈ HS ℓ) (k : ComplexSU2) :
    cProj μ hp ℓ h (complexSU2Embedding k) = h (complexSU2Embedding k) := by
  obtain ⟨p,hp',he⟩ := hh
  have he' := congrFun he
  rw [cProj_eval, characterAverage_formula]
  have e1 : (fun t : ComplexSU2 => star (su2HarmonicCharacter ℓ t) *
      h (complexSU2Embedding k * complexSU2Embedding t)) =
      (fun t => star (su2HarmonicCharacter ℓ t) * polynomialCompactRestriction p (k*t)) := by
    funext t
    rw [← complexSU2Embedding.map_mul]
    exact congrArg (star (su2HarmonicCharacter ℓ t) * ·) (he' (k*t)).symm
  rw [e1, CompactPolynomial.harmonic_character_projection_diagonal μ hhaar hp ℓ p hp' k]
  exact he' k
private theorem cProj_sum_eval (μ : Measure ComplexSU2) (hp : IsProbabilityMeasure μ)
    (ℓ : ℕ) {ι : Type} [Fintype ι] (h : ι → PrincipalSeries positiveParameter)
    (c : ι → ℂ) (g : ComplexGL2) :
    characterAverage positiveParameter μ ℓ (∑ j, c j • h j) g =
      ∑ j, c j * cProj μ hp ℓ (h j) g := by
  simp only [characterAverage_formula, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have hint : ∀ j : ι, Integrable (fun k => c j *
      (star (su2HarmonicCharacter ℓ k) * h j (g * complexSU2Embedding k))) μ := by
    intro j
    exact (characterAverage_integrable positiveParameter μ hp ℓ (h j) g).const_mul _
  have he : (fun k : ComplexSU2 => ∑ j, star (su2HarmonicCharacter ℓ k) *
      (c j * h j (g * complexSU2Embedding k))) =
      (fun k => ∑ j, c j * (star (su2HarmonicCharacter ℓ k) * h j (g * complexSU2Embedding k))) := by
    funext k; apply Finset.sum_congr rfl; intro j hj; ring
  rw [he, integral_finsetSum _ (fun j _ => hint j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, cProj_eval, characterAverage_formula]
  ring
 def tw (s : ℂ) (g : ComplexGL2) : ℂ :=
  Complex.exp (2 * s * (Real.log (sphericalRatio g) : ℂ))

 theorem entire_of_real {f h : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hh : AnalyticOnNhd ℂ h Set.univ)
    (he : ∀ t : ℝ, f t = h t) : f = h := by
  have hc : (0 : ℂ) ∈ closure ({z | f z = h z} \ {0}) := by
    apply mem_closure_of_tendsto
      (Complex.continuous_ofReal.tendsto 0 |>.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    apply Filter.Eventually.of_forall
    intro n
    refine ⟨he _, ?_⟩
    simp only [Set.mem_singleton_iff, Function.comp_apply, Complex.ofReal_eq_zero]
    positivity
  exact funext (fun z => hf.eqOn_of_preconnected_of_mem_closure hh
    isPreconnected_univ (Set.mem_univ 0) hc (Set.mem_univ z))
private theorem clear_ratio_pos (g : ComplexGL2) : 0 < sphericalRatio g := by
  have hb := RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.rowB_pos g
  exact div_pos (norm_pos_iff.mpr (Units.ne_zero _)) hb
private theorem clear_spherical_real (t : ℝ) (g : ComplexGL2) :
    KPContHolomorphicKGeneration.complexSpherical t g = sphericalSection (positiveParameter + t) g := by
  change Complex.exp (_ * (Real.log (sphericalRatio g) : ℂ)) =
    ((sphericalRatio g ^ (1 + 2 * (positiveParameter + t)) : ℝ) : ℂ)
  rw [Real.rpow_def_of_pos (clear_ratio_pos g), Complex.ofReal_exp]
  congr 1
  push_cast
  ring
private theorem clear_word_real (w : KPContHolomorphicKGeneration.RealLieWord) (t : ℝ) (g : ComplexGL2) :
    KPContHolomorphicKGeneration.complexSphericalWord w t g =
      KPContHolomorphicKGeneration.rightWord (positiveParameter + t) w
        (sphericalSection (positiveParameter + t)) g := by
  have hw (f : PrincipalSeries (positiveParameter + t)) :
      (KPContHolomorphicKGeneration.rightWord (positiveParameter + t) w f : ComplexGL2 → ℂ) =
        w.foldr (fun X h => KPContHolomorphicKGeneration.rightLieFunction X h) (f : ComplexGL2 → ℂ) := by
    induction w with
    | nil => rfl
    | cons X w ih =>
      change KPContHolomorphicKGeneration.rightLieFunction X
        ↑(KPContHolomorphicKGeneration.rightWord (positiveParameter + t) w f) = _
      rw [ih]; rfl
  unfold KPContHolomorphicKGeneration.complexSphericalWord
  rw [show KPContHolomorphicKGeneration.complexSpherical (t : ℂ) =
    (sphericalSection (positiveParameter + t) : ComplexGL2 → ℂ) from funext (clear_spherical_real t)]
  exact congrFun (hw _).symm g
private theorem clear_word_factor (w : KPContHolomorphicKGeneration.RealLieWord) (s : ℂ) (g : ComplexGL2)
    (a d : ℂˣ) (b : ℂ) (k : ComplexSU2)
    (hg : g = upperTriangular a d b * complexSU2Embedding k) :
    KPContHolomorphicKGeneration.complexSphericalWord w s g =
      KPContHolomorphicKGeneration.complexSpherical s g *
        KPContHolomorphicKGeneration.complexSphericalWord w s (complexSU2Embedding k) := by
  have hr : ∀ t : ℝ, KPContHolomorphicKGeneration.complexSphericalWord w t g =
      KPContHolomorphicKGeneration.complexSpherical t g *
        KPContHolomorphicKGeneration.complexSphericalWord w t (complexSU2Embedding k) := by
    intro t
    rw [clear_word_real, clear_word_real, hg,
      (KPContHolomorphicKGeneration.rightWord (positiveParameter + t) w
        (sphericalSection (positiveParameter + t))).property.1]
    rw [clear_spherical_real, (sphericalSection (positiveParameter + t)).property.1]
    rw [RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.spherical_compact,
      mul_one]
  exact congrFun (entire_of_real (KPContHolomorphicKGeneration.complexSphericalWord_holomorphic w g)
    ((KPContHolomorphicKGeneration.complexSphericalWord_holomorphic [] g).mul
      (KPContHolomorphicKGeneration.complexSphericalWord_holomorphic w (complexSU2Embedding k))) hr) s
private theorem clear_section_factor (h : PrincipalSeries positiveParameter) (g : ComplexGL2)
    (a d : ℂˣ) (b : ℂ) (k : ComplexSU2)
    (hg : g = upperTriangular a d b * complexSU2Embedding k) :
    h g = sphericalSection positiveParameter g * h (complexSU2Embedding k) := by
  rw [hg, h.property.1, (sphericalSection positiveParameter).property.1,
    RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.spherical_compact, mul_one]
private theorem clear_spherical_tw (s : ℂ) (g : ComplexGL2) :
    KPContHolomorphicKGeneration.complexSpherical s g = tw s g * sphericalSection positiveParameter g := by
  rw [← KPContHolomorphicKGeneration.complexSpherical_zero]
  unfold KPContHolomorphicKGeneration.complexSpherical tw sphericalRatio
  rw [← Complex.exp_add]
  congr 1 <;> ring
private theorem compact_to_global {ι : Type} [Fintype ι]
    (s : ℂ) (h : PrincipalSeries positiveParameter)
    (w : ι → KPContHolomorphicKGeneration.RealLieWord) (c : ι → ℂ)
    (he : ∀ k, h (complexSU2Embedding k) = ∑ j, c j *
      KPContHolomorphicKGeneration.complexSphericalWord (w j) s (complexSU2Embedding k)) :
    ∀ g, tw s g * h g = ∑ j, c j * KPContHolomorphicKGeneration.complexSphericalWord (w j) s g := by
  intro g
  obtain ⟨a,d,b,hg⟩ := RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2_factor g
  let k := RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2 g
  rw [clear_section_factor h g a d b k hg, ← mul_assoc, ← clear_spherical_tw, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [clear_word_factor (w j) s g a d b k hg]
  ring

private theorem projected_word_polynomial (μ : Measure ComplexSU2) (hhaar : μ.IsHaarMeasure)
    (hp : IsProbabilityMeasure μ) (ℓ : ℕ) (w : KPContHolomorphicKGeneration.RealLieWord) :
    ∃ (n m : ℕ) (v : Fin n → KPContHolomorphicKGeneration.RealLieWord) (c : Fin n → ℂ)
      (p : Fin m → Polynomial ℂ) (h : Fin m → HS ℓ),
      (∀ s g, tw s g * (∑ r, (p r).eval s • (h r : PrincipalSeries positiveParameter)) g =
        ∑ j, c j * KPContHolomorphicKGeneration.complexSphericalWord (v j) s g) ∧
      ∀ k, (∑ r, (p r).eval 0 • (h r : PrincipalSeries positiveParameter)) (complexSU2Embedding k) =
        characterAverage positiveParameter μ ℓ
          (KPContHolomorphicKGeneration.rightWord positiveParameter w (sphericalSection positiveParameter))
          (complexSU2Embedding k) := by
  classical
  letI := hhaar
  obtain ⟨n,v,c,ev⟩ := sphericalWord_character_projector_words μ hp.measure_univ ℓ w
  obtain ⟨N,m,h,p,hh,eh⟩ := sphericalWord_polynomial_harmonic_band w
  let u : Fin m → HS ℓ := fun r => ⟨cProj μ hp ℓ (h r), cProj_mem μ hhaar hp ℓ (h r)⟩
  have ec (s : ℂ) (k : ComplexSU2) :
      (∑ r, (p r).eval s • (u r : PrincipalSeries positiveParameter)) (complexSU2Embedding k) =
        ∑ j, c j * KPContHolomorphicKGeneration.complexSphericalWord (v j) s (complexSU2Embedding k) := by
    rw [← ev]
    have ee : (fun t : ComplexSU2 => star (su2HarmonicCharacter ℓ t) *
        KPContHolomorphicKGeneration.complexSphericalWord w s (complexSU2Embedding k * complexSU2Embedding t)) =
        (fun t => star (su2HarmonicCharacter ℓ t) *
          (∑ r, (p r).eval s • h r) (complexSU2Embedding k * complexSU2Embedding t)) := by
      funext t
      rw [← complexSU2Embedding.map_mul, eh]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [ee]
    have eavg := cProj_sum_eval μ hp ℓ h (fun r => (p r).eval s) (complexSU2Embedding k)
    rw [characterAverage_formula] at eavg
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at eavg
    rw [eavg]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u]
  refine ⟨n,m,v,c,p,u,?_,?_⟩
  · intro s
    exact compact_to_global s _ v c (ec s)
  · intro k
    rw [ec, ← ev]
    rw [characterAverage_formula]
    push_cast
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [KPContHolomorphicKGeneration.complexSphericalWord_zero]

private theorem harmonic_polynomial_word_family (μ : Measure ComplexSU2) (hhaar : μ.IsHaarMeasure)
    (hp : IsProbabilityMeasure μ) (ℓ : ℕ) (f : HS ℓ) :
    ∃ (n m : ℕ) (v : Fin n → KPContHolomorphicKGeneration.RealLieWord)
      (c : Fin n → Polynomial ℂ) (p : Fin m → Polynomial ℂ) (h : Fin m → HS ℓ),
      (∀ s g, tw s g * (∑ r, (p r).eval s • (h r : PrincipalSeries positiveParameter)) g =
        ∑ j, (c j).eval s * KPContHolomorphicKGeneration.complexSphericalWord (v j) s g) ∧
      (∑ r, (p r).eval 0 • h r) = f := by
  classical
  obtain ⟨t,w,d,ew⟩ := native_harmonic_finite_words ℓ f f.property
  choose n m v c p h eg e0 using (fun j => projected_word_polynomial μ hhaar hp ℓ (w j))
  let I := (j : Fin t) × Fin (n j)
  let J := (j : Fin t) × Fin (m j)
  let ei : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ej : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card I,Fintype.card J,fun j => v (ei j).1 (ei j).2,
    fun j => Polynomial.C (d (ei j).1 * c (ei j).1 (ei j).2),
    fun r => Polynomial.C (d (ej r).1) * p (ej r).1 (ej r).2,
    fun r => h (ej r).1 (ej r).2, ?_, ?_⟩
  · intro s g
    simp only [Polynomial.eval_C, Polynomial.eval_mul, Submodule.coe_sum,
      Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [ei.sum_comp (fun j : I => d j.1 * c j.1 j.2 *
      KPContHolomorphicKGeneration.complexSphericalWord (v j.1 j.2) s g),
      ej.sum_comp (fun r : J => d r.1 * (p r.1 r.2).eval s * (h r.1 r.2 : PrincipalSeries positiveParameter) g),
      Fintype.sum_sigma, Fintype.sum_sigma]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have he := eg j s g
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at he
    calc
      ∑ r, tw s g * (d j * (p j r).eval s * (h j r : PrincipalSeries positiveParameter) g) =
          d j * (tw s g * ∑ r, (p j r).eval s * (h j r : PrincipalSeries positiveParameter) g) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r hr; ring
      _ = d j * ∑ r, c j r * KPContHolomorphicKGeneration.complexSphericalWord (v j r) s g := by rw [he]
      _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r hr; ring
  · apply Subtype.ext
    apply compactRestriction_injective positiveParameter
    ext k
    change ((∑ r, (Polynomial.C (d (ej r).1) * p (ej r).1 (ej r).2).eval 0 •
      h (ej r).1 (ej r).2 : HS ℓ) : PrincipalSeries positiveParameter) (complexSU2Embedding k) = _
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C]
    rw [ej.sum_comp (fun r : J => d r.1 * (p r.1 r.2).eval 0 *
      (h r.1 r.2 : PrincipalSeries positiveParameter) (complexSU2Embedding k)), Fintype.sum_sigma]
    have hp0 (j : Fin t) := e0 j k
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at hp0
    have eqsum : (∑ j, d j * ∑ r, (p j r).eval 0 * (h j r : PrincipalSeries positiveParameter) (complexSU2Embedding k)) =
        ∑ j, d j * characterAverage positiveParameter μ ℓ
          (KPContHolomorphicKGeneration.rightWord positiveParameter (w j) (sphericalSection positiveParameter))
          (complexSU2Embedding k) := by simp_rw [hp0]
    have hnative : (∑ j, d j • KPContHolomorphicKGeneration.rightWord positiveParameter (w j)
        (sphericalSection positiveParameter)) = (f : PrincipalSeries positiveParameter) := by
      apply Subtype.ext
      funext g
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [ew]
      simp_rw [KPContHolomorphicKGeneration.complexSphericalWord_zero]
    have hsum := cProj_sum_eval μ hp ℓ
      (fun j => KPContHolomorphicKGeneration.rightWord positiveParameter (w j) (sphericalSection positiveParameter)) d
      (complexSU2Embedding k)
    rw [hnative] at hsum
    simp_rw [cProj_eval] at hsum
    have hself := cProj_self_compact μ hhaar hp ℓ f f.property k
    rw [cProj_eval] at hself
    change _ = (f : PrincipalSeries positiveParameter) (complexSU2Embedding k)
    calc
      _ = ∑ j, d j * ∑ r, (p j r).eval 0 * (h j r : PrincipalSeries positiveParameter) (complexSU2Embedding k) := by
        apply Finset.sum_congr rfl; intro j hj; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r hr; ring
      _ = _ := eqsum
      _ = _ := hsum.symm.trans hself

private theorem harmonic_clearing_assembly (ℓ : ℕ) (f : HS ℓ) :
    ∃ (n : ℕ) (w : Fin n → KPContHolomorphicKGeneration.RealLieWord)
      (q : ℂ → ℂ) (b : Fin n → ℂ → ℂ),
      AnalyticOnNhd ℂ q Set.univ ∧ q 0 = 1 ∧
      (∀ j, AnalyticOnNhd ℂ (b j) Set.univ) ∧
      ∀ s g, q s * tw s g * (f : PrincipalSeries positiveParameter) g =
        ∑ j, b j s * KPContHolomorphicKGeneration.complexSphericalWord (w j) s g := by
  classical
  obtain ⟨μ,hhaar,hprob⟩ := exists_su2_probability_haar
  letI : Module.Finite ℂ (HS ℓ) := KPCplxHarmonicIntertwinerSpectrum.harmonicKType_finite positiveParameter ℓ
  letI : Module.Free ℂ (HS ℓ) := Module.Free.of_divisionRing ℂ (HS ℓ)
  let B := Module.finBasis ℂ (HS ℓ)
  let d := Module.finrank ℂ (HS ℓ)
  choose n m v c p h eg e0 using (fun j : Fin d => harmonic_polynomial_word_family μ hhaar hprob ℓ (B j))
  let H (j : Fin d) (s : ℂ) : HS ℓ := ∑ r, (p j r).eval s • h j r
  have H0 (j : Fin d) : H j 0 = B j := e0 j
  let A (s : ℂ) : Matrix (Fin d) (Fin d) ℂ := fun i j => B.equivFun (H j s) i
  have Aentire : ∀ i j, AnalyticOnNhd ℂ (fun s => A s i j) Set.univ := by
    intro i j
    change AnalyticOnNhd ℂ (fun s => B.equivFun (∑ r, (p j r).eval s • h j r) i) Set.univ
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.analyticOnNhd_fun_sum
    intro r hr
    exact (AnalyticOnNhd.eval_polynomial (p j r)).mul analyticOnNhd_const
  have A0 : A 0 = 1 := by
    ext i j
    simp only [A,H0,Module.Basis.equivFun_apply,Module.Basis.repr_self,Matrix.one_apply]
    simp [Finsupp.single_apply,eq_comm]
  obtain ⟨q,b,hq,q0,hb,eb⟩ := normalized_adjugate_clearing A Aentire
    (by rw [A0,Matrix.det_one]; exact one_ne_zero) (B.equivFun f)
  have eH (s : ℂ) : ∑ j, b j s • H j s = q s • f := by
    apply B.equivFun.injective
    ext i
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    have he := eb s i
    change (∑ j, b j s * A s i j) = q s * B.equivFun f i
    simpa only [mul_comm] using he
  let I := (j : Fin d) × Fin (n j)
  let ei : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j => v (ei j).1 (ei j).2, q,
    fun j s => b (ei j).1 s * (c (ei j).1 (ei j).2).eval s, hq,q0,?_,?_⟩
  · intro j
    exact (hb (ei j).1).mul (AnalyticOnNhd.eval_polynomial (c (ei j).1 (ei j).2))
  · intro s g
    have ef := congrArg (fun h : HS ℓ => (h : PrincipalSeries positiveParameter) g) (eH s)
    simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at ef
    rw [ei.sum_comp (fun j : I => (b j.1 s * (c j.1 j.2).eval s) *
      KPContHolomorphicKGeneration.complexSphericalWord (v j.1 j.2) s g),Fintype.sum_sigma]
    calc
      q s * tw s g * (f : PrincipalSeries positiveParameter) g =
          tw s g * (q s * (f : PrincipalSeries positiveParameter) g) := by ring
      _ = tw s g * ∑ j, b j s * (H j s : PrincipalSeries positiveParameter) g := by rw [ef]
      _ = ∑ j, b j s * (tw s g * (H j s : PrincipalSeries positiveParameter) g) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
      _ = ∑ j, b j s * ∑ r, (c j r).eval s * KPContHolomorphicKGeneration.complexSphericalWord (v j r) s g := by
        apply Finset.sum_congr rfl
        intro j hj
        have he := eg j s g
        change tw s g * (∑ r, (p j r).eval s • (h j r : PrincipalSeries positiveParameter)) g = _ at he
        have hh : (H j s : PrincipalSeries positiveParameter) = ∑ r, (p j r).eval s • (h j r : PrincipalSeries positiveParameter) := by
          simp only [H,Submodule.coe_sum,Submodule.coe_smul]
        rw [hh,he]
      _ = _ := by
        apply Finset.sum_congr rfl; intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r hr; ring

end HarmonicClearingAssembly

theorem local_harmonic_cleared_word_reconstruction
    (ℓ : ℕ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : f ∈ KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter ℓ) :
    ∃ (n : ℕ) (w : Fin n → KPContHolomorphicKGeneration.RealLieWord)
      (q : ℂ → ℂ) (b : Fin n → ℂ → ℂ),
      AnalyticOnNhd ℂ q Set.univ ∧ q 0 = 1 ∧
      (∀ j, AnalyticOnNhd ℂ (b j) Set.univ) ∧
      ∀ s : ℂ, ∀ a : KPCplxCharacterHaar.ComplexGL2,
        q s * Complex.exp (2 * s * (Real.log
          (‖((Matrix.GeneralLinearGroup.det a : ℂˣ) : ℂ)‖ /
            KPCplxPrincipalSeriesCharts.bottomRowNormSq a) : ℂ)) * f a =
          ∑ j, b j s * KPContHolomorphicKGeneration.complexSphericalWord (w j) s a := by
  exact harmonic_clearing_assembly ℓ ⟨f, hf⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

end
