module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HopfMatrixCoordinates

@[expose] public section

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts.RotationToChartsSteps
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

def hemisphereSign (north : Bool) : ℝ := if north then 1 else -1

noncomputable def inverseHopfCoordinate (north : Bool) (x : Ambient) : ℂ :=
  ((x 0 : ℂ) - (hemisphereSign north : ℂ) * Complex.I * (x 1 : ℂ)) /
    ((‖x‖ : ℂ) + (hemisphereSign north : ℂ) * (x 2 : ℂ))

noncomputable def inverseHopfWeight (s : ℝ) (north : Bool) (x : Ambient) : ℂ :=
  (Real.rpow (2 * ‖x‖ / (‖x‖ + hemisphereSign north * x 2)) (1 + 2 * s) : ℂ)

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts.RotationToChartsSteps

end

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open RotationToChartsSteps

theorem inverse_hopf_disc_cover (p : Sphere) :
    ∃ north : Bool,
      0 ≤ hemisphereSign north * (p : Ambient) 2 ∧
      (p : Ambient) ≠ 0 ∧
      0 < ‖(p : Ambient)‖ + hemisphereSign north * (p : Ambient) 2 ∧
      inverseHopfCoordinate north p ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hn : ‖(p : Ambient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  have hp : (p : Ambient) ≠ 0 := by
    intro h
    simp [h] at hn
  have hs : (p : Ambient) 0 ^ 2 + (p : Ambient) 1 ^ 2 + (p : Ambient) 2 ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hn
    simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs,
      sq_abs, one_pow] using h
  have hdisc : ∀ north, 0 ≤ hemisphereSign north * (p : Ambient) 2 →
      inverseHopfCoordinate north p ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro north hside
    rw [Metric.mem_closedBall, dist_zero_right, inverseHopfCoordinate, norm_div]
    have hd : 0 < 1 + hemisphereSign north * (p : Ambient) 2 := by linarith
    have hnorm : ‖((p : Ambient) 0 : ℂ) - (hemisphereSign north : ℂ) * Complex.I * ((p : Ambient) 1 : ℂ)‖ ≤
        1 + hemisphereSign north * (p : Ambient) 2 := by
      have hsq : ‖((p : Ambient) 0 : ℂ) - (hemisphereSign north : ℂ) * Complex.I * ((p : Ambient) 1 : ℂ)‖ ^ 2 =
          (p : Ambient) 0 ^ 2 + (p : Ambient) 1 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq]
        cases north <;> simp [hemisphereSign, Complex.normSq_apply, Complex.mul_re,
          Complex.mul_im, sq]
      nlinarith [sq_nonneg (hemisphereSign north * (p : Ambient) 2), norm_nonneg
        (((p : Ambient) 0 : ℂ) - (hemisphereSign north : ℂ) * Complex.I * ((p : Ambient) 1 : ℂ))]
    have hdennorm : ‖((‖(p : Ambient)‖ : ℂ) + (hemisphereSign north : ℂ) * ((p : Ambient) 2 : ℂ))‖ =
        1 + hemisphereSign north * (p : Ambient) 2 := by
      rw [hn, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd]
    rw [hdennorm, div_le_one hd]
    exact hnorm
  by_cases h : 0 ≤ (p : Ambient) 2
  · refine ⟨true, ?_, hp, ?_, hdisc true ?_⟩ <;> simp [hemisphereSign, hn] <;> linarith
  · refine ⟨false, ?_, hp, ?_, hdisc false ?_⟩ <;> simp [hemisphereSign, hn] <;> linarith

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open RotationToChartsSteps
open scoped BigOperators

def hopfDomain (north : Bool) : Set Ambient :=
  {x | x ≠ 0 ∧ 0 < ‖x‖ + hemisphereSign north * x 2}

private lemma hopfDomain_open (north : Bool) : IsOpen (hopfDomain north) := by
  exact isOpen_ne.inter (isOpen_lt continuous_const
    (show Continuous (fun x : Ambient => ‖x‖ + hemisphereSign north * x 2) by fun_prop))

private lemma inverseHopf_smooth (north : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (inverseHopfCoordinate north) (hopfDomain north) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  unfold inverseHopfCoordinate
  have hreal : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  simp only [div_eq_mul_inv]
  apply ContDiffAt.mul
  · have hc : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    fun_prop
  · apply ContDiffAt.inv
    · have hn : ContDiffAt ℝ (⊤ : ℕ∞) (norm : Ambient → ℝ) x := contDiffAt_norm ℝ hx.1
      have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
      exact hc.add (by fun_prop)
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx.2)

private lemma inverseHopfWeight_smooth (s : ℝ) (north : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (inverseHopfWeight s north) (hopfDomain north) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  unfold inverseHopfWeight
  apply Complex.ofRealCLM.contDiff.contDiffAt.comp x
  apply ContDiffAt.rpow_const_of_ne
  · apply ContDiffAt.div
    · exact contDiffAt_const.mul (contDiffAt_norm ℝ hx.1)
    · exact (contDiffAt_norm ℝ hx.1).add (by fun_prop)
    · exact ne_of_gt hx.2
  · exact ne_of_gt (div_pos (mul_pos (by norm_num) (norm_pos_iff.mpr hx.1)) hx.2)

private lemma hemisphere_compact (north : Bool) :
    IsCompact {x : Ambient | ‖x‖ = 1 ∧ 0 ≤ hemisphereSign north * x 2} := by
  have hs : {x : Ambient | ‖x‖ = 1} = Metric.sphere (0 : Ambient) 1 := by
    ext x
    simp [Metric.mem_sphere, dist_zero_right]
  rw [show {x : Ambient | ‖x‖ = 1 ∧ 0 ≤ hemisphereSign north * x 2} =
    {x | ‖x‖ = 1} ∩ {x | 0 ≤ hemisphereSign north * x 2} from rfl, hs]
  exact (isCompact_sphere (0 : Ambient) 1).inter_right
    (isClosed_le continuous_const (by fun_prop))

private lemma hemisphere_mem (north : Bool) (p : Sphere)
    (hp : 0 ≤ hemisphereSign north * (p : Ambient) 2) : (p : Ambient) ∈ hopfDomain north := by
  have hn : ‖(p : Ambient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  exact ⟨by intro h; simp [h] at hn, by rw [hn]; linarith⟩

private lemma hemisphere_jet_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (north : Bool) (f : Ambient → E)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (hopfDomain north)) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ p : Sphere,
      0 ≤ hemisphereSign north * (p : Ambient) 2 → ‖iteratedFDeriv ℝ i f p‖ ≤ D := by
  classical
  have hb : ∀ i : Fin (n + 1), ∃ D : ℝ, ∀ p : Sphere,
      0 ≤ hemisphereSign north * (p : Ambient) 2 → ‖iteratedFDeriv ℝ i.val f p‖ ≤ max 1 D := by
    intro i
    have hc := (ContinuousOn.continuousOn_iteratedFDeriv hf (hopfDomain_open north) (k := i.val) (by simp)).norm
    have hsub : {x : Ambient | ‖x‖ = 1 ∧ 0 ≤ hemisphereSign north * x 2} ⊆ hopfDomain north := by
      intro x hx
      exact ⟨by intro h; simp [h] at hx, by rw [hx.1]; linarith [hx.2]⟩
    obtain ⟨D, hD⟩ := (hemisphere_compact north).bddAbove_image (hc.mono hsub)
    refine ⟨D, fun p hp => ?_⟩
    apply (hD (Set.mem_image_of_mem _ ?_)).trans (le_max_right _ _)
    exact ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using p.property, hp⟩
  choose D hD using hb
  let A := ∑ i : Fin (n + 1), max 1 (D i)
  have hA (i : Fin (n + 1)) : max 1 (D i) ≤ A :=
    Finset.single_le_sum (fun _ _ => (zero_le_one.trans (le_max_left _ _))) (Finset.mem_univ i)
  refine ⟨A, (le_max_left 1 (D ⟨0, by omega⟩)).trans (hA _), ?_⟩
  intro i hi p hp
  exact (hD ⟨i, by omega⟩ p hp).trans (hA _)

private lemma within_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {north : Bool} {f : Ambient → E} {N : WithTop ℕ∞}
    (hf : ContDiffOn ℝ N f (hopfDomain north)) {p : Ambient} (hp : p ∈ hopfDomain north)
    (j : ℕ) (hj : (j : WithTop ℕ∞) ≤ N) :
    iteratedFDerivWithin ℝ j f (hopfDomain north) p = iteratedFDeriv ℝ j f p :=
  iteratedFDerivWithin_eq_iteratedFDeriv (hopfDomain_open north).uniqueDiffOn
    ((hf.contDiffAt ((hopfDomain_open north).mem_nhds hp)).of_le hj) hp

theorem inverse_hopf_jet_bound (s : ℝ) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (north : Bool) (g : ℂ → ℂ), ContDiff ℝ (n : ℕ∞) g →
        ∀ (B : ℝ), 0 ≤ B →
          ∀ (p : Sphere), 0 ≤ hemisphereSign north * (p : Ambient) 2 →
            (∀ k ≤ n, ‖iteratedFDeriv ℝ k g (inverseHopfCoordinate north p)‖ ≤ B) →
            ∀ j ≤ n,
              ‖iteratedFDeriv ℝ j
                (fun y : Ambient => inverseHopfWeight s north y *
                  g (inverseHopfCoordinate north y)) p‖ ≤ A * B := by
  classical
  have hb : ∀ north : Bool, ∃ A : ℝ, 0 ≤ A ∧
      ∀ (g : ℂ → ℂ), ContDiff ℝ (n : ℕ∞) g → ∀ B : ℝ, 0 ≤ B →
        ∀ p : Sphere, 0 ≤ hemisphereSign north * (p : Ambient) 2 →
          (∀ k ≤ n, ‖iteratedFDeriv ℝ k g (inverseHopfCoordinate north p)‖ ≤ B) →
          ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun y : Ambient =>
            inverseHopfWeight s north y * g (inverseHopfCoordinate north y)) p‖ ≤ A * B := by
    intro north
    obtain ⟨D, hD1, hD⟩ := hemisphere_jet_bounds north _ (inverseHopf_smooth north) n
    obtain ⟨W, hW1, hW⟩ := hemisphere_jet_bounds north _ (inverseHopfWeight_smooth s north) n
    let C : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * W * ((j-i).factorial * D ^ (j-i))
    have hC : ∀ j, 0 ≤ C j := fun j => Finset.sum_nonneg (fun _ _ => by positivity)
    let A := ∑ j : Fin (n+1), C j.val
    refine ⟨A, Finset.sum_nonneg (fun _ _ => hC _), ?_⟩
    intro g hg B hB p hp hjet j hj
    have hpm := hemisphere_mem north p hp
    have hc : ContDiffOn ℝ (n : ℕ∞) (inverseHopfCoordinate north) (hopfDomain north) :=
      (inverseHopf_smooth north).of_le (by simp)
    have hw : ContDiffOn ℝ (n : ℕ∞) (inverseHopfWeight s north) (hopfDomain north) :=
      (inverseHopfWeight_smooth s north).of_le (by simp)
    have hgcomp : ContDiffOn ℝ (n : ℕ∞) (g ∘ inverseHopfCoordinate north) (hopfDomain north) :=
      hg.comp_contDiffOn hc
    have hm := hw.mul hgcomp
    have hcomp (k : ℕ) (hk : k ≤ n) :
        ‖iteratedFDerivWithin ℝ k (g ∘ inverseHopfCoordinate north) (hopfDomain north) p‖ ≤
          k.factorial * B * D ^ k := by
      apply norm_iteratedFDerivWithin_comp_le hg.contDiffOn hc (by exact_mod_cast hk)
        uniqueDiffOn_univ (hopfDomain_open north).uniqueDiffOn
        (fun _ _ => Set.mem_univ _) hpm
      · intro i hi
        rw [iteratedFDerivWithin_univ]
        exact hjet i (hi.trans hk)
      · intro i hi hik
        rw [within_eq hc hpm i (by exact_mod_cast hik.trans hk)]
        exact (hD i (hik.trans hk) p hp).trans (le_self_pow₀ hD1 (by omega))
    change ‖iteratedFDeriv ℝ j (fun y => inverseHopfWeight s north y *
      (g ∘ inverseHopfCoordinate north) y) p‖ ≤ A * B
    rw [← within_eq hm hpm j (by exact_mod_cast hj)]
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (inverseHopfWeight s north) (hopfDomain north) p‖ *
          ‖iteratedFDerivWithin ℝ (j-i) (g ∘ inverseHopfCoordinate north) (hopfDomain north) p‖ :=
        norm_iteratedFDerivWithin_mul_le hw hgcomp (hopfDomain_open north).uniqueDiffOn hpm
          (by exact_mod_cast hj)
      _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * W * ((j-i).factorial * B * D ^ (j-i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := (Finset.mem_range_succ_iff.mp hi).trans hj
        rw [within_eq hw hpm i (by exact_mod_cast hin)]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hW i hin p hp) (Nat.cast_nonneg _))
          (hcomp (j-i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
      _ = C j * B := by
        dsimp only [C]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ A * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact Finset.single_le_sum (f := fun k : Fin (n+1) => C k.val)
          (fun k _ => hC k.val) (Finset.mem_univ (⟨j, by omega⟩ : Fin (n+1)))
  choose A hA hb using hb
  refine ⟨A false + A true, add_nonneg (hA false) (hA true), ?_⟩
  intro north g hg B hB p hp hj j hjn
  apply (hb north g hg B hB p hp hj j hjn).trans
  apply mul_le_mul_of_nonneg_right _ hB
  cases north
  · exact le_add_of_nonneg_right (hA true)
  · exact le_add_of_nonneg_left (hA false)

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped NNReal

theorem actual_chart_jet_le_range_sup (s : ℝ) (n j : ℕ) (hj : j ≤ n)
    (f : PrincipalSeries s) (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖iteratedFDeriv ℝ j (openCoordinate f) z‖ ≤
      ((Finset.range (n + 1)).sup (chartSeminorm s)) f ∧
    ‖iteratedFDeriv ℝ j (infinityCoordinate f) z‖ ≤
      ((Finset.range (n + 1)).sup (chartSeminorm s)) f := by
  have hfo : ContDiff ℝ (⊤ : ℕ∞) (openCoordinate f) := f.property.2.1
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate f) := f.property.2.2
  have hbo : BddAbove ((fun z : ℂ => ‖iteratedFDeriv ℝ j (openCoordinate f) z‖) ''
      Metric.closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
      (hfo.continuous_iteratedFDeriv (by simp)).norm.continuousOn
  have hbi : BddAbove ((fun z : ℂ => ‖iteratedFDeriv ℝ j (infinityCoordinate f) z‖) ''
      Metric.closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
      (hfi.continuous_iteratedFDeriv (by simp)).norm.continuousOn
  have hjs : chartSeminorm s j f ≤ ((Finset.range (n + 1)).sup (chartSeminorm s)) f :=
    Finset.le_sup (f := chartSeminorm s) (Finset.mem_range.mpr (by omega)) f
  constructor
  · apply le_trans _ hjs
    change ‖iteratedFDeriv ℝ j (openCoordinate f) z‖ ≤ max _ _
    exact (le_csSup hbo (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
  · apply le_trans _ hjs
    change ‖iteratedFDeriv ℝ j (infinityCoordinate f) z‖ ≤ max _ _
    exact (le_csSup hbi (Set.mem_image_of_mem _ hz)).trans (le_max_right _ _)

theorem rotation_le_charts_of_word_bounds (H : ComplexSU2 → Sphere)
    (s : ℝ) (n : ℕ)
    (hword : ∀ w : List (Fin 3), w.length ≤ n →
      ∃ C : ℝ≥0, ∀ (f : PrincipalSeries s) (F : Sphere → ℂ), IsSphereSmooth F →
        (∀ k : ComplexSU2, compactRestriction s f k = F (H k)) →
        ∀ x : Sphere, ‖rotationWord w F x‖ ≤
          (C • (Finset.range (n + 1)).sup (chartSeminorm s)) f) :
    ∃ D : ℝ≥0, D ≠ 0 ∧
      ∀ (f : PrincipalSeries s) (F : Sphere → ℂ), IsSphereSmooth F →
        (∀ k : ComplexSU2, compactRestriction s f k = F (H k)) →
        rotationSup n F ≤
          (D • (Finset.range (n + 1)).sup (chartSeminorm s)) f := by
  classical
  let W := {w : List (Fin 3) // w.length ≤ n}
  letI : Fintype W := (List.finite_length_le (Fin 3) n).fintype
  let C : W → ℝ≥0 := fun w => Classical.choose (hword w.val w.property)
  have hC : ∀ w : W, ∀ (f : PrincipalSeries s) (F : Sphere → ℂ), IsSphereSmooth F →
      (∀ k : ComplexSU2, compactRestriction s f k = F (H k)) →
      ∀ x : Sphere, ‖rotationWord w.val F x‖ ≤
        (C w • (Finset.range (n + 1)).sup (chartSeminorm s)) f :=
    fun w => Classical.choose_spec (hword w.val w.property)
  let D : ℝ≥0 := 1 + Finset.univ.sup C
  refine ⟨D, ?_, ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (show 1 ≤ D from le_add_of_nonneg_right (zero_le)))
  · intro f F hF hf
    apply Real.sSup_le _ (apply_nonneg _ _)
    rintro r ⟨w, hw, x, rfl⟩
    have hCD : C ⟨w, hw⟩ ≤ D := by
      exact (Finset.le_sup (f := C) (Finset.mem_univ ⟨w, hw⟩)).trans
        (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ 1))
    exact (hC ⟨w, hw⟩ f F hF hf x).trans
      (by
        simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCD)
          (apply_nonneg _ _))

private lemma rt_sphere_ne (p : Sphere) : (p : Ambient) ≠ 0 := by
  have hn : ‖(p : Ambient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  intro hz
  simp [hz] at hn

private lemma rt_radial_pos_smul (F : Sphere → ℂ) (t : ℝ) (ht : 0 < t) (x : Ambient) :
    radialExtension F (t • x) = radialExtension F x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  have htx : t • x ≠ 0 := smul_ne_zero (ne_of_gt ht) hx
  simp only [radialExtension, dif_pos hx, dif_pos htx]
  congr 1
  apply Subtype.ext
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), mul_one]

private lemma rt_radial_rotation (F : Sphere → ℂ) (hF : IsSphereSmooth F)
    (x : Ambient) (hx : x ≠ 0) (i : Fin 3) :
    radialExtension (rotationDeriv i F) x =
      fderiv ℝ (radialExtension F) x (rotationVector i x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let t := ‖x‖⁻¹
  have ht : 0 < t := inv_pos.mpr hn
  have htx : t • x ≠ 0 := smul_ne_zero (ne_of_gt ht) hx
  have he : (fun y : Ambient => radialExtension F (t • y)) = radialExtension F :=
    funext (rt_radial_pos_smul F t ht)
  have hd := ((hF.contDiffAt (isOpen_ne.mem_nhds htx)).differentiableAt
    (by simp)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  change HasFDerivAt (fun y : Ambient => radialExtension F (t • y)) _ x at hd
  rw [he] at hd
  have hh := congrArg (fun L : Ambient →L[ℝ] ℂ => L (rotationVector i x)) hd.fderiv
  have hs : rotationVector i (t • x) = t • rotationVector i x := by
    apply PiLp.ext
    intro j
    simp only [rotationVector, PiLp.smul_apply, WithLp.toLp]
    split_ifs <;> simp
  simp only [radialExtension, dif_pos hx, rotationDeriv]
  rw [hs]
  exact hh.symm

private lemma rt_toWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Ambient → E} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {x : Ambient | x ≠ 0})
    (n : ℕ) {x : Ambient} (hx : x ≠ 0) :
    iteratedFDerivWithin ℝ n f {x : Ambient | x ≠ 0} x = iteratedFDeriv ℝ n f x :=
  iteratedFDerivWithin_eq_iteratedFDeriv isOpen_ne.uniqueDiffOn
    ((hf.contDiffAt (isOpen_ne.mem_nhds hx)).of_le (by simp)) hx

private lemma rt_vector_jet_bound (i : Fin 3) (n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j ≤ n, ∀ p : Sphere,
      ‖iteratedFDeriv ℝ j (rotationVector i) p‖ ≤ D := by
  classical
  have hb : ∀ j : Fin (n + 1), ∃ D : ℝ, 0 ≤ D ∧ ∀ p : Sphere,
      ‖iteratedFDeriv ℝ j.val (rotationVector i) p‖ ≤ D := by
    intro j
    obtain ⟨D, hD⟩ := (isCompact_sphere (0 : Ambient) 1).bddAbove_image
      ((rotationVector_smooth i).continuous_iteratedFDeriv (by simp)).norm.continuousOn
    exact ⟨max 0 D, le_max_left _ _, fun p =>
      (hD (Set.mem_image_of_mem _ p.property)).trans (le_max_right _ _)⟩
  choose D hD0 hD using hb
  refine ⟨∑ j, D j, Finset.sum_nonneg (fun j _ => hD0 j), ?_⟩
  intro j hj p
  exact (hD ⟨j, by omega⟩ p).trans
    (Finset.single_le_sum (fun k _ => hD0 k) (Finset.mem_univ _))

theorem rotation_word_radial_jet_bound (w : List (Fin 3)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Sphere → ℂ, IsSphereSmooth F →
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ m + w.length, ∀ p : Sphere,
        ‖iteratedFDeriv ℝ j (radialExtension F) p‖ ≤ B) →
      ∀ j ≤ m, ∀ p : Sphere,
        ‖iteratedFDeriv ℝ j (radialExtension (rotationWord w F)) p‖ ≤ C * B := by
  classical
  induction w generalizing m with
  | nil =>
    refine ⟨1, zero_le_one, ?_⟩
    intro F hF B hB hb j hj p
    simpa only [rotationWord, List.length_nil, add_zero, one_mul] using hb j hj p
  | cons i w ih =>
    obtain ⟨A, hA0, hA⟩ := ih (m + 1)
    obtain ⟨D, hD0, hD⟩ := rt_vector_jet_bound i m
    let C := ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) * A * D
    have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => by positivity))
    refine ⟨C, hC0, ?_⟩
    intro F hF B hB hb j hj p
    have htail : ∀ k ≤ m + 1, ∀ p : Sphere,
        ‖iteratedFDeriv ℝ k (radialExtension (rotationWord w F)) p‖ ≤ A * B := by
      apply hA F hF B hB
      intro k hk p
      apply hb k _ p
      simp only [List.length_cons]
      omega
    have hG := rotationWord_smooth w hF
    have hne := rt_sphere_ne p
    have hd : ContDiffOn ℝ (⊤ : ℕ∞)
        (fderiv ℝ (radialExtension (rotationWord w F))) {x : Ambient | x ≠ 0} :=
      hG.fderiv_of_isOpen isOpen_ne (by simp)
    have he : radialExtension (rotationWord (i :: w) F) =ᶠ[nhds (p : Ambient)]
        (fun x => fderiv ℝ (radialExtension (rotationWord w F)) x (rotationVector i x)) := by
      filter_upwards [isOpen_ne.mem_nhds hne] with x hx
      exact rt_radial_rotation _ hG x hx i
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    rw [← rt_toWithin (hd.clm_apply (rotationVector_smooth i).contDiffOn) j hne]
    apply (norm_iteratedFDerivWithin_clm_apply hd (rotationVector_smooth i).contDiffOn
      isOpen_ne.uniqueDiffOn hne (by simp)).trans
    simp_rw [rt_toWithin hd _ hne, rt_toWithin (rotationVector_smooth i).contDiffOn _ hne]
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (A * B) * D := by
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
        rw [norm_iteratedFDeriv_fderiv]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (htail (k + 1) (by omega) p)
          (Nat.cast_nonneg _)) (hD (j-k) (by omega) p) (norm_nonneg _)
          (by positivity)
      _ = (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * A * D) * B := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ C * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact Finset.single_le_sum
          (f := fun k => ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * A * D)
          (fun k _ => Finset.sum_nonneg (fun l _ => by positivity))
          (Finset.mem_range.mpr (by omega))

theorem rotation_le_charts_of_radial_jet_bounds (H : ComplexSU2 → Sphere)
    (s : ℝ) (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hrad : ∀ (f : PrincipalSeries s) (F : Sphere → ℂ), IsSphereSmooth F →
      (∀ k : ComplexSU2, compactRestriction s f k = F (H k)) →
      ∀ j ≤ n, ∀ p : Sphere,
        ‖iteratedFDeriv ℝ j (radialExtension F) p‖ ≤
          A * ((Finset.range (n + 1)).sup (chartSeminorm s)) f) :
    ∃ D : ℝ≥0, D ≠ 0 ∧
      ∀ (f : PrincipalSeries s) (F : Sphere → ℂ), IsSphereSmooth F →
        (∀ k : ComplexSU2, compactRestriction s f k = F (H k)) →
        rotationSup n F ≤
          (D • (Finset.range (n + 1)).sup (chartSeminorm s)) f := by
  apply rotation_le_charts_of_word_bounds
  intro w hw
  obtain ⟨C, hC0, hC⟩ := rotation_word_radial_jet_bound w 0
  refine ⟨⟨C * A, mul_nonneg hC0 hA⟩, ?_⟩
  intro f F hF hf p
  have hb : 0 ≤ A * ((Finset.range (n + 1)).sup (chartSeminorm s)) f :=
    mul_nonneg hA (apply_nonneg _ _)
  have h := hC F hF _ hb (fun j hj p => hrad f F hF hf j (by omega) p) 0 (by omega) p
  change ‖rotationWord w F p‖ ≤ (C * A) * ((Finset.range (n + 1)).sup (chartSeminorm s)) f
  simpa only [norm_iteratedFDeriv_zero, radialExtension_sphere, mul_assoc] using h

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end
