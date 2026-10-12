module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PositiveSideJetSeminorms

@[expose] public section

noncomputable section
open scoped ContDiff
open DedekindZetaZeroFree.LargeSieve DedekindZetaZeroFree.LargeSieve.Vendor
namespace DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets

def localized (χ ψ K : ℝ → ℂ) (scale : ℝ) (p : ℝ × ℝ) : ℂ :=
  χ p.1 * ψ p.2 * K (scale * Real.exp ((p.1+p.2)/2))

def mixed (i j : ℕ) (H : ℝ × ℝ → ℂ) (x y : ℝ) : ℂ :=
  iteratedDeriv i (fun u => iteratedDeriv j (fun v => H (u,v)) y) x

def jet (R : ℝ) (H : ℝ × ℝ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
    sSup {v : ℝ | ∃ x ∈ Set.Icc (-R) R, ∃ y ∈ Set.Icc (-R) R,
      v = ‖mixed i j H x y‖}
private lemma euler_smooth (K : ℝ → ℂ) (hK : ContDiffOn ℝ ∞ K (Set.Ioi 0)) (n : ℕ) :
    ContDiffOn ℝ ∞ (EulerIter n K) (Set.Ioi 0) := by
  induction n with
  | zero => exact hK
  | succ n ih =>
    have hd : ContDiffOn ℝ ∞ (deriv (EulerIter n K)) (Set.Ioi 0) :=
      ih.deriv_of_isOpen isOpen_Ioi (by simp)
    have hh : ContDiffOn ℝ ∞ (fun x : ℝ => (x : ℂ) * deriv (EulerIter n K) x) (Set.Ioi 0) :=
      Complex.ofRealCLM.contDiff.contDiffOn.mul hd
    apply hh.congr
    intro x hx
    exact EulerIter_succ_of_pos n K x hx
private lemma log_smooth (K : ℝ → ℂ) (hK : ContDiffOn ℝ ∞ K (Set.Ioi 0))
    (scale : ℝ) (hs : 0 < scale) : ContDiff ℝ ∞ (fun u : ℝ => K (scale * Real.exp (u / 2))) := by
  apply hK.comp_contDiff
  · fun_prop
  · intro u; exact mul_pos hs (Real.exp_pos _)
private lemma log_deriv (K : ℝ → ℂ) (hK : ContDiffOn ℝ ∞ K (Set.Ioi 0))
    (scale : ℝ) (hs : 0 < scale) (u : ℝ) :
    deriv (fun v : ℝ => K (scale * Real.exp (v / 2))) u =
      (2 : ℂ)⁻¹ * EulerIter 1 K (scale * Real.exp (u / 2)) := by
  have hp : 0 < scale * Real.exp (u / 2) := mul_pos hs (Real.exp_pos _)
  have hkd := (hK.contDiffAt (isOpen_Ioi.mem_nhds hp)).differentiableAt (by simp)
  have he : HasDerivAt (fun v : ℝ => scale * Real.exp (v / 2))
      (scale * Real.exp (u / 2) / 2) u := by
    convert ((Real.hasDerivAt_exp (u / 2)).comp u ((hasDerivAt_id u).div_const 2)).const_mul scale using 1
    · rfl
    · ring
  have hchain : deriv (fun v : ℝ => K (scale * Real.exp (v / 2))) u =
      (scale * Real.exp (u / 2) / 2) • deriv K (scale * Real.exp (u / 2)) :=
    (hkd.hasDerivAt.scomp u he).deriv
  rw [hchain, EulerIter_succ_of_pos 0 K _ hp]
  simp only [EulerIter_zero, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring
private lemma log_iterated (K : ℝ → ℂ) (hK : ContDiffOn ℝ ∞ K (Set.Ioi 0))
    (scale : ℝ) (hs : 0 < scale) (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => K (scale * Real.exp (u / 2))) =
      fun u => (2 : ℂ)⁻¹ ^ n * EulerIter n K (scale * Real.exp (u / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    rw [deriv_const_mul_field, log_deriv _ (euler_smooth K hK n) scale hs]
    have he : EulerIter 1 (EulerIter n K) = EulerIter (n + 1) K := by
      funext x
      simp [EulerIter]
    rw [he]
    ring
private lemma smooth_iter (L : ℝ → ℂ) (hL : ContDiff ℝ ∞ L) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n L) := by
  induction n with
  | zero => exact hL
  | succ n ih =>
    rw [iteratedDeriv_succ]
    rw [← contDiffOn_univ]
    exact ih.contDiffOn.deriv_of_isOpen isOpen_univ (by simp)
private lemma mixed_formula (χ ψ L : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) (hL : ContDiff ℝ ∞ L)
    (i j : ℕ) (x y : ℝ) :
    mixed i j (fun p => χ p.1 * ψ p.2 * L (p.1 + p.2)) x y =
      ∑ l ∈ Finset.range (j+1), ∑ k ∈ Finset.range (i+1),
        (j.choose l : ℂ) * (i.choose k : ℂ) * iteratedDeriv k χ x * iteratedDeriv l ψ y *
          iteratedDeriv ((i-k)+(j-l)) L (x+y) := by
  have hinner : ∀ u : ℝ,
      iteratedDeriv j (fun v : ℝ => χ u * ψ v * L (u+v)) y =
        ∑ l ∈ Finset.range (j+1), (j.choose l : ℂ) * iteratedDeriv l ψ y *
          (χ u * iteratedDeriv (j-l) L (u+y)) := by
    intro u
    rw [show (fun v : ℝ => χ u * ψ v * L (u+v)) =
        fun v => χ u * (ψ v * L (u+v)) by funext v; ring]
    rw [iteratedDeriv_const_mul_field]
    have hh : ContDiff ℝ ∞ (fun v : ℝ => L (u+v)) := by
      exact hL.comp (contDiff_const.add contDiff_id)
    rw [iteratedDeriv_fun_mul (hψ.of_le (by simp)).contDiffAt
      (hh.of_le (by simp)).contDiffAt]
    simp only [iteratedDeriv_comp_const_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  unfold mixed
  simp_rw [hinner]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [iteratedDeriv_const_mul_field]
    have hLj : ContDiff ℝ ∞ (iteratedDeriv (j-l) L) := smooth_iter L hL (j-l)
    have hh : ContDiff ℝ ∞ (fun u : ℝ => iteratedDeriv (j-l) L (u+y)) :=
      hLj.comp (contDiff_id.add contDiff_const)
    rw [iteratedDeriv_fun_mul (hχ.of_le (by simp)).contDiffAt
      (hh.of_le (by simp)).contDiffAt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [iteratedDeriv_comp_add_const]
    have hadd : iteratedDeriv (i-k) (iteratedDeriv (j-l) L) = iteratedDeriv ((i-k)+(j-l)) L := by
      simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
    rw [hadd]
    ring
  · intro l hl
    have hLj : ContDiff ℝ ∞ (iteratedDeriv (j-l) L) := smooth_iter L hL (j-l)
    exact ((contDiff_const.mul (hχ.mul (hLj.comp (contDiff_id.add contDiff_const)))).of_le (by simp)).contDiffAt
private lemma log_iter_bound (K : ℝ → ℂ) (hK : ContDiffOn ℝ ∞ K (Set.Ioi 0))
    (R c scale B : ℝ) (hc : 0 < c) (hs : 0 < scale) (hB : 0 ≤ B)
    (hbound : ∀ j ≤ 4, ∀ x : ℝ, 0 < x → ‖DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter j K x‖ ≤ B * Real.rpow x (-c))
    (n : ℕ) (hn : n ≤ 4) (u : ℝ) (hu : -2*R ≤ u) :
    ‖iteratedDeriv n (fun v : ℝ => K (scale * Real.exp (v/2))) u‖ ≤
      B * Real.rpow scale (-c) * Real.exp (c*R) := by
  rw [log_iterated K hK scale hs, norm_mul]
  have hnorm : ‖(2 : ℂ)⁻¹ ^ n‖ ≤ 1 := by
    rw [norm_pow, norm_inv]
    norm_num
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hp : 0 < scale * Real.exp (u/2) := mul_pos hs (Real.exp_pos _)
  have he : Real.exp ((u/2)*(-c)) ≤ Real.exp (c*R) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ B * Real.rpow (scale * Real.exp (u/2)) (-c) := by
      exact mul_le_of_le_one_left (norm_nonneg _) hnorm |>.trans (hbound n hn _ hp)
    _ = B * Real.rpow scale (-c) * Real.exp ((u/2)*(-c)) := by
      have hp : Real.rpow (scale * Real.exp (u/2)) (-c) =
          Real.rpow scale (-c) * Real.exp ((u/2)*(-c)) := by
        calc
          _ = Real.rpow scale (-c) * Real.rpow (Real.exp (u/2)) (-c) :=
            Real.mul_rpow hs.le (Real.exp_pos (u/2)).le
          _ = _ := congrArg (fun z : ℝ => Real.rpow scale (-c) * z) (Real.exp_mul (u/2) (-c)).symm
      rw [hp]
      ring
    _ ≤ B * Real.rpow scale (-c) * Real.exp (c*R) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hB (Real.rpow_nonneg hs.le _))
private lemma mixed_bound (χ ψ L : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) (hL : ContDiff ℝ ∞ L)
    (R T : ℝ) (hT : 0 ≤ T) (Aχ Aψ : ℕ → ℝ)
    (haχ : ∀ n, 0 ≤ Aχ n) (haψ : ∀ n, 0 ≤ Aψ n)
    (hboundχ : ∀ n, ∀ x ∈ Set.Icc (-R) R, ‖iteratedDeriv n χ x‖ ≤ Aχ n)
    (hboundψ : ∀ n, ∀ y ∈ Set.Icc (-R) R, ‖iteratedDeriv n ψ y‖ ≤ Aψ n)
    (hboundL : ∀ n ≤ 4, ∀ u, -2*R ≤ u → ‖iteratedDeriv n L u‖ ≤ T)
    (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (x y : ℝ)
    (hx : x ∈ Set.Icc (-R) R) (hy : y ∈ Set.Icc (-R) R) :
    ‖mixed i j (fun p => χ p.1 * ψ p.2 * L (p.1+p.2)) x y‖ ≤
      (∑ l ∈ Finset.range (j+1), ∑ k ∈ Finset.range (i+1),
        ‖(j.choose l : ℂ)‖ * ‖(i.choose k : ℂ)‖ * Aχ k * Aψ l) * T := by
  rw [mixed_formula χ ψ L hχ hψ hL]
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  simp only [norm_mul]
  have hu : -2*R ≤ x+y := by have := hx.1; have := hy.1; linarith
  have hn : i-k+(j-l) ≤ 4 := by omega
  have hχb := hboundχ k x hx
  have hψb := hboundψ l y hy
  have hLb := hboundL _ hn _ hu
  have hχ0 := haχ k
  have hψ0 := haψ l
  gcongr <;> first | positivity | assumption

theorem uniform_jet_bound
    (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (χ ψ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ → ℂ) (B : ℝ),
      ContDiffOn ℝ ∞ K (Set.Ioi 0) → 0 ≤ B →
      (∀ j ≤ 4, ∀ x : ℝ, 0 < x → ‖EulerIter j K x‖ ≤ B * Real.rpow x (-c)) →
      ∀ scale : ℝ, 0 < scale →
        jet R (localized χ ψ K scale) ≤ C * B * Real.rpow scale (-c) := by
  have hbχ : ∀ n : ℕ, ∃ A : ℝ, ∀ x ∈ Set.Icc (-R) R, ‖iteratedDeriv n χ x‖ ≤ A := by
    intro n
    exact isCompact_Icc.exists_bound_of_continuousOn
      (hχ.continuous_iteratedDeriv n (by simp)).continuousOn
  have hbψ : ∀ n : ℕ, ∃ A : ℝ, ∀ x ∈ Set.Icc (-R) R, ‖iteratedDeriv n ψ x‖ ≤ A := by
    intro n
    exact isCompact_Icc.exists_bound_of_continuousOn
      (hψ.continuous_iteratedDeriv n (by simp)).continuousOn
  choose Aχ haχ using hbχ
  choose Aψ haψ using hbψ
  let Pχ := fun n => |Aχ n| + 1
  let Pψ := fun n => |Aψ n| + 1
  have hPχ : ∀ n, 0 ≤ Pχ n := by intro n; dsimp [Pχ]; positivity
  have hPψ : ∀ n, 0 ≤ Pψ n := by intro n; dsimp [Pψ]; positivity
  have hbPχ : ∀ n, ∀ x ∈ Set.Icc (-R) R, ‖iteratedDeriv n χ x‖ ≤ Pχ n := by
    intro n x hx; exact (haχ n x hx).trans (by dsimp [Pχ]; have := le_abs_self (Aχ n); linarith)
  have hbPψ : ∀ n, ∀ x ∈ Set.Icc (-R) R, ‖iteratedDeriv n ψ x‖ ≤ Pψ n := by
    intro n x hx; exact (haψ n x hx).trans (by dsimp [Pψ]; have := le_abs_self (Aψ n); linarith)
  let A := fun i j : ℕ => ∑ l ∈ Finset.range (j+1), ∑ k ∈ Finset.range (i+1),
        ‖(j.choose l : ℂ)‖ * ‖(i.choose k : ℂ)‖ * Pχ k * Pψ l
  let C := (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, A i j) * Real.exp (c*R) + 1
  have hA : ∀ i j, 0 ≤ A i j := by
    intro i j; exact Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hPχ k)) (hPψ l)
  have hsum : 0 ≤ ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, A i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA i j
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K B hK hB hbound scale hs
  let L := fun u : ℝ => K (scale * Real.exp (u/2))
  have hL : ContDiff ℝ ∞ L := log_smooth K hK scale hs
  let T := B * Real.rpow scale (-c) * Real.exp (c*R)
  have hT : 0 ≤ T := mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hs.le _)) (Real.exp_pos _).le
  have hbL : ∀ n ≤ 4, ∀ u, -2*R ≤ u → ‖iteratedDeriv n L u‖ ≤ T :=
    fun n hn u hu => log_iter_bound K hK R c scale B hc hs hB hbound n hn u hu
  have hjet : jet R (localized χ ψ K scale) ≤
      (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, A i j) * T := by
    unfold jet
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hin : i ≤ 2 := by simp only [Finset.mem_range] at hi; omega
    have hjn : j ≤ 2 := by simp only [Finset.mem_range] at hj; omega
    apply csSup_le
    · exact ⟨‖mixed i j (localized χ ψ K scale) 0 0‖,
        0, ⟨by linarith, hR.le⟩, 0, ⟨by linarith, hR.le⟩, rfl⟩
    · intro v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := hv
      exact mixed_bound χ ψ L hχ hψ hL R T hT Pχ Pψ hPχ hPψ hbPχ hbPψ hbL
        i j hin hjn x y hx hy
  apply hjet.trans
  dsimp [C, T]
  have hp : 0 ≤ B * Real.rpow scale (-c) := mul_nonneg hB (Real.rpow_nonneg hs.le _)
  have hr : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, A i j) *
      (B * Real.rpow scale (-c) * Real.exp (c*R)) =
      ((∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, A i j) * Real.exp (c*R)) *
        (B * Real.rpow scale (-c)) := by ring
  apply le_of_eq_of_le hr
  have he : ((∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, A i j) * Real.exp (c*R)) *
      (B * Real.rpow scale (-c)) ≤
      (((∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, A i j) * Real.exp (c*R)) + 1) *
        (B * Real.rpow scale (-c)) := mul_le_mul_of_nonneg_right (by linarith) hp
  convert he using 1
  simp only [← Real.rpow_eq_pow]
  ring
end DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets

end
