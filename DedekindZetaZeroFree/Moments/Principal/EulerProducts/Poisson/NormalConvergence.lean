module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.GoodPrimeBounds
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.BadPrimeBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerProductAux

noncomputable section

open DedekindZetaZeroFree DedekindZetaZeroFree.CorrectionFactors DedekindZetaZeroFree.LocalFiniteSums
open scoped NumberField Classical

set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private lemma Q_gt_one (p : ExteriorPrime A) : 1 < Q p := by
  change 1 < (Ideal.absNorm p.val.asIdeal : ℝ)
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val

private lemma chi_le (p : ExteriorPrime A) (u : A.R) :
    ‖chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u)‖ ≤ 1 := by
  letI := A.exteriorResidue_finite (primeIdeal p)
  letI := Fintype.ofFinite (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ
  by_cases hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u)
  · obtain ⟨v, hv⟩ := hu
    rw [← hv]
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((chi (σ := σ) p).apply_mem_rootsOfUnity v)
    simpa only [MulChar.coe_equivToUnitHom] using h.le
  · simp [MulChar.map_nonunit _ hu]

private lemma eta_le (p : ExteriorPrime A) : ‖η p.val.asIdeal‖ ≤ 1 := by
  by_cases h : η p.val.asIdeal = 0
  · simp [h]
  · exact (RayClassBridge.rayClassCharacter_norm_of_ne_zero F
      (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
      A.modulus A.modulus_ne_zero η p.val.asIdeal h).le

private lemma qPower_norm (p : ExteriorPrime A) (s : ℂ) :
    ‖qPower p s‖ = Real.exp (s.re * Real.log (Q p)) := by
  simp [qPower, Complex.norm_exp]

private lemma norm_V' (p : ExteriorPrime A) (z : ℂ) :
    ‖V p z‖ = Real.exp ((-6 * z.re) * Real.log (Q p)) := by
  simp [V, qPower_norm]

private lemma norm_W' (p : ExteriorPrime A) (u : A.R) (w : ℂ) :
    ‖W (σ := σ) p u w‖ ≤ Real.exp (-w.re * Real.log (Q p)) := by
  simp only [W, norm_mul, qPower_norm, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (chi_le p u)

private lemma norm_D' (p : ExteriorPrime A) (u : A.R) (ξ : ℂ) :
    ‖D (σ := σ) (η := η) p u ξ‖ ≤ Real.exp (-ξ.re * Real.log (Q p)) := by
  simp only [D, norm_mul, norm_star, qPower_norm, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.exp_pos _).le
    (mul_le_one₀ (eta_le p) (norm_nonneg _) (chi_le p u))

private lemma norm_E' (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (ξ z : ℂ) :
    ‖E C p ξ z‖ = Real.exp ((4 - 6 * ξ.re - 6 * z.re) * Real.log (Q p)) := by
  have hθ : ‖vartheta C p‖ = 1 := Circle.norm_coe _
  simp only [E, norm_mul, norm_pow, hθ, one_pow, one_mul,
    qPower_norm, norm_V']
  rw [← Real.exp_add]
  congr 1
  simp
  ring

private lemma star_region (x : Coordinates) (hx : x ∈ DedekindZetaZeroFree.Quantitative.EulerDomain.OmegaStar) :
    0 < 6 * x.2.2.re ∧ 0 < x.2.1.re ∧ 0 < x.1.re ∧ 0 < 6 * x.1.re + 6 * x.2.2.re - 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hx
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma norms_lt_one_star (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R) (x : Coordinates)
    (hx : x ∈ DedekindZetaZeroFree.Quantitative.EulerDomain.OmegaStar) :
    ‖V p x.2.2‖ < 1 ∧ ‖W (σ := σ) p u x.2.1‖ < 1 ∧
    ‖D (σ := σ) (η := η) p u x.1‖ < 1 ∧ ‖E C p x.1 x.2.2‖ < 1 := by
  obtain ⟨hz, hw, hξ, he⟩ := star_region x hx
  have hlog := Real.log_pos (Q_gt_one p)
  have hexp : ∀ a : ℝ, a < 0 → Real.exp (a * Real.log (Q p)) < 1 := by
    intro a ha
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos ha hlog)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_V']; exact hexp _ (by linarith)
  · exact (norm_W' p u _).trans_lt (hexp _ (by linarith))
  · exact (norm_D' p u _).trans_lt (hexp _ (by linarith))
  · rw [norm_E']; exact hexp _ (by linarith)

private lemma denominators_ne_zero_star (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R) (x : Coordinates)
    (hx : x ∈ DedekindZetaZeroFree.Quantitative.EulerDomain.OmegaStar) :
    1 - V p x.2.2 ≠ 0 ∧
    1 - W (σ := σ) p u x.2.1 ≠ 0 ∧
    1 - D (σ := σ) (η := η) p u x.1 ≠ 0 ∧
    1 - E C p x.1 x.2.2 ≠ 0 := by
  obtain ⟨hv, hw, hd, he⟩ := norms_lt_one_star C p u x hx
  have h : ∀ a : ℂ, ‖a‖ < 1 → 1 - a ≠ 0 := by
    intro a ha heq
    have : a = 1 := (sub_eq_zero.mp heq).symm
    simp [this] at ha
  exact ⟨h _ hv, h _ hw, h _ hd, h _ he⟩

set_option maxHeartbeats 1500000 in
theorem goodFactor_differentiableOn_star
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (u : A.R) :
    DifferentiableOn ℂ (fun x : Coordinates => goodFactor C p u x.1 x.2.1 x.2.2)
      DedekindZetaZeroFree.Quantitative.EulerDomain.OmegaStar := by
  have hξ : Differentiable ℂ (fun x : Coordinates => x.1) := differentiable_fst
  have hw : Differentiable ℂ (fun x : Coordinates => x.2.1) := differentiable_snd.fst
  have hz : Differentiable ℂ (fun x : Coordinates => x.2.2) := differentiable_snd.snd
  have hv : Differentiable ℂ (fun x : Coordinates => V p x.2.2) := by
    unfold V qPower; fun_prop
  have hw' : Differentiable ℂ (fun x : Coordinates => W (σ := σ) p u x.2.1) := by
    unfold W qPower; fun_prop
  have hd : Differentiable ℂ (fun x : Coordinates => D (σ := σ) (η := η) p u x.1) := by
    unfold D qPower; fun_prop
  have he : Differentiable ℂ (fun x : Coordinates => E C p x.1 x.2.2) := by
    unfold E V qPower; fun_prop
  intro x hx
  obtain ⟨nv, nw, nd, ne⟩ := denominators_ne_zero_star C p u x hx
  have hvx := hv x
  have hwx := hw' x
  have hdx := hd x
  have hex := he x
  apply DifferentiableAt.differentiableWithinAt
  unfold goodFactor goodRational
  dsimp only
  fun_prop (disch := assumption)

theorem frequency_good_cofinite
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C) :
    ∀ᶠ p : ExteriorPrime A in Filter.cofinite, (U.j p).val = 0 := by
  apply Filter.eventually_cofinite.mpr
  have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) :=
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective
  simpa [Frequency.j, idealPrimeExponent, Multiset.count_eq_zero] using
    (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).finite_toSet.preimage
      hinj.injOn

private theorem exterior_not_mem (p : ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have he := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
  simp only [sup_idem] at he
  exact p.val.isPrime.ne_top he

theorem summable_majorant (M a : ℝ) (ha : 1 < a) :
    Summable (fun p : ExteriorPrime A => M * (Q p) ^ (-a)) := by
  let i : ExteriorPrime A → {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} :=
    fun p => ⟨p.val, exterior_not_mem p⟩
  have hi : Function.Injective i := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r : {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} => r.val) h
  have hs := (summable_exterior_prime_norm_rpow F A.Sf a ha).comp_injective hi
  simpa [Function.comp_def, i, Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
    using hs.mul_left M

theorem exists_margin (K : Set Coordinates) (hK : IsCompact K)
    (hKO : K ⊆ DedekindZetaZeroFree.Quantitative.EulerDomain.OmegaStar) :
    ∃ δ : ℝ, 0 < δ ∧ K ⊆ DedekindZetaZeroFree.Quantitative.EulerDomain.OmegaStarMargin δ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, Set.empty_subset _⟩
  let g : Coordinates → ℝ := fun p =>
    min p.1.re (min p.2.1.re (min p.2.2.re (min (6 * p.2.2.re + p.2.1.re - 1)
      (min (p.1.re + 6 * p.2.2.re - 1) (min (p.1.re + p.2.1.re - 1)
      (min (p.1.re + p.2.1.re + 6 * p.2.2.re - 2) (min (6 * p.1.re + 6 * p.2.2.re - 5)
      (min (p.1.re - 1 / 2) (min (3 * p.1.re - 2) (3 * p.1.re + p.2.1.re - 5 / 2))))))))))
  have hg : Continuous g := by
    simp only [g]
    repeat' refine Continuous.min ?_ ?_
    all_goals fun_prop
  obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
  have key : ∀ (δ : ℝ) (q : Coordinates), δ ≤ g q →
      q ∈ DedekindZetaZeroFree.Quantitative.EulerDomain.OmegaStarMargin δ := by
    intro δ q hq
    simp only [g, le_min_iff] at hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hpos : 0 < g p0 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hKO hp0
    simp only [g, lt_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  exact ⟨g p0, hpos, fun q hq => key _ q (isMinOn_iff.mp hmin q hq)⟩

section MultiVitali

open Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_fderiv_le_of_bound {G : E → ℂ} {y : E} {r M : ℝ} (hr : 0 < r)
    (hd : ∀ z ∈ closedBall y r, DifferentiableAt ℂ G z)
    (hb : ∀ z ∈ closedBall y r, ‖G z‖ ≤ M) : ‖fderiv ℂ G y‖ ≤ M / r := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb y (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM hr.le) fun h => ?_
  by_cases h0 : h = 0
  · simp [h0]
  have hh : 0 < ‖h‖ := norm_pos_iff.mpr h0
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = r / ‖h‖ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact div_pos hr hh
  have hcr : c * ‖h‖ = r := by rw [hc]; exact div_mul_cancel₀ _ hh.ne'
  obtain ⟨v, hv⟩ : ∃ v : E, v = (c : ℂ) • h := ⟨_, rfl⟩
  have hmem : ∀ t : ℂ, ‖t‖ ≤ 1 → y + t • v ∈ closedBall y r := by
    intro t ht
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, hv, norm_smul,
      Complex.norm_real, Real.norm_of_nonneg hcpos.le, hcr]
    calc ‖t‖ * r ≤ 1 * r := mul_le_mul_of_nonneg_right ht hr.le
      _ = r := one_mul r
  have haff : ∀ t : ℂ, HasDerivAt (fun t : ℂ => y + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hGy : HasFDerivAt G (fderiv ℂ G y) (y + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact (hd y (mem_closedBall_self hr.le)).hasFDerivAt
  have hderiv : HasDerivAt (fun t : ℂ => G (y + t • v)) (fderiv ℂ G y v) 0 :=
    hGy.comp_hasDerivAt (0 : ℂ) (haff 0)
  have hdφ : DifferentiableOn ℂ (fun t : ℂ => G (y + t • v)) (closedBall 0 1) := by
    intro t ht
    have ht' : ‖t‖ ≤ 1 := by simpa using ht
    have h1 : HasFDerivAt G (fderiv ℂ G (y + t • v)) (y + t • v) :=
      (hd _ (hmem t ht')).hasFDerivAt
    exact (h1.comp_hasDerivAt t (haff t)).differentiableAt.differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun t : ℂ => G (y + t • v)) (Metric.ball 0 1) :=
    ⟨hdφ.mono ball_subset_closedBall,
      hdφ.continuousOn.mono (closure_ball (0 : ℂ) one_ne_zero).subset⟩
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ)) (R := 1)
    one_pos hdc (C := M) (fun t ht => hb _ (hmem t (by simpa using ht.le)))
  rw [hderiv.deriv, div_one, hv, map_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg hcpos.le] at hest
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  have := mul_le_mul_of_nonneg_right hest hh.le
  calc ‖fderiv ℂ G y h‖ * r = c * ‖fderiv ℂ G y h‖ * ‖h‖ := by rw [← hcr]; ring
    _ ≤ M * ‖h‖ := this

theorem differentiableOn_of_tendstoLocallyUniformlyOn [ProperSpace E] {ι : Type*}
    [SemilatticeSup ι] [Nonempty ι]
    {F : ι → E → ℂ} {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : TendstoLocallyUniformlyOn F f atTop U) (hF : ∀ n, DifferentiableOn ℂ (F n) U) :
    DifferentiableOn ℂ f U := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ : ∃ r : ℝ, 0 < r ∧ closedBall x (2 * r) ⊆ U := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩
  have hK : TendstoUniformlyOn F f atTop (closedBall x (2 * r)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf _ hsub
      (isCompact_closedBall x (2 * r))
  have hKc := Metric.uniformCauchySeqOn_iff.mp hK.uniformCauchySeqOn
  have hFd : ∀ n, ∀ z ∈ closedBall x (2 * r), DifferentiableAt ℂ (F n) z :=
    fun n z hz => (hF n).differentiableAt (hU.mem_nhds (hsub hz))
  have hcauchy : UniformCauchySeqOn (fun n => fderiv ℂ (F n)) atTop (Metric.ball x r) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hKc (ε * r / 2) (by positivity)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have hyr : closedBall y r ⊆ closedBall x (2 * r) := by
      intro z hz
      rw [mem_closedBall_iff_norm] at hz ⊢
      have hy' : ‖y - x‖ < r := mem_ball_iff_norm.mp hy
      calc ‖z - x‖ = ‖(z - y) + (y - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - y‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ 2 * r := by linarith
    have hdm : ∀ z ∈ closedBall y r, DifferentiableAt ℂ (fun z => F m z - F n z) z :=
      fun z hz => (hFd m z (hyr hz)).sub (hFd n z (hyr hz))
    have hest := norm_fderiv_le_of_bound (G := fun z => F m z - F n z) (y := y) (r := r)
      (M := ε * r / 2) hr hdm (fun z hz => by
        have := hN m hm n hn z (hyr hz)
        rw [dist_eq_norm] at this
        exact this.le)
    have hy0 : y ∈ closedBall y r := mem_closedBall_self hr.le
    have heq : fderiv ℂ (fun z => F m z - F n z) y = fderiv ℂ (F m) y - fderiv ℂ (F n) y :=
      ((hFd m y (hyr hy0)).hasFDerivAt.sub (hFd n y (hyr hy0)).hasFDerivAt).fderiv
    rw [heq] at hest
    rw [dist_eq_norm]
    have : ε * r / 2 / r = ε / 2 := by field_simp
    rw [this] at hest
    linarith
  have hex : ∀ y ∈ Metric.ball x r, ∃ a, Tendsto (fun n => fderiv ℂ (F n) y) atTop (𝓝 a) :=
    fun y hy => cauchySeq_tendsto_of_complete (hcauchy.cauchySeq hy)
  choose! g' hg' using hex
  have hlim := hcauchy.tendstoUniformlyOn_of_tendsto hg'
  have hder := hasFDerivAt_of_tendstoUniformlyOn (f := F) (g := f) isOpen_ball hlim
    (fun n y hy => (hFd n y (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hy)).hasFDerivAt)
    (fun y hy => hf.tendsto_at (hsub (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hy)))
    (mem_ball_self hr)
  exact hder.differentiableAt.differentiableWithinAt

theorem diffOn_finsetProd {ι : Type*} (s : Finset ι) {G : ι → E → ℂ} {U : Set E}
    (h : ∀ i ∈ s, DifferentiableOn ℂ (G i) U) :
    DifferentiableOn ℂ (fun x => ∏ i ∈ s, G i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end MultiVitali

end

end DedekindZetaZeroFree.Quantitative.EulerProductAux

namespace DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

theorem OmegaStar_isOpen : IsOpen OmegaStar := by
  simp only [OmegaStar, Set.setOf_and]
  repeat' apply IsOpen.inter
  all_goals exact isOpen_lt (by fun_prop) (by fun_prop)

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private theorem localFactor_diffOn_star (u : D.Row)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) :
    DifferentiableOn ℂ
      (fun p : Coordinates => CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)
      OmegaStar := by
  by_cases hj : (CorrectionFactors.Frequency.j u.toFrequency pr).val = 0
  · simpa only [CorrectionFactors.localFactor, if_pos hj] using
      DedekindZetaZeroFree.Quantitative.EulerProductAux.goodFactor_differentiableOn_star D.context pr (CorrectionFactors.Frequency.u u.toFrequency)
  · exact DedekindZetaZeroFree.Quantitative.EulerBadPrime.localFactor_differentiableOn D u pr hj

private theorem hasProdUniformlyOn_star (u : D.Row) (K : Set Coordinates)
    (hK : IsCompact K) (hKO : K ⊆ OmegaStar) :
    HasProdUniformlyOn
      (fun (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (p : Coordinates) =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)
      (fun p : Coordinates =>
        ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
          CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) K := by
  obtain ⟨δ', hδ', hKm⟩ := DedekindZetaZeroFree.Quantitative.EulerProductAux.exists_margin K hK hKO
  obtain ⟨M, δ, hM, hδ, hbound⟩ := DedekindZetaZeroFree.Quantitative.EulerGoodPrime.localFactor_sub_one_le D δ' hδ'
  have hb : ∀ᶠ pr : LocalFiniteSums.ExteriorPrime D.recipe.A in Filter.cofinite,
      ∀ x ∈ K, ‖CorrectionFactors.localFactor D.context u.toFrequency pr x.1 x.2.1 x.2.2 - 1‖ ≤
        M * (LocalFiniteSums.Q pr) ^ (-(1 + δ)) := by
    filter_upwards [DedekindZetaZeroFree.Quantitative.EulerProductAux.frequency_good_cofinite D.context u.toFrequency]
      with pr hpr
    intro x hx
    have h := hbound u pr hpr x (hKm hx)
    have e : (-1 - δ) = -(1 + δ) := by ring
    rwa [e] at h
  have hcts : ∀ pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
      ContinuousOn (fun x : Coordinates =>
        CorrectionFactors.localFactor D.context u.toFrequency pr x.1 x.2.1 x.2.2 - 1) K := by
    intro pr
    exact ((localFactor_diffOn_star D u pr).continuousOn.mono hKO).sub continuousOn_const
  simpa only [add_sub_cancel] using
    (DedekindZetaZeroFree.Quantitative.EulerProductAux.summable_majorant (A := D.recipe.A) M (1 + δ)
      (by linarith)).hasProdUniformlyOn_one_add hK hb hcts

theorem Hu_normal_convergence (u : D.Row) :
    OmegaStar ⊆
      {p : Coordinates | Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)} ∧
    HasProdLocallyUniformlyOn
      (fun (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (p : Coordinates) =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)
      (fun p : Coordinates =>
        ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
          CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) OmegaStar ∧
    DifferentiableOn ℂ
      (fun p : Coordinates =>
        ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
          CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) OmegaStar ∧
    (∀ p ∈ OmegaStar ∩ CorrectionFactors.Omega,
      ∀ h : Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2),
        CorrectionFactors.H_u D.context u.toFrequency p.1 p.2.1 p.2.2 h =
          ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
            CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) := by
  have hloc : HasProdLocallyUniformlyOn
      (fun (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (p : Coordinates) =>
        CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)
      (fun p : Coordinates =>
        ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
          CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2) OmegaStar :=
    hasProdLocallyUniformlyOn_of_forall_compact OmegaStar_isOpen
      (fun K hKO hK => hasProdUniformlyOn_star D u K hK hKO)
  refine ⟨fun p hp => ?_, hloc, ?_, fun p _ h => rfl⟩
  · exact ((hasProdUniformlyOn_star D u {p} isCompact_singleton
      (Set.singleton_subset_iff.mpr hp)).hasProd (Set.mem_singleton p)).multipliable
  · have htlu : TendstoLocallyUniformlyOn
        (fun (s : Finset (LocalFiniteSums.ExteriorPrime D.recipe.A)) (p : Coordinates) =>
          ∏ pr ∈ s, CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)
        (fun p : Coordinates =>
          ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
            CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)
        Filter.atTop OmegaStar := hloc
    exact DedekindZetaZeroFree.Quantitative.EulerProductAux.differentiableOn_of_tendstoLocallyUniformlyOn
      OmegaStar_isOpen htlu fun s =>
        DedekindZetaZeroFree.Quantitative.EulerProductAux.diffOn_finsetProd s fun pr _ => localFactor_diffOn_star D u pr

end

end DedekindZetaZeroFree.Quantitative.EulerDomain
