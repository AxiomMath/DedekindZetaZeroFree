module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.ProfiledDyadicMasks
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ProductPowerClassRank
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SixthPowerChineseRemainder

@[expose] public section

namespace DedekindZetaZeroFree.RMDyadicSieveAggregation
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch ThetaPhaseSeparation

variable {F : Type} [Field F] [NumberField F]

private theorem classes_finite (A : SArithmeticData F) : Finite A.V := by
  have hn (n : ℕ) (h : n = 2 ∨ n = 3) : Finite (A.LocalPowerClasses n) := by
    have hnpos : n ≠ 0 := by rcases h with rfl | rfl <;> norm_num
    have hc := A.Vn_card F n h
    have : Finite (SArithmeticData.Vn F A n) := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hnpos)
    exact Finite.of_equiv _ (Equiv.sumPiEquivProdPi (fun v : A.Place => PowerQuotient (A.Completion v)ˣ n))
  letI := hn 2 (Or.inl rfl)
  letI := hn 3 (Or.inr rfl)
  exact Finite.of_equiv _ A.localSixthPowerCRT.symm.toEquiv

private theorem finiteMinkowski {I J : Type*} [Fintype I]
    (s : Finset J) (a : J → I → ℂ) :
    Real.sqrt (∑ i, ‖∑ j ∈ s, a j i‖ ^ 2) ≤
      ∑ j ∈ s, Real.sqrt (∑ i, ‖a j i‖ ^ 2) := by
  let v : J → EuclideanSpace ℂ I := fun j => WithLp.toLp 2 (a j)
  have he : (WithLp.toLp 2 (fun i => ∑ j ∈ s, a j i) : EuclideanSpace ℂ I) =
      ∑ j ∈ s, v j := by
    ext i
    simp [v]
  calc
    _ = ‖(WithLp.toLp 2 (fun i => ∑ j ∈ s, a j i) : EuclideanSpace ℂ I)‖ := by
      simpa only [PiLp.toLp_apply] using
        (EuclideanSpace.norm_eq (WithLp.toLp 2 (fun i => ∑ j ∈ s, a j i) :
          EuclideanSpace ℂ I)).symm
    _ = ‖∑ j ∈ s, v j‖ := congrArg norm he
    _ ≤ ∑ j ∈ s, ‖v j‖ := norm_sum_le _ _
    _ = _ := by simp only [v, EuclideanSpace.norm_eq, PiLp.toLp_apply]

theorem frozen_scalar_norm_le (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1) (T : Frozen A) :
    ‖omega A G U σ ψ L T / (A.exteriorNorm T.n : ℂ)‖ ≤
      betaIdeal (RMSeparatedExpansion.activeSupport A T) T.a.val /
        A.exteriorNorm T.n := by
  have hn : 0 < A.exteriorNorm T.n :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.n.property.1)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  exact (RMSeparatedExpansion.factors_norm_le_betaIdeal A G U σ ψ hψ L hL T T.h T.f).1

theorem frozen_profileArgument_dyadic (A : SArithmeticData F) (T : Frozen A)
    (d c : A.Exterior) (Z C D : ℝ) (hC : 0 < C) (hD : 0 < D) :
    profileArgument A T d c Z =
      (Z * A.exteriorNorm T.a * A.exteriorNorm T.n ^ 3 * C /
        (D ^ 2 * A.exteriorNorm T.f ^ 2)) *
        (A.exteriorNorm c / C) * (A.exteriorNorm d / D) ^ (-2 : ℤ) := by
  have hd : 0 < A.exteriorNorm d :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ d.property.1)
  have hf : 0 < A.exteriorNorm T.f :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.f.property.1)
  simp only [profileArgument, zpow_neg, zpow_ofNat]
  field_simp
  <;> ring

theorem frozen_summand_sieve_form (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (h𝓕 : ∀ d c : ExteriorSquarefreeIdeal A.cS,
      (𝓕.χ c.val.val) d.val.val = quadraticPairing A G σ d.val c.val)
    (T : Frozen A) (d c : ExteriorSquarefreeIdeal A.cS)
    (sd sc : G.B) (hd : RMSeparatedExpansion.rowClass A G d.val = sd)
    (hc : RMSeparatedExpansion.rowClass A G c.val = sc)
    (Φ : ℝ → ℂ) (hΦ : H (profileIndex A G U T sd sc) = Φ)
    (Z C D : ℝ) (hC : 0 < C) (hD : 0 < D) :
    RMSeparatedExpansion.summand A G U σ ψ L H T d.val c Z =
      if d.val.val ⊔ (T.h.val * T.n.val) = ⊤ ∧ c.val.val ⊔ T.f.val = ⊤ then
        (omega A G U σ ψ L T / (A.exteriorNorm T.n : ℂ)) *
          rho A G U σ ψ L T d.val *
          (lambda A G U σ ψ L T c.val *
            Complex.ofReal ((A.exteriorNorm c.val) ^ (-(1 / 2 : ℝ))) *
            (𝓕.χ c.val.val) d.val.val *
            Φ ((Z * A.exteriorNorm T.a * A.exteriorNorm T.n ^ 3 * C /
                (D ^ 2 * A.exteriorNorm T.f ^ 2)) *
              (A.exteriorNorm c.val / C) * (A.exteriorNorm d.val / D) ^ (-2 : ℤ)))
      else 0 := by
  have he : H (RMSeparatedExpansion.termClass A G U T d.val c.val) = Φ := by
    simpa only [RMSeparatedExpansion.termClass, hd, hc] using hΦ
  have hcn : 0 < A.exteriorNorm c.val :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ c.val.property.1)
  have hn : 0 < A.exteriorNorm T.n :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.n.property.1)
  have hs : 0 < Real.sqrt (A.exteriorNorm c.val) := Real.sqrt_pos.mpr hcn
  have hp : (A.exteriorNorm c.val) ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt (A.exteriorNorm c.val))⁻¹ := by
    rw [Real.rpow_neg hcn.le, Real.sqrt_eq_rpow]
  rw [RMSeparatedExpansion.summand, he,
    frozen_profileArgument_dyadic A T _ _ Z C D hC hD,
    separatedCoefficient, ← h𝓕 d c, hp]
  simp only [rowMask, columnMask, Complex.ofReal_inv]
  split_ifs <;> simp_all <;> field_simp <;> ring

theorem frozen_row_window_finite (A : SArithmeticData F) (h : A.Exterior) (D : ℝ) :
    {d : ExteriorSquarefreeIdeal A.cS |
      D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D ∧
        d.val.val ⊔ h.val = ⊤}.Finite := by
  let f : ExteriorSquarefreeIdeal A.cS → NonzeroIdeal F :=
    fun d => ⟨d.val.val, d.val.property.1⟩
  apply Set.Finite.of_injOn (f := f) (t := normBoundedIdeals F (2 * D))
  · intro d hd
    exact hd.2.1.le
  · intro d _ e _ hde
    exact Subtype.ext (Subtype.ext (congrArg (fun i : NonzeroIdeal F => i.val) hde))
  · exact normBoundedIdeals_finite F (2 * D)

theorem frozen_row_finsum_eq_sum (A : SArithmeticData F) (h : A.Exterior)
    (D : ℝ) (g : ExteriorSquarefreeIdeal A.cS → ℝ) :
    (∑ᶠ d : {d : ExteriorSquarefreeIdeal A.cS |
      D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D ∧
        d.val.val ⊔ h.val = ⊤}, g d.val) =
      ∑ d ∈ (frozen_row_window_finite A h D).toFinset, g d := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_mem_eq_finite_toFinset_sum g (frozen_row_window_finite A h D)

theorem frozen_profile_scale_pos (A : SArithmeticData F) (T : Frozen A)
    (Z C D : ℝ) (hZ : 0 < Z) (hC : 0 < C) (hD : 0 < D) :
    0 < Z * A.exteriorNorm T.a * A.exteriorNorm T.n ^ 3 * C /
      (D ^ 2 * A.exteriorNorm T.f ^ 2) := by
  have ha : 0 < A.exteriorNorm T.a :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.a.property.1)
  have hn : 0 < A.exteriorNorm T.n :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.n.property.1)
  have hf : 0 < A.exteriorNorm T.f :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.f.property.1)
  positivity

 def liftColumn (A : SArithmeticData F) (f : ExteriorSquarefreeIdeal A.cS → ℂ)
    (I : Ideal (𝓞 F)) : ℂ :=
  if h : ∃ d : ExteriorSquarefreeIdeal A.cS, d.val.val = I then f h.choose else 0
private theorem liftColumn_apply (A : SArithmeticData F)
    (f : ExteriorSquarefreeIdeal A.cS → ℂ) (d : ExteriorSquarefreeIdeal A.cS) :
    liftColumn A f d.val.val = f d := by
  have h : ∃ e : ExteriorSquarefreeIdeal A.cS, e.val.val = d.val.val := ⟨d, rfl⟩
  have he : h.choose = d := Subtype.ext (Subtype.ext h.choose_spec)
  simp only [liftColumn, dif_pos h, he]
private theorem liftColumn_norm_le (A : SArithmeticData F)
    (f : ExteriorSquarefreeIdeal A.cS → ℂ) (hf : ∀ d, ‖f d‖ ≤ 1) :
    ∀ I, ‖liftColumn A f I‖ ≤ 1 := by
  intro I
  dsimp [liftColumn]
  split_ifs <;> simp_all

theorem frozen_exterior_profiled_hgl
     (A : SArithmeticData F)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (J : Type) [Fintype J] (Φ : J → ℝ → ℂ)
    (hΦ : RMFourierProfile.UniformLogBounds Φ) (b : ℝ) (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : J) (C D v : ℝ)
      (cs rs : Finset (ExteriorSquarefreeIdeal A.cS))
      (lam ρ : ExteriorSquarefreeIdeal A.cS → ℂ),
      1 ≤ C → 1 ≤ D → 0 < v →
      (∀ c ∈ cs, C ≤ A.exteriorNorm c.val ∧ A.exteriorNorm c.val < 2 * C) →
      (∀ d ∈ rs, D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D) →
      (∀ c, ‖lam c‖ ≤ 1) → (∀ d, ‖ρ d‖ ≤ 1) →
      Real.sqrt (∑ d ∈ rs, ‖ρ d * ∑ c ∈ cs,
        lam c * Complex.ofReal ((A.exteriorNorm c.val) ^ (-(1 / 2 : ℝ))) *
          (𝓕.χ c.val.val) d.val.val *
          Φ j (v * (A.exteriorNorm c.val / C) *
            (A.exteriorNorm d.val / D) ^ (-2 : ℤ))‖ ^ 2) ≤
        M * (D * C) ^ (b / 2) * Real.sqrt (D + C) := by
  obtain ⟨M, hM, hbound⟩ := RMMaskedDyadic.finite_profiled_hgl F A.zeta12
    A.primitive_zeta12 A.cS 𝓕 J Φ hΦ b hb
  refine ⟨M, hM, ?_⟩
  intro j C D v cs rs lam ρ hC hD hv hcs hrs hlam hρ
  let f : ExteriorSquarefreeIdeal A.cS → Ideal (𝓞 F) := fun d => d.val.val
  have hf : Function.Injective f := fun d e h => Subtype.ext (Subtype.ext h)
  have hc : ∀ I ∈ cs.image f, Squarefree I ∧ I ⊔ A.cS = ⊤ ∧
      C ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) < 2 * C := by
    intro I hI
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨c.property, c.val.property.2, hcs c hc⟩
  have hr : ∀ I ∈ rs.image f, Squarefree I ∧ I ⊔ A.cS = ⊤ ∧
      D ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) < 2 * D := by
    intro I hI
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨d.property, d.val.property.2, hrs d hd⟩
  have h := hbound j C D v (cs.image f) (rs.image f) (liftColumn A lam)
    (liftColumn A ρ) hC hD hv hc hr (liftColumn_norm_le A lam hlam)
    (liftColumn_norm_le A ρ hρ)
  rw [Finset.sum_image hf.injOn] at h
  simp_rw [Finset.sum_image hf.injOn] at h
  dsimp only [f] at h
  simp_rw [liftColumn_apply] at h
  exact h

set_option maxHeartbeats 1000000 in
theorem frozen_sliced_dyadic_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (h𝓕 : ∀ d c : ExteriorSquarefreeIdeal A.cS,
      (𝓕.χ c.val.val) d.val.val = quadraticPairing A G σ d.val c.val)
    (b : ℝ) (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ (u : A.UnitQuotient) (T : Frozen A)
      (sd sc : G.B) (Z C D : ℝ)
      (cs rs : Finset (ExteriorSquarefreeIdeal A.cS)),
      0 < Z → 1 ≤ C → 1 ≤ D →
      (∀ c ∈ cs, RMSeparatedExpansion.rowClass A G c.val = sc ∧
        C ≤ A.exteriorNorm c.val ∧ A.exteriorNorm c.val < 2 * C) →
      (∀ d ∈ rs, RMSeparatedExpansion.rowClass A G d.val = sd ∧
        D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D) →
      Real.sqrt (∑ d ∈ rs, ‖∑ c ∈ cs,
        RMSeparatedExpansion.summand A G U σ ψ (L u) (H u) T d.val c Z‖ ^ 2) ≤
        M * (betaIdeal (RMSeparatedExpansion.activeSupport A T) T.a.val /
          A.exteriorNorm T.n) *
          Real.rpow (D * C) (b / 2) * Real.sqrt (D + C) := by
  obtain ⟨I, P, hcover, hC2, hdecay⟩ := hH
  have hp : RMFourierProfile.UniformLogBounds P := ⟨hC2, hdecay⟩
  obtain ⟨M, hM, hbound⟩ := frozen_exterior_profiled_hgl A 𝓕 I P hp b hb
  refine ⟨M, hM, ?_⟩
  intro u T sd sc Z C D cs rs hZ hC hD hcs hrs
  have hCp : 0 < C := by linarith
  have hDp : 0 < D := by linarith
  obtain ⟨j, hj⟩ := hcover u (profileIndex A G U T sd sc)
  let v := Z * A.exteriorNorm T.a * A.exteriorNorm T.n ^ 3 * C /
    (D ^ 2 * A.exteriorNorm T.f ^ 2)
  let W : ℂ := omega A G U σ ψ (L u) T / (A.exteriorNorm T.n : ℂ)
  let R : ExteriorSquarefreeIdeal A.cS → ℂ := fun d =>
    if d.val.val ⊔ (T.h.val * T.n.val) = ⊤ then rho A G U σ ψ (L u) T d.val else 0
  let K : ExteriorSquarefreeIdeal A.cS → ℂ := fun c =>
    if c.val.val ⊔ T.f.val = ⊤ then lambda A G U σ ψ (L u) T c.val else 0
  have hR : ∀ d, ‖R d‖ ≤ 1 := by
    intro d
    dsimp [R]
    split_ifs
    · exact (RMSeparatedExpansion.factors_norm_le_betaIdeal A G U σ ψ hψ (L u)
        (hL u) T d.val T.f).2.1
    · simp
  have hK : ∀ c, ‖K c‖ ≤ 1 := by
    intro c
    dsimp [K]
    split_ifs
    · exact (RMSeparatedExpansion.factors_norm_le_betaIdeal A G U σ ψ hψ (L u)
        (hL u) T T.h c.val).2.2
    · simp
  let k : ExteriorSquarefreeIdeal A.cS → ExteriorSquarefreeIdeal A.cS → ℂ :=
    fun c d => K c * Complex.ofReal ((A.exteriorNorm c.val) ^ (-(1 / 2 : ℝ))) *
      (𝓕.χ c.val.val) d.val.val *
      P j (v * (A.exteriorNorm c.val / C) * (A.exteriorNorm d.val / D) ^ (-2 : ℤ))
  have he (d) (hd : d ∈ rs) (c) (hc : c ∈ cs) :
      RMSeparatedExpansion.summand A G U σ ψ (L u) (H u) T d.val c Z =
        W * R d * k c d := by
    rw [frozen_summand_sieve_form A G U σ ψ (L u) (H u) 𝓕 h𝓕 T d c sd sc
      (hrs d hd).1 (hcs c hc).1 (P j) hj Z C D hCp hDp]
    dsimp [W, R, K, k, v]
    split_ifs <;> simp_all
  have hes (d) (hd : d ∈ rs) :
      (∑ c ∈ cs, RMSeparatedExpansion.summand A G U σ ψ (L u) (H u) T d.val c Z) =
        W * (R d * ∑ c ∈ cs, k c d) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [he d hd c hc, mul_assoc]
  have hm : (∑ d ∈ rs, ‖∑ c ∈ cs,
      RMSeparatedExpansion.summand A G U σ ψ (L u) (H u) T d.val c Z‖ ^ 2) =
      ‖W‖ ^ 2 * ∑ d ∈ rs, ‖R d * ∑ c ∈ cs, k c d‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hes d hd, norm_mul, mul_pow]
  have hs : Real.sqrt (∑ d ∈ rs, ‖∑ c ∈ cs,
      RMSeparatedExpansion.summand A G U σ ψ (L u) (H u) T d.val c Z‖ ^ 2) =
      ‖W‖ * Real.sqrt (∑ d ∈ rs, ‖R d * ∑ c ∈ cs, k c d‖ ^ 2) := by
    rw [hm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hB := hbound j C D v cs rs K R hC hD
    (frozen_profile_scale_pos A T Z C D hZ hCp hDp)
    (fun c hc => (hcs c hc).2) (fun d hd => (hrs d hd).2) hK hR
  have hW := frozen_scalar_norm_le A G U σ ψ hψ (L u) (hL u) T
  rw [hs]
  calc
    _ ≤ ‖W‖ * (M * (D * C) ^ (b / 2) * Real.sqrt (D + C)) :=
      mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ ≤ (betaIdeal (RMSeparatedExpansion.activeSupport A T) T.a.val /
      A.exteriorNorm T.n) * (M * (D * C) ^ (b / 2) * Real.sqrt (D + C)) :=
      mul_le_mul_of_nonneg_right hW (by positivity)
    _ = _ := by simp only [Real.rpow_eq_pow]; ring

theorem frozen_dyadic_block_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (h𝓕 : ∀ d c : ExteriorSquarefreeIdeal A.cS,
      (𝓕.χ c.val.val) d.val.val = quadraticPairing A G σ d.val c.val)
    (b : ℝ) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : A.UnitQuotient) (h : A.Exterior)
        (T : {T : Frozen A // T.h = h}) (Z C D : ℝ)
        (s : Finset (RMSeparatedExpansion.Index A h)),
        0 < Z → 1 ≤ C → 1 ≤ D →
        (∀ i ∈ s, i.1 = T ∧
          C ≤ A.exteriorNorm i.2.val ∧ A.exteriorNorm i.2.val < 2 * C) →
        Real.sqrt (∑ᶠ d : {d : ExteriorSquarefreeIdeal A.cS |
          D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D ∧
            d.val.val ⊔ h.val = ⊤},
          ‖∑ i ∈ s,
            RMSeparatedExpansion.summand A G U σ ψ (L u) (H u)
              i.1.val d.val.val i.2 Z‖ ^ 2) ≤
          K * (betaIdeal (RMSeparatedExpansion.activeSupport A T.val) T.val.a.val /
            A.exteriorNorm T.val.n) *
            Real.rpow (D * C) (b / 2) * Real.sqrt (D + C) := by
  letI : Finite A.V := classes_finite A
  letI : Fintype G.B := Fintype.ofFinite _
  obtain ⟨M, hM, hbound⟩ := frozen_sliced_dyadic_bound A G U σ ψ hψ L hL H hH 𝓕 h𝓕 b hb
  refine ⟨(Fintype.card (G.B × G.B) : ℝ) * M, by positivity, ?_⟩
  intro u h T Z C D s hZ hC hD hs
  let cs := s.image (fun i => i.2)
  let rs := (frozen_row_window_finite A h D).toFinset
  let f : ExteriorSquarefreeIdeal A.cS → ExteriorSquarefreeIdeal A.cS → ℂ :=
    fun d c => RMSeparatedExpansion.summand A G U σ ψ (L u) (H u) T.val d.val c Z
  have hinj : Set.InjOn (fun i : RMSeparatedExpansion.Index A h => i.2) s := by
    intro i hi j hj he
    exact Prod.ext ((hs i hi).1.trans (hs j hj).1.symm) he
  have hsum (d : ExteriorSquarefreeIdeal A.cS) :
      (∑ i ∈ s, RMSeparatedExpansion.summand A G U σ ψ (L u) (H u)
        i.1.val d.val i.2 Z) = ∑ c ∈ cs, f d c := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f, (hs i hi).1]
  have hcs (c) (hc : c ∈ cs) :
      C ≤ A.exteriorNorm c.val ∧ A.exteriorNorm c.val < 2 * C := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    exact (hs i hi).2
  have hrs (d) (hd : d ∈ rs) :
      D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D := by
    exact ⟨((frozen_row_window_finite A h D).mem_toFinset.mp hd).1,
      ((frozen_row_window_finite A h D).mem_toFinset.mp hd).2.1⟩
  letI : Fintype rs := inferInstance
  let a : G.B × G.B → ExteriorSquarefreeIdeal A.cS → ℂ := fun q d =>
    if RMSeparatedExpansion.rowClass A G d.val = q.1 then
      ∑ c ∈ cs.filter (fun c => RMSeparatedExpansion.rowClass A G c.val = q.2), f d c
    else 0
  have ha (d : ExteriorSquarefreeIdeal A.cS) : (∑ c ∈ cs, f d c) = ∑ q, a q d := by
    simp only [a, Fintype.sum_prod_type, Finset.sum_filter]
    simp
    rw [Finset.sum_comm]
    simp
  have hq (q : G.B × G.B) : Real.sqrt (∑ d : rs, ‖a q d.val‖ ^ 2) ≤
      M * (betaIdeal (RMSeparatedExpansion.activeSupport A T.val) T.val.a.val /
        A.exteriorNorm T.val.n) * Real.rpow (D * C) (b / 2) * Real.sqrt (D + C) := by
    have hbq := hbound u T.val q.1 q.2 Z C D
      (cs.filter (fun c => RMSeparatedExpansion.rowClass A G c.val = q.2))
      (rs.filter (fun d => RMSeparatedExpansion.rowClass A G d.val = q.1))
      hZ hC hD
      (fun c hc => ⟨(Finset.mem_filter.mp hc).2, hcs c (Finset.mem_filter.mp hc).1⟩)
      (fun d hd => ⟨(Finset.mem_filter.mp hd).2, hrs d (Finset.mem_filter.mp hd).1⟩)
    have he : (∑ d : rs, ‖a q d.val‖ ^ 2) =
        ∑ d ∈ rs.filter (fun d => RMSeparatedExpansion.rowClass A G d.val = q.1),
          ‖∑ c ∈ cs.filter (fun c => RMSeparatedExpansion.rowClass A G c.val = q.2),
            RMSeparatedExpansion.summand A G U σ ψ (L u) (H u) T.val d.val c Z‖ ^ 2 := by
      rw [Finset.sum_coe_sort rs (fun d => ‖a q d‖ ^ 2), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases he : RMSeparatedExpansion.rowClass A G d.val = q.1
      · simp only [a, f, he, if_true]
      · simp only [a, he, if_false, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    rw [he]
    exact hbq
  rw [frozen_row_finsum_eq_sum A h D (fun d =>
    ‖∑ i ∈ s, RMSeparatedExpansion.summand A G U σ ψ (L u) (H u)
      i.1.val d.val i.2 Z‖ ^ 2)]
  simp_rw [hsum]
  change Real.sqrt (∑ d ∈ rs, ‖∑ c ∈ cs, f d c‖ ^ 2) ≤ _
  rw [← Finset.sum_coe_sort]
  simp_rw [ha]
  apply (finiteMinkowski Finset.univ (fun q (d : rs) => a q d.val)).trans
  calc
    _ ≤ ∑ q : G.B × G.B, M *
        (betaIdeal (RMSeparatedExpansion.activeSupport A T.val) T.val.a.val /
          A.exteriorNorm T.val.n) * Real.rpow (D * C) (b / 2) * Real.sqrt (D + C) :=
      Finset.sum_le_sum (fun q _ => hq q)
    _ = _ := by simp; ring

end
end DedekindZetaZeroFree.RMDyadicSieveAggregation
