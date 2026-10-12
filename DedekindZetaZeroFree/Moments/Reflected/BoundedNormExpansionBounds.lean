module

public import DedekindZetaZeroFree.Moments.Reflected.DyadicBranchAggregation
public import DedekindZetaZeroFree.Moments.Reflected.DyadicSquareSum

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.RMParameterAbsorption
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch RMSeparatedExpansion

variable {F : Type} [Field F] [NumberField F]

private theorem idealSymbol_norm_le_one (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : Fˣ) : ‖ThetaPhaseSeparation.idealSymbol A σ I x‖ ≤ 1 := by
  unfold ThetaPhaseSeparation.idealSymbol
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro p _; exact norm_nonneg _
  · intro p _
    unfold symbol
    let q := supportPrime A I p
    let χ := residueCharacter A σ q
    let a := unitResidue q.val x
    change ‖χ a‖ ≤ 1
    by_cases ha : a = 0
    · simp [ha, MulChar.map_zero]
    · letI : Fintype (DHCubic.Residue F q.val) := Fintype.ofFinite _
      have hn := Complex.norm_eq_one_of_mem_rootsOfUnity
        (χ.apply_mem_rootsOfUnity (Units.mk0 a ha))
      simpa using hn.le

private theorem separatedCoefficient_norm_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (T : ThetaPhaseSeparation.Frozen A) (d c : A.Exterior) :
    ‖ThetaPhaseSeparation.separatedCoefficient A G U σ ψ L T d c‖ ≤
      betaIdeal (activeSupport A T) T.a.val /
        (Real.sqrt (A.exteriorNorm c) * A.exteriorNorm T.n) := by
  have hc : 0 < A.exteriorNorm c := lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ c.property.1)
  have hn : 0 < A.exteriorNorm T.n := lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.n.property.1)
  have hbeta : 0 ≤ betaIdeal (activeSupport A T) T.a.val := by
    have h := factors_norm_le_betaIdeal A G U σ ψ hψ L hL T d c
    exact (norm_nonneg _).trans h.1
  have hf := factors_norm_le_betaIdeal A G U σ ψ hψ L hL T d c
  have hs := idealSymbol_norm_le_one A σ d (G.generator c)
  rw [separatedCoefficient_support A G U σ ψ L T d c]
  split_ifs
  · simp only [norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ betaIdeal (activeSupport A T) T.a.val * 1 * 1 * 1 ^ 3 := by
        gcongr
        · exact hf.1
        · exact hf.2.1
        · exact hf.2.2
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

private theorem summand_positiveRowWeight_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (H : A.V → ℝ → ℂ) (K : ℝ) (hK : 0 < K)
    (hH : ∀ v x, 0 < x → ‖H v x‖ ≤ K / x)
    (T : ThetaPhaseSeparation.Frozen A) (d : A.Exterior)
    (c : ExteriorSquarefreeIdeal A.cS) (Z : ℝ) (hZ : 0 < Z) :
    ‖summand A G U σ ψ L H T d c Z‖ ≤
      (K * (A.exteriorNorm d ^ 2 * A.exteriorNorm T.f ^ 2) / Z) *
        positiveRowWeight (activeSupport A T) 1
          (⟨T.a, T.a_supported⟩, c, T.n) := by
  have ha : 0 < A.exteriorNorm T.a :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.a.property.1)
  have hc : 0 < A.exteriorNorm c.val :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ c.val.property.1)
  have hn : 0 < A.exteriorNorm T.n :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.n.property.1)
  have hd : 0 < A.exteriorNorm d :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ d.property.1)
  have hf : 0 < A.exteriorNorm T.f :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.f.property.1)
  have hx : 0 < ThetaPhaseSeparation.profileArgument A T d c.val Z := by
    unfold ThetaPhaseSeparation.profileArgument; positivity
  have hcoeff := separatedCoefficient_norm_bound A G U σ ψ hψ L hL T d c.val
  have hb : 0 ≤ betaIdeal (activeSupport A T) T.a.val :=
    (norm_nonneg _).trans (factors_norm_le_betaIdeal A G U σ ψ hψ L hL T d c.val).1
  have hprofile := hH (termClass A G U T d c.val)
    (ThetaPhaseSeparation.profileArgument A T d c.val Z) hx
  unfold summand
  rw [norm_mul]
  calc
    _ ≤ (betaIdeal (activeSupport A T) T.a.val /
        (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm T.n)) *
        (K / ThetaPhaseSeparation.profileArgument A T d c.val Z) := by
      exact mul_le_mul hcoeff hprofile (norm_nonneg _) (by positivity)
    _ = _ := by
      unfold positiveRowWeight ThetaPhaseSeparation.profileArgument rowNorm
      change _ = (K * (A.exteriorNorm d ^ 2 * A.exteriorNorm T.f ^ 2) / Z) *
        (betaIdeal (activeSupport A T) T.a.val *
          (A.exteriorNorm T.a * A.exteriorNorm c.val * A.exteriorNorm T.n ^ 3) ^ (-1 : ℝ) /
          (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm T.n))
      rw [Real.rpow_neg_one]
      have hsc : 0 < Real.sqrt (A.exteriorNorm c.val) := Real.sqrt_pos.mpr hc
      field_simp

 abbrev CompactMajorantIndex (A : SArithmeticData F) (h : A.Exterior) :=
  (f : {f : ExteriorSquarefreeIdeal A.cS //
      f.val.val ∈ activeSquarefreeDivisors h.val}) ×
    (A.UnitQuotient × PositiveRowIndex f.val)

 def compactMajorantIndexMap (A : SArithmeticData F) (h : A.Exterior) :
    Index A h → CompactMajorantIndex A h := fun i =>
  ⟨⟨activeSupport A i.1.val,
      (mem_activeSquarefreeDivisors_iff h.val h.property.1 _).mpr
        ⟨i.1.val.f.property.1, i.1.val.f_squarefree,
          by simpa only [activeSupport, i.1.property] using i.1.val.f_divides_radical⟩⟩,
    i.1.val.epsilon, ⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n⟩

private theorem compactMajorantIndexMap_injective (A : SArithmeticData F) (h : A.Exterior) :
    Function.Injective (compactMajorantIndexMap A h) := by
  intro i j hij
  have hf : i.1.val.f = j.1.val.f := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.1.val.val) hij
    exact hh
  have he : i.1.val.epsilon = j.1.val.epsilon := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.1) hij
    exact hh
  have ha : i.1.val.a = j.1.val.a := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.2.1.val) hij
    exact hh
  have hc : i.2 = j.2 := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.2.2.1) hij
    exact hh
  have hn : i.1.val.n = j.1.val.n := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.2.2.2) hij
    exact hh
  have hh : i.1.val.h = j.1.val.h := i.1.property.trans j.1.property.symm
  have hT : i.1.val = j.1.val := by
    generalize hi : i.1.val = Ti at hf he ha hn hh ⊢
    generalize hj : j.1.val = Tj at hf he ha hn hh ⊢
    cases Ti
    cases Tj
    simp_all
  exact Prod.ext (Subtype.ext hT) hc

private theorem positiveRowWeight_nonneg {A : SArithmeticData F} (f : ExteriorSquarefreeIdeal A.cS)
    (x : PositiveRowIndex f) : 0 ≤ positiveRowWeight f 1 x := by
  have hb := betaIdealTerm_nonneg f 0 (by norm_num) x.1
  simp only [betaIdealTerm, neg_zero] at hb
  change 0 ≤ betaIdeal f x.1.val.val * (idealNorm x.1.val.val) ^ (0 : ℝ) at hb
  simp only [Real.rpow_zero, mul_one] at hb
  unfold positiveRowWeight
  have ha := idealNorm_ge_one _ x.1.val.property.1
  have hc := idealNorm_ge_one _ x.2.1.val.property.1
  have hn := idealNorm_ge_one _ x.2.2.property.1
  unfold rowNorm
  apply div_nonneg
  · exact mul_nonneg hb (Real.rpow_nonneg (by positivity) _)
  · positivity

private theorem unitQuotient_finite (A : SArithmeticData F) : Finite A.UnitQuotient := by
  letI := SArithmeticData.sunitSixthPowerQuotient_finite F A
  exact Finite.of_equiv (PowerQuotient A.Rˣ 6)
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ 6 A.unitEquiv).symm.toEquiv

private theorem compactActive_finite (A : SArithmeticData F) (h : A.Exterior) :
    Finite {f : ExteriorSquarefreeIdeal A.cS //
      f.val.val ∈ activeSquarefreeDivisors h.val} := by
  let e : {f : ExteriorSquarefreeIdeal A.cS // f.val.val ∈ activeSquarefreeDivisors h.val} →
      {f : Ideal (𝓞 F) // f ∈ activeSquarefreeDivisors h.val} :=
    fun f => ⟨f.val.val.val, f.property⟩
  have he : Function.Injective e := by
    intro f g hh
    have hv : f.val.val.val = g.val.val.val := congrArg (fun k => k.val) hh
    exact Subtype.ext (Subtype.ext (Subtype.ext hv))
  exact Finite.of_injective e he

set_option maxHeartbeats 1200000 in

private theorem compactWeightedMajorant_summable (A : SArithmeticData F) (h : A.Exterior) :
    Summable (fun k : CompactMajorantIndex A h =>
      A.exteriorNorm k.1.val.val ^ 2 * positiveRowWeight k.1.val 1 k.2.2) := by
  letI := unitQuotient_finite A
  letI := Fintype.ofFinite A.UnitQuotient
  let T := {f : ExteriorSquarefreeIdeal A.cS // f.val.val ∈ activeSquarefreeDivisors h.val}
  letI : Finite T := compactActive_finite A h
  letI : Fintype T := Fintype.ofFinite _
  let W : (f : T) → (A.UnitQuotient × PositiveRowIndex f.val) → ℝ :=
    fun f k => A.exteriorNorm f.val.val ^ 2 * positiveRowWeight f.val 1 k.2
  have hw : ∀ f k, 0 ≤ W f k := fun f k =>
    mul_nonneg (sq_nonneg _) (positiveRowWeight_nonneg (A := A) f.val k.2)
  have hf : ∀ f, Summable (W f) := by
    intro f
    have hs := (positiveRowWeight_summable_le f.val 1 (by norm_num)).1
    have hs' := hs.mul_left (A.exteriorNorm f.val.val ^ 2)
    exact (summable_prod_of_nonneg (hw f)).2
      ⟨fun _ => hs', (hasSum_fintype _).summable⟩
  have he : Summable (fun k : (f : T) × (A.UnitQuotient × PositiveRowIndex f.val) => W k.1 k.2) := by
    apply (summable_sigma_of_nonneg (f := fun k : (f : T) × (A.UnitQuotient × PositiveRowIndex f.val) => W k.1 k.2)
      (fun k => hw k.1 k.2)).2
    exact ⟨hf, (hasSum_fintype _).summable⟩
  simpa only [T, W, CompactMajorantIndex] using he

 def compactRowMajorant (A : SArithmeticData F) (h : A.Exterior) : ℝ :=
  ∑' k : CompactMajorantIndex A h,
    A.exteriorNorm k.1.val.val ^ 2 * positiveRowWeight k.1.val 1 k.2.2

 private theorem compactRowMajorant_nonneg (A : SArithmeticData F) (h : A.Exterior) :
    0 ≤ compactRowMajorant A h :=
  tsum_nonneg (fun k => mul_nonneg (sq_nonneg _) (positiveRowWeight_nonneg (A := A) k.1.val k.2.2))

private theorem expansion_compactRowMajorant_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (H : A.V → ℝ → ℂ) (K : ℝ) (hK : 0 < K)
    (hH : ∀ v x, 0 < x → ‖H v x‖ ≤ K / x)
    (h d : A.Exterior) (Z : ℝ) (hZ : 0 < Z) :
    ‖expansion A G U σ ψ L H h d Z‖ ≤
      (K * A.exteriorNorm d ^ 2 / Z) * compactRowMajorant A h := by
  let W : CompactMajorantIndex A h → ℝ := fun k =>
    A.exteriorNorm k.1.val.val ^ 2 * positiveRowWeight k.1.val 1 k.2.2
  let c : ℝ := K * A.exteriorNorm d ^ 2 / Z
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hW : Summable W := compactWeightedMajorant_summable A h
  have hW0 : ∀ k, 0 ≤ W k := fun k =>
    mul_nonneg (sq_nonneg _) (positiveRowWeight_nonneg (A := A) k.1.val k.2.2)
  let e := compactMajorantIndexMap A h
  have he : Function.Injective e := compactMajorantIndexMap_injective A h
  have hs := (hW.comp_injective he).mul_left c
  have hb : ∀ i : Index A h,
      ‖summand A G U σ ψ L H i.1.val d i.2 Z‖ ≤ c * W (e i) := by
    intro i
    have hi := summand_positiveRowWeight_bound A G U σ ψ hψ L hL H K hK hH i.1.val d i.2 Z hZ
    convert hi using 1 <;> dsimp [c, W, e, compactMajorantIndexMap, activeSupport] <;> ring
  have hn : Summable (fun i : Index A h => ‖summand A G U σ ψ L H i.1.val d i.2 Z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  unfold expansion
  calc
    _ ≤ ∑' i : Index A h, ‖summand A G U σ ψ L H i.1.val d i.2 Z‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i : Index A h, c * W (e i) := hn.tsum_le_tsum hb hs
    _ ≤ ∑' k, c * W k := tsum_comp_le_tsum_of_inj (hW.mul_left c)
      (fun k => mul_nonneg hc (hW0 k)) he
    _ = _ := by rw [tsum_mul_left]; rfl

theorem bounded_norm_expansion
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (Kprofile : ℝ) (hKprofile : 0 < Kprofile)
    (hH : ∀ u v x, 0 < x → ‖H u v x‖ ≤ Kprofile / x)
    (X : ℝ) (hX : 0 < X) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Z : ℝ), 1 ≤ Z →
      ∀ (u : A.UnitQuotient) (h d : A.Exterior),
        A.exteriorNorm h ≤ X → A.exteriorNorm d ≤ X →
        ‖expansion A G U σ ψ (L u) (H u) h d Z‖ ≤ B := by
  let e : A.Exterior → NonzeroIdeal F := fun I => ⟨I.val, I.property.1⟩
  have he : Function.Injective e := by
    intro I J h
    exact Subtype.ext (congrArg (fun k : NonzeroIdeal F => k.val) h)
  have hs : {h : A.Exterior | A.exteriorNorm h ≤ X}.Finite := by
    exact (normBoundedIdeals_finite F X).preimage he.injOn
  let s : Finset A.Exterior := hs.toFinset
  let C : ℝ := ∑ h ∈ s, compactRowMajorant A h
  have hC : 0 ≤ C := Finset.sum_nonneg (fun h _ => compactRowMajorant_nonneg A h)
  refine ⟨1 + Kprofile * X ^ 2 * C, by positivity, ?_⟩
  intro Z hZ u h d hh hd
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hd0 : 0 ≤ A.exteriorNorm d :=
    zero_le_one.trans (idealNorm_ge_one _ d.property.1)
  have hr : compactRowMajorant A h ≤ C := by
    exact Finset.single_le_sum (fun k _ => compactRowMajorant_nonneg A k)
      (hs.mem_toFinset.mpr hh)
  have hc : Kprofile * A.exteriorNorm d ^ 2 / Z ≤ Kprofile * X ^ 2 := by
    calc
      _ ≤ Kprofile * A.exteriorNorm d ^ 2 := div_le_self (by positivity) hZ
      _ ≤ Kprofile * X ^ 2 := by gcongr
  have hb := expansion_compactRowMajorant_bound A G U σ ψ hψ
    (L u) (hL u) (H u) Kprofile hKprofile (hH u) h d Z hZ0
  calc
    _ ≤ (Kprofile * A.exteriorNorm d ^ 2 / Z) * compactRowMajorant A h := hb
    _ ≤ Kprofile * X ^ 2 * C :=
      mul_le_mul hc hr (compactRowMajorant_nonneg A h) (by positivity)
    _ ≤ 1 + Kprofile * X ^ 2 * C := by linarith

end
end DedekindZetaZeroFree.RepresentationTheory.RMParameterAbsorption

end

section

namespace DedekindZetaZeroFree.RMParameterAbsorption
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch RMSeparatedExpansion

theorem scalar_parameter_absorption (M Cstar ε : ℝ)
    (hM : 1 < M) (hCstar : 0 < Cstar) (hε : 0 < ε) :
    ∃ θ b₁ b₂ b₃ b decayOrder K : ℝ,
      0 < θ ∧ 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃ ∧ 0 < b ∧
      1 < decayOrder ∧ 0 < K ∧
      θ + 2 * M * b₁ + (3 * M - 1 + θ) * b₂ + b₃ < ε ∧
      2 * M * b + 4 * M - 2 - 2 * θ * (decayOrder - 1) < ε ∧
      ∀ (Z P D : ℝ), 2 ≤ Z → 1 ≤ P → 1 ≤ D →
        P * D ≤ Cstar * Real.rpow Z M →
        (let R₀ := RMTailCutoff.threshold Z P D θ
         (1 ≤ R₀ →
           Real.rpow P ((1 / 2 : ℝ) + 2 * b₁) *
               Real.log (2 * R₀) ^ 4 * (D + R₀) * Real.rpow (D * R₀) b₂ ≤
             K * Real.rpow Z ε * Real.sqrt P * (D + D ^ 2 * P / Z)) ∧
         Real.rpow P ((1 / 2 : ℝ) + 2 * b) * D *
             (RMTailCutoff.length Z P D) ^ 2 *
             Real.rpow (RMTailCutoff.gain Z P D θ) (-2 * (decayOrder - 1)) ≤
           K * Real.rpow Z ε * Real.sqrt P * D) := by
  let t : ℝ := min (1 / 10) (ε / (100 * (M + 1) ^ 2))
  have ht : 0 < t := by
    dsimp [t]
    apply lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 / 10 := min_le_left _ _
  have hte : 100 * t * (M + 1) ^ 2 ≤ ε := by
    have hden : 0 < 100 * (M + 1) ^ 2 := by positivity
    have hh : t ≤ ε / (100 * (M + 1) ^ 2) := min_le_right _ _
    apply (le_div_iff₀ hden).mp at hh
    nlinarith
  let t₃ : ℝ := 4 * (2 * M + t) * t
  have ht₃ : 0 < t₃ := by dsimp [t₃]; positivity
  let B : ℝ := 1 + (2 * M * t + 4 * M + 1) / (2 * t)
  have hB : 1 < B := by
    dsimp [B]
    have : 0 < (2 * M * t + 4 * M + 1) / (2 * t) := by positivity
    linarith
  have halloc : t + 2 * M * t + (3 * M - 1 + t) * t + t₃ < ε := by
    have ht2 : 0 ≤ t := ht.le
    have hm : 0 ≤ M := by linarith
    dsimp [t₃]
    nlinarith [mul_nonneg ht2 (sq_nonneg (M + 1)),
      mul_nonneg ht2 (sq_nonneg (M - 1)), sq_nonneg (M - 1)]
  have htail : 2 * M * t + 4 * M - 2 - 2 * t * (B - 1) < ε := by
    have heq : 2 * t * (B - 1) = 2 * M * t + 4 * M + 1 := by
      dsimp [B]
      field_simp
      ring
    rw [heq]
    linarith
  let C : ℝ := max Cstar 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let cL : ℝ := 8 * C ^ 2
  let cD : ℝ := 8 * C ^ 3
  let cP : ℝ := C ^ (2 * t)
  let cLog : ℝ := (2 * cL) ^ t / t
  let K₁ : ℝ := cP * cLog ^ 4 * 8 * cD ^ t
  let K₂ : ℝ := cP * cL ^ 2
  have hcL : 0 < cL := by dsimp [cL]; positivity
  have hcD : 0 < cD := by dsimp [cD]; positivity
  have hcP : 0 < cP := Real.rpow_pos_of_pos hC _
  have hcLog : 0 < cLog := div_pos (Real.rpow_pos_of_pos (by positivity) _) ht
  have hK₁ : 0 < K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 < K₂ := by dsimp [K₂]; positivity
  refine ⟨t, t, t, t₃, t, B, K₁ + K₂, ht, ht, ht, ht₃, ht, hB,
    add_pos hK₁ hK₂, halloc, htail, ?_⟩
  intro Z P D hZ hP hD hPD
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hP0 : 0 < P := by linarith
  have hD0 : 0 < D := by linarith
  have hzM : 0 < Z ^ M := Real.rpow_pos_of_pos hZ0 _
  have hrange : P * D ≤ C * Z ^ M :=
    hPD.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hzM.le)
  have hPu : P ≤ C * Z ^ M := (le_mul_of_one_le_right hP0.le hD).trans hrange
  have hDu : D ≤ C * Z ^ M := (le_mul_of_one_le_left hD0.le hP).trans hrange
  have hlen : RMTailCutoff.length Z P D ≤ cL * Z ^ (2 * M) := by
    unfold RMTailCutoff.length
    calc
      _ ≤ 8 * D ^ 2 * P := div_le_self (by positivity) hZ1
      _ = 8 * D * (P * D) := by ring
      _ ≤ 8 * (C * Z ^ M) * (C * Z ^ M) := by gcongr
      _ = cL * Z ^ (2 * M) := by
        dsimp [cL]
        rw [show 2 * M = M + M by ring, Real.rpow_add hZ0]
        ring
  have hlen0 : 0 < RMTailCutoff.length Z P D := by
    unfold RMTailCutoff.length; positivity
  have hr : RMTailCutoff.threshold Z P D t ≤ cL * Z ^ (2 * M + t) := by
    unfold RMTailCutoff.threshold
    calc
      _ ≤ Z ^ t * (cL * Z ^ (2 * M)) := by gcongr
      _ = _ := by rw [Real.rpow_add hZ0]; ring
  have hr0 : 0 < RMTailCutoff.threshold Z P D t := by
    unfold RMTailCutoff.threshold; positivity
  have hdr : D * RMTailCutoff.threshold Z P D t ≤ cD * Z ^ (3 * M + t) := by
    calc
      _ ≤ (C * Z ^ M) * (cL * Z ^ (2 * M + t)) := by
        gcongr
      _ = _ := by
        dsimp [cD, cL]
        rw [show 3 * M + t = M + (2 * M + t) by ring]
        simp only [Real.rpow_add hZ0]
        ring
  have hpw : P ^ (2 * t) ≤ cP * Z ^ (2 * M * t) := by
    calc
      _ ≤ (C * Z ^ M) ^ (2 * t) := Real.rpow_le_rpow hP0.le hPu (by positivity)
      _ = _ := by
        rw [Real.mul_rpow hC.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
        dsimp [cP]; congr 2; ring
  have hsqrt : Real.rpow P ((1 / 2 : ℝ) + 2 * t) = Real.sqrt P * P ^ (2 * t) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_add hP0 _ _
  constructor
  · intro hR
    have hr0 : 0 < RMTailCutoff.threshold Z P D t := by
      unfold RMTailCutoff.threshold; positivity
    have hlog0 : 0 ≤ Real.log (2 * RMTailCutoff.threshold Z P D t) :=
      Real.log_nonneg (by linarith)
    have hlog : Real.log (2 * RMTailCutoff.threshold Z P D t) ≤
        cLog * Z ^ ((2 * M + t) * t) := by
      calc
        _ ≤ (2 * RMTailCutoff.threshold Z P D t) ^ t / t :=
          Real.log_le_rpow_div (by positivity) ht
        _ ≤ (2 * (cL * Z ^ (2 * M + t))) ^ t / t := by gcongr
        _ = _ := by
          rw [show 2 * (cL * Z ^ (2 * M + t)) = (2 * cL) * Z ^ (2 * M + t) by ring,
            Real.mul_rpow (by positivity : 0 ≤ 2 * cL) (Real.rpow_nonneg hZ0.le _),
            ← Real.rpow_mul hZ0.le]
          dsimp [cLog]; ring
    have hsum : D + RMTailCutoff.threshold Z P D t ≤
        8 * Z ^ t * (D + D ^ 2 * P / Z) := by
      have hzt : 1 ≤ Z ^ t := Real.one_le_rpow hZ1 ht.le
      unfold RMTailCutoff.threshold RMTailCutoff.length
      have hq : 0 ≤ D ^ 2 * P / Z := by positivity
      have hdzt := mul_le_mul_of_nonneg_left hzt hD0.le
      have heq : Z ^ t * (8 * D ^ 2 * P / Z) = 8 * Z ^ t * (D ^ 2 * P / Z) := by ring
      rw [heq]
      nlinarith
    have hdrw : (D * RMTailCutoff.threshold Z P D t) ^ t ≤
        cD ^ t * Z ^ ((3 * M + t) * t) := by
      calc
        _ ≤ (cD * Z ^ (3 * M + t)) ^ t := Real.rpow_le_rpow (by positivity) hdr ht.le
        _ = _ := by
          rw [Real.mul_rpow hcD.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
    have hpowlog : Real.log (2 * RMTailCutoff.threshold Z P D t) ^ 4 ≤
        cLog ^ 4 * Z ^ t₃ := by
      calc
        _ ≤ (cLog * Z ^ ((2 * M + t) * t)) ^ 4 := by gcongr
        _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast (Z ^ ((2 * M + t) * t)) 4, ← Real.rpow_mul hZ0.le]
          dsimp [t₃]; congr 2; ring
    have he : 2 * M * t + t₃ + t + (3 * M + t) * t < ε := by
      dsimp [t₃]
      nlinarith [mul_nonneg ht.le (sq_nonneg (M - 1))]
    change P ^ ((1 / 2 : ℝ) + 2 * t) * Real.log (2 * RMTailCutoff.threshold Z P D t) ^ 4 *
      (D + RMTailCutoff.threshold Z P D t) * (D * RMTailCutoff.threshold Z P D t) ^ t ≤
      (K₁ + K₂) * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)
    rw [show P ^ ((1 / 2 : ℝ) + 2 * t) = Real.sqrt P * P ^ (2 * t) from hsqrt]
    calc
      _ ≤ (Real.sqrt P * (cP * Z ^ (2 * M * t))) *
          (cLog ^ 4 * Z ^ t₃) * (8 * Z ^ t * (D + D ^ 2 * P / Z)) *
          (cD ^ t * Z ^ ((3 * M + t) * t)) := by gcongr
      _ = K₁ * Z ^ (2 * M * t + t₃ + t + (3 * M + t) * t) *
          Real.sqrt P * (D + D ^ 2 * P / Z) := by
        dsimp [K₁]
        simp only [Real.rpow_add hZ0]
        ring
      _ ≤ (K₁ + K₂) * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
        gcongr <;> linarith
  · have hg : Z ^ t ≤ RMTailCutoff.gain Z P D t := le_max_left _ _
    have hg0 : 0 < RMTailCutoff.gain Z P D t :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 _) hg
    have hgw : (RMTailCutoff.gain Z P D t) ^ (-2 * (B - 1)) ≤
        Z ^ (-2 * t * (B - 1)) := by
      calc
        _ ≤ (Z ^ t) ^ (-2 * (B - 1)) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hZ0 _) hg (by linarith)
        _ = _ := by rw [← Real.rpow_mul hZ0.le]; congr 1; ring
    have hlw : (RMTailCutoff.length Z P D) ^ 2 ≤ cL ^ 2 * Z ^ (4 * M) := by
      calc
        _ ≤ (cL * Z ^ (2 * M)) ^ 2 := by gcongr
        _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast (Z ^ (2 * M)) 2, ← Real.rpow_mul hZ0.le]
          congr 2; ring
    have he : 2 * M * t + 4 * M - 2 * t * (B - 1) < ε := by
      have heq : 2 * t * (B - 1) = 2 * M * t + 4 * M + 1 := by
        dsimp [B]; field_simp; ring
      rw [heq]; linarith
    change P ^ ((1 / 2 : ℝ) + 2 * t) * D * (RMTailCutoff.length Z P D) ^ 2 *
      (RMTailCutoff.gain Z P D t) ^ (-2 * (B - 1)) ≤
      (K₁ + K₂) * Z ^ ε * Real.sqrt P * D
    rw [show P ^ ((1 / 2 : ℝ) + 2 * t) = Real.sqrt P * P ^ (2 * t) from hsqrt]
    calc
      _ ≤ (Real.sqrt P * (cP * Z ^ (2 * M * t))) * D *
          (cL ^ 2 * Z ^ (4 * M)) * Z ^ (-2 * t * (B - 1)) := by gcongr
      _ = K₂ * Z ^ (2 * M * t + 4 * M - 2 * t * (B - 1)) * Real.sqrt P * D := by
        dsimp [K₂]
        rw [show 2 * M * t + 4 * M - 2 * t * (B - 1) =
          (2 * M * t + 4 * M) + (-2 * t * (B - 1)) by ring]
        simp only [Real.rpow_add hZ0]
        ring
      _ ≤ (K₁ + K₂) * Z ^ ε * Real.sqrt P * D := by
        gcongr <;> linarith

variable {F : Type} [Field F] [NumberField F]

theorem finiteProfileFamily_reciprocal_bound
    (A : SArithmeticData F) (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : FiniteProfileFamily A H) :
    ∃ K : ℝ, 0 < K ∧ ∀ u v x, 0 < x → ‖H u v x‖ ≤ K / x := by
  obtain ⟨I, Q, hQ, _, hdecay⟩ := hH
  obtain ⟨K, hK, hbound⟩ := hdecay 1 (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro u v x hx
  obtain ⟨i, hi⟩ := hQ u v
  have hb := hbound i 0 (by norm_num) x hx
  simp only [iteratedDeriv_zero, logProfile, Real.exp_log hx] at hb
  rw [hi]
  calc
    _ ≤ K * min (x ^ (1 / 8 : ℝ)) (x ^ (-1 : ℝ)) := hb
    _ ≤ K * x ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
    _ = K / x := by rw [Real.rpow_neg_one, div_eq_mul_inv]

theorem compact_norm_range (M Cstar Z P D : ℝ)
    (hM : 1 < M) (hC : 0 < Cstar)
    (hZ : 1 ≤ Z) (hZ2 : Z ≤ 2) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hPD : P * D ≤ Cstar * Real.rpow Z M) :
    P ≤ Cstar * Real.rpow 2 M ∧ D ≤ Cstar * Real.rpow 2 M ∧
      RMTailCutoff.length Z P D ≤ 8 * (Cstar * Real.rpow 2 M) ^ 2 := by
  have hP0 : 0 ≤ P := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hp : Z ^ M ≤ (2 : ℝ) ^ M := Real.rpow_le_rpow hZ0 hZ2 (by linarith)
  have hr : P * D ≤ Cstar * Real.rpow 2 M :=
    hPD.trans (mul_le_mul_of_nonneg_left hp hC.le)
  have hPu := (le_mul_of_one_le_right hP0 hD).trans hr
  have hDu := (le_mul_of_one_le_left hD0 hP).trans hr
  refine ⟨hPu, hDu, ?_⟩
  unfold RMTailCutoff.length
  calc
    _ ≤ 8 * D ^ 2 * P := div_le_self (by positivity) hZ
    _ = 8 * D * (P * D) := by ring
    _ ≤ 8 * (Cstar * Real.rpow 2 M) * (Cstar * Real.rpow 2 M) := by
      have hCpow : 0 ≤ Cstar * Real.rpow 2 M := hP0.trans hPu
      gcongr
    _ = _ := by ring

theorem idealSymbol_norm_le_one (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : Fˣ) : ‖ThetaPhaseSeparation.idealSymbol A σ I x‖ ≤ 1 := by
  unfold ThetaPhaseSeparation.idealSymbol
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro p _; exact norm_nonneg _
  · intro p _
    unfold symbol
    let q := supportPrime A I p
    let χ := residueCharacter A σ q
    let a := unitResidue q.val x
    change ‖χ a‖ ≤ 1
    by_cases ha : a = 0
    · simp [ha, MulChar.map_zero]
    · letI : Fintype (DHCubic.Residue F q.val) := Fintype.ofFinite _
      have hn := Complex.norm_eq_one_of_mem_rootsOfUnity
        (χ.apply_mem_rootsOfUnity (Units.mk0 a ha))
      simpa using hn.le

theorem separatedCoefficient_norm_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (T : ThetaPhaseSeparation.Frozen A) (d c : A.Exterior) :
    ‖ThetaPhaseSeparation.separatedCoefficient A G U σ ψ L T d c‖ ≤
      betaIdeal (activeSupport A T) T.a.val /
        (Real.sqrt (A.exteriorNorm c) * A.exteriorNorm T.n) := by
  have hc : 0 < A.exteriorNorm c := lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ c.property.1)
  have hn : 0 < A.exteriorNorm T.n := lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.n.property.1)
  have hbeta : 0 ≤ betaIdeal (activeSupport A T) T.a.val := by
    have h := factors_norm_le_betaIdeal A G U σ ψ hψ L hL T d c
    exact (norm_nonneg _).trans h.1
  have hf := factors_norm_le_betaIdeal A G U σ ψ hψ L hL T d c
  have hs := idealSymbol_norm_le_one A σ d (G.generator c)
  rw [separatedCoefficient_support A G U σ ψ L T d c]
  split_ifs
  · simp only [norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ betaIdeal (activeSupport A T) T.a.val * 1 * 1 * 1 ^ 3 := by
        gcongr
        · exact hf.1
        · exact hf.2.1
        · exact hf.2.2
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem summand_positiveRowWeight_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (H : A.V → ℝ → ℂ) (K : ℝ) (hK : 0 < K)
    (hH : ∀ v x, 0 < x → ‖H v x‖ ≤ K / x)
    (T : ThetaPhaseSeparation.Frozen A) (d : A.Exterior)
    (c : ExteriorSquarefreeIdeal A.cS) (Z : ℝ) (hZ : 0 < Z) :
    ‖summand A G U σ ψ L H T d c Z‖ ≤
      (K * (A.exteriorNorm d ^ 2 * A.exteriorNorm T.f ^ 2) / Z) *
        positiveRowWeight (activeSupport A T) 1
          (⟨T.a, T.a_supported⟩, c, T.n) := by
  have ha : 0 < A.exteriorNorm T.a :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.a.property.1)
  have hc : 0 < A.exteriorNorm c.val :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ c.val.property.1)
  have hn : 0 < A.exteriorNorm T.n :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.n.property.1)
  have hd : 0 < A.exteriorNorm d :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ d.property.1)
  have hf : 0 < A.exteriorNorm T.f :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ T.f.property.1)
  have hx : 0 < ThetaPhaseSeparation.profileArgument A T d c.val Z := by
    unfold ThetaPhaseSeparation.profileArgument; positivity
  have hcoeff := separatedCoefficient_norm_bound A G U σ ψ hψ L hL T d c.val
  have hb : 0 ≤ betaIdeal (activeSupport A T) T.a.val :=
    (norm_nonneg _).trans (factors_norm_le_betaIdeal A G U σ ψ hψ L hL T d c.val).1
  have hprofile := hH (termClass A G U T d c.val)
    (ThetaPhaseSeparation.profileArgument A T d c.val Z) hx
  unfold summand
  rw [norm_mul]
  calc
    _ ≤ (betaIdeal (activeSupport A T) T.a.val /
        (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm T.n)) *
        (K / ThetaPhaseSeparation.profileArgument A T d c.val Z) := by
      exact mul_le_mul hcoeff hprofile (norm_nonneg _) (by positivity)
    _ = _ := by
      unfold positiveRowWeight ThetaPhaseSeparation.profileArgument rowNorm
      change _ = (K * (A.exteriorNorm d ^ 2 * A.exteriorNorm T.f ^ 2) / Z) *
        (betaIdeal (activeSupport A T) T.a.val *
          (A.exteriorNorm T.a * A.exteriorNorm c.val * A.exteriorNorm T.n ^ 3) ^ (-1 : ℝ) /
          (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm T.n))
      rw [Real.rpow_neg_one]
      have hsc : 0 < Real.sqrt (A.exteriorNorm c.val) := Real.sqrt_pos.mpr hc
      field_simp

abbrev CompactMajorantIndex (A : SArithmeticData F) (h : A.Exterior) :=
  (f : {f : ExteriorSquarefreeIdeal A.cS //
      f.val.val ∈ activeSquarefreeDivisors h.val}) ×
    (A.UnitQuotient × PositiveRowIndex f.val)

def compactMajorantIndexMap (A : SArithmeticData F) (h : A.Exterior) :
    Index A h → CompactMajorantIndex A h := fun i =>
  ⟨⟨activeSupport A i.1.val,
      (mem_activeSquarefreeDivisors_iff h.val h.property.1 _).mpr
        ⟨i.1.val.f.property.1, i.1.val.f_squarefree,
          by simpa only [activeSupport, i.1.property] using i.1.val.f_divides_radical⟩⟩,
    i.1.val.epsilon, ⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n⟩

theorem compactMajorantIndexMap_injective (A : SArithmeticData F) (h : A.Exterior) :
    Function.Injective (compactMajorantIndexMap A h) := by
  intro i j hij
  have hf : i.1.val.f = j.1.val.f := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.1.val.val) hij
    exact hh
  have he : i.1.val.epsilon = j.1.val.epsilon := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.1) hij
    exact hh
  have ha : i.1.val.a = j.1.val.a := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.2.1.val) hij
    exact hh
  have hc : i.2 = j.2 := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.2.2.1) hij
    exact hh
  have hn : i.1.val.n = j.1.val.n := by
    have hh := congrArg (fun k : CompactMajorantIndex A h => k.2.2.2.2) hij
    exact hh
  have hh : i.1.val.h = j.1.val.h := i.1.property.trans j.1.property.symm
  have hT : i.1.val = j.1.val := by
    generalize hi : i.1.val = Ti at hf he ha hn hh ⊢
    generalize hj : j.1.val = Tj at hf he ha hn hh ⊢
    cases Ti
    cases Tj
    simp_all
  exact Prod.ext (Subtype.ext hT) hc

theorem positiveRowWeight_nonneg {A : SArithmeticData F} (f : ExteriorSquarefreeIdeal A.cS)
    (x : PositiveRowIndex f) : 0 ≤ positiveRowWeight f 1 x := by
  have hb := betaIdealTerm_nonneg f 0 (by norm_num) x.1
  simp only [betaIdealTerm, neg_zero] at hb
  change 0 ≤ betaIdeal f x.1.val.val * (idealNorm x.1.val.val) ^ (0 : ℝ) at hb
  simp only [Real.rpow_zero, mul_one] at hb
  unfold positiveRowWeight
  have ha := idealNorm_ge_one _ x.1.val.property.1
  have hc := idealNorm_ge_one _ x.2.1.val.property.1
  have hn := idealNorm_ge_one _ x.2.2.property.1
  unfold rowNorm
  apply div_nonneg
  · exact mul_nonneg hb (Real.rpow_nonneg (by positivity) _)
  · positivity

private theorem unitQuotient_finite (A : SArithmeticData F) : Finite A.UnitQuotient := by
  letI := SArithmeticData.sunitSixthPowerQuotient_finite F A
  exact Finite.of_equiv (PowerQuotient A.Rˣ 6)
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ 6 A.unitEquiv).symm.toEquiv

private theorem compactActive_finite (A : SArithmeticData F) (h : A.Exterior) :
    Finite {f : ExteriorSquarefreeIdeal A.cS //
      f.val.val ∈ activeSquarefreeDivisors h.val} := by
  let e : {f : ExteriorSquarefreeIdeal A.cS // f.val.val ∈ activeSquarefreeDivisors h.val} →
      {f : Ideal (𝓞 F) // f ∈ activeSquarefreeDivisors h.val} :=
    fun f => ⟨f.val.val.val, f.property⟩
  have he : Function.Injective e := by
    intro f g hh
    have hv : f.val.val.val = g.val.val.val := congrArg (fun k => k.val) hh
    exact Subtype.ext (Subtype.ext (Subtype.ext hv))
  exact Finite.of_injective e he

set_option maxHeartbeats 1200000 in

theorem compactWeightedMajorant_summable (A : SArithmeticData F) (h : A.Exterior) :
    Summable (fun k : CompactMajorantIndex A h =>
      A.exteriorNorm k.1.val.val ^ 2 * positiveRowWeight k.1.val 1 k.2.2) := by
  letI := unitQuotient_finite A
  letI := Fintype.ofFinite A.UnitQuotient
  let T := {f : ExteriorSquarefreeIdeal A.cS // f.val.val ∈ activeSquarefreeDivisors h.val}
  letI : Finite T := compactActive_finite A h
  letI : Fintype T := Fintype.ofFinite _
  let W : (f : T) → (A.UnitQuotient × PositiveRowIndex f.val) → ℝ :=
    fun f k => A.exteriorNorm f.val.val ^ 2 * positiveRowWeight f.val 1 k.2
  have hw : ∀ f k, 0 ≤ W f k := fun f k =>
    mul_nonneg (sq_nonneg _) (positiveRowWeight_nonneg (A := A) f.val k.2)
  have hf : ∀ f, Summable (W f) := by
    intro f
    have hs := (positiveRowWeight_summable_le f.val 1 (by norm_num)).1
    have hs' := hs.mul_left (A.exteriorNorm f.val.val ^ 2)
    exact (summable_prod_of_nonneg (hw f)).2
      ⟨fun _ => hs', (hasSum_fintype _).summable⟩
  have he : Summable (fun k : (f : T) × (A.UnitQuotient × PositiveRowIndex f.val) => W k.1 k.2) := by
    apply (summable_sigma_of_nonneg (f := fun k : (f : T) × (A.UnitQuotient × PositiveRowIndex f.val) => W k.1 k.2)
      (fun k => hw k.1 k.2)).2
    exact ⟨hf, (hasSum_fintype _).summable⟩
  simpa only [T, W, CompactMajorantIndex] using he

theorem compact_expansion_square_bound
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : FiniteProfileFamily A H)
    (M Cstar : ℝ) (hM : 1 < M) (hCstar : 0 < Cstar) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Z P D : ℝ),
      1 ≤ Z → Z ≤ 2 → 1 ≤ P → 1 ≤ D →
      P * D ≤ Cstar * Real.rpow Z M →
      ∀ (u : A.UnitQuotient),
        (∑' h : {h : A.Exterior // h ∈ exteriorPowerfulDyad A.cS P},
          ∑' d : {d : ExteriorSquarefreeIdeal A.cS //
              d ∈ RMTailCutoff.rowDyad A h.val D},
            ‖expansion A G U σ ψ (L u) (H u) h.val d.val.val Z‖ ^ 2) ≤
          K * Real.sqrt P * D := by
  obtain ⟨Kprofile, hKprofile, hprofile⟩ :=
    finiteProfileFamily_reciprocal_bound A H hH
  let X : ℝ := 2 * (Cstar * Real.rpow 2 M)
  have hX : 0 < X := by dsimp [X]; positivity
  obtain ⟨B, hB, hentry⟩ :=
    RepresentationTheory.RMParameterAbsorption.bounded_norm_expansion
      A G U σ ψ hψ L hL H Kprofile hKprofile hprofile X hX
  obtain ⟨Kcount, hKcount, hcount⟩ :=
    RepresentationTheory.RMParameterAbsorption.bounded_dyad_square_sum A
  refine ⟨Kcount * B ^ 2, by positivity, ?_⟩
  intro Z P D hZ hZ2 hP hD hPD u
  obtain ⟨hPu, hDu, _⟩ := compact_norm_range M Cstar Z P D hM hCstar hZ hZ2 hP hD hPD
  apply hcount P D hP hD
    (fun h d => expansion A G U σ ψ (L u) (H u) h.val d.val.val Z) B hB.le
  intro h d
  apply hentry Z hZ u h.val d.val.val
  · have hh := h.property.2.2
    change A.exteriorNorm h.val < 2 * P at hh
    exact hh.le.trans (mul_le_mul_of_nonneg_left hPu (by norm_num))
  · have hd := d.property.2.1
    change A.exteriorNorm d.val.val < 2 * D at hd
    exact hd.le.trans (mul_le_mul_of_nonneg_left hDu (by norm_num))

end
end DedekindZetaZeroFree.RMParameterAbsorption

end
