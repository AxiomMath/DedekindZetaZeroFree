module

public import DedekindZetaZeroFree.Moments.Reflected.SeparatedProfileExpansion
public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.PowerfulIdeals
public import DedekindZetaZeroFree.Moments.Reflected.PositiveRowMajorants
public import DedekindZetaZeroFree.Moments.Reflected.ActivePrimeSubpowerMass
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitPowerQuotientCoordinates

@[expose] public section

namespace DedekindZetaZeroFree.RMTailCutoff
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch ThetaPhaseSeparation RMSeparatedExpansion

variable {F : Type} [Field F] [NumberField F]

def length (Z P D : ℝ) : ℝ := 8 * D ^ 2 * P / Z

def threshold (Z P D θ : ℝ) : ℝ := Z ^ θ * length Z P D

def gain (Z P D θ : ℝ) : ℝ := max (Z ^ θ) (length Z P D)⁻¹

def frozenNorm (A : SArithmeticData F) (T : Frozen A)
    (c : ExteriorSquarefreeIdeal A.cS) : ℝ :=
  rowNorm T.a c.val T.n

def retained (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z P D θ : ℝ) : ℂ :=
  ∑' i : Index A h,
    if frozenNorm A i.1.val i.2 ≤ threshold Z P D θ then
      summand A G U σ ψ L H i.1.val d i.2 Z else 0

def tail (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ)
    (h d : A.Exterior) (Z P D θ : ℝ) : ℂ :=
  ∑' i : Index A h,
    if threshold Z P D θ < frozenNorm A i.1.val i.2 then
      summand A G U σ ψ L H i.1.val d i.2 Z else 0

def rowDyad (A : SArithmeticData F) (h : A.Exterior) (D : ℝ) :
    Set (ExteriorSquarefreeIdeal A.cS) :=
  {d | D ≤ A.exteriorNorm d.val ∧ A.exteriorNorm d.val < 2 * D ∧
    d.val.val ⊔ h.val = ⊤}

theorem frozenNorm_ge_one (A : SArithmeticData F) (T : Frozen A)
    (c : ExteriorSquarefreeIdeal A.cS) : 1 ≤ frozenNorm A T c := by
  have ha := idealNorm_ge_one T.a.val T.a.property.1
  have hc := idealNorm_ge_one c.val.val c.val.property.1
  have hn := idealNorm_ge_one T.n.val T.n.property.1
  unfold frozenNorm rowNorm
  calc
    (1 : ℝ) = 1 * 1 * 1 ^ 3 := by norm_num
    _ ≤ idealNorm T.a.val * idealNorm c.val.val * idealNorm T.n.val ^ 3 := by gcongr

private theorem profileArgument_cutoff (A : SArithmeticData F) (T : Frozen A)
    (c : ExteriorSquarefreeIdeal A.cS) (h : A.Exterior) (d : ExteriorSquarefreeIdeal A.cS)
    (Z P D θ : ℝ) (hZ : 2 ≤ Z) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hT : T.h = h) (hh : h ∈ exteriorPowerfulDyad A.cS P)
    (hd : d ∈ rowDyad A h D) (hcut : threshold Z P D θ < frozenNorm A T c) :
    0 < profileArgument A T d.val c.val Z ∧
      (profileArgument A T d.val c.val Z)⁻¹ ≤ length Z P D / frozenNorm A T c ∧
      gain Z P D θ ≤ profileArgument A T d.val c.val Z := by
  have hZ0 : 0 < Z := by linarith
  have hn := idealNorm_ge_one T.f.val T.f.property.1
  have hdn := idealNorm_ge_one d.val.val d.val.property.1
  have hQ := frozenNorm_ge_one A T c
  have hQ0 : 0 < frozenNorm A T c := by linarith
  have hf : A.exteriorNorm T.f ^ 2 ≤ A.exteriorNorm h := by
    have := (squarefree_radical_divisor_pow_two_le_powerful T.h.val T.h.property.1
      T.powerful T.f.val T.f_squarefree T.f_divides_radical).2
    simpa only [hT] using this
  have hfp : A.exteriorNorm T.f ^ 2 < 2 * P := hf.trans_lt hh.2.2
  have hdD : A.exteriorNorm d.val < 2 * D := hd.2.1
  have hnum : A.exteriorNorm d.val ^ 2 * A.exteriorNorm T.f ^ 2 ≤ 8 * D ^ 2 * P := by
    have hd2 : A.exteriorNorm d.val ^ 2 ≤ (2 * D) ^ 2 := by
      gcongr
    have := mul_le_mul hd2 hfp.le (sq_nonneg _) (sq_nonneg _)
    nlinarith
  let t := (A.exteriorNorm d.val ^ 2 * A.exteriorNorm T.f ^ 2) / Z
  have ht : 0 < t := by dsimp [t]; positivity
  have htL : t ≤ length Z P D := by
    exact div_le_div_of_nonneg_right hnum hZ0.le
  have hx : profileArgument A T d.val c.val Z = frozenNorm A T c / t := by
    dsimp [profileArgument, frozenNorm, rowNorm, t]
    field_simp
  have hl : 0 < length Z P D := ht.trans_le htL
  rw [hx]
  refine ⟨div_pos hQ0 ht, ?_, ?_⟩
  · rw [inv_div]
    exact div_le_div_of_nonneg_right htL hQ0.le
  · apply max_le
    · apply (le_div_iff₀ ht).mpr
      have hzθ := Real.rpow_pos_of_pos hZ0 θ
      exact (mul_le_mul_of_nonneg_left htL hzθ.le).trans hcut.le
    · apply (le_div_iff₀ ht).mpr
      have hi : (length Z P D)⁻¹ * t ≤ 1 := by
        calc
          _ ≤ (length Z P D)⁻¹ * length Z P D :=
            mul_le_mul_of_nonneg_left htL (inv_nonneg.mpr hl.le)
          _ = 1 := inv_mul_cancel₀ hl.ne'
      exact hi.trans hQ

private theorem profileFamily_decay (A : SArithmeticData F)
    (H : A.UnitQuotient → A.V → ℝ → ℂ) (hH : FiniteProfileFamily A H)
    (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧ ∀ u v x, 0 < x → ‖H u v x‖ ≤ K * x ^ (-B) := by
  obtain ⟨I, P, hP, _, hbound⟩ := hH
  obtain ⟨K, hK, hk⟩ := hbound B hB
  refine ⟨K, hK, ?_⟩
  intro u v x hx
  obtain ⟨i, hi⟩ := hP u v
  rw [hi]
  have hh := hk i 0 (by norm_num) x hx
  simp only [iteratedDeriv_zero, logProfile, Real.exp_log hx] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le)

private theorem profile_tail_decay (A : SArithmeticData F) (T : Frozen A)
    (c : ExteriorSquarefreeIdeal A.cS) (h : A.Exterior) (d : ExteriorSquarefreeIdeal A.cS)
    (Z P D θ B : ℝ) (hZ : 2 ≤ Z) (hP : 1 ≤ P) (hD : 1 ≤ D) (hB : 1 < B)
    (hT : T.h = h) (hh : h ∈ exteriorPowerfulDyad A.cS P)
    (hd : d ∈ rowDyad A h D) (hcut : threshold Z P D θ < frozenNorm A T c) :
    (profileArgument A T d.val c.val Z) ^ (-B) ≤
      (length Z P D / frozenNorm A T c) * gain Z P D θ ^ (-(B - 1)) := by
  obtain ⟨hx, hi, hj⟩ := profileArgument_cutoff A T c h d Z P D θ hZ hP hD hT hh hd hcut
  have hZ0 : 0 < Z := by linarith
  have hg : 0 < gain Z P D θ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 θ) (le_max_left _ _)
  have he : -B = -1 + -(B - 1) := by ring
  rw [he, Real.rpow_add hx, Real.rpow_neg_one]
  apply mul_le_mul hi (Real.rpow_le_rpow_of_nonpos hg hj (by linarith))
    (Real.rpow_nonneg hx.le _) _
  have hl : 0 < length Z P D := by unfold length; positivity
  exact div_nonneg hl.le (zero_le_one.trans (frozenNorm_ge_one A T c))

private theorem mulChar_norm_le_one {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (x : k) : ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · let u := (isUnit_iff_ne_zero.mpr hx).unit
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    have hn' : ‖χ x‖ = 1 := by
      simpa [MulChar.coe_equivToUnitHom, u] using hn
    exact hn'.le

private theorem summand_norm_le (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1)
    (H : A.V → ℝ → ℂ) (T : Frozen A) (d : A.Exterior)
    (c : ExteriorSquarefreeIdeal A.cS) (Z : ℝ) :
    ‖summand A G U σ ψ L H T d c Z‖ ≤
      betaIdeal (activeSupport A T) T.a.val /
        (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm T.n) *
        ‖H (termClass A G U T d c.val) (profileArgument A T d c.val Z)‖ := by
  obtain ⟨hw, hr, hl⟩ := factors_norm_le_betaIdeal A G U σ ψ hψ L hL T d c.val
  have hb : 0 ≤ betaIdeal (activeSupport A T) T.a.val := (norm_nonneg _).trans hw
  have hc : 0 ≤ A.exteriorNorm c.val :=
    zero_le_one.trans (idealNorm_ge_one c.val.val c.val.property.1)
  have hn : 0 ≤ A.exteriorNorm T.n :=
    zero_le_one.trans (idealNorm_ge_one T.n.val T.n.property.1)
  have hs : ‖idealSymbol A σ d (G.generator c.val)‖ ≤ 1 := by
    unfold idealSymbol
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun p _ => mulChar_norm_le_one (residueCharacter A σ (supportPrime A d p)) _)
  unfold summand
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [separatedCoefficient_support]
  split_ifs
  · simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc, abs_of_nonneg hn, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply div_le_div_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) hn)
    calc
      _ ≤ betaIdeal (activeSupport A T) T.a.val * 1 * 1 * 1 ^ 3 := by gcongr
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

private theorem tail_summand_majorant (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1)
    (H : A.V → ℝ → ℂ) (K B : ℝ) (hK : 0 < K) (hB : 1 < B)
    (hH : ∀ v x, 0 < x → ‖H v x‖ ≤ K * x ^ (-B))
    (h : A.Exterior) (d : ExteriorSquarefreeIdeal A.cS) (Z P D θ : ℝ)
    (hZ : 2 ≤ Z) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hh : h ∈ exteriorPowerfulDyad A.cS P) (hd : d ∈ rowDyad A h D)
    (i : Index A h) :
    ‖(if threshold Z P D θ < frozenNorm A i.1.val i.2 then
        summand A G U σ ψ L H i.1.val d.val i.2 Z else 0)‖ ≤
      (K * length Z P D * gain Z P D θ ^ (-(B - 1))) *
        positiveRowWeight (activeSupport A i.1.val) 1
          (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n) := by
  have hn := summand_norm_le A G U σ ψ hψ L hL H i.1.val d.val i.2 Z
  have hb : 0 ≤ betaIdeal (activeSupport A i.1.val) i.1.val.a.val := by
    have hw := (factors_norm_le_betaIdeal A G U σ ψ hψ L hL i.1.val d.val i.2.val).1
    exact (norm_nonneg _).trans hw
  have hQ := frozenNorm_ge_one A i.1.val i.2
  have hQ0 : 0 < frozenNorm A i.1.val i.2 := by linarith
  have hc := idealNorm_ge_one i.2.val.val i.2.val.property.1
  have hn' := idealNorm_ge_one i.1.val.n.val i.1.val.n.property.1
  have hl : 0 < length Z P D := by unfold length; positivity
  have hZ0 : 0 < Z := by linarith
  have hg : 0 < gain Z P D θ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 θ) (le_max_left _ _)
  split_ifs with hi
  · have hx := (profileArgument_cutoff A i.1.val i.2 h d Z P D θ hZ hP hD
      i.1.property hh hd hi).1
    have hp := hH (termClass A G U i.1.val d.val i.2.val) _ hx
    have hdcy := profile_tail_decay A i.1.val i.2 h d Z P D θ B hZ hP hD hB
      i.1.property hh hd hi
    calc
      _ ≤ betaIdeal (activeSupport A i.1.val) i.1.val.a.val /
          (Real.sqrt (A.exteriorNorm i.2.val) * A.exteriorNorm i.1.val.n) *
          (K * (length Z P D / frozenNorm A i.1.val i.2) *
            gain Z P D θ ^ (-(B - 1))) := by
        apply hn.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hp.trans (by calc
          _ ≤ K * ((length Z P D / frozenNorm A i.1.val i.2) *
              gain Z P D θ ^ (-(B - 1))) := mul_le_mul_of_nonneg_left hdcy hK.le
          _ = _ := by ring)
      _ = _ := by
        unfold positiveRowWeight frozenNorm
        dsimp only [Prod.fst, Prod.snd, Subtype.coe_mk]
        change _ = (K * length Z P D * gain Z P D θ ^ (-(B - 1))) *
          (betaIdeal (activeSupport A i.1.val) i.1.val.a.val *
            (rowNorm i.1.val.a i.2.val i.1.val.n) ^ (-1 : ℝ) /
              (Real.sqrt (A.exteriorNorm i.2.val) * A.exteriorNorm i.1.val.n))
        rw [Real.rpow_neg_one]
        change _ = (K * length Z P D * gain Z P D θ ^ (-(B - 1))) *
          (betaIdeal (activeSupport A i.1.val) i.1.val.a.val *
            (rowNorm i.1.val.a i.2.val i.1.val.n)⁻¹ /
              (Real.sqrt (A.exteriorNorm i.2.val) * A.exteriorNorm i.1.val.n))
        ring
  · simp only [norm_zero]
    change 0 ≤ (K * length Z P D * gain Z P D θ ^ (-(B - 1))) *
      (betaIdeal (activeSupport A i.1.val) i.1.val.a.val *
        (rowNorm i.1.val.a i.2.val i.1.val.n) ^ (-1 : ℝ) /
          (Real.sqrt (A.exteriorNorm i.2.val) * A.exteriorNorm i.1.val.n))
    positivity

theorem numerical_tail_from_joint_majorant (A : SArithmeticData F)
    (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ u : A.UnitQuotient, ∀ x : Fˣ, ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : FiniteProfileFamily A H)
    (B b : ℝ) (hB : 1 < B) (Kj : ℝ) (hKj : 0 < Kj)
    (hmajor : ∀ h : A.Exterior, Powerful h.val →
      (Summable fun i : Index A h => positiveRowWeight (activeSupport A i.1.val) 1
        (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ∧
      (∑' i : Index A h, positiveRowWeight (activeSupport A i.1.val) 1
        (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ≤
        Kj * A.exteriorNorm h ^ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Z P D θ : ℝ), 2 ≤ Z → 1 ≤ P → 1 ≤ D → 0 < θ →
      ∀ (h : A.Exterior), h ∈ exteriorPowerfulDyad A.cS P →
      ∀ (d : ExteriorSquarefreeIdeal A.cS), d ∈ rowDyad A h D →
      ∀ (u : A.UnitQuotient),
        ‖tail A G U σ ψ (L u) (H u) h d.val Z P D θ‖ ≤
          K * (A.exteriorNorm h) ^ b * length Z P D *
            (gain Z P D θ) ^ (-(B - 1)) := by
  obtain ⟨Kp, hKp, hprof⟩ := profileFamily_decay A H hH B (by linarith)
  refine ⟨Kp * Kj, mul_pos hKp hKj, ?_⟩
  intro Z P D θ hZ hP hD hθ h hh d hd u
  obtain ⟨hs, hsum⟩ := hmajor h hh.1
  let W : Index A h → ℝ := fun i => positiveRowWeight (activeSupport A i.1.val) 1
    (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)
  let k := Kp * length Z P D * gain Z P D θ ^ (-(B - 1))
  have hZ0 : 0 < Z := by linarith
  have hl : 0 < length Z P D := by unfold length; positivity
  have hg : 0 < gain Z P D θ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 θ) (le_max_left _ _)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hkn : Summable (fun i => k * W i) := hs.mul_left k
  have ht : ∀ i : Index A h,
      ‖(if threshold Z P D θ < frozenNorm A i.1.val i.2 then
        summand A G U σ ψ (L u) (H u) i.1.val d.val i.2 Z else 0)‖ ≤ k * W i := by
    intro i
    exact tail_summand_majorant A G U σ ψ hψ (L u) (hL u) (H u) Kp B hKp hB
      (hprof u) h d Z P D θ hZ hP hD hh hd i
  have htn := Summable.of_nonneg_of_le (fun i => norm_nonneg _) ht hkn
  unfold tail
  calc
    _ ≤ ∑' i : Index A h, ‖(if threshold Z P D θ < frozenNorm A i.1.val i.2 then
        summand A G U σ ψ (L u) (H u) i.1.val d.val i.2 Z else 0)‖ :=
      norm_tsum_le_tsum_norm htn
    _ ≤ ∑' i : Index A h, k * W i := Summable.tsum_le_tsum ht htn hkn
    _ = k * ∑' i : Index A h, W i := tsum_mul_left
    _ ≤ k * (Kj * A.exteriorNorm h ^ b) := mul_le_mul_of_nonneg_left hsum hk
    _ = _ := by dsimp [k]; ring

namespace Reindex
set_option maxHeartbeats 1000000

theorem unit_finite (A : SArithmeticData F) : Finite A.UnitQuotient := by
  letI := SArithmeticData.sunitSixthPowerQuotient_finite F A
  exact Finite.of_equiv (PowerQuotient A.Rˣ 6)
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ 6 A.unitEquiv).symm.toEquiv

abbrev ActiveIndex (A : SArithmeticData F) (h : A.Exterior) :=
  {f : ExteriorSquarefreeIdeal A.cS // f.val.val ∈ activeSquarefreeDivisors h.val}

abbrev MajorantIndex (A : SArithmeticData F) (h : A.Exterior) :=
  Σ f : ActiveIndex A h, PositiveRowIndex f.val × A.UnitQuotient

def encode (A : SArithmeticData F) (h : A.Exterior) (i : Index A h) : MajorantIndex A h :=
  ⟨⟨activeSupport A i.1.val, (mem_activeSquarefreeDivisors_iff h.val h.property.1 _).mpr
    ⟨i.1.val.f.property.1, i.1.val.f_squarefree, by simpa only [activeSupport, i.1.property] using i.1.val.f_divides_radical⟩⟩,
    (⟨⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n⟩, i.1.val.epsilon)⟩

private theorem frozen_ext (A : SArithmeticData F) (T S : Frozen A)
    (hh : T.h = S.h) (hf : T.f = S.f) (ha : T.a = S.a)
    (hn : T.n = S.n) (he : T.epsilon = S.epsilon) : T = S := by
  cases T
  cases S
  simp_all

theorem encode_injective (A : SArithmeticData F) (h : A.Exterior) : Function.Injective (encode A h) := by
  intro i j hij
  have hf : i.1.val.f = j.1.val.f := congrArg (fun x : MajorantIndex A h => x.1.val.val) hij
  have ha : i.1.val.a = j.1.val.a := congrArg (fun x : MajorantIndex A h => x.2.1.1.val) hij
  have hc : i.2 = j.2 := congrArg (fun x : MajorantIndex A h => x.2.1.2.1) hij
  have hn : i.1.val.n = j.1.val.n := congrArg (fun x : MajorantIndex A h => x.2.1.2.2) hij
  have he : i.1.val.epsilon = j.1.val.epsilon := congrArg (fun x : MajorantIndex A h => x.2.2) hij
  have hh : i.1.val.h = j.1.val.h := i.1.property.trans j.1.property.symm
  have ht : i.1.val = j.1.val := frozen_ext A _ _ hh hf ha hn he
  exact Prod.ext (Subtype.ext ht) hc

theorem active_finite (A : SArithmeticData F) (h : A.Exterior) : Finite (ActiveIndex A h) := by
  let f : ActiveIndex A h → {f // f ∈ activeSquarefreeDivisors h.val} := fun f => ⟨f.val.val.val, f.property⟩
  apply Finite.of_injective f
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun f : {f // f ∈ activeSquarefreeDivisors h.val} => f.val) hij

def weight (A : SArithmeticData F) (h : A.Exterior) (i : MajorantIndex A h) : ℝ :=
  positiveRowWeight i.1.val 1 i.2.1

theorem rowWeight_nonneg {cS : Ideal (𝓞 F)} (f : ExteriorSquarefreeIdeal cS)
    (x : PositiveRowIndex f) : 0 ≤ positiveRowWeight f 1 x := by
  have hb := betaIdealTerm_nonneg f 0 (by norm_num) x.1
  simp only [betaIdealTerm, neg_zero, Real.rpow_zero, mul_one] at hb
  change 0 ≤ betaIdeal f x.1.val.val * (idealNorm x.1.val.val) ^ (0 : ℝ) at hb
  rw [Real.rpow_zero, mul_one] at hb
  unfold positiveRowWeight
  apply div_nonneg
  · exact mul_nonneg hb (Real.rpow_nonneg (by unfold rowNorm idealNorm; positivity) _)
  · unfold idealNorm
    positivity

theorem weight_summable (A : SArithmeticData F) (h : A.Exterior) : Summable (weight A h) := by
  letI := unit_finite A
  letI := active_finite A h
  apply (summable_sigma_of_nonneg (f := weight A h) (fun x => rowWeight_nonneg x.1.val x.2.1)).mpr
  refine ⟨?_, Summable.of_finite⟩
  intro f
  apply (summable_prod_of_nonneg (fun x => rowWeight_nonneg f.val x.1)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [weight, tsum_const, nsmul_eq_mul]
  exact (positiveRowWeight_summable_le f.val 1 (by norm_num)).1.mul_left _

theorem weight_tsum_le (A : SArithmeticData F) (h : A.Exterior) :
    (∑' i : MajorantIndex A h, weight A h i) ≤
      (Nat.card A.UnitQuotient : ℝ) * exteriorNormZeta A.cS (3 / 2) *
        exteriorNormZeta A.cS 4 * activeEulerSum h.val 1 := by
  letI := unit_finite A
  letI := active_finite A h
  have hw := weight_summable A h
  rw [hw.tsum_sigma]
  have he : ∀ f : ActiveIndex A h,
      (∑' i : PositiveRowIndex f.val × A.UnitQuotient, weight A h ⟨f, i⟩) =
        (Nat.card A.UnitQuotient : ℝ) * ∑' i : PositiveRowIndex f.val, positiveRowWeight f.val 1 i := by
    intro f
    have hs := hw.sigma_factor f
    rw [hs.tsum_prod]
    simp only [weight, tsum_const, nsmul_eq_mul, tsum_mul_left]
  simp_rw [he]
  have hnonneg : 0 ≤ (Nat.card A.UnitQuotient : ℝ) * exteriorNormZeta A.cS (3 / 2) * exteriorNormZeta A.cS 4 := by
    have hz : ∀ s : ℝ, 0 ≤ exteriorNormZeta A.cS s := by
      intro s
      exact tsum_nonneg (fun i => Real.rpow_nonneg
        (zero_le_one.trans (idealNorm_ge_one i.val i.property.1)) _)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hz _)) (hz _)
  calc
    _ ≤ ∑' f : ActiveIndex A h,
      (Nat.card A.UnitQuotient : ℝ) * (eulerIdeal f.val 1 * exteriorNormZeta A.cS (3 / 2) * exteriorNormZeta A.cS 4) := by
      apply Summable.tsum_le_tsum _ (Summable.of_finite) (Summable.of_finite)
      intro f
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      convert (positiveRowWeight_summable_le f.val 1 (by norm_num)).2 using 1 <;> norm_num
    _ = ((Nat.card A.UnitQuotient : ℝ) * exteriorNormZeta A.cS (3 / 2) * exteriorNormZeta A.cS 4) *
      ∑' f : ActiveIndex A h, activeEulerFactor f.val.val.val 1 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro f
      rw [activeEulerFactor_eq_eulerIdeal]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      let e : ActiveIndex A h → {f // f ∈ activeSquarefreeDivisors h.val} := fun f => ⟨f.val.val.val, f.property⟩
      have he : Function.Injective e := by
        intro i j hij
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun f : {f // f ∈ activeSquarefreeDivisors h.val} => f.val) hij
      have hh : ∀ f : {f // f ∈ activeSquarefreeDivisors h.val}, 0 ≤ activeEulerFactor f.val 1 := by
        intro f
        apply activeEulerFactor_nonneg _ _ _ (by norm_num)
        exact ((mem_activeSquarefreeDivisors_iff h.val h.property.1 f.val).mp f.property).1
      have ht := Summable.tsum_le_tsum_of_inj e he (fun f _ => hh f)
        (fun _ => le_rfl : ∀ f : ActiveIndex A h, activeEulerFactor f.val.val.val 1 ≤ activeEulerFactor (e f).val 1)
        Summable.of_finite Summable.of_finite
      convert ht using 1
      simp only [activeEulerSum, tsum_fintype]
      exact (Finset.sum_attach _ _).symm

theorem jointWeight_summable_le (A : SArithmeticData F) (h : A.Exterior) :
    Summable (fun i : Index A h => positiveRowWeight (activeSupport A i.1.val) 1
      (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ∧
    (∑' i : Index A h, positiveRowWeight (activeSupport A i.1.val) 1
      (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ≤
      (Nat.card A.UnitQuotient : ℝ) * exteriorNormZeta A.cS (3 / 2) *
        exteriorNormZeta A.cS 4 * activeEulerSum h.val 1 := by
  have hs := (weight_summable A h).comp_injective (encode_injective A h)
  refine ⟨hs, ?_⟩
  apply le_trans _ (weight_tsum_le A h)
  exact Summable.tsum_le_tsum_of_inj (encode A h) (encode_injective A h)
    (fun i _ => rowWeight_nonneg i.1.val i.2.1) (fun _ => le_rfl) hs (weight_summable A h)

theorem jointWeight_subpower (A : SArithmeticData F) (b : ℝ) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ h : A.Exterior,
      (Summable fun i : Index A h => positiveRowWeight (activeSupport A i.1.val) 1
        (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ∧
      (∑' i : Index A h, positiveRowWeight (activeSupport A i.1.val) 1
        (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ≤
        K * A.exteriorNorm h ^ b := by
  obtain ⟨Ka, hKa, ha⟩ := active_subpower (F := F) b hb
  let C := (Nat.card A.UnitQuotient : ℝ) * exteriorNormZeta A.cS (3 / 2) * exteriorNormZeta A.cS 4
  have hz : ∀ s : ℝ, 0 ≤ exteriorNormZeta A.cS s := by
    intro s
    exact tsum_nonneg (fun i => Real.rpow_nonneg
      (zero_le_one.trans (idealNorm_ge_one i.val i.property.1)) _)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hz _)) (hz _)
  refine ⟨(C + 1) * Ka, mul_pos (by linarith) hKa, ?_⟩
  intro h
  obtain ⟨hs, hsum⟩ := jointWeight_summable_le A h
  refine ⟨hs, ?_⟩
  calc
    _ ≤ C * activeEulerSum h.val 1 := hsum
    _ ≤ C * (Ka * A.exteriorNorm h ^ b) :=
      mul_le_mul_of_nonneg_left (ha h.val h.property.1 1 (by norm_num)).1 hC
    _ ≤ (C + 1) * (Ka * A.exteriorNorm h ^ b) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hKa.le (Real.rpow_nonneg (zero_le_one.trans (idealNorm_ge_one h.val h.property.1)) _))
    _ = _ := by ring

end Reindex

end
end DedekindZetaZeroFree.RMTailCutoff
