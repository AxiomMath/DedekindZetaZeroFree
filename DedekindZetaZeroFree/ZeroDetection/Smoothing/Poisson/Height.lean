module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.GammaShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorHeight

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef
open scoped Classical
open Filter Topology

variable {F : Type} [Field F] [NumberField F]

def smoothedSum (F : Type) [Field F] [NumberField F] (U : ℝ) {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (β γ : ℝ) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    ((DetectorDef.a F U n : ℝ) : ℂ) * ω n *
      (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
      ((Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℝ) : ℂ)

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def ConvexityExponent (A_F : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) →
        ∀ t : ℝ,
          ‖g (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |t|) ^ A_F) ∧
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s) →
        ∀ t : ℝ,
          ‖g (((1 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((99 / 200 : ℝ) + ε) * (2 + |t|) ^ A_F)

def HeightSpec (A_F ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1 / 10000 ∧ ρ < 1 / (1000 * (A_F + 1)) ∧
  -3 / 1250 + A_F * ρ + 1 / 10000 < 0 ∧
  79 / 125 + ρ + 1 / 16000 + 1 / 10000 < 317 / 500 ∧
  ∀ e : ℝ, 0 < e → ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
    ∀ u ∈ exceptionalSet D ρ U, ∀ s : ℂ, IsLZero (D.omega u) s → σ₀ ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ 4 * U ^ ρ →
      ‖smoothedSum F U (D.omega u).character s.re s.im‖ ≤ e

theorem detector_height_numerics (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hρ : 0 < ρ)
    (h1 : ρ < 1 / 10000) (h2 : ρ < 1 / (1000 * (A_F + 1))) :
    -3 / 1250 + A_F * ρ + 1 / 10000 < 0 ∧
      79 / 125 + ρ + 1 / 16000 + 1 / 10000 < 317 /500 := by
  have h2' : ρ * (1000 * (A_F + 1)) < 1 := (lt_div_iff₀ (by linarith)).mp h2
  have hAρ : A_F * ρ < 1 / 1000 := by nlinarith
  constructor
  · linarith
  · linarith

private theorem smoothedSum_eq_shift (U β γ : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) :
    smoothedSum F U ω.character β γ = DetectorShift.smoothedSum F U β γ ω := by
  unfold smoothedSum DetectorShift.smoothedSum
  refine tsum_congr fun n => ?_
  by_cases hn : n = ⊥
  · subst hn
    have h0 : ω.character ⊥ = 0 := (ω.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
    simp [h0]
  · simp [hn]

private theorem height_of_bound (A_F A' : ℝ) (hA : 0 ≤ A_F) (hA' : 0 ≤ A')
    (hsh : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ β γ : ℝ, σ₀ ≤ β → β ≤ 1 →
          IsLZero (D.omega u) ((β : ℂ) + (γ : ℂ) * Complex.I) →
          ‖DetectorShift.smoothedSum F U β γ (D.omega u)‖ ≤
            C * U ^ (-(3 / 1250 : ℝ) + ε) * (2 + |γ|) ^ A') :
    ∃ ρ : ℝ, HeightSpec D A_F ρ := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 1 / (10000 * (A_F + A' + 2)) := ⟨_, rfl⟩
  have hK : 0 < A_F + A' + 2 := by linarith
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact div_pos one_pos (by linarith)
  have hρ1 : ρ < 1 / 10000 := by
    rw [hρdef, div_lt_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hρ2 : ρ < 1 / (1000 * (A_F + 1)) := by
    rw [hρdef, div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hρ3 : ρ < 1 / (1000 * (A' + 1)) := by
    rw [hρdef, div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have h3 : ρ * (1000 * (A' + 1)) < 1 := (lt_div_iff₀ (by linarith)).mp hρ3
  have hA'ρ : ρ * A' < 1 / 1000 := by nlinarith
  obtain ⟨n1, n2⟩ := detector_height_numerics A_F ρ hA hρpos hρ1 hρ2
  obtain ⟨C, hC, hbound⟩ := hsh (1 / 10000) (by norm_num)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 3 / 1250 - 1 / 10000 - ρ * A' := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = C * (6 : ℝ) ^ A' := ⟨_, rfl⟩
  have htend : Tendsto (fun U : ℝ => M * U ^ (-δ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hδ).const_mul M
    rw [mul_zero] at this
    exact this
  refine ⟨ρ, ?_⟩
  unfold HeightSpec
  refine ⟨hρpos, hρ1, hρ2, n1, n2, ?_⟩
  intro e he
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds he))
  refine ⟨max 2 N, le_max_left _ _, fun U hU u hu s hs0 hs1 hs2 hsim => ?_⟩
  have hU2 : 2 ≤ U := le_trans (le_max_left _ _) hU
  have hUN : N ≤ U := le_trans (le_max_right _ _) hU
  have hUpos : 0 < U := by linarith
  have hU1 : 1 ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρpos.le
  obtain ⟨huu, hq1, hq2, -⟩ := hu
  have hL : IsLZero (D.omega u) ((s.re : ℂ) + (s.im : ℂ) * Complex.I) := by
    rw [Complex.re_add_im]; exact hs0
  have hb := hbound u huu U hU2 hq1 hq2 s.re s.im hs1 hs2 hL
  rw [smoothedSum_eq_shift]
  have hle : 2 + |s.im| ≤ 6 * U ^ ρ := by linarith
  have hpos : 0 ≤ 2 + |s.im| := by positivity
  have hmono : (2 + |s.im|) ^ A' ≤ (6 * U ^ ρ) ^ A' :=
    Real.rpow_le_rpow hpos hle hA'
  have hC0 : 0 ≤ C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) :=
    mul_nonneg hC.le (Real.rpow_nonneg hUpos.le _)
  have hEq : C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * (6 * U ^ ρ) ^ A' = M * U ^ (-δ) := by
    have hm : (6 * U ^ ρ) ^ A' = (6 : ℝ) ^ A' * U ^ (ρ * A') := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hUpos.le _), ← Real.rpow_mul hUpos.le]
    have hp : U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * U ^ (ρ * A') = U ^ (-δ) := by
      rw [← Real.rpow_add hUpos]; congr 1; rw [hδdef]; ring
    rw [hm, hMdef, ← hp]; ring
  calc ‖DetectorShift.smoothedSum F U s.re s.im (D.omega u)‖
      ≤ C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * (2 + |s.im|) ^ A' := hb
    _ ≤ C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * (6 * U ^ ρ) ^ A' :=
        mul_le_mul_of_nonneg_left hmono hC0
    _ = M * U ^ (-δ) := hEq
    _ ≤ e := (hN U hUN).le

theorem detector_height (A_F : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F) :
    ∃ ρ : ℝ, HeightSpec D A_F ρ := by
  have hex := DetectorShift.detector_shift (D := D)
  obtain ⟨A', hA', hsh⟩ := hex
  exact height_of_bound D A_F A' hA hA' hsh

theorem detector_height_exists :
    ∃ A_F ρ : ℝ, 0 ≤ A_F ∧ ConvexityExponent D A_F ∧ HeightSpec D A_F ρ := by
  have hex := DedekindZetaZeroFree.Quantitative.Convex.convexity (D := D)
  obtain ⟨A_F, hA0, hconv⟩ := hex
  have hCE : ConvexityExponent D A_F := by
    unfold ConvexityExponent
    constructor
    · intro ε hε
      obtain ⟨C, hC, h1, -⟩ := hconv ε hε (3 / 25 : ℝ) (by norm_num)
      refine ⟨C, hC, fun u hu U hU2 hUq hUq2 g hg hgs t => ?_⟩
      have key := h1 u hu U hU2 hUq hUq2 g hg hgs (3 / 25 : ℝ) t le_rfl (by norm_num)
      have e : U ^ ((11 / 25 : ℝ) + ε) = U ^ ((1 - 3 / 25 : ℝ) / 2 + ε) := by norm_num
      rw [e]
      exact key
    · intro ε hε
      obtain ⟨C, hC, -, h2⟩ := hconv ε hε (1 / 100 : ℝ) (by norm_num)
      refine ⟨C, hC, fun u hu U hU2 hUq hUq2 g hg hgs t => ?_⟩
      have key := h2 u hu U hU2 hUq hUq2 g hg hgs (1 / 100 : ℝ) t (by norm_num) (by norm_num)
      have e : U ^ ((99 / 200 : ℝ) + ε) = U ^ ((1 - 1 / 100 : ℝ) / 2 + ε) := by norm_num
      rw [e]
      exact key
  obtain ⟨ρ, hρ⟩ := detector_height D A_F hA0 hCE
  exact ⟨A_F, ρ, hA0, hCE, hρ⟩

end

end DedekindZetaZeroFree.Quantitative.DetectorHeight
