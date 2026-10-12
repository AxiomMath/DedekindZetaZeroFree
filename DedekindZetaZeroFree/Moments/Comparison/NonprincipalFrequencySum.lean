module

public import DedekindZetaZeroFree.Moments.Comparison.GoodDyadContourEstimate
public import DedekindZetaZeroFree.Moments.Comparison.ContourExponentMargins

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open MeasureTheory
open scoped Classical

private lemma dyad_index_unique {ι : Type*} (q : ι → ℝ) (principal : ι)
    (K : ℝ) (D : ℕ → Finset ι)
    (hD : ∀ j, comparisonFrequencyDyad q principal K ((2 : ℝ) ^ j) (D j))
    {u : ι} {j k : ℕ} (hj : u ∈ D j) (hk : u ∈ D k) : j = k := by
  have hlt : ∀ a b : ℕ, a < b → u ∈ D a → u ∈ D b → False := by
    intro a b hab ha hb
    have hp : (2 : ℝ) ^ (a + 1) ≤ (2 : ℝ) ^ b :=
      pow_le_pow_right₀ (by norm_num) hab
    have hqa := (hD a).1 u ha
    have hqb := (hD b).1 u hb
    rw [pow_succ] at hp
    nlinarith
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim (hlt j k h hj hk)
  · exact h
  · exact False.elim (hlt k j h hk hj)

private lemma initial_sum_dyads {ι : Type*} (q : ι → ℝ) (principal : ι)
    (K : ℝ) (D : ℕ → Finset ι)
    (hD : ∀ j, comparisonFrequencyDyad q principal K ((2 : ℝ) ^ j) (D j))
    (hCover : ∀ u, u ≠ principal → ∃ j, u ∈ D j)
    (f : ι → ℂ) (hf : Summable (fun u : {u : ι // u ≠ principal} => f u)) :
    Summable (fun j => ∑ u ∈ D j, f u) ∧
      (∑' u : {u : ι // u ≠ principal}, f u) = ∑' j, ∑ u ∈ D j, f u := by
  let g : (Σ j, ↥(D j)) → {u : ι // u ≠ principal} :=
    fun p => ⟨p.2, (hD p.1).1 p.2 p.2.property |>.1⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      have hv : a.2.val = b.2.val := congrArg Subtype.val hab
      have hi : a.1 = b.1 := dyad_index_unique q principal K D hD a.2.property
        (hv.symm ▸ b.2.property)
      cases a with | mk a x =>
        cases b with | mk b y =>
          dsimp at hi hv
          subst b
          congr 1
          exact Subtype.ext hv
    · intro u
      obtain ⟨j, hj⟩ := hCover u u.property
      exact ⟨⟨j, ⟨u, hj⟩⟩, Subtype.ext rfl⟩
  let e := Equiv.ofBijective g hg
  have hs : Summable (fun p : Σ j, ↥(D j) => f p.2) :=
    e.summable_iff.mpr hf
  have heq : (∑' u : {u : ι // u ≠ principal}, f u) =
      ∑' j, ∑' u : ↥(D j), f u := by
    rw [← hs.tsum_sigma]
    exact (e.tsum_eq (fun u => f u.val)).symm
  simpa only [Finset.tsum_subtype] using And.intro hs.sigma heq

private lemma frequencyIntegral_sum {ι : Type*}
    (q : ι → ℝ) (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (Z : ℝ) (C : Finset ι)
    (hi : ∀ u ∈ C, Integrable (fun t : ℝ × ℝ × ℝ =>
      comparisonFrequencyKernel q M W E Z u
        ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
        ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I))) :
    comparisonFrequencyIntegral q M W E C Z 4 4 2 =
      ∑ u ∈ C, comparisonFrequencyIntegral q M W E {u} Z 4 4 2 := by
  simp only [comparisonFrequencyIntegral, comparisonTripleVerticalIntegral, Finset.sum_singleton,
    Complex.ofReal_ofNat]
  rw [integral_finset_sum C hi, Finset.mul_sum]

private lemma near_power_bound (Z U a b c t δ : ℝ)
    (hZ : 1 ≤ Z) (hU : 1 ≤ U) (hb : 0 ≤ b) (hUmax : U ≤ Z ^ b)
    (hδ : 0 < δ) (ha : 0 ≤ a + δ)
    (hexp : c + b * (a + δ) ≤ t) :
    Z ^ c * U ^ a ≤ Z ^ t * U ^ (-δ) := by
  have hZpos : 0 < Z := by linarith
  have hUpos : 0 < U := by linarith
  have hp : U ^ (a + δ) ≤ Z ^ (b * (a + δ)) := by
    calc
      U ^ (a + δ) ≤ (Z ^ b) ^ (a + δ) :=
        Real.rpow_le_rpow (by positivity) hUmax ha
      _ = Z ^ (b * (a + δ)) := by rw [← Real.rpow_mul (le_trans (by norm_num) hZ)]
  have hpow : Z ^ (c + b * (a + δ)) ≤ Z ^ t :=
    Real.rpow_le_rpow_of_exponent_le hZ hexp
  calc
    Z ^ c * U ^ a = Z ^ c * U ^ (a + δ) * U ^ (-δ) := by
      rw [mul_assoc, ← Real.rpow_add hUpos (a + δ) (-δ)]
      congr 2 <;> ring
    _ ≤ Z ^ c * Z ^ (b * (a + δ)) * U ^ (-δ) := by
      gcongr
    _ = Z ^ (c + b * (a + δ)) * U ^ (-δ) := by rw [Real.rpow_add hZpos]
    _ ≤ Z ^ t * U ^ (-δ) := by gcongr

private lemma near_power_bound_negative (Z U a c t δ : ℝ)
    (hZ : 1 ≤ Z) (hU : 1 ≤ U) (hδ : 0 < δ)
    (ha : a + δ ≤ 0) (hc : c ≤ t) :
    Z ^ c * U ^ a ≤ Z ^ t * U ^ (-δ) := by
  have hUpos : 0 < U := by linarith
  have ht : U ^ (a + δ) ≤ 1 := by
    simpa using Real.rpow_le_one_of_one_le_of_nonpos hU ha
  have hp : Z ^ c ≤ Z ^ t := Real.rpow_le_rpow_of_exponent_le hZ hc
  calc
    Z ^ c * U ^ a = Z ^ c * U ^ (a + δ) * U ^ (-δ) := by
      rw [mul_assoc, ← Real.rpow_add hUpos (a + δ) (-δ)]
      congr 2 <;> ring
    _ ≤ Z ^ t * U ^ (-δ) := by
      gcongr
      exact (mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg (by positivity) _)).trans
        (by simpa using hp)

private lemma dyad_filter {ι : Type*} (q : ι → ℝ) (principal : ι)
    (K U : ℝ) (D : Finset ι) (hD : comparisonFrequencyDyad q principal K U D)
    (p : ι → Prop) : comparisonFrequencyDyad q principal K U (D.filter p) := by
  constructor
  · intro u hu
    exact hD.1 u (Finset.mem_of_mem_filter u hu)
  · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans hD.2

private lemma near_finite (Z : ℝ) (f : ℕ → ℝ) :
    (Function.support (fun j : ℕ =>
      if (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ) then f j else 0)).Finite := by
  obtain ⟨n, _, hn⟩ := Filter.exists_lt_of_tendsto_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    0 (Z ^ (10001 / 100000 : ℝ))
  refine (Set.finite_le_nat n).subset ?_
  intro j hj
  have hp : (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ) := by
    by_contra h
    simpa [Function.mem_support, h] using hj
  by_contra h
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ j :=
    pow_le_pow_right₀ (by norm_num) (le_of_not_ge h)
  linarith

section AnalyticSummation

variable
    {ι : Type*} (principal : ι) (q : ι → ℝ) (M W : ℂ → ℂ)
    (E P : ι → ℂ → ℂ → ℂ → ℂ) (L : ι → ℂ → ℂ)
    (good : ℝ → ι → Prop)
    (Ω : Set (ℂ × ℂ × ℂ)) (hΩ : IsOpen Ω)
    (hbox : ∀ ξ w z : ℂ,
      ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
      w ∈ comparisonClosedStrip (3 / 1000) 4 →
      z ∈ comparisonClosedStrip (2 / 5) 2 → (ξ, w, z) ∈ Ω)
    (hE : ∀ u : ι, u ≠ principal →
      DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => E u p.1 p.2.1 p.2.2) Ω)
    (hM : DifferentiableOn ℂ M {z : ℂ | 2 / 5 - 1 / 100000 < z.re})
    (hW : DifferentiableOn ℂ W {w : ℂ | 3 / 1000 - 1 / 100000 < w.re})
    (hMdecay : comparisonRapidStripDecay M (2 / 5) 2)
    (hWdecay : comparisonRapidStripDecay W (3 / 1000) 4)
    (hEBound : ∃ d : ℝ, 0 ≤ d ∧ ∀ δ : ℝ, 0 < δ →
      ∃ B : ℝ, 0 < B ∧ ∀ u : ι, u ≠ principal → 1 ≤ q u →
        ∀ ξ w z : ℂ,
          ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
          w ∈ comparisonClosedStrip (3 / 1000) 4 →
          z ∈ comparisonClosedStrip (2 / 5) 2 →
          ‖E u ξ w z‖ ≤ B * (q u) ^ (1 / 2 + δ) * (2 + |w.im|) ^ d)
    (Ωleft : Set (ℂ × ℂ × ℂ)) (hΩleft : IsOpen Ωleft)
    (hleft : ∀ ξ w z : ℂ,
      ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
      w.re = 3 / 1000 → z.re = 2 / 5 → (ξ, w, z) ∈ Ωleft)
    (hP : ∀ u : ι, u ≠ principal →
      DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => P u p.1 p.2.1 p.2.2) Ωleft)
    (hL : ∀ (U : ℝ) (u : ι), 1 ≤ U → good U u →
      DifferentiableOn ℂ (L u) {ξ : ℂ | 0 < ξ.re})
    (hfactor : ∀ (u : ι) (ξ w z : ℂ), u ≠ principal →
      (ξ, w, z) ∈ Ωleft → L u ξ ≠ 0 → E u ξ w z = P u ξ w z / L u ξ)
    (A_F : ℝ) (hAF : 0 ≤ A_F)
    (hPBound : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧
      ∀ (u : ι) (ξ w z : ℂ), u ≠ principal → 1 ≤ q u →
        ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
        w.re = 3 / 1000 → z.re = 2 / 5 →
        ‖P u ξ w z‖ ≤ B * (q u) ^ (1 / 2 + δ) *
          (2 + |ξ.im|) ^ A_F * (2 + |w.im|) ^ A_F * (2 + |z.im|) ^ A_F)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hρsmall : ρ < min (1 / 10) (1 / (A_F + 1)))
    (hdetector : ∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
      ∀ (U : ℝ) (u : ι), Udet ≤ U → good U u → U ≤ q u → q u < 2 * U →
        ∀ ξ : ℂ, 499 / 500 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ →
          L u ξ ≠ 0 ∧ ‖(L u ξ)⁻¹‖ ≤ B * U ^ δ)
    (K : ℝ) (hK : 0 < K)
    (hFar : comparisonFarContourInput q principal M W E)
    (D : ℕ → Finset ι)
    (hDyads : ∀ j : ℕ,
      comparisonFrequencyDyad q principal K ((2 : ℝ) ^ j) (D j))
    (hCover : ∀ u : ι, u ≠ principal → ∃ j : ℕ, u ∈ D j)
    (hExceptional : ∃ B Uexc : ℝ, 0 < B ∧ 1 ≤ Uexc ∧
      ∀ j : ℕ, Uexc ≤ (2 : ℝ) ^ j →
        (((D j).filter (fun u => ¬ good ((2 : ℝ) ^ j) u)).card : ℝ) ≤
          B * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ))
    (hInitialAbsolute : ∀ Z : ℝ, 1 ≤ Z →
      (∀ u : ι, u ≠ principal →
        Integrable (fun t : ℝ × ℝ × ℝ =>
          comparisonFrequencyKernel q M W E Z u
            ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
            ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I))) ∧
      Summable (fun u : {u : ι // u ≠ principal} =>
        ∫ t : ℝ × ℝ × ℝ,
          ‖comparisonFrequencyKernel q M W E Z u.val
            ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
            ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I)‖))

include hΩ hbox hE hM hW hMdecay hWdecay hEBound
  hΩleft hleft hP hL hfactor hAF hPBound hρ hρsmall hdetector hK
  hFar hDyads hCover hExceptional hInitialAbsolute

set_option maxHeartbeats 1500000 in

theorem comparison_nonprincipal_sum_margins_analytic :
    ∃ ε A₁ C Z₀ : ℝ,
      0 < ε ∧ (1 + 10001 / 100000) * ε < 1 / 10000 ∧
      1 / ρ < A₁ ∧ 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        let near := fun j : ℕ =>
          if (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ) then
            ‖comparisonFrequencyIntegral q M W E (D j) Z 4 4 2‖ else 0
        let far := fun j : ℕ =>
          if Z ^ (10001 / 100000 : ℝ) < (2 : ℝ) ^ j then
            ‖comparisonFrequencyIntegral q M W E (D j) Z 4 4 2‖ else 0
        (Function.support near).Finite ∧
        (∑' j : ℕ, near j) ≤ C * Z ^ (7 / 15 - 1 / 2500 : ℝ) ∧
        Summable far ∧
        (∑' j : ℕ, far j) ≤
          C * Z ^ (44901 / 100000 + (10001 / 100000) * ε) ∧
        (∑' j : ℕ, far j) ≤ C * Z ^ (7 / 15 - 1 / 2500 : ℝ) ∧
        (∀ j : ℕ,
          Z ^ (9 / 100 : ℝ) < (2 : ℝ) ^ j →
          (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ) →
          let G := (D j).filter (fun u => good ((2 : ℝ) ^ j) u)
          ∃ E_tail : ℂ,
            comparisonFrequencyIntegral q M W E G Z 4 4 2 =
              comparisonTruncatedFrequencyIntegral q M W E G Z
                (499 / 500) (3 / 1000) (2 / 5) (((2 : ℝ) ^ j) ^ ρ) + E_tail ∧
            ‖comparisonTruncatedFrequencyIntegral q M W E G Z
                (499 / 500) (3 / 1000) (2 / 5) (((2 : ℝ) ^ j) ^ ρ)‖ ≤
              C * Z ^ (comparisonE (499 / 500) (3 / 1000) (2 / 5)) *
                ((2 : ℝ) ^ j) ^ (11 / 10 + ε) ∧
            ‖E_tail‖ ≤
              C * Z ^ (comparisonE comparisonSigma₁ (3 / 1000) (2 / 5)) *
                ((2 : ℝ) ^ j) ^ (11 / 10 + ε - ρ * A₁)) := by
  let ε : ℝ := 1 / 100000
  let A₁ : ℝ := 4 / ρ
  have hε : 0 < ε := by norm_num [ε]
  have hA₁ : 0 < A₁ := div_pos (by norm_num) hρ
  have hA₁big : 1 / ρ < A₁ := by dsimp [A₁]; exact div_lt_div_of_pos_right (by norm_num) hρ
  have hρA₁ : ρ * A₁ = 4 := by dsimp [A₁]; field_simp
  obtain ⟨Bexc, Uexc, hBexc, hUexc, hExc⟩ := hExceptional
  obtain ⟨Ao, hAo, ho⟩ := comparison_ordinary_dyad_analytic principal q M W E Ω hΩ hbox hE
    hM hW hMdecay hWdecay hEBound 1 K ε (by norm_num) hK hε
  obtain ⟨Ae, hAe, he⟩ := comparison_ordinary_dyad_analytic principal q M W E Ω hΩ hbox hE
    hM hW hMdecay hWdecay hEBound (1 / 2) Bexc ε (by norm_num) hBexc hε
  obtain ⟨Bc, hBc, hg⟩ := comparison_good_dyad_analytic principal q M W E P L good Ω hΩ hbox hE
    hM hW hMdecay hWdecay hEBound Ωleft hΩleft hleft hP hL hfactor A_F hAF hPBound
    ρ hρ hρsmall hdetector K hK ε hε
  obtain ⟨Bt, Ug, hBt, hUg, hg⟩ := hg A₁ hA₁
  obtain ⟨Af, hAf, hf⟩ := comparison_far_dyad_sum q principal M W E hFar K hK ε hε
  obtain ⟨Zg, hZg⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 100)).eventually
      (Filter.eventually_ge_atTop (max Uexc Ug)))
  let B := Ao + Ae + Bc + Bt + Af + 1
  let w := fun j : ℕ => ((2 : ℝ) ^ j) ^ (-ε)
  have hw : Summable w := by
    have hs := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-ε))
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith : -ε < 0))
    exact hs.congr (fun j => Real.rpow_pow_comm (by norm_num) (-ε) j)
  have hw0 : ∀ j, 0 ≤ w j := fun j => Real.rpow_nonneg (by positivity) _
  let C := B * (1 + ∑' j, w j)
  have htsum0 : 0 ≤ ∑' j, w j := tsum_nonneg hw0
  have hB : 0 < B := by dsimp [B]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; nlinarith
  have hAoB : Ao ≤ B := by dsimp [B]; linarith
  have hAeB : Ae ≤ B := by dsimp [B]; linarith
  have hBcB : Bc ≤ B := by dsimp [B]; linarith
  have hBtB : Bt ≤ B := by dsimp [B]; linarith
  have hAfB : Af ≤ B := by dsimp [B]; linarith
  refine ⟨ε, A₁, C, max 1 Zg, hε, by norm_num [ε], hA₁big, hC,
    le_max_left _ _, ?_⟩
  intro Z hZ
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZpos : 0 < Z := by linarith
  have hZlarge := hZg Z ((le_max_right _ _).trans hZ)
  let t : ℝ := 7 / 15 - 1 / 2500
  let c : ℝ := comparisonE comparisonSigma₁ (3 / 1000) (2 / 5)
  let c' : ℝ := comparisonE (499 / 500) (3 / 1000) (2 / 5)
  have hc : c ≤ t := by
    dsimp [c, t]
    have hm := comparisonE_first_dyadic_margin
    linarith
  have hNearBound : ∀ j : ℕ, (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ) →
      ‖comparisonFrequencyIntegral q M W E (D j) Z 4 4 2‖ ≤ B * Z ^ t * w j := by
    intro j hCut
    let U : ℝ := (2 : ℝ) ^ j
    have hU : 1 ≤ U := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hUp : 0 < U := by linarith
    have hD := hDyads j
    by_cases hSmall : U ≤ Z ^ (9 / 100 : ℝ)
    · have hb := (ho Z U hZ1 hU (D j) hD.1 (by simpa using hD.2)).2
      have hp := near_power_bound Z U (1 + 1 / 2 - 2 / 5 + ε) (9 / 100) c t ε
        hZ1 hU (by norm_num) hSmall hε (by norm_num [ε]) (by
          have hm := comparisonE_first_dyadic_margin
          dsimp [c, t, ε]; linarith)
      calc
        _ ≤ Ao * (Z ^ c * U ^ (1 + 1 / 2 - 2 / 5 + ε)) := by simpa [mul_assoc] using hb
        _ ≤ Ao * (Z ^ t * U ^ (-ε)) := mul_le_mul_of_nonneg_left hp (le_of_lt hAo)
        _ ≤ B * Z ^ t * w j := by
          simpa only [w, U, mul_assoc] using
            mul_le_mul_of_nonneg_right hAoB (by positivity : 0 ≤ Z ^ t * U ^ (-ε))
    · have hMedium : Z ^ (9 / 100 : ℝ) < U := lt_of_not_ge hSmall
      have hUexc' : Uexc ≤ U := (le_max_left _ _).trans (hZlarge.trans (le_of_lt hMedium))
      have hUg' : Ug ≤ U := (le_max_right _ _).trans (hZlarge.trans (le_of_lt hMedium))
      let G := (D j).filter (fun u => good U u)
      let X := (D j).filter (fun u => ¬ good U u)
      have hGD : comparisonFrequencyDyad q principal K U G :=
        dyad_filter q principal K U (D j) hD (fun u => good U u)
      have hXD : comparisonFrequencyDyad q principal K U X := by
        constructor
        · intro u hu
          exact hD.1 u (Finset.mem_filter.mp hu).1
        · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans hD.2
      obtain ⟨tail, hdecomp, hcentral, htail⟩ := hg Z U G hZ1 hUg' hMedium hCut hGD
        (fun u hu => (Finset.mem_filter.mp hu).2)
      have hexception := (he Z U hZ1 hU X hXD.1 (by simpa only [X, U] using hExc j hUexc')).2
      have hsplit : comparisonFrequencyIntegral q M W E (D j) Z 4 4 2 =
          comparisonFrequencyIntegral q M W E G Z 4 4 2 +
          comparisonFrequencyIntegral q M W E X Z 4 4 2 := by
        have hi := (hInitialAbsolute Z hZ1).1
        rw [frequencyIntegral_sum q M W E Z (D j) (fun u hu => hi u (hD.1 u hu).1),
          frequencyIntegral_sum q M W E Z G (fun u hu => hi u (hGD.1 u hu).1),
          frequencyIntegral_sum q M W E Z X (fun u hu => hi u (hXD.1 u hu).1)]
        exact (Finset.sum_filter_add_sum_filter_not (D j) (fun u => good U u) _).symm
      have pc := near_power_bound Z U (11 / 10 + ε) (10001 / 100000) c' t ε
        hZ1 hU (by norm_num) hCut hε (by norm_num [ε]) (by
          have hm := comparisonE_left_contour_margin
          dsimp [c', t, ε]; linarith)
      have pe := near_power_bound Z U (1 / 2 + 1 / 2 - 2 / 5 + ε) (10001 / 100000) c t ε
        hZ1 hU (by norm_num) hCut hε (by norm_num [ε]) (by
          have hm := comparisonE_second_dyadic_margin
          dsimp [c, t, ε]; linarith)
      have pt := near_power_bound_negative Z U (11 / 10 + ε - ρ * A₁) c t ε
        hZ1 hU hε (by rw [hρA₁]; norm_num [ε]) hc
      have hcb : ‖comparisonTruncatedFrequencyIntegral q M W E G Z
          (499 / 500) (3 / 1000) (2 / 5) (U ^ ρ)‖ ≤ Bc * (Z ^ t * U ^ (-ε)) := by
        calc
          _ ≤ Bc * (Z ^ c' * U ^ (11 / 10 + ε)) := by simpa only [c', mul_assoc] using hcentral
          _ ≤ _ := mul_le_mul_of_nonneg_left pc hBc.le
      have htb : ‖tail‖ ≤ Bt * (Z ^ t * U ^ (-ε)) := by
        calc
          _ ≤ Bt * (Z ^ c * U ^ (11 / 10 + ε - ρ * A₁)) := by simpa only [c, mul_assoc] using htail
          _ ≤ _ := mul_le_mul_of_nonneg_left pt hBt.le
      have heb : ‖comparisonFrequencyIntegral q M W E X Z 4 4 2‖ ≤ Ae * (Z ^ t * U ^ (-ε)) := by
        calc
          _ ≤ Ae * (Z ^ c * U ^ (1 / 2 + 1 / 2 - 2 / 5 + ε)) := by simpa only [c, mul_assoc] using hexception
          _ ≤ _ := mul_le_mul_of_nonneg_left pe hAe.le
      rw [hsplit, hdecomp]
      calc
        _ ≤ (‖comparisonTruncatedFrequencyIntegral q M W E G Z
            (499 / 500) (3 / 1000) (2 / 5) (U ^ ρ)‖ + ‖tail‖) +
            ‖comparisonFrequencyIntegral q M W E X Z 4 4 2‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
        _ ≤ Bc * (Z ^ t * U ^ (-ε)) + Bt * (Z ^ t * U ^ (-ε)) + Ae * (Z ^ t * U ^ (-ε)) :=
          add_le_add (add_le_add hcb htb) heb
        _ ≤ B * Z ^ t * w j := by
          have hcoef : Bc + Bt + Ae ≤ B := by dsimp [B]; linarith
          have hm := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ Z ^ t * U ^ (-ε))
          dsimp [w]; nlinarith
  let near := fun j : ℕ => if (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ) then
    ‖comparisonFrequencyIntegral q M W E (D j) Z 4 4 2‖ else 0
  let far := fun j : ℕ => if Z ^ (10001 / 100000 : ℝ) < (2 : ℝ) ^ j then
    ‖comparisonFrequencyIntegral q M W E (D j) Z 4 4 2‖ else 0
  have hnfinite : (Function.support near).Finite := near_finite Z _
  have hn : Summable near := summable_of_finite_support hnfinite
  have hnmajor : ∀ j, near j ≤ B * Z ^ t * w j := by
    intro j
    dsimp [near]
    split_ifs with h
    · exact hNearBound j h
    · positivity
  have hnBound : (∑' j, near j) ≤ C * Z ^ t := by
    calc
      _ ≤ ∑' j, B * Z ^ t * w j := hn.tsum_le_tsum hnmajor (hw.mul_left _)
      _ = B * Z ^ t * ∑' j, w j := tsum_mul_left
      _ ≤ C * Z ^ t := by dsimp [C]; nlinarith [Real.rpow_nonneg hZpos.le t]
  obtain ⟨hfs, hfbound⟩ := hf Z D hZ1 hDyads
  have hfBound : (∑' j, far j) ≤ C * Z ^ (44901 / 100000 + (10001 / 100000) * ε) := by
    exact hfbound.trans (mul_le_mul_of_nonneg_right (hAfB.trans hBC) (by positivity))
  have hfarExp : 44901 / 100000 + (10001 / 100000) * ε ≤ t := by norm_num [ε, t]
  have hfTarget : (∑' j, far j) ≤ C * Z ^ t :=
    hfBound.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1 hfarExp) hC.le)
  refine ⟨hnfinite, hnBound, hfs, hfBound, hfTarget, ?_⟩
  intro j hMedium hCut
  let U : ℝ := (2 : ℝ) ^ j
  have hUg' : Ug ≤ U := (le_max_right _ _).trans (hZlarge.trans hMedium.le)
  have hGD := dyad_filter q principal K U (D j) (hDyads j) (fun u => good U u)
  obtain ⟨tail, ht, hcentral, htail⟩ := hg Z U _ hZ1 hUg' hMedium hCut hGD
    (fun u hu => (Finset.mem_filter.mp hu).2)
  refine ⟨tail, ht, hcentral.trans ?_, htail.trans ?_⟩
  · gcongr
    exact hBcB.trans hBC
  · gcongr
    exact hBtB.trans hBC

theorem comparison_nonprincipal_sum_analytic :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        let singleton := fun u : {u : ι // u ≠ principal} =>
          comparisonFrequencyIntegral q M W E {u.val} Z 4 4 2
        let dyadic := fun j : ℕ =>
          comparisonFrequencyIntegral q M W E (D j) Z 4 4 2
        Summable (fun u => ‖singleton u‖) ∧
        Summable singleton ∧
        Summable (fun j => ‖dyadic j‖) ∧
        Summable dyadic ∧
        (∑' u : {u : ι // u ≠ principal}, singleton u) =
          (∑' j : ℕ, dyadic j) ∧
        ‖∑' u : {u : ι // u ≠ principal}, singleton u‖ ≤
          C * Z ^ (7 / 15 - 1 / 2500 : ℝ) := by
  obtain ⟨ε, A₁, C, Z₀, hε, hεsmall, hA₁, hC, hZ₀, hmargin⟩ :=
    comparison_nonprincipal_sum_margins_analytic principal q M W E P L good Ω hΩ hbox hE
      hM hW hMdecay hWdecay hEBound Ωleft hΩleft hleft hP hL hfactor A_F hAF hPBound
      ρ hρ hρsmall hdetector K hK hFar D hDyads hCover hExceptional hInitialAbsolute
  refine ⟨2 * C, Z₀, by positivity, hZ₀, ?_⟩
  intro Z hZ
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  obtain ⟨hInt, hAbs⟩ := hInitialAbsolute Z hZ1
  let singleton := fun u : {u : ι // u ≠ principal} =>
    comparisonFrequencyIntegral q M W E {u.val} Z 4 4 2
  let dyadic := fun j => comparisonFrequencyIntegral q M W E (D j) Z 4 4 2
  let near := fun j : ℕ =>
    if (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ) then ‖dyadic j‖ else 0
  let far := fun j : ℕ =>
    if Z ^ (10001 / 100000 : ℝ) < (2 : ℝ) ^ j then ‖dyadic j‖ else 0
  have hSingletonNorm : Summable (fun u => ‖singleton u‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
      (hAbs.mul_left ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖)
    intro u
    dsimp [singleton]
    simp only [comparisonFrequencyIntegral, comparisonTripleVerticalIntegral,
      Finset.sum_singleton, Complex.ofReal_ofNat, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  have hSingleton : Summable singleton := hSingletonNorm.of_norm
  have hSum : ∀ j, dyadic j = ∑ u ∈ D j,
      comparisonFrequencyIntegral q M W E {u} Z 4 4 2 := by
    intro j
    exact frequencyIntegral_sum q M W E Z (D j)
      (fun u hu => hInt u ((hDyads j).1 u hu).1)
  obtain ⟨hDyadic, hEq⟩ := initial_sum_dyads q principal K D hDyads hCover
    (fun u => comparisonFrequencyIntegral q M W E {u} Z 4 4 2) hSingleton
  have hDyadic' : Summable dyadic := hDyadic.congr (fun j => (hSum j).symm)
  have hEq' : (∑' u, singleton u) = ∑' j, dyadic j :=
    hEq.trans (tsum_congr (fun j => (hSum j).symm))
  obtain ⟨hFinite, hNearBound, hFar, hFarStrong, hFarBound, hGood⟩ := hmargin Z hZ
  have hNear : Summable near := summable_of_finite_support hFinite
  have hSplit : ∀ j, ‖dyadic j‖ = near j + far j := by
    intro j
    dsimp [near, far]
    by_cases h : (2 : ℝ) ^ j ≤ Z ^ (10001 / 100000 : ℝ)
    · simp [h, not_lt_of_ge h]
    · simp [h, lt_of_not_ge h]
  have hDyadicNorm : Summable (fun j => ‖dyadic j‖) :=
    (hNear.add hFar).congr (fun j => (hSplit j).symm)
  refine ⟨hSingletonNorm, hSingleton, hDyadicNorm, hDyadic', hEq', ?_⟩
  rw [hEq']
  calc
    ‖∑' j, dyadic j‖ ≤ ∑' j, ‖dyadic j‖ := norm_tsum_le_tsum_norm hDyadicNorm
    _ = (∑' j, near j) + ∑' j, far j :=
      (tsum_congr hSplit).trans (hNear.tsum_add hFar)
    _ ≤ C * Z ^ (7 / 15 - 1 / 2500 : ℝ) + C * Z ^ (7 / 15 - 1 / 2500 : ℝ) :=
      add_le_add hNearBound hFarBound
    _ = (2 * C) * Z ^ (7 / 15 - 1 / 2500 : ℝ) := by ring

end AnalyticSummation
end
end DedekindZetaZeroFree
