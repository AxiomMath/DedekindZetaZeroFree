module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEnvelopes
public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.RadicalCoprimeColumnExpansion

@[expose] public section

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectAssembly
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorBin (P : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F (2 * P)).filter (ErrorRectangles.InBin P)

def rectangleMass (C : Context Q) (B : ℝ) (unit : Bool) (P : ℝ × ℝ) : ℝ :=
  ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
    ∑ a ∈ C.originalRows B unit,
      ‖C.pairSum (fun p hp => if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
        C.coefficient p * C.primitive p hp a else 0)‖

lemma row_sqrt_le (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hM : 1 ≤ C.M) (hB : 1 ≤ B)
    {a : Ideal (𝓞 F)} (ha : a ∈ C.originalRows B unit) :
    Real.sqrt (C.M / norm a) ≤ Real.sqrt (C.M / B) := by
  apply Real.sqrt_le_sqrt
  have hBa : B ≤ norm a := by
    cases unit
    · obtain ⟨ha, -⟩ := Finset.mem_filter.mp ha
      exact ((Sieve.mem_paperShell F (c * C.d) B a).mp ha).2.2.1.le
    · have hat : a = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp ha).1
      simp [hat, hunit rfl, norm]
  exact div_le_div_of_nonneg_left (by linarith) (by linarith) hBa

private lemma pairSum_mul (C : Context Q) (z : ℂ)
    (f : (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ) :
    C.pairSum (fun p hp => z * f p hp) = z * C.pairSum f := by
  unfold Context.pairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

private lemma pairSum_sum {α : Type*} (C : Context Q) (s : Finset α)
    (f : α → (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ) :
    C.pairSum (fun p hp => ∑ i ∈ s, f i p hp) =
      ∑ i ∈ s, C.pairSum (f i) := by
  unfold Context.pairSum
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

theorem assembly (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hM : 1 ≤ C.M) (hB : 1 ≤ B)
    (w : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hdensity : ∀ p ∈ C.pairs,
      Context.largeDensity ((c * C.d) * (p.1 * p.2)) (C.Z2 B) =
        ∑ e ∈ C.mobiusDivisors, ∑ P ∈ ErrorRectangles.directRectangles C B,
          ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
            w e f₁ f₂ * (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then 1 else 0))
    (hw : ∀ e ∈ C.mobiusDivisors, ∀ P ∈ ErrorRectangles.directRectangles C B,
      ∀ f₁ ∈ divisorBin (F := F) P.1, ∀ f₂ ∈ divisorBin (F := F) P.2,
        ‖w e f₁ f₂‖ ≤ (1 / norm e) / (P.1 * P.2)) :
    ‖E4 C B unit‖ ≤ Real.sqrt (C.M / B) *
      (‖C.kappa * C.mass‖ * (∑ e ∈ C.mobiusDivisors, 1 / norm e) *
        ∑ P ∈ ErrorRectangles.directRectangles C B,
          rectangleMass C B unit P / (P.1 * P.2)) := by
  let S := ErrorRectangles.directRectangles C B
  let R := C.originalRows B unit
  let v := fun f₁ f₂ a => C.pairSum (fun p hp =>
    if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then C.coefficient p * C.primitive p hp a else 0)
  have heq : E4 C B unit =
      ∑ e ∈ C.mobiusDivisors, ∑ P ∈ S,
        ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
          ∑ a ∈ R, (C.kappa * C.mass) * (Real.sqrt (C.M / norm a) : ℂ) *
            w e f₁ f₂ * v f₁ f₂ a := by
    unfold E4
    have hrewrite : C.pairSum (fun p hp => C.coefficient p *
        ∑ a ∈ R, C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) *
          C.mass * Context.largeDensity ((c * C.d) * (p.1 * p.2)) (C.Z2 B)) =
        C.pairSum (fun p hp => C.coefficient p *
        ∑ a ∈ R, C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) *
          C.mass * (∑ e ∈ C.mobiusDivisors, ∑ P ∈ S,
            ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
              w e f₁ f₂ * (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then 1 else 0))) := by
      unfold Context.pairSum
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp only
      rw [hdensity p hp]
    rw [hrewrite]
    simp only [Finset.mul_sum, pairSum_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro P hP
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f₁ hf₁
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f₂ hf₂
    apply Finset.sum_congr rfl
    intro a ha
    rw [← pairSum_mul]
    unfold Context.pairSum
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> simp [v, mul_assoc] <;> ring
  rw [heq]
  apply le_trans (norm_sum_le _ _)
  calc
    _ ≤ ∑ e ∈ C.mobiusDivisors, ∑ P ∈ S,
        ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
          ∑ a ∈ R, Real.sqrt (C.M / B) * ‖C.kappa * C.mass‖ *
            ((1 / norm e) / (P.1 * P.2)) * ‖v f₁ f₂ a‖ := by
      apply Finset.sum_le_sum
      intro e he
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f₁ hf₁
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f₂ hf₂
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have h := hw e he P hP f₁ hf₁ f₂ hf₂
      have hr := row_sqrt_le C B unit hunit hM hB ha
      calc
        _ ≤ ‖C.kappa * C.mass‖ * Real.sqrt (C.M / B) *
            ((1 / norm e) / (P.1 * P.2)) * ‖v f₁ f₂ a‖ := by
          gcongr
          simp only [norm_mul]; exact le_rfl
        _ = _ := by simp only [norm_mul]; ring
    _ = _ := by
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul,
        rectangleMass, S, R, v]
      simp_rw [← Finset.sum_comm (s := C.mobiusDivisors)]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro f₁ hf₁
      apply Finset.sum_congr rfl
      intro f₂ hf₂
      apply Finset.sum_congr rfl
      intro a ha
      ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectAssembly

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectGeometry
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma norm_le_of_dvd {a b : Ideal (𝓞 F)} (hb : b ≠ ⊥) (h : a ∣ b) :
    norm a ≤ norm b := by
  unfold norm
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp h))

private lemma norm_mul (a b : Ideal (𝓞 F)) : norm (a * b) = norm a * norm b := by
  simp [norm, map_mul]

private lemma bin_exists (X : ℝ) (hX : 1 ≤ 2 * X) (f : Ideal (𝓞 F))
    (hf0 : f ≠ ⊥) (hf : norm f ≤ 2 * X) :
    ∃ P ∈ ErrorRectangles.scales X, 1 ≤ P ∧ P ≤ 2 * X ∧ ErrorRectangles.InBin P f := by
  have hfn : 1 ≤ norm f := by
    unfold norm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hf0)
  have hXX : 2 * X ≤ 2 * max 1 X := by gcongr; exact le_max_right _ _
  have hcover : ∃ j : ℕ, norm f ≤ (2 : ℝ) ^ j :=
    ⟨Vendor.dyadicLength (2 * max 1 X), hf.trans (hXX.trans (Vendor.dyadicLength_cover _))⟩
  let j := Nat.find hcover
  have hj : norm f ≤ (2 : ℝ) ^ j := Nat.find_spec hcover
  have hjle : j ≤ Vendor.dyadicLength (2 * max 1 X) :=
    Nat.find_min' hcover (hf.trans (hXX.trans (Vendor.dyadicLength_cover _)))
  rcases hj0 : j with _ | k
  · refine ⟨1, by simp [ErrorRectangles.scales], le_rfl, hX, hf0, ?_, ?_⟩
    · simpa using hfn
    · have hh : norm f ≤ 1 := by simpa [hj0] using hj
      linarith
  · have hk : k < Vendor.dyadicLength (2 * max 1 X) := by omega
    have hlow : (2 : ℝ) ^ k < norm f := by
      exact lt_of_not_ge (Nat.find_min hcover (by omega))
    refine ⟨(2 : ℝ) ^ k, ?_, one_le_pow₀ (by norm_num), hlow.le.trans hf, hf0, ?_, ?_⟩
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    · split_ifs <;> linarith
    · simpa [hj0, pow_succ'] using hj

private lemma bin_unique {X P R : ℝ} {f : Ideal (𝓞 F)}
    (hP : P ∈ ErrorRectangles.scales X) (hR : R ∈ ErrorRectangles.scales X)
    (hp : ErrorRectangles.InBin P f) (hr : ErrorRectangles.InBin R f) : P = R := by
  have power {S : ℝ} (hS : S ∈ ErrorRectangles.scales X) : ∃ i : ℕ, S = 2 ^ i := by
    rcases Finset.mem_insert.mp hS with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact ⟨i, hi.symm⟩
  obtain ⟨i, rfl⟩ := power hP
  obtain ⟨j, rfl⟩ := power hR
  have step {i j : ℕ} (hij : i < j) : 2 * (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j := by
    calc
      _ = (2 : ℝ) ^ (i+1) := by rw [pow_succ'];
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hij
  have nonone {j : ℕ} (hj : 0 < j) : (2 : ℝ) ^ j ≠ 1 := by
    have hh : (2 : ℝ) ≤ 2 ^ j := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
    linarith
  rcases lt_trichotomy i j with hij | hij | hij
  · have hj := nonone (by omega : 0 < j)
    have hl : (2 : ℝ) ^ j < norm f := by simpa [hj] using hr.2.1
    have hh := step hij
    linarith [hp.2.2]
  · rw [hij]
  · have hi := nonone (by omega : 0 < i)
    have hl : (2 : ℝ) ^ i < norm f := by simpa [hi] using hp.2.1
    have hh := step hij
    linarith [hr.2.2]

private lemma norm_nonneg (a : Ideal (𝓞 F)) : 0 ≤ norm a := by
  unfold norm; positivity

private lemma bin_admissible (C : Context Q) (B : ℝ)
    (hn : 1 ≤ norm C.d) {e : Ideal (𝓞 F)} (he : e ∈ C.mobiusDivisors)
    {P : ℝ × ℝ} (hrect : P ∈ ErrorRectangles.rectangles C)
    {a b : Ideal (𝓞 F)} (ha : ErrorRectangles.InBin P.1 a)
    (hb : ErrorRectangles.InBin P.2 b) (hl : C.Z2 B < norm (e * (a*b))) :
    P ∈ ErrorRectangles.directRectangles C B := by
  have hcd0 : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have hed : e ∣ c * C.d := by
    have hr0 : (c * C.d).radical ≠ ⊥ := by
      intro h
      apply hcd0
      apply bot_unique
      simpa [h] using (Ideal.le_radical : c * C.d ≤ (c * C.d).radical)
    have hd := (mem_idealDivisors hr0).mp he
    exact hd.trans (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  have hen : norm e ≤ norm c * norm C.d := by
    simpa [norm_mul] using norm_le_of_dvd hcd0 hed
  have hP := ErrorRectangles.rectangle_endpoints C P hrect
  have hh : norm (e * (a*b)) ≤ (max 1 (norm c) * norm C.d) * (4 * (P.1*P.2)) := by
    rw [norm_mul, norm_mul]
    have hab : norm a * norm b ≤ (2*P.1)*(2*P.2) :=
      mul_le_mul ha.2.2 hb.2.2 (norm_nonneg b) (by linarith [hP.1])
    calc
      _ ≤ (norm c * norm C.d) * ((2*P.1)*(2*P.2)) :=
        mul_le_mul hen hab (mul_nonneg (norm_nonneg a) (norm_nonneg b))
          (mul_nonneg (norm_nonneg c) (norm_nonneg C.d))
      _ ≤ (max 1 (norm c) * norm C.d) * ((2*P.1)*(2*P.2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 (norm c)) (norm_nonneg C.d))
          (by nlinarith [hP.1, hP.2.1])
      _ = _ := by ring
  apply Finset.mem_filter.mpr
  refine ⟨hrect, ?_⟩
  change ErrorRectangles.lowerConstant c * Real.sqrt (C.M / B) *
    Real.rpow (C.M*C.N) C.δ / norm C.d ≤ P.1*P.2
  rw [mul_assoc]
  change ErrorRectangles.lowerConstant c * C.Z2 B / norm C.d ≤ P.1*P.2
  rw [ErrorRectangles.lowerConstant, div_le_iff₀ (by linarith : 0 < norm C.d)]
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * max 1 (norm c))).mpr
  nlinarith

private lemma sum_if_out {α : Type*} (s : Finset α) (P : Prop) [Decidable P]
    (f : α → ℂ) : (if P then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if P then f i else 0 := by
  split_ifs <;> simp [*]

def weight (Z : ℝ) (e a b : Ideal (𝓞 F)) : ℂ :=
  if Z < norm (e * (a*b)) then
    (UniqueFactorizationMonoid.moebius e : ℂ) * (UniqueFactorizationMonoid.moebius a : ℂ) *
      (UniqueFactorizationMonoid.moebius b : ℂ) /
        ((norm e : ℂ) * (norm a : ℂ) * (norm b : ℂ)) else 0

private lemma density_bins (C : Context Q) (B : ℝ)
    (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2*C.N)
    {p : Ideal (𝓞 F) × Ideal (𝓞 F)} (hp : p ∈ C.pairs)
    {e : Ideal (𝓞 F)} (he : e ∈ C.mobiusDivisors) :
    (∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2, weight (C.Z2 B) e a b) =
      ∑ P ∈ ErrorRectangles.directRectangles C B,
        ∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2,
          if ErrorRectangles.InBin P.1 a ∧ ErrorRectangles.InBin P.2 b then
            weight (C.Z2 B) e a b else 0 := by
  have hpv := (Finset.mem_filter.mp hp).2
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have had := (mem_idealDivisors hpv.hu0).mp ha
  have hbd := (mem_idealDivisors hpv.hv0).mp hb
  by_cases hl : C.Z2 B < norm (e*(a*b))
  · have hpp := (Finset.mem_filter.mp hp).1
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hpp
    have huN : norm p.1 ≤ 2*C.N / norm C.d :=
      ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (Finset.mem_filter.mp hu).1).2.2
    have hvN : norm p.2 ≤ 2*C.N / norm C.d :=
      ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (Finset.mem_filter.mp hv).1).2.2
    have hX : 1 ≤ 2*(C.N / norm C.d) := by
      rw [← mul_div_assoc, le_div_iff₀ (by linarith : 0 < norm C.d)]
      simpa using hnN
    obtain ⟨P₁,hP₁s,hP₁,hP₁N,hP₁a⟩ := bin_exists _ hX a (ne_bot_of_mem_idealDivisors ha)
      ((norm_le_of_dvd hpv.hu0 had).trans (by simpa [mul_div_assoc] using huN))
    obtain ⟨P₂,hP₂s,hP₂,hP₂N,hP₂b⟩ := bin_exists _ hX b (ne_bot_of_mem_idealDivisors hb)
      ((norm_le_of_dvd hpv.hv0 hbd).trans (by simpa [mul_div_assoc] using hvN))
    have hrect : (P₁,P₂) ∈ ErrorRectangles.rectangles C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hP₁s,hP₂s⟩,hP₁,hP₂,?_,?_,p,hp,a,b,had,hbd,hP₁a,hP₂b⟩ <;>
        simpa [mul_div_assoc] using (by assumption : _)
    have hAdm := bin_admissible C B hn he hrect hP₁a hP₂b hl
    symm
    rw [Finset.sum_eq_single (P₁,P₂)]
    · simp [hP₁a, hP₂b]
    · intro R hR hne
      have hRs := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
      by_cases hRa : ErrorRectangles.InBin R.1 a
      · by_cases hRb : ErrorRectangles.InBin R.2 b
        · have h1 := bin_unique hRs.1 hP₁s hRa hP₁a
          have h2 := bin_unique hRs.2 hP₂s hRb hP₂b
          exact (hne (Prod.ext h1 h2)).elim
        · simp [hRb]
      · simp [hRa]
    · intro hnmem
      exact (hnmem hAdm).elim
  · simp [weight, hl]

private lemma sum_bin (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) (P : ℝ) (H : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ idealDivisors u, if ErrorRectangles.InBin P a then H a else 0) =
      ∑ a ∈ LargeDirectAssembly.divisorBin (F := F) P, if a ∣ u then H a else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (by intros; rfl)
  ext a
  simp only [Finset.mem_filter, mem_idealDivisors hu, LargeDirectAssembly.divisorBin,
    mem_boundedNormIdeals]
  constructor
  · rintro ⟨had, hbin⟩
    exact ⟨⟨hbin.2.2, hbin⟩, had⟩
  · rintro ⟨⟨_, hbin⟩, had⟩
    exact ⟨had, hbin⟩

theorem density_expansion (C : Context Q) (B : ℝ)
    (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2*C.N)
    {p : Ideal (𝓞 F) × Ideal (𝓞 F)} (hp : p ∈ C.pairs) :
    Context.largeDensity ((c*C.d)*(p.1*p.2)) (C.Z2 B) =
      ∑ e ∈ C.mobiusDivisors, ∑ P ∈ ErrorRectangles.directRectangles C B,
        ∑ a ∈ LargeDirectAssembly.divisorBin (F := F) P.1,
          ∑ b ∈ LargeDirectAssembly.divisorBin (F := F) P.2,
            weight (C.Z2 B) e a b * (if a ∣ p.1 ∧ b ∣ p.2 then 1 else 0) := by
  have hpv := (Finset.mem_filter.mp hp).2
  rw [LargeDirectDictionary.largeDensity_triple C p hpv]
  apply Finset.sum_congr rfl
  intro e he
  change (∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2, weight (C.Z2 B) e a b) = _
  rw [density_bins C B hn hnN hp he]
  apply Finset.sum_congr rfl
  intro P hP
  have heq : (∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2,
      if ErrorRectangles.InBin P.1 a ∧ ErrorRectangles.InBin P.2 b then weight (C.Z2 B) e a b else 0) =
      ∑ a ∈ idealDivisors p.1, if ErrorRectangles.InBin P.1 a then
        ∑ b ∈ idealDivisors p.2, if ErrorRectangles.InBin P.2 b then weight (C.Z2 B) e a b else 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp [*]
  rw [heq, sum_bin p.1 hpv.hu0]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_bin p.2 hpv.hv0, sum_if_out]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h1 : a ∣ p.1 <;> by_cases h2 : b ∣ p.2 <;> simp [h1, h2]

private lemma moebius_norm_le (a : Ideal (𝓞 F)) :
    ‖(UniqueFactorizationMonoid.moebius a : ℂ)‖ ≤ 1 := by
  by_cases ha : Squarefree a
  · rw [ha.moebius_eq]
    simp
  · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree ha]

theorem weight_bound (C : Context Q) (B : ℝ)
    {e : Ideal (𝓞 F)} (he : e ∈ C.mobiusDivisors)
    {P : ℝ × ℝ} (hP : P ∈ ErrorRectangles.directRectangles C B)
    {a b : Ideal (𝓞 F)} (ha : a ∈ LargeDirectAssembly.divisorBin (F := F) P.1)
    (hb : b ∈ LargeDirectAssembly.divisorBin (F := F) P.2) :
    ‖weight (C.Z2 B) e a b‖ ≤ (1 / norm e) / (P.1*P.2) := by
  have hrect := (Finset.mem_filter.mp hP).1
  have hPend := ErrorRectangles.rectangle_endpoints C P hrect
  have habin := (Finset.mem_filter.mp ha).2
  have hbbin := (Finset.mem_filter.mp hb).2
  have hPa : P.1 ≤ norm a := by
    by_cases h : P.1 = 1
    · simpa [h] using habin.2.1
    · exact (by simpa [h] using habin.2.1 : P.1 < norm a).le
  have hPb : P.2 ≤ norm b := by
    by_cases h : P.2 = 1
    · simpa [h] using hbbin.2.1
    · exact (by simpa [h] using hbbin.2.1 : P.2 < norm b).le
  have hepos : 0 < norm e := by
    unfold norm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ne_bot_of_mem_idealDivisors he))
  have hapos : 0 < norm a := by linarith [hPend.1]
  have hbpos : 0 < norm b := by linarith [hPend.2.1]
  have hPpos : 0 < P.1*P.2 := by nlinarith [hPend.1, hPend.2.1]
  unfold weight
  split_ifs
  · simp only [norm_div, _root_.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hepos, abs_of_pos hapos, abs_of_pos hbpos]
    calc
      _ ≤ 1 / (norm e * norm a * norm b) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          _ ≤ 1*1*1 := mul_le_mul (mul_le_mul (moebius_norm_le e) (moebius_norm_le a)
            (by positivity) (by norm_num)) (moebius_norm_le b) (by positivity) (by norm_num)
          _ = 1 := by ring
      _ ≤ (1 / norm e) / (P.1*P.2) := by
        rw [div_div]
        apply one_div_le_one_div_of_le (by positivity)
        have hh := mul_le_mul hPa hPb (by linarith [hPend.2.1]) (by linarith [hPend.1])
        nlinarith
  · simp only [norm_zero]
    positivity

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectGeometry

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorBin (P : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F (2 * P)).filter (ErrorRectangles.InBin P)

def rectangleMass (C : Context Q) (B : ℝ) (unit : Bool) (P : ℝ × ℝ) : ℝ :=
  ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
    ∑ a ∈ C.originalRows B unit,
      ‖C.pairSum (fun p hp =>
        if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
          C.coefficient p * C.primitive p hp a
        else 0)‖

def residueMagnitude (C : Context Q) : ℝ := ‖C.kappa * C.mass‖

def fixedDivisorMass (C : Context Q) : ℝ :=
  ∑ f₀ ∈ C.mobiusDivisors, 1 / norm f₀

theorem large_divisor_expansion (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ)
    (hB : 1 ≤ B) (hBK : B ≤ C.K) (hKM : C.K ≤ C.M)
    (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2 * C.N) :
    ‖E4 C B unit‖ ≤ Real.sqrt (C.M / B) *
      (residueMagnitude C * fixedDivisorMass C *
        ∑ P ∈ ErrorRectangles.directRectangles C B,
          rectangleMass C B unit P / (P.1 * P.2)) := by
  simpa only [residueMagnitude, fixedDivisorMass, rectangleMass,
    divisorBin, LargeDirectAssembly.rectangleMass, LargeDirectAssembly.divisorBin] using
    LargeDirectAssembly.assembly C B unit hunit hM hB
      (LargeDirectGeometry.weight (C.Z2 B))
      (fun p hp => LargeDirectGeometry.density_expansion C B hn hnN hp)
      (fun e he P hP a ha b hb => LargeDirectGeometry.weight_bound C B he hP ha hb)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

end

end
