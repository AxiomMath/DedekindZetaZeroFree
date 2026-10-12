module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicWeights

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open Filter
open scoped Classical Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def HolomorphicNear (A : ℂ → ℂ) (p : ℂ) : Prop :=
  ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ A s

def HasFinitePrincipalPart (M : ℂ → ℂ) (p : ℂ) (coeff : ℕ → ℂ) (N : ℕ) : Prop :=
  ∃ B : ℂ → ℂ, HolomorphicNear B p ∧
    ∀ᶠ s in nhdsWithin p ({p}ᶜ),
      M s = B s + ∑ j ∈ Finset.Icc 1 N, coeff j / (s - p) ^ j

private lemma HolomorphicNear.analyticAt' {A : ℂ → ℂ} {p : ℂ} (h : HolomorphicNear A p) :
    AnalyticAt ℂ A p := Complex.analyticAt_iff_eventually_differentiableAt.mpr h

private lemma AnalyticAt.holomorphicNear' {A : ℂ → ℂ} {p : ℂ} (h : AnalyticAt ℂ A p) :
    HolomorphicNear A p := Complex.analyticAt_iff_eventually_differentiableAt.mp h

private lemma HolomorphicNear.add' {A B : ℂ → ℂ} {p : ℂ}
    (hA : HolomorphicNear A p) (hB : HolomorphicNear B p) :
    HolomorphicNear (fun s => A s + B s) p := by
  filter_upwards [hA, hB] with s ha hb
  exact ha.add hb

private lemma HolomorphicNear.mul' {A B : ℂ → ℂ} {p : ℂ}
    (hA : HolomorphicNear A p) (hB : HolomorphicNear B p) :
    HolomorphicNear (fun s => A s * B s) p := by
  filter_upwards [hA, hB] with s ha hb
  exact ha.mul hb

private lemma HolomorphicNear.const' (c : ℂ) (p : ℂ) :
    HolomorphicNear (fun _ => c) p :=
  Filter.Eventually.of_forall fun _ => differentiableAt_const c

private lemma HolomorphicNear.const_mul' {B : ℂ → ℂ} {p : ℂ} (c : ℂ)
    (hB : HolomorphicNear B p) : HolomorphicNear (fun s => c * B s) p := by
  filter_upwards [hB] with s hs
  exact hs.const_mul c

private lemma HolomorphicNear.congr' {A B : ℂ → ℂ} {p : ℂ} (hAB : A =ᶠ[𝓝 p] B)
    (hA : HolomorphicNear A p) : HolomorphicNear B p :=
  AnalyticAt.holomorphicNear' ((analyticAt_congr hAB).mp (hA.analyticAt'))

private lemma HolomorphicNear.sub_const_comp {A : ℂ → ℂ} {p : ℂ}
    (hA : HolomorphicNear A 0) : HolomorphicNear (fun s => A (s - p)) p := by
  have hmap : Tendsto (fun s : ℂ => s - p) (𝓝 p) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => s - p) (𝓝 p) (𝓝 (p - p)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using h
  filter_upwards [hmap.eventually hA] with s hs
  exact hs.comp s (by fun_prop)

private lemma HolomorphicNear.finset_sum {ι : Type*} (K : Finset ι) {B : ι → ℂ → ℂ} {p : ℂ}
    (hB : ∀ k ∈ K, HolomorphicNear (B k) p) :
    HolomorphicNear (fun s => ∑ k ∈ K, B k s) p := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using HolomorphicNear.const' 0 p
  | insert a s ha ih =>
    have h1 : HolomorphicNear (B a) p := hB a (Finset.mem_insert_self a s)
    have h2 : HolomorphicNear (fun t => ∑ k ∈ s, B k t) p :=
      ih (fun k hk => hB k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert ha] using h1.add' h2

private lemma taylor_split {g : ℂ → ℂ} {p : ℂ} (hg : HolomorphicNear g p) (n : ℕ) :
    ∃ F : ℂ → ℂ, HolomorphicNear F p ∧ ∀ᶠ s in 𝓝 p,
      g s = (∑ i ∈ Finset.range n, (iteratedDeriv i g p / (i.factorial : ℂ)) * (s - p) ^ i)
        + (s - p) ^ n * F s := by
  have hg' : AnalyticAt ℂ (fun t : ℂ => g (p + t)) 0 := by
    have h1 : AnalyticAt ℂ (fun t : ℂ => p + t) 0 := by fun_prop
    have hgan : AnalyticAt ℂ g (p + 0) := by simpa using hg.analyticAt'
    simpa [Function.comp_def] using hgan.comp h1
  obtain ⟨F', hF'an, hF'⟩ := AnalyticAt.exists_eventuallyEq_sum_add_pow_mul hg' n
  refine ⟨fun s => F' (s - p), (AnalyticAt.holomorphicNear' hF'an).sub_const_comp, ?_⟩
  have hshift : Tendsto (fun s : ℂ => s - p) (𝓝 p) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => s - p) (𝓝 p) (𝓝 (p - p)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using h
  have hiter : ∀ i, iteratedDeriv i (fun t : ℂ => g (p + t)) 0 = iteratedDeriv i g p := by
    intro i
    simpa using congrFun (iteratedDeriv_comp_const_add i g p) 0
  filter_upwards [hshift.eventually hF'] with s hs
  rw [show p + (s - p) = s by ring] at hs
  simp only [smul_eq_mul, hiter] at hs
  have hsum : (∑ i ∈ Finset.range n, ((s - p) ^ i / (i.factorial : ℂ)) * iteratedDeriv i g p)
      = ∑ i ∈ Finset.range n, (iteratedDeriv i g p / (i.factorial : ℂ)) * (s - p) ^ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum] at hs
  exact hs

private lemma taylor_reindex (a : ℕ → ℂ) (z : ℂ) (N : ℕ) :
    (∑ i ∈ Finset.range N, a i * z ^ i) = ∑ j ∈ Finset.Icc 1 N, a (N - j) * z ^ (N - j) := by
  symm
  have hset : Finset.Icc 1 N = (Finset.range N).image (fun i => N - i) := by
    ext j
    constructor
    · intro hj
      rw [Finset.mem_Icc] at hj
      exact Finset.mem_image.mpr ⟨N - j, Finset.mem_range.mpr (by omega), by omega⟩
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      rw [Finset.mem_range] at hi
      rw [Finset.mem_Icc]
      omega
  rw [hset]
  rw [Finset.sum_image (by
    intro x hx y hy h
    have hx' : x < N := Finset.mem_range.mp hx
    have hy' : y < N := Finset.mem_range.mp hy
    have h' : N - x = N - y := h
    omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < N := Finset.mem_range.mp hi
  rw [show N - (N - i) = i by omega]

private lemma div_pow_split {A : ℂ → ℂ} {p : ℂ} {N : ℕ} (hN : 1 ≤ N)
    {c : ℕ → ℂ} {F : ℂ → ℂ} (hF : HolomorphicNear F p)
    (hA : ∀ᶠ s in 𝓝 p,
      A s = (∑ j ∈ Finset.Icc 1 N, c j * (s - p) ^ (N - j)) + (s - p) ^ N * F s) :
    HasFinitePrincipalPart (fun s => A s / (s - p) ^ N) p c N := by
  refine ⟨F, hF, ?_⟩
  filter_upwards [hA.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hAs hs
  have hsp : s - p ≠ 0 := sub_ne_zero.mpr hs
  rw [hAs]
  have hterm : ∀ j ∈ Finset.Icc 1 N,
      c j * (s - p) ^ (N - j) / (s - p) ^ N = c j / (s - p) ^ j := by
    intro j hj
    have hjN : j ≤ N := (Finset.mem_Icc.mp hj).2
    have h1 : (s - p) ^ (N - j) / (s - p) ^ N = ((s - p) ^ j)⁻¹ := by
      rw [pow_sub₀ _ hsp hjN, mul_div_cancel_left₀ ((s - p) ^ j)⁻¹ (pow_ne_zero N hsp)]
    rw [mul_div_assoc, h1, div_eq_mul_inv]
  rw [add_div, Finset.sum_div, mul_div_cancel_left₀ (F s) (pow_ne_zero N hsp),
    Finset.sum_congr rfl hterm]
  exact add_comm _ _

private lemma hasFinitePrincipalPart_of_holomorphicNear {B : ℂ → ℂ} {p : ℂ}
    (hB : HolomorphicNear B p) (N : ℕ) :
    HasFinitePrincipalPart B p (fun _ => 0) N := by
  refine ⟨B, hB, ?_⟩
  filter_upwards with s
  simp

namespace HasFinitePrincipalPart

private lemma congr_fun {M M' : ℂ → ℂ} {p : ℂ} {coeff : ℕ → ℂ} {N : ℕ}
    (h : HasFinitePrincipalPart M p coeff N) (hMM' : M =ᶠ[𝓝[≠] p] M') :
    HasFinitePrincipalPart M' p coeff N := by
  obtain ⟨B, hB, hEq⟩ := h
  exact ⟨B, hB, hMM'.symm.trans hEq⟩

private lemma congr_coeff {M : ℂ → ℂ} {p : ℂ} {coeff coeff' : ℕ → ℂ} {N : ℕ}
    (h : HasFinitePrincipalPart M p coeff N)
    (hcc : ∀ j ∈ Finset.Icc 1 N, coeff j = coeff' j) :
    HasFinitePrincipalPart M p coeff' N := by
  obtain ⟨B, hB, hEq⟩ := h
  refine ⟨B, hB, ?_⟩
  filter_upwards [hEq] with s hs
  rw [hs]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [hcc j hj]

private lemma const_mul {M : ℂ → ℂ} {p : ℂ} {coeff : ℕ → ℂ} {N : ℕ} (c : ℂ)
    (h : HasFinitePrincipalPart M p coeff N) :
    HasFinitePrincipalPart (fun s => c * M s) p (fun j => c * coeff j) N := by
  obtain ⟨B, hB, hEq⟩ := h
  refine ⟨fun s => c * B s, hB.const_mul' c, ?_⟩
  filter_upwards [hEq] with s hs
  rw [hs, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc]

private lemma add {M M' : ℂ → ℂ} {p : ℂ} {coeff coeff' : ℕ → ℂ} {N : ℕ}
    (h : HasFinitePrincipalPart M p coeff N) (h' : HasFinitePrincipalPart M' p coeff' N) :
    HasFinitePrincipalPart (fun s => M s + M' s) p (fun j => coeff j + coeff' j) N := by
  obtain ⟨B, hB, hEq⟩ := h
  obtain ⟨B', hB', hEq'⟩ := h'
  refine ⟨fun s => B s + B' s, hB.add' hB', ?_⟩
  filter_upwards [hEq, hEq'] with s hs hs'
  have hsum : (∑ j ∈ Finset.Icc 1 N, (coeff j + coeff' j) / (s - p) ^ j)
      = (∑ j ∈ Finset.Icc 1 N, coeff j / (s - p) ^ j)
        + ∑ j ∈ Finset.Icc 1 N, coeff' j / (s - p) ^ j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_div]
  rw [hs, hs', hsum]
  ring

private lemma mono {M : ℂ → ℂ} {p : ℂ} {coeff : ℕ → ℂ} {N N' : ℕ}
    (h : HasFinitePrincipalPart M p coeff N) (hNN : N ≤ N') :
    HasFinitePrincipalPart M p (fun j => if j ≤ N then coeff j else 0) N' := by
  obtain ⟨B, hB, hEq⟩ := h
  refine ⟨B, hB, ?_⟩
  filter_upwards [hEq] with s hs
  rw [hs]
  congr 1
  have hite : ∀ j, (if j ≤ N then coeff j else 0) / (s - p) ^ j
      = if j ≤ N then coeff j / (s - p) ^ j else 0 := by
    intro j; by_cases hj : j ≤ N <;> simp [hj]
  rw [show (∑ j ∈ Finset.Icc 1 N', (if j ≤ N then coeff j else 0) / (s - p) ^ j)
      = ∑ j ∈ Finset.Icc 1 N', (if j ≤ N then coeff j / (s - p) ^ j else 0) from
    Finset.sum_congr rfl fun j _ => hite j]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun j _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

private lemma finset_sum {ι : Type*} (K : Finset ι) {M : ι → ℂ → ℂ}
    {p : ℂ} {coeff : ι → ℕ → ℂ} {N : ℕ}
    (h : ∀ k ∈ K, HasFinitePrincipalPart (M k) p (coeff k) N) :
    HasFinitePrincipalPart (fun s => ∑ k ∈ K, M k s) p (fun j => ∑ k ∈ K, coeff k j) N := by
  classical
  have hB : ∀ k, ∃ B : ℂ → ℂ, HolomorphicNear B p ∧
      (k ∈ K → ∀ᶠ s in 𝓝[≠] p, M k s = B s + ∑ j ∈ Finset.Icc 1 N, coeff k j / (s - p) ^ j) := by
    intro k
    by_cases hk : k ∈ K
    · obtain ⟨B, hB1, hB2⟩ := h k hk
      exact ⟨B, hB1, fun _ => hB2⟩
    · exact ⟨0, HolomorphicNear.const' 0 p, fun hk' => absurd hk' hk⟩
  choose B hBhol hBeq using hB
  refine ⟨fun s => ∑ k ∈ K, B k s, HolomorphicNear.finset_sum K (fun k _ => hBhol k), ?_⟩
  have hall : ∀ᶠ s in 𝓝[≠] p, ∀ k ∈ K,
      M k s = B k s + ∑ j ∈ Finset.Icc 1 N, coeff k j / (s - p) ^ j :=
    (Finset.eventually_all K).mpr (fun k hk => hBeq k hk)
  filter_upwards [hall] with s hs
  rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]

end HasFinitePrincipalPart

private lemma logPrincipalPart_holomorphicNear (P : Polynomial ℂ) {p : ℂ} (hp : p ≠ 0) :
    HolomorphicNear (logPrincipalPart P) p := by
  unfold logPrincipalPart
  refine HolomorphicNear.finset_sum P.support fun k _ => ?_
  filter_upwards [isOpen_ne.mem_nhds hp] with s hs
  exact (differentiableAt_const _).div (by fun_prop) (pow_ne_zero _ hs)

private lemma cpow_const_holomorphicNear (X : ℝ) (hX : 0 < X) (p : ℂ) :
    HolomorphicNear (fun s : ℂ => (X : ℂ) ^ s) p :=
  AnalyticAt.holomorphicNear' (AnalyticAt.cpow analyticAt_const analyticAt_id (Complex.ofReal_mem_slitPlane.2 hX))

namespace LogMellinAdmissible

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}

private lemma decomp (h : LogMellinAdmissible f δ P H) :
    ∃ A : ℂ → ℂ, HolomorphicNear A 0 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), H s = A s + logPrincipalPart P s := by
  obtain ⟨A, hAdiff, hAeq⟩ := h.holomorphic_remainder
  have hopen : {s : ℂ | -δ < s.re} ∈ 𝓝 (0 : ℂ) :=
    IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
      (by simpa using neg_lt_zero.mpr h.delta_pos)
  refine ⟨A, ?_, ?_⟩
  · filter_upwards [hopen] with s hs
    exact hAdiff s hs
  · filter_upwards [(show ∀ᶠ s in 𝓝[≠] (0 : ℂ), -δ < s.re from
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ s in 𝓝 (0:ℂ), -δ < s.re from hopen)),
      self_mem_nhdsWithin] with s hs hs0
    exact hAeq s hs hs0

private lemma holomorphicNear (h : LogMellinAdmissible f δ P H) {p : ℂ}
    (hp : -δ < p.re) (hp0 : p ≠ 0) : HolomorphicNear H p := by
  obtain ⟨A, hAdiff, hAeq⟩ := h.holomorphic_remainder
  have hopen : {s : ℂ | -δ < s.re} ∈ 𝓝 p :=
    IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hp
  have hAhol : HolomorphicNear A p :=
    (show ∀ᶠ s in 𝓝 p, -δ < s.re from hopen).mono fun s hs => hAdiff s hs
  have hsum : HolomorphicNear (fun s => A s + logPrincipalPart P s) p :=
    hAhol.add' (logPrincipalPart_holomorphicNear P hp0)
  have heq : (fun s => A s + logPrincipalPart P s) =ᶠ[𝓝 p] H := by
    filter_upwards [hopen, isOpen_ne.mem_nhds hp0] with s hs hs0
    exact (hAeq s hs hs0).symm
  exact hsum.congr' heq

end LogMellinAdmissible

theorem holomorphic_div_pow_principalPart (A : ℂ → ℂ) (p : ℂ)
    (hA : HolomorphicNear A p) (N : ℕ) (hN : 1 ≤ N) :
    HasFinitePrincipalPart (fun s => A s / (s - p) ^ N) p
      (fun j => iteratedDeriv (N - j) A p / ((N - j).factorial : ℂ)) N := by
  obtain ⟨F, hF, hFtay⟩ := taylor_split hA N
  refine div_pow_split hN hF ?_
  filter_upwards [hFtay] with s hs
  rw [hs]
  rw [taylor_reindex (fun i => iteratedDeriv i A p / (i.factorial : ℂ)) (s - p) N]

def logMellinProduct (H L : ℂ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  H s * (X : ℂ) ^ s * L s

def logProductPrincipalCoeff (P : Polynomial ℂ) (X : ℝ) (L : ℂ → ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ P.support.filter (fun k => j ≤ k + 1),
    ((-1 : ℂ) ^ k * (k.factorial : ℂ) * P.coeff k) *
      iteratedDeriv (k + 1 - j) (fun s : ℂ => (X : ℂ) ^ s * L s) 0 /
        ((k + 1 - j).factorial : ℂ)

def logProductResidue0 (P : Polynomial ℂ) (X : ℝ) (L : ℂ → ℂ) : ℂ :=
  ∑ k ∈ P.support, (-1 : ℂ) ^ k * P.coeff k *
    iteratedDeriv k (fun s : ℂ => (X : ℂ) ^ s * L s) 0

theorem logProductPrincipalCoeff_one (P : Polynomial ℂ) (X : ℝ) (L : ℂ → ℂ) :
    logProductPrincipalCoeff P X L 1 = logProductResidue0 P X L := by
  unfold logProductPrincipalCoeff logProductResidue0
  rw [Finset.filter_true_of_mem (fun k _ => by omega : ∀ k ∈ P.support, 1 ≤ k + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show k + 1 - 1 = k by omega]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

theorem logMellinProduct_principalPart_zero {f : ℝ → ℂ} {δ : ℝ}
    {P : Polynomial ℂ} {H : ℂ → ℂ} (h : LogMellinAdmissible f δ P H)
    (X : ℝ) (hX : 0 < X) (L : ℂ → ℂ) (hL : HolomorphicNear L 0) :
    HasFinitePrincipalPart (logMellinProduct H L X) 0
      (logProductPrincipalCoeff P X L) (P.natDegree + 1) := by
  obtain ⟨A, hA, hAeq⟩ := h.decomp
  have hc : HolomorphicNear (fun s : ℂ => (X : ℂ) ^ s) 0 := cpow_const_holomorphicNear X hX 0
  have hG : HolomorphicNear (fun s : ℂ => (X : ℂ) ^ s * L s) 0 := hc.mul' hL
  set c : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (k.factorial : ℂ) * P.coeff k with hcdef
  have hpart2 : HasFinitePrincipalPart (fun s => logPrincipalPart P s * ((X : ℂ) ^ s * L s)) 0
      (logProductPrincipalCoeff P X L) (P.natDegree + 1) := by
    have hterms : HasFinitePrincipalPart
        (fun s => ∑ k ∈ P.support, c k * (((X : ℂ) ^ s * L s) / s ^ (k + 1))) 0
        (fun j => ∑ k ∈ P.support,
          if j ≤ k + 1 then c k *
            (iteratedDeriv (k + 1 - j) (fun s : ℂ => (X : ℂ) ^ s * L s) 0 /
              ((k + 1 - j).factorial : ℂ)) else 0)
        (P.natDegree + 1) := by
      refine HasFinitePrincipalPart.finset_sum P.support fun k hk => ?_
      have hkN : k ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp k hk
      have hbase := (holomorphic_div_pow_principalPart
        (fun s : ℂ => (X : ℂ) ^ s * L s) 0 hG (k + 1) (by omega)).const_mul (c k)
      simpa using hbase.mono (show k + 1 ≤ P.natDegree + 1 by omega)
    refine hterms.congr_fun ?_ |>.congr_coeff ?_
    · filter_upwards with s
      unfold logPrincipalPart
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hcdef]
      ring
    · intro j hj
      unfold logProductPrincipalCoeff
      rw [← Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hcdef]
      rw [mul_div_assoc]
  have hpart1 : HasFinitePrincipalPart (fun s => A s * ((X : ℂ) ^ s * L s)) 0
      (fun _ => 0) (P.natDegree + 1) :=
    hasFinitePrincipalPart_of_holomorphicNear (hA.mul' hG) _
  have hmain := hpart1.add hpart2
  refine hmain.congr_fun ?_ |>.congr_coeff ?_
  · filter_upwards [hAeq] with s hs
    rw [logMellinProduct, hs]
    ring
  · intro j hj
    simp

theorem logMellinProduct_principalPart_one {f : ℝ → ℂ} {δ : ℝ}
    {P : Polynomial ℂ} {H : ℂ → ℂ} (h : LogMellinAdmissible f δ P H)
    (X : ℝ) (hX : 0 < X) (L : ℂ → ℂ) (κ : ℂ)
    (hL : HasFinitePrincipalPart L 1 (fun _ => κ) 1) :
    HasFinitePrincipalPart (logMellinProduct H L X) 1
      (fun _ => κ * (X : ℂ) * H 1) 1 := by
  obtain ⟨BL, hBL, hLeq⟩ := hL
  have hH : HolomorphicNear H 1 :=
    h.holomorphicNear (by simp only [Complex.one_re]; linarith [h.delta_pos]) one_ne_zero
  have hc : HolomorphicNear (fun s : ℂ => (X : ℂ) ^ s) 1 := cpow_const_holomorphicNear X hX 1
  have hG : HolomorphicNear (fun s : ℂ => H s * (X : ℂ) ^ s) 1 := hH.mul' hc
  obtain ⟨F, hF, hFtay⟩ := taylor_split hG 1
  refine ⟨fun s => (H s * (X : ℂ) ^ s) * BL s + κ * F s, ?_, ?_⟩
  · exact (hG.mul' hBL).add' (hF.const_mul' κ)
  · filter_upwards [hLeq, hFtay.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hs hs' hs1
    have hs1' : L s = BL s + κ / (s - 1) := by simpa using hs
    have hGs : H s * (X : ℂ) ^ s = H 1 * (X : ℂ) + (s - 1) * F s := by simpa using hs'
    have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [logMellinProduct, hs1', hGs]
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one]
    field_simp
    ring

end DedekindZetaZeroFree.LargeSieve.Vendor

end
