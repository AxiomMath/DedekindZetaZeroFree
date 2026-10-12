module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Ultra

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace DedekindZetaZeroFree.KPFiniteLocal

def ordinaryDifferences {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (n : AddChar K G) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ (x : K) (φ : V), z = ρ (n x) φ - φ}

def whittakerValue {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (a : Kˣ → G)
    (ell : V →ₗ[ℂ] ℂ) (φ : V) (y : Kˣ) : ℂ := ell (ρ (a y) φ)

theorem character_trivial_near_zero {K : Type*} [NormedField K] [IsUltrametricDist K]
    (ψ : AddChar K Circle) (hc : Continuous ψ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : K, ‖x‖ < r → ψ x = 1 := by
  have he : ∀ᶠ x in 𝓝 (0 : K), ψ x ∈ Circle.centeredArc (Real.pi / 2) := by
    apply hc.continuousAt.eventually
    apply (Circle.isOpen_centeredArc _).mem_nhds
    rw [AddChar.map_zero_eq_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r, hr, fun x hx => ?_⟩
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro m hm
  rw [← AddChar.map_nsmul_eq_pow]
  apply hb
  simp only [dist_zero_right, nsmul_eq_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg x)
    (IsUltrametricDist.norm_natCast_le_one K m)) hx

theorem ordinaryDifferences_vanish_near_zero
    {K G V : Type*} [NormedField K] [IsUltrametricDist K] [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (n : AddChar K G) (a : Kˣ → G)
    (hconj : ∀ (y : Kˣ) (x : K), a y * n x = n ((y : K) * x) * a y)
    (ψ : AddChar K Circle) (hc : Continuous ψ) (ell : V →ₗ[ℂ] ℂ)
    (hWh : ∀ (x : K) (φ : V), ell (ρ (n x) φ) = (ψ x : ℂ) * ell φ)
    (z : V) (hz : z ∈ ordinaryDifferences ρ n) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : Kˣ, ‖(y : K)‖ < r → whittakerValue ρ a ell z y = 0 := by
  obtain ⟨s, hs, hchar⟩ := character_trivial_near_zero ψ hc
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, φ, rfl⟩ := hz
      refine ⟨s / (‖x‖ + 1), by positivity, ?_⟩
      intro y hy
      have hxy : ‖(y : K) * x‖ < s := by
        rw [norm_mul]
        have hh := (lt_div_iff₀ (by positivity : 0 < ‖x‖ + 1)).mp hy
        have := norm_nonneg (y : K)
        nlinarith
      have hcxy : (ψ ((y : K) * x) : ℂ) = 1 := by simp [hchar _ hxy]
      unfold whittakerValue
      rw [map_sub, map_sub]
      have heq : ell (ρ (a y) (ρ (n x) φ)) = (ψ ((y : K) * x) : ℂ) * ell (ρ (a y) φ) := by
        rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply, hWh]
      rw [heq, hcxy, one_mul, sub_self]
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intros
      simp [whittakerValue]
  | add z w hz hw ihz ihw =>
      obtain ⟨r, hr, hzr⟩ := ihz
      obtain ⟨s, hs, hws⟩ := ihw
      refine ⟨min r s, lt_min hr hs, ?_⟩
      intro y hy
      simp only [whittakerValue, map_add]
      rw [show ell (ρ (a y) z) = 0 from hzr y (lt_of_lt_of_le hy (min_le_left _ _)),
        show ell (ρ (a y) w) = 0 from hws y (lt_of_lt_of_le hy (min_le_right _ _)), add_zero]
  | smul c z hz ih =>
      obtain ⟨r, hr, hzr⟩ := ih
      refine ⟨r, hr, ?_⟩
      intro y hy
      simp only [whittakerValue, map_smul]
      rw [show ell (ρ (a y) z) = 0 from hzr y hy, smul_zero]

theorem jacquet_eventual_recurrence
    {K G V : Type*} [NormedField K] [IsUltrametricDist K] [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (n : AddChar K G) (a : Kˣ → G)
    (hconj : ∀ (y : Kˣ) (x : K), a y * n x = n ((y : K) * x) * a y)
    (p : Kˣ) (ha : ∀ y : Kˣ, a (y * p) = a y * a p)
    (α β : ℂ)
    (hJ : ∀ φ : V, ((ρ (a p) - α • LinearMap.id) *
      (ρ (a p) - β • LinearMap.id) : Module.End ℂ V) φ ∈ ordinaryDifferences ρ n)
    (ψ : AddChar K Circle) (hc : Continuous ψ) (ell : V →ₗ[ℂ] ℂ)
    (hWh : ∀ (x : K) (φ : V), ell (ρ (n x) φ) = (ψ x : ℂ) * ell φ)
    (φ : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : Kˣ, ‖(y : K)‖ < r →
      whittakerValue ρ a ell φ (y * p * p) -
        (α + β) * whittakerValue ρ a ell φ (y * p) +
        (α * β) * whittakerValue ρ a ell φ y = 0 := by
  obtain ⟨r, hr, hvan⟩ := ordinaryDifferences_vanish_near_zero ρ n a hconj ψ hc ell hWh
    _ (hJ φ)
  refine ⟨r, hr, ?_⟩
  intro y hy
  have hzero := hvan y hy
  simp only [whittakerValue, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul] at hzero
  have h1 : ell (ρ (a y) (ρ (a p) φ)) = whittakerValue ρ a ell φ (y * p) := by
    simp [whittakerValue, ha, map_mul, Module.End.mul_apply]
  have h2 : ell (ρ (a y) (ρ (a p) (ρ (a p) φ))) =
      whittakerValue ρ a ell φ (y * p * p) := by
    simp [whittakerValue, ha, map_mul, Module.End.mul_apply]
  change ell (ρ (a y) (ρ (a p) (ρ (a p) φ))) -
      α * ell (ρ (a y) (ρ (a p) φ)) -
      β * (ell (ρ (a y) (ρ (a p) φ)) - α * ell (ρ (a y) φ)) = 0 at hzero
  rw [h1, h2] at hzero
  unfold whittakerValue at *
  linear_combination hzero

theorem distinct_root_recurrence_formula (u : ℕ → ℂ) (α β : ℂ)
    (hne : α ≠ β)
    (hrec : ∀ n : ℕ, u (n + 2) - (α + β) * u (n + 1) + α * β * u n = 0)
    (n : ℕ) :
    u n = ((u 1 - β * u 0) / (α - β)) * α ^ n +
      ((α * u 0 - u 1) / (α - β)) * β ^ n := by
  have hnz : α - β ≠ 0 := sub_ne_zero.mpr hne
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [pow_zero, mul_one]
    field_simp
    ring
  | one =>
    simp only [pow_one]
    field_simp
    ring
  | more n ih0 ih1 =>
    have hh := hrec n
    rw [ih0, ih1] at hh
    rw [pow_succ, pow_succ, pow_succ, pow_succ]
    linear_combination hh

theorem distinct_root_recurrence_uniform_bound (u : ℕ → ℂ) (α β : ℂ)
    (hne : α ≠ β) (hnorm : ‖β‖ ≤ ‖α‖)
    (hrec : ∀ n : ℕ, u (n + 2) - (α + β) * u (n + 1) + α * β * u n = 0)
    (H : ℝ) (hH : 0 ≤ H) (h0 : ‖u 0‖ ≤ H) (h1 : ‖u 1‖ ≤ H)
    (n : ℕ) :
    ‖u n‖ ≤ ((2 + ‖α‖ + ‖β‖) * H / ‖α - β‖) * ‖α‖ ^ n := by
  have hd : 0 < ‖α - β‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hA : ‖(u 1 - β * u 0) / (α - β)‖ ≤ (H + ‖β‖ * H) / ‖α - β‖ := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ ‖u 1‖ + ‖β * u 0‖ := norm_sub_le _ _
      _ = ‖u 1‖ + ‖β‖ * ‖u 0‖ := by rw [norm_mul]
      _ ≤ _ := by gcongr
  have hB : ‖(α * u 0 - u 1) / (α - β)‖ ≤ (‖α‖ * H + H) / ‖α - β‖ := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ ‖α * u 0‖ + ‖u 1‖ := norm_sub_le _ _
      _ = ‖α‖ * ‖u 0‖ + ‖u 1‖ := by rw [norm_mul]
      _ ≤ _ := by gcongr
  rw [distinct_root_recurrence_formula u α β hne hrec n]
  calc
    _ ≤ ‖((u 1 - β * u 0) / (α - β)) * α ^ n‖ +
        ‖((α * u 0 - u 1) / (α - β)) * β ^ n‖ := norm_add_le _ _
    _ = ‖(u 1 - β * u 0) / (α - β)‖ * ‖α‖ ^ n +
        ‖(α * u 0 - u 1) / (α - β)‖ * ‖β‖ ^ n := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ ((H + ‖β‖ * H) / ‖α - β‖) * ‖α‖ ^ n +
        ((‖α‖ * H + H) / ‖α - β‖) * ‖α‖ ^ n := by
      gcongr
    _ = _ := by ring

theorem whittakerValue_locallyConstant
    {K G V : Type*} [Field K] [TopologicalSpace K] [Group G]
    [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmooth : ∀ φ : V, IsLocallyConstant (fun g : G => ρ g φ))
    (a : Kˣ → G) (ha : Continuous a) (ell : V →ₗ[ℂ] ℂ) (φ : V) :
    IsLocallyConstant (whittakerValue ρ a ell φ) := by
  exact ((hsmooth φ).comp ell).comp_continuous ha

theorem whittakerValue_compact_bound
    {K G V : Type*} [Field K] [TopologicalSpace K] [Group G]
    [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmooth : ∀ φ : V, IsLocallyConstant (fun g : G => ρ g φ))
    (a : Kˣ → G) (ha : Continuous a) (ell : V →ₗ[ℂ] ℂ) (φ : V)
    (S : Set Kˣ) (hS : IsCompact S) :
    ∃ H : ℝ, 0 < H ∧ ∀ y ∈ S, ‖whittakerValue ρ a ell φ y‖ ≤ H := by
  obtain ⟨H, hH⟩ := hS.bddAbove_image
    ((whittakerValue_locallyConstant ρ hsmooth a ha ell φ).continuous.norm.continuousOn)
  refine ⟨max H 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  exact (hH (Set.mem_image_of_mem _ hy)).trans (le_max_left _ _)

theorem generic_fixed_vector_support
    {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmooth : ∀ φ : V, IsLocallyConstant (fun g : G => ρ g φ))
    (n : AddChar (v.adicCompletion F) G) (hn : Continuous n)
    (a : (v.adicCompletion F)ˣ → G)
    (hconj : ∀ (y : (v.adicCompletion F)ˣ) (x : v.adicCompletion F),
      a y * n x = n ((y : v.adicCompletion F) * x) * a y)
    (ψ : AddChar (v.adicCompletion F) Circle) (hψ : ψ ≠ 1)
    (ell : V →ₗ[ℂ] ℂ)
    (hWh : ∀ (x : v.adicCompletion F) (φ : V),
      ell (ρ (n x) φ) = (ψ x : ℂ) * ell φ)
    (φ : V) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : (v.adicCompletion F)ˣ,
      M < ‖(y : v.adicCompletion F)‖ → whittakerValue ρ a ell φ y = 0 := by
  have ht : ∃ t : v.adicCompletion F, ψ t ≠ 1 := by
    by_contra! h
    apply hψ
    ext t
    simpa using congrArg (fun z : Circle => (z : ℂ)) (h t)
  obtain ⟨t, ht⟩ := ht
  have he : ∀ᶠ x in 𝓝 (0 : v.adicCompletion F), ρ (n x) φ = φ := by
    simpa using hn.continuousAt.eventually ((hsmooth φ).eventually_eq (n 0))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨‖t‖ / r + 1, by positivity, ?_⟩
  intro y hy
  have hyr : ‖t‖ / r < ‖(y : v.adicCompletion F)‖ := by linarith
  have hx : ‖t / (y : v.adicCompletion F)‖ < r := by
    rw [norm_div]
    exact (div_lt_iff₀ (norm_pos_iff.mpr y.ne_zero)).mpr
      (by simpa only [mul_comm] using (div_lt_iff₀ hr).mp hyr)
  have hfix := hball (show dist (t / (y : v.adicCompletion F)) 0 < r by simpa using hx)
  have heq : whittakerValue ρ a ell φ y = (ψ t : ℂ) * whittakerValue ρ a ell φ y := by
    calc
      whittakerValue ρ a ell φ y = ell (ρ (a y) (ρ (n (t / (y : v.adicCompletion F))) φ)) := by rw [hfix]; rfl
      _ = ell (ρ (a y * n (t / (y : v.adicCompletion F))) φ) := by simp [map_mul, Module.End.mul_apply]
      _ = ell (ρ (n t * a y) φ) := by rw [hconj, mul_div_cancel₀ t y.ne_zero]
      _ = (ψ t : ℂ) * whittakerValue ρ a ell φ y := by simp [map_mul, Module.End.mul_apply, hWh, whittakerValue]
  have ht' : (ψ t : ℂ) ≠ 1 := by
    intro h
    apply ht
    exact Subtype.ext h
  have hz : (1 - (ψ t : ℂ)) * whittakerValue ρ a ell φ y = 0 := by
    linear_combination heq
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm ht'))

private theorem norm_annulus_isCompact {K : Type*} [NormedField K] [ProperSpace K] (l u : ℝ) (hl : 0 < l) :
    IsCompact {y : Kˣ | l ≤ ‖(y : K)‖ ∧ ‖(y : K)‖ ≤ u} := by
  have hc2 : IsCompact (MulOpposite.opHomeomorph.symm ⁻¹' Metric.closedBall (0 : K) l⁻¹) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr (isCompact_closedBall (0 : K) l⁻¹)
  have hc := (isCompact_closedBall (0 : K) u).prod hc2
  have hpre := Units.isClosedEmbedding_embedProduct.isCompact_preimage hc
  have heq : (Units.embedProduct K) ⁻¹'
      (Metric.closedBall (0 : K) u ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' Metric.closedBall (0 : K) l⁻¹)) =
      {y : Kˣ | l ≤ ‖(y : K)‖ ∧ ‖(y : K)‖ ≤ u} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_closedBall, dist_zero_right,
      Units.embedProduct, MulOpposite.unop_op]
    change (‖(y : K)‖ ≤ u ∧ ‖(↑y⁻¹ : K)‖ ≤ l⁻¹) ↔ (l ≤ ‖(y : K)‖ ∧ ‖(y : K)‖ ≤ u)
    rw [show ‖(↑y⁻¹ : K)‖ = ‖(y : K)‖⁻¹ by simp]
    have hy : 0 < ‖(y : K)‖ := norm_pos_iff.mpr y.ne_zero
    rw [inv_le_inv₀ hy hl]
    exact and_comm
  rwa [heq] at hpre

private theorem recurrence_decay {K : Type*} [NormedField K] (f : Kˣ → ℂ)
    (p : Kˣ) (α β : ℂ) (hp : ‖(p : K)‖ < 1)
    (hne : α ≠ β) (hnorm : ‖β‖ ≤ ‖α‖)
    (δ : ℝ) (hd : 0 < δ) (hα : ‖α‖ ≤ Real.rpow ‖(p : K)‖ δ)
    (r : ℝ) (hr : 0 < r)
    (hrec : ∀ y : Kˣ, ‖(y : K)‖ < r →
      f (y * p * p) - (α + β) * f (y * p) + α * β * f y = 0)
    (H : ℝ) (hH : 0 < H)
    (hbound : ∀ y : Kˣ, min (r / 2) 1 * ‖(p : K)‖ ^ 2 ≤ ‖(y : K)‖ →
      ‖(y : K)‖ ≤ 1 → ‖f y‖ ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Kˣ, ‖(y : K)‖ ≤ 1 →
      ‖f y‖ ≤ C * Real.rpow ‖(y : K)‖ δ := by
  let q := ‖(p : K)‖
  have hq : 0 < q := norm_pos_iff.mpr p.ne_zero
  let s := min (r / 2) 1
  have hs : 0 < s := lt_min (by positivity) zero_lt_one
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let D := (2 + ‖α‖ + ‖β‖) * H / ‖α - β‖
  have hden : 0 < ‖α - β‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hD : 0 < D := by dsimp [D]; positivity
  let L := Real.rpow (s * q) δ
  have hL : 0 < L := Real.rpow_pos_of_pos (mul_pos hs hq) _
  refine ⟨max H D / L, div_pos (lt_of_lt_of_le hH (le_max_left _ _)) hL, ?_⟩
  intro y hy
  have hyn : 0 < ‖(y : K)‖ := norm_pos_iff.mpr y.ne_zero
  have hql : q ≤ 1 := hp.le
  by_cases hys : ‖(y : K)‖ ≤ s
  · obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
      (div_pos hyn hs) ((div_le_one hs).mpr hys) hq hp
    let z := y / p ^ n
    have hz : ‖(z : K)‖ = ‖(y : K)‖ / q ^ n := by simp [z, q, norm_div, norm_pow]
    have hzlo : s * q < ‖(z : K)‖ := by
      rw [hz, lt_div_iff₀ (pow_pos hq n)]
      have hh := (lt_div_iff₀ hs).mp hnlo
      rw [pow_succ] at hh
      nlinarith
    have hzhi : ‖(z : K)‖ ≤ s := by
      rw [hz, div_le_iff₀ (pow_pos hq n)]
      have hh := (div_le_iff₀ hs).mp hnhi
      nlinarith
    have hzp : ‖((z * p : Kˣ) : K)‖ = ‖(z : K)‖ * q := by simp [q, norm_mul]
    have h0 : ‖f z‖ ≤ H := hbound z (by
      change s * q ^ 2 ≤ _
      have : q ^ 2 ≤ q := by nlinarith
      nlinarith) (hzhi.trans hs1)
    have h1 : ‖f (z * p)‖ ≤ H := hbound (z * p) (by
      rw [hzp]
      change s * q ^ 2 ≤ _
      nlinarith) (by rw [hzp]; nlinarith)
    have hrec' : ∀ k : ℕ,
        f (z * p ^ (k + 2)) - (α + β) * f (z * p ^ (k + 1)) +
          α * β * f (z * p ^ k) = 0 := by
      intro k
      have hzk : ‖((z * p ^ k : Kˣ) : K)‖ < r := by
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
        have hk : q ^ k ≤ 1 := pow_le_one₀ hq.le hp.le
        have : ‖(z : K)‖ * q ^ k ≤ s := by nlinarith [norm_nonneg (z : K)]
        exact this.trans_lt hsr
      simpa only [pow_succ, mul_assoc] using hrec (z * p ^ k) hzk
    have hb := distinct_root_recurrence_uniform_bound (fun k => f (z * p ^ k))
      α β hne hnorm hrec' H hH.le (by simpa using h0) (by simpa using h1) n
    have hzy : z * p ^ n = y := div_mul_cancel _ _
    rw [hzy] at hb
    have hpow : ‖α‖ ^ n ≤ (Real.rpow q δ) ^ n := pow_le_pow_left₀ (norm_nonneg α) hα n
    have hscale : L * (Real.rpow q δ) ^ n ≤ Real.rpow ‖(y : K)‖ δ := by
      have hh : s * q * q ^ n ≤ ‖(y : K)‖ := by
        have := (lt_div_iff₀ hs).mp hnlo
        rw [pow_succ] at this
        nlinarith
      have hh' := Real.rpow_le_rpow (by positivity : 0 ≤ s * q * q ^ n) hh hd.le
      have hpr : (q ^ n) ^ δ = (q ^ δ) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, mul_comm, Real.rpow_mul hq.le,
          Real.rpow_natCast]
      rw [Real.mul_rpow (by positivity) (by positivity), hpr] at hh'
      exact hh'
    have hC : D * (Real.rpow q δ) ^ n ≤ max H D / L * Real.rpow ‖(y : K)‖ δ := by
      have he : max H D / L * Real.rpow ‖(y : K)‖ δ =
          (max H D * Real.rpow ‖(y : K)‖ δ) / L := by ring
      rw [he]
      apply (le_div_iff₀ hL).mpr
      calc
        D * (Real.rpow q δ) ^ n * L = D * (L * (Real.rpow q δ) ^ n) := by ring
        _ ≤ max H D * Real.rpow ‖(y : K)‖ δ :=
          mul_le_mul (le_max_right H D) hscale (mul_nonneg hL.le (pow_nonneg (Real.rpow_pos_of_pos hq δ).le n)) (le_trans hD.le (le_max_right H D))
        _ = (max H D * Real.rpow ‖(y : K)‖ δ) := rfl
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hD.le).trans hC)
  · have hsy : s ≤ ‖(y : K)‖ := (not_le.mp hys).le
    have hb := hbound y (by
      change s * q ^ 2 ≤ _
      have : q ^ 2 ≤ 1 := pow_le_one₀ hq.le hp.le
      nlinarith) hy
    have hLy : L ≤ Real.rpow ‖(y : K)‖ δ := by
      apply Real.rpow_le_rpow (by positivity) _ hd.le
      nlinarith
    calc
      ‖f y‖ ≤ H := hb
      _ ≤ max H D := le_max_left _ _
      _ = max H D / L * L := (div_mul_cancel₀ _ hL.ne').symm
      _ ≤ max H D / L * Real.rpow ‖(y : K)‖ δ := by gcongr

private theorem jacquet_roots_bounds (Q : ℕ) (hQ : (1 : ℝ) < Q) (δ : ℝ) (hδ : δ < 1 / 3) :
    let α : ℂ := (Q : ℂ)⁻¹
    let β : ℂ := ((Q : ℂ) ^ 2)⁻¹
    α ≠ β ∧ ‖β‖ ≤ ‖α‖ ∧
      ‖α‖ ≤ Real.rpow ((Q : ℝ)⁻¹ ^ 3) δ := by
  dsimp only
  have hQ0 : 0 < (Q : ℝ) := by linarith
  let t : ℝ := (Q : ℝ)⁻¹
  have ht : 0 < t := inv_pos.mpr hQ0
  have ht1 : t < 1 := (inv_lt_one₀ hQ0).mpr hQ
  have ha : ‖(Q : ℂ)⁻¹‖ = t := by simp [norm_inv, t]
  have hb : ‖((Q : ℂ) ^ 2)⁻¹‖ = t ^ 2 := by simp [norm_inv, norm_pow, t, inv_pow]
  constructor
  · intro he
    have hn := congrArg norm he
    rw [ha, hb] at hn
    nlinarith
  constructor
  · rw [ha, hb]; nlinarith
  · rw [ha]
    change t ≤ (t ^ 3).rpow δ
    have hp : (t ^ 3 : ℝ) ^ δ = t ^ (3 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num
    change t ≤ (t ^ 3 : ℝ) ^ δ
    rw [hp]
    calc
      t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
      _ ≤ t ^ (3 * δ) := Real.rpow_le_rpow_of_exponent_ge ht ht1.le (by linarith)

theorem generic_fixed_vector_small_norm
    {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmooth : ∀ φ : V, IsLocallyConstant (fun g : G => ρ g φ))
    (n : AddChar (v.adicCompletion F) G) (hn : Continuous n)
    (a : (v.adicCompletion F)ˣ → G) (ha : Continuous a)
    (hconj : ∀ (y : (v.adicCompletion F)ˣ) (x : v.adicCompletion F),
      a y * n x = n ((y : v.adicCompletion F) * x) * a y)
    (π : (v.adicCompletion F)ˣ)
    (hπ : ‖(π : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹)
    (haCube : ∀ y : (v.adicCompletion F)ˣ, a (y * π ^ 3) = a y * a (π ^ 3))
    (hJacquet : ∀ φ : V,
      ((ρ (a (π ^ 3)) - ((v.asIdeal.absNorm : ℂ)⁻¹) • LinearMap.id) *
        (ρ (a (π ^ 3)) - (((v.asIdeal.absNorm : ℂ) ^ 2)⁻¹) • LinearMap.id) :
          Module.End ℂ V) φ ∈ ordinaryDifferences ρ n)
    (ψ : AddChar (v.adicCompletion F) Circle) (hψcont : Continuous ψ)
    (ell : V →ₗ[ℂ] ℂ)
    (hWh : ∀ (x : v.adicCompletion F) (φ : V),
      ell (ρ (n x) φ) = (ψ x : ℂ) * ell φ)
    (φ : V) (δ : ℝ) (hδ : 0 < δ) (hδthird : δ < 1 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : (v.adicCompletion F)ˣ,
      0 < ‖(y : v.adicCompletion F)‖ → ‖(y : v.adicCompletion F)‖ ≤ 1 →
      ‖whittakerValue ρ a ell φ y‖ ≤ C * Real.rpow ‖(y : v.adicCompletion F)‖ δ := by
  have hQ : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨hne, hnorm, hroot⟩ := jacquet_roots_bounds v.asIdeal.absNorm hQ δ hδthird
  have hp : ‖((π ^ 3 : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ < 1 := by
    rw [Units.val_pow_eq_pow_val, norm_pow, hπ]
    have hQ0 : 0 < (v.asIdeal.absNorm : ℝ) := by linarith
    have hi : 0 < (v.asIdeal.absNorm : ℝ)⁻¹ := inv_pos.mpr hQ0
    have hi1 : (v.asIdeal.absNorm : ℝ)⁻¹ < 1 := (inv_lt_one₀ hQ0).mpr hQ
    exact pow_lt_one₀ hi.le hi1 (by decide : 3 ≠ 0)
  obtain ⟨r, hr, hrec⟩ := jacquet_eventual_recurrence ρ n a hconj (π ^ 3) haCube
    ((v.asIdeal.absNorm : ℂ)⁻¹) (((v.asIdeal.absNorm : ℂ) ^ 2)⁻¹)
    hJacquet ψ hψcont ell hWh φ
  let l : ℝ := min (r / 2) 1 * ‖((π ^ 3 : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^ 2
  have hl : 0 < l := by
    have hh : 0 < ‖((π ^ 3 : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ :=
      norm_pos_iff.mpr (π ^ 3).ne_zero
    dsimp [l]
    positivity
  obtain ⟨H, hH, hbound⟩ := whittakerValue_compact_bound ρ hsmooth a ha ell φ
    {y | l ≤ ‖(y : v.adicCompletion F)‖ ∧ ‖(y : v.adicCompletion F)‖ ≤ 1}
    (norm_annulus_isCompact l 1 hl)
  obtain ⟨C, hC, hdec⟩ := recurrence_decay (whittakerValue ρ a ell φ) (π ^ 3)
    ((v.asIdeal.absNorm : ℂ)⁻¹) (((v.asIdeal.absNorm : ℂ) ^ 2)⁻¹)
    hp hne hnorm δ hδ (by simpa only [Units.val_pow_eq_pow_val, norm_pow, hπ] using hroot)
    r hr hrec H hH (fun y hy hy1 => hbound y ⟨hy, hy1⟩)
  exact ⟨C, hC, fun y _ hy => hdec y hy⟩

end DedekindZetaZeroFree.KPFiniteLocal

end
