module

public import DedekindZetaZeroFree.Analysis.SpectralTheory.ResolventPencils.FiniteWindowIsolation
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

@[expose] public section

namespace DedekindZetaZeroFree

namespace KPBelowThreshold

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def realSpectrum (B : H →L[ℂ] H) : Set ℝ :=
  {μ | ¬ IsUnit (1 - (μ + 1) • B)}

def eigenspace (Δ : H →ₗ.[ℂ] H) (μ : ℝ) : Submodule ℂ H :=
  (Δ.toFun - (μ : ℂ) • Δ.domain.subtype).ker.map Δ.domain.subtype

noncomputable def spectralSubspace (B : H →L[ℂ] H) (J : Set ℝ) : Submodule ℂ H :=
  ⨅ (f : ℝ → ℝ) (_ : Continuous f)
    (_ : ∀ μ ∈ J, f (1 / (1 + μ)) = 0),
    (cfc f B).toLinearMap.ker

def IsIsolatedFiniteEigenvalue (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (μ : ℝ) : Prop :=
  eigenspace Δ μ ≠ ⊥ ∧ Module.Finite ℂ (eigenspace Δ μ) ∧
    ∃ η : ℝ, 0 < η ∧ ∀ ν ∈ realSpectrum B, |ν - μ| < η → ν = μ

def essentialSpectrum (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) : Set ℝ :=
  {μ | μ ∈ realSpectrum B ∧ ¬ IsIsolatedFiniteEigenvalue Δ B μ}

lemma sub_apply_eq {Δ : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u) (u : H) :
    u - B u = (Δ ⟨B u, hBdom u⟩ : H) :=
  sub_eq_iff_eq_add.mpr (hleft u).symm

lemma re_inner_apply_eq {Δ : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u) (u : H) :
    (inner ℂ (B u) u).re =
      ‖B u‖ ^ 2 + (inner ℂ (B u) (Δ ⟨B u, hBdom u⟩)).re := by
  have key : inner ℂ (B u) u =
      inner ℂ (B u) ((Δ ⟨B u, hBdom u⟩ : H) + B u) := by
    conv_rhs => rw [hleft u]
  rw [key, inner_add_right, Complex.add_re]
  rw [show (inner ℂ (B u) (B u)).re = ‖B u‖ ^ 2 from by
    change RCLike.re (inner ℂ (B u) (B u)) = ‖B u‖ ^ 2
    rw [inner_self_eq_norm_sq]]
  ring

lemma form_nonneg {Δ : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u) (u : H) :
    0 ≤ (inner ℂ (B u) u).re := by
  have h := re_inner_apply_eq hBdom hleft u
  have hq := hpos ⟨B u, hBdom u⟩
  nlinarith [h, hq, sq_nonneg ‖B u‖]

lemma norm_apply_le {Δ : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u) (u : H) :
    ‖B u‖ ≤ ‖u‖ := by
  have h := re_inner_apply_eq hBdom hleft u
  have hq := hpos ⟨B u, hBdom u⟩
  have hlow : ‖B u‖ ^ 2 ≤ (inner ℂ (B u) u).re := by nlinarith [h, hq]
  have hup : (inner ℂ (B u) u).re ≤ ‖B u‖ * ‖u‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (B u)) with h0 | h0
  · rw [← h0]; exact norm_nonneg u
  · have hmul : ‖B u‖ * ‖B u‖ ≤ ‖B u‖ * ‖u‖ := by
      calc ‖B u‖ * ‖B u‖ = ‖B u‖ ^ 2 := (sq ‖B u‖).symm
        _ ≤ (inner ℂ (B u) u).re := hlow
        _ ≤ ‖B u‖ * ‖u‖ := hup
    exact le_of_mul_le_mul_left hmul h0

lemma norm_le_one {Δ : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u) :
    ‖B‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by
    simpa using norm_apply_le hpos hBdom hleft u)

lemma coercive_bound {Δ : H →ₗ.[ℂ] H} {B : H →L[ℂ] H} (d : ℝ)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u)
    (hcoercivity : ∀ ε : ℝ, 0 < ε →
      ∃ K : H →L[ℂ] H, IsCompactOperator K ∧
        ∀ u : H, (d - ε) * ‖B u‖ ^ 2 ≤
          (inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : H →L[ℂ] H, IsCompactOperator K ∧
      ∀ u : H, (1 + d - ε) * ‖B u‖ ^ 2 ≤ ‖B u‖ * ‖u‖ + ‖K u‖ ^ 2 := by
  obtain ⟨K, hK, hKc⟩ := hcoercivity ε hε
  refine ⟨K, hK, fun u => ?_⟩
  have hsplit : (inner ℂ (B u) (u - B u)).re = (inner ℂ (B u) u).re - ‖B u‖ ^ 2 := by
    rw [sub_apply_eq hBdom hleft u, re_inner_apply_eq hBdom hleft u]
    ring
  have hup : (inner ℂ (B u) u).re ≤ ‖B u‖ * ‖u‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  calc (1 + d - ε) * ‖B u‖ ^ 2
      = (d - ε) * ‖B u‖ ^ 2 + ‖B u‖ ^ 2 := by ring
    _ ≤ ((inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2) + ‖B u‖ ^ 2 := by linarith [hKc u]
    _ = (inner ℂ (B u) u).re + ‖K u‖ ^ 2 := by rw [hsplit]; ring
    _ ≤ ‖B u‖ * ‖u‖ + ‖K u‖ ^ 2 := by linarith [hup]

lemma finite_of_compact_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K : E →L[ℂ] F) (hK : IsCompactOperator K)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ v, c * ‖v‖ ≤ ‖K v‖) :
    Module.Finite ℂ E := by
  have ha : AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ K := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    change ‖x - y‖ ≤ c⁻¹ * ‖K (x - y)‖
    exact (le_inv_mul_iff₀ hc).mpr (hlow (x-y))
  obtain ⟨S, hS, hsub⟩ := hK.image_closedBall_subset_compact 1
  have ht : TotallyBounded (Metric.closedBall (0 : E) 1) := by
    apply (totallyBounded_image_iff (ha.isUniformInducing K.uniformContinuous)).mp
    exact hS.totallyBounded.subset hsub
  exact FiniteDimensional.of_totallyBounded_nhds_zero ℂ (Metric.closedBall_mem_nhds 0 zero_lt_one) ht

lemma finite_of_compact_sq_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K : E →L[ℂ] F) (hK : IsCompactOperator K)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ v, c * ‖v‖ ^ 2 ≤ ‖K v‖ ^ 2) :
    Module.Finite ℂ E := by
  apply finite_of_compact_lower_bound K hK (Real.sqrt c) (Real.sqrt_pos.mpr hc)
  intro v
  have h := hlow v
  have hs := Real.sq_sqrt hc.le
  have hsn := Real.sqrt_nonneg c
  nlinarith [norm_nonneg v, norm_nonneg (K v)]

lemma mem_eigenspace_iff (Δ : H →ₗ.[ℂ] H) (μ : ℝ) (v : H) :
    v ∈ eigenspace Δ μ ↔ ∃ hv : v ∈ Δ.domain,
      Δ ⟨v, hv⟩ = (μ : ℂ) • v := by
  change v ∈ (Δ.toFun - (μ : ℂ) • Δ.domain.subtype).ker.map Δ.domain.subtype ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.property, ?_⟩
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, sub_eq_zero, LinearPMap.toFun_eq_coe] using hw
  · rintro ⟨hv, he⟩
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, sub_eq_zero, LinearPMap.toFun_eq_coe] using he

lemma finite_eigenspace_below_threshold
    (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (d : ℝ)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u)
    (hright : ∀ v : Δ.domain, B (Δ v + (v : H)) = (v : H))
    (hcoercivity : ∀ ε : ℝ, 0 < ε →
      ∃ K : H →L[ℂ] H, IsCompactOperator K ∧
        ∀ u : H, (d - ε) * ‖B u‖ ^ 2 ≤
          (inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2)
    (μ : ℝ) (hμ : μ < d) : Module.Finite ℂ (eigenspace Δ μ) := by
  let ε := (d - μ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨K, hK, hest⟩ := hcoercivity ε hε
  let T : eigenspace Δ μ →L[ℂ] H :=
    ((μ + 1 : ℝ) • (eigenspace Δ μ).subtypeL)
  apply finite_of_compact_sq_lower_bound (K.comp T) (hK.comp_clm T) ε hε
  intro v
  obtain ⟨hv, he⟩ := (mem_eigenspace_iff Δ μ v).mp v.property
  have hTv : T v = Δ ⟨(v : H), hv⟩ + (v : H) := by
    simp only [T, ContinuousLinearMap.smul_apply, Submodule.subtypeL_apply, he]
    rw [add_smul, one_smul, ← Complex.coe_smul]
  have hBT : B (T v) = (v : H) := by rw [hTv]; exact hright ⟨v, hv⟩
  have hinner : (inner ℂ (v : H) (T v - (v : H))).re = μ * ‖(v : H)‖ ^ 2 := by
    rw [hTv, add_sub_cancel_right, he, inner_smul_right, Complex.mul_re]
    simp [inner_self_eq_norm_sq, ← Complex.ofReal_pow]
  have h := hest (T v)
  rw [hBT, hinner] at h
  change ε * ‖(v : H)‖ ^ 2 ≤ ‖K (T v)‖ ^ 2
  dsimp [ε] at *
  nlinarith [sq_nonneg ‖(v : H)‖]

lemma isClosed_realSpectrum (B : H →L[ℂ] H) : IsClosed (realSpectrum B) := by
  change IsClosed {μ : ℝ | ¬ IsUnit (1 - (μ + 1) • B)}
  exact (Units.isOpen.preimage (by fun_prop : Continuous (fun μ : ℝ => (1 : H →L[ℂ] H) - (μ + 1) • B))).isClosed_compl

lemma essential_empty_of_isolated_below (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (d : ℝ)
    (hiso : ∀ μ ∈ realSpectrum B, μ < d → IsIsolatedFiniteEigenvalue Δ B μ) :
    essentialSpectrum Δ B ∩ Set.Iio d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro μ ⟨⟨hs, hn⟩, hμ⟩
  exact hn (hiso μ hs hμ)

lemma no_accPt_of_isolated_below (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (d : ℝ)
    (hiso : ∀ μ ∈ realSpectrum B, μ < d → IsIsolatedFiniteEigenvalue Δ B μ)
    (a : ℝ) (ha : a < d) :
    ¬ AccPt a (Filter.principal (realSpectrum B ∩ Set.Iio d)) := by
  intro hacc
  have hacc' : AccPt a (Filter.principal (realSpectrum B)) :=
    hacc.mono (Filter.principal_mono.mpr Set.inter_subset_left)
  have has : a ∈ realSpectrum B := (isClosed_iff_accPt.mp (isClosed_realSpectrum B)) a hacc'
  obtain ⟨_, _, η, hη, hloc⟩ := hiso a has ha
  obtain ⟨ν, ⟨hνball, hνspec⟩, hνne⟩ := (accPt_iff_nhds.mp hacc')
    (Metric.ball a η) (Metric.ball_mem_nhds a hη)
  exact hνne (hloc ν hνspec (by simpa [Real.dist_eq] using hνball))

lemma window_norm_bound (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (hBp : 0 ≤ B)
    (hinj : Function.Injective B) (J : Set ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hJ : ∀ μ ∈ J, μ ≤ m) (v : spectralSubspace B J) :
    ‖(v : H)‖ ≤ (1 + m) * ‖B v‖ := by
  let a : ℝ := 1 / (1 + m)
  have ha : 0 < a := by dsimp [a]; positivity
  let f : ℝ → ℝ := fun x => max 0 x * max 0 (a - x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfJ : ∀ μ ∈ J, f (1 / (1 + μ)) = 0 := by
    intro μ hμ
    by_cases hμ0 : 0 < 1 + μ
    · have ht : a ≤ 1 / (1 + μ) := by
        dsimp [a]; exact one_div_le_one_div_of_le hμ0 (by linarith [hJ μ hμ])
      simp only [f, max_eq_left (sub_nonpos.mpr ht), mul_zero]
    · have ht : 1 / (1 + μ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one (le_of_not_gt hμ0)
      simp only [f, max_eq_left ht, zero_mul]
  have hvf : cfc f B (v : H) = 0 := by
    have hv := v.property
    change (v : H) ∈ ⨅ (f : ℝ → ℝ) (_ : Continuous f)
      (_ : ∀ μ ∈ J, f (1 / (1 + μ)) = 0), (cfc f B).toLinearMap.ker at hv
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hv f) hf) hfJ
  let g : ℝ → ℝ := fun x => max 0 (a - x)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hfg : cfc f B = B * cfc g B := by
    have hh := cfc_mul (fun x : ℝ => x) g B continuousOn_id hg.continuousOn
    rw [cfc_id' ℝ B hB] at hh
    rw [← hh]
    apply cfc_congr
    intro x hx
    simp [f, g, max_eq_right (spectrum_nonneg_of_nonneg hBp hx)]
  have hgv : cfc g B (v : H) = 0 := by
    apply hinj
    simpa only [map_zero, ← ContinuousLinearMap.mul_apply, ← hfg] using hvf
  let k : ℝ → ℝ := fun x => max a x
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hkB : cfc k B = B + cfc g B := by
    have hh := cfc_add B (fun x : ℝ => x) g continuousOn_id hg.continuousOn
    rw [cfc_id' ℝ B hB] at hh
    rw [← hh]
    apply cfc_congr
    intro x hx
    dsimp [k, g]
    rcases le_total a x with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
  have hkval : cfc k B (v : H) = B v := by rw [hkB, ContinuousLinearMap.add_apply, hgv, add_zero]
  let r : ℝ → ℝ := fun x => 1 / k x
  have hkr : ∀ x, 0 < k x := fun x => ha.trans_le (le_max_left _ _)
  have hr : Continuous r := by exact continuous_const.div hk (fun x => ne_of_gt (hkr x))
  have hinv : cfc r B * cfc k B = 1 := by
    rw [← cfc_mul r k B hr.continuousOn hk.continuousOn, ← cfc_const_one ℝ B hB]
    apply cfc_congr
    intro x hx
    exact div_mul_cancel₀ 1 (ne_of_gt (hkr x))
  have hv : cfc r B (B v) = (v : H) := by
    rw [← hkval, ← ContinuousLinearMap.mul_apply, hinv, ContinuousLinearMap.one_apply]
  have hnorm : ‖cfc r B‖ ≤ 1 + m := by
    apply norm_cfc_le (by linarith)
    intro x hx
    change ‖1 / k x‖ ≤ 1 + m
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 1 / k x ≤ 1 / a := one_div_le_one_div_of_le ha (le_max_left _ _)
      _ = 1 + m := by dsimp [a]; field_simp
  calc ‖(v : H)‖ = ‖cfc r B (B v)‖ := congrArg norm hv.symm
    _ ≤ ‖cfc r B‖ * ‖B v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1 + m) * ‖B v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

lemma finite_spectralSubspace_below_threshold
    (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (d : ℝ) (hd : 0 < d)
    (hB : IsSelfAdjoint B)
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u)
    (hcoercivity : ∀ ε : ℝ, 0 < ε →
      ∃ K : H →L[ℂ] H, IsCompactOperator K ∧
        ∀ u : H, (d - ε) * ‖B u‖ ^ 2 ≤
          (inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2)
    (J : Set ℝ) (hJc : IsCompact J) (hJd : J ⊆ Set.Iio d) :
    Module.Finite ℂ (spectralSubspace B J) := by
  have hBp : 0 ≤ B := by
    rw [ContinuousLinearMap.le_def, sub_zero]
    apply ContinuousLinearMap.isPositive_def'.mpr
    exact ⟨hB, form_nonneg hpos hBdom hleft⟩
  have hinj : Function.Injective B := by
    intro x y hxy
    have hx := hleft x
    have hy := hleft y
    have hΔxy : Δ ⟨B x, hBdom x⟩ = Δ ⟨B y, hBdom y⟩ := by
      congr 1
      exact Subtype.ext hxy
    rw [hΔxy, hxy, hy] at hx
    exact hx.symm
  obtain ⟨m, hm, hmd, hJm⟩ : ∃ m : ℝ, 0 ≤ m ∧ m < d ∧ ∀ μ ∈ J, μ ≤ m := by
    rcases J.eq_empty_or_nonempty with hJe | hJe
    · exact ⟨0, le_rfl, hd, by simp [hJe]⟩
    · obtain ⟨j, hj⟩ := hJc.exists_isGreatest hJe
      refine ⟨max 0 j, le_max_left _ _, max_lt hd (hJd hj.1), ?_⟩
      intro μ hμ
      exact (hj.2 hμ).trans (le_max_right _ _)
  let ε := (d - m) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨K, hK, hest⟩ := coercive_bound d hBdom hleft hcoercivity ε hε
  let a : ℝ := 1 / (1 + m)
  have ha : 0 < a := by dsimp [a]; positivity
  apply finite_of_compact_sq_lower_bound (K.comp (spectralSubspace B J).subtypeL)
    (hK.comp_clm _) (ε * a ^ 2) (by positivity)
  intro v
  have hn := window_norm_bound B hB hBp hinj J m hm hJm v
  have hn' : a * ‖(v : H)‖ ≤ ‖B v‖ := by
    dsimp [a]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + m)]
    simpa [mul_comm] using hn
  have hh := hest (v : H)
  have hmultip : ‖B v‖ * ‖(v : H)‖ ≤ (1 + m) * ‖B v‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (B v))]
  have hsq : a ^ 2 * ‖(v : H)‖ ^ 2 ≤ ‖B v‖ ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ a * ‖(v : H)‖) hn'
    nlinarith only [h]
  change ε * a ^ 2 * ‖(v : H)‖ ^ 2 ≤ ‖K v‖ ^ 2
  have hk : ε * ‖B v‖ ^ 2 ≤ ‖K v‖ ^ 2 := by dsimp [ε] at *; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hε.le]

lemma eigenspace_ne_bot_of_pencil_eigenvector
    (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u)
    (μ : ℝ) (u : H) (hu : u ≠ 0) (he : u = (μ + 1) • B u) :
    eigenspace Δ μ ≠ ⊥ := by
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨B u, (mem_eigenspace_iff Δ μ (B u)).mpr ⟨hBdom u, ?_⟩, ?_⟩
  · have h := hleft u
    conv at h => rhs; rw [he, add_smul, one_smul]
    have he' : Δ ⟨B u, hBdom u⟩ = μ • B u := add_right_cancel h
    simpa only [Complex.coe_smul] using he'
  · intro hzero
    apply hu
    rw [he, hzero, smul_zero]

lemma isolated_below_of_finite_windows
    (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (d : ℝ)
    (hB : IsSelfAdjoint B)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u)
    (hright : ∀ v : Δ.domain, B (Δ v + (v : H)) = (v : H))
    (hcoercivity : ∀ ε : ℝ, 0 < ε →
      ∃ K : H →L[ℂ] H, IsCompactOperator K ∧
        ∀ u : H, (d - ε) * ‖B u‖ ^ 2 ≤
          (inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2)
    (hfinite : ∀ J : Set ℝ, IsCompact J → J ⊆ Set.Iio d →
      Module.Finite ℂ (spectralSubspace B J)) :
    ∀ μ ∈ realSpectrum B, μ < d → IsIsolatedFiniteEigenvalue Δ B μ := by
  intro μ hμ hμd
  let J : Set ℝ := Set.Icc (μ - 1) ((μ + d) / 2)
  have hJd : J ⊆ Set.Iio d := by
    intro ν hν
    have hν' : ν ≤ (μ + d) / 2 := hν.2
    change ν < d
    linarith
  have hμJ : μ ∈ interior J := by
    rw [show J = Set.Icc (μ - 1) ((μ + d) / 2) from rfl, interior_Icc]
    constructor <;> linarith
  have hfin := hfinite J isCompact_Icc hJd
  obtain ⟨u, hu, he⟩ := KPFiniteWindowPencil.pencil_eigenvector_of_finite_window
    B hB μ hμ J hμJ hfin
  refine ⟨eigenspace_ne_bot_of_pencil_eigenvector Δ B hBdom hleft μ u hu he,
    finite_eigenspace_below_threshold Δ B d hBdom hleft hright hcoercivity μ hμd, ?_⟩
  exact KPFiniteWindowPencil.pencil_isolated_of_finite_window B hB μ hμ J hμJ hfin

end KPBelowThreshold

open KPBelowThreshold

theorem kp_cont_below_threshold_discreteness
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (d : ℝ) (hd : 0 < d)
    (hΔ : IsSelfAdjoint Δ) (hB : IsSelfAdjoint B)
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (hBdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hBdom u⟩ + B u = u)
    (hright : ∀ v : Δ.domain, B (Δ v + (v : H)) = (v : H))
    (hcoercivity : ∀ ε : ℝ, 0 < ε →
      ∃ K : H →L[ℂ] H, IsCompactOperator K ∧
        ∀ u : H, (d - ε) * ‖B u‖ ^ 2 ≤
          (inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2) :
    (essentialSpectrum Δ B ∩ Set.Iio d = ∅) ∧
    (∀ J : Set ℝ, IsCompact J → J ⊆ Set.Iio d →
      Module.Finite ℂ (spectralSubspace B J)) ∧
    (∀ μ ∈ realSpectrum B, μ < d → IsIsolatedFiniteEigenvalue Δ B μ) ∧
    (∀ a : ℝ, a < d →
      ¬ AccPt a (Filter.principal (realSpectrum B ∩ Set.Iio d))) := by
  have hfinite : ∀ J : Set ℝ, IsCompact J → J ⊆ Set.Iio d →
      Module.Finite ℂ (spectralSubspace B J) :=
    finite_spectralSubspace_below_threshold Δ B d hd hB hpos hBdom hleft hcoercivity
  have hiso : ∀ μ ∈ realSpectrum B, μ < d → IsIsolatedFiniteEigenvalue Δ B μ :=
    isolated_below_of_finite_windows Δ B d hB hBdom hleft hright hcoercivity hfinite
  exact ⟨essential_empty_of_isolated_below Δ B d hiso, hfinite, hiso,
    no_accPt_of_isolated_below Δ B d hiso⟩

end DedekindZetaZeroFree
