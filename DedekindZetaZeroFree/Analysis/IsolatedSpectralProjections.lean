module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.KPIsolatedProjection

open scoped InnerProductSpace

noncomputable section

def IsIsolatedSpectralPoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (B : H →L[ℂ] H) (β : ℝ) : Prop :=
  (β : ℂ) ∈ spectrum ℂ B ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ B, dist w (β : ℂ) < ε → w = (β : ℂ)

def eigenspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (β : ℝ) : Submodule ℂ H :=
  (B - (β : ℂ) • (1 : H →L[ℂ] H)).ker

instance eigenspace_completeSpace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H) (β : ℝ) :
    CompleteSpace (eigenspace B β) := by
  unfold eigenspace
  infer_instance

end

end DedekindZetaZeroFree.KPIsolatedProjection

section

namespace DedekindZetaZeroFree.KPIsolatedProjection

open scoped InnerProductSpace

noncomputable section

def projection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (B : H →L[ℂ] H) (β : ℝ) : H →L[ℂ] H :=
  (eigenspace B β).starProjection

private theorem continuousOn_isolated_ite
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (β : ℝ) (hiso : IsIsolatedSpectralPoint B β)
    (a : ℂ) (F : ℂ → ℂ)
    (hF : ∀ w ∈ spectrum ℂ B, w ≠ (β : ℂ) → ContinuousAt F w) :
    ContinuousOn (fun w => if w = (β : ℂ) then a else F w) (spectrum ℂ B) := by
  classical
  intro w hw
  by_cases he : w = (β : ℂ)
  · subst w
    obtain ⟨ε, hε, hi⟩ := hiso.2
    apply (continuousWithinAt_const (b := a)).congr_of_eventuallyEq _ (by simp)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (β : ℂ) hε),
      self_mem_nhdsWithin] with z hz hzs
    simp [hi z hzs hz]
  · apply (hF w hw he).continuousWithinAt.congr_of_eventuallyEq _ (by simp [he])
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds he)] with z hz
    simp_all

theorem projection_eq_cfc
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (β : ℝ)
    (hβ : β ≠ 0) (hiso : IsIsolatedSpectralPoint B β) :
    projection B β = cfc (fun w : ℂ => if w = (β : ℂ) then (1 : ℂ) else 0) B := by
  classical
  let f : ℂ → ℂ := fun w => if w = (β : ℂ) then 1 else 0
  let g : ℂ → ℂ := fun w => if w = (β : ℂ) then 0 else (w - (β : ℂ))⁻¹
  have hn : IsStarNormal B := hB.isStarNormal
  have hf : ContinuousOn f (spectrum ℂ B) :=
    continuousOn_isolated_ite B β hiso 1 (fun _ => 0) (by intros; fun_prop)
  have hg : ContinuousOn g (spectrum ℂ B) :=
    continuousOn_isolated_ite B β hiso 0 _ (by
      intro w hw he
      exact (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr he))
  have hP : IsStarProjection (cfc f B) := by
    constructor
    · change cfc f B * cfc f B = cfc f B
      rw [← cfc_mul f f B hf hf]
      apply cfc_congr
      intro w hw
      simp [f]
    · change star (cfc f B) = cfc f B
      rw [← cfc_star]
      apply cfc_congr
      intro w hw
      simp [f]
  have hmul : (B - (β : ℂ) • 1) * cfc f B = 0 := by
    have hd : cfc (fun w : ℂ => w - (β : ℂ)) B = B - (β : ℂ) • 1 := by
      rw [cfc_sub (fun w : ℂ => w) (fun _ : ℂ => (β : ℂ)) B
        continuousOn_id continuousOn_const, cfc_id' ℂ B hn, cfc_const (β : ℂ) B hn]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [← hd, ← cfc_mul _ f B (by fun_prop) hf, ← cfc_const_zero ℂ B]
    apply cfc_congr
    intro w hw
    by_cases he : w = (β : ℂ) <;> simp [f, he]
  have hinv : cfc g B * (B - (β : ℂ) • 1) = 1 - cfc f B := by
    have hd : cfc (fun w : ℂ => w - (β : ℂ)) B = B - (β : ℂ) • 1 := by
      rw [cfc_sub (fun w : ℂ => w) (fun _ : ℂ => (β : ℂ)) B
        continuousOn_id continuousOn_const, cfc_id' ℂ B hn, cfc_const (β : ℂ) B hn]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [← hd, ← cfc_mul g _ B hg (by fun_prop), ← cfc_const_one ℂ B,
      ← cfc_sub _ f B continuousOn_const hf]
    apply cfc_congr
    intro w hw
    by_cases he : w = (β : ℂ)
    · simp [f, g, he]
    · simp [f, g, he, sub_ne_zero.mpr he]
  apply ContinuousLinearMap.IsStarProjection.ext
    (isStarProjection_starProjection (U := eigenspace B β)) hP
  change (eigenspace B β).starProjection.range = (cfc f B).range
  rw [Submodule.range_starProjection]
  apply le_antisymm
  · intro x hx
    refine ⟨x, ?_⟩
    have hz : (B - (β : ℂ) • 1) x = 0 := hx
    have ht := congrArg (fun T : H →L[ℂ] H => T x) hinv
    simp only [ContinuousLinearMap.mul_apply, hz, map_zero,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at ht
    exact (sub_eq_zero.mp ht.symm).symm
  · rintro x ⟨y, rfl⟩
    change (B - (β : ℂ) • 1) (cfc f B y) = 0
    exact congrArg (fun T : H →L[ℂ] H => T y) hmul

theorem projection_spec
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (β : ℝ)
    (hβ : β ≠ 0) (hiso : IsIsolatedSpectralPoint B β) :
    projection B β ≠ 0 ∧ IsSelfAdjoint (projection B β) ∧
    projection B β * projection B β = projection B β ∧
    (projection B β).range = eigenspace B β ∧
    B * projection B β = (β : ℂ) • projection B β ∧
    projection B β * B = (β : ℂ) • projection B β := by
  classical
  have hP : IsSelfAdjoint (projection B β) := isSelfAdjoint_starProjection _
  have hmul : B * projection B β = (β : ℂ) • projection B β := by
    ext x
    have hx := (eigenspace B β).starProjection_apply_mem x
    change B (projection B β x) - (β : ℂ) • projection B β x = 0 at hx
    exact sub_eq_zero.mp hx
  refine ⟨?_, hP, (eigenspace B β).isIdempotentElem_starProjection,
    Submodule.range_starProjection _, hmul, ?_⟩
  · rw [projection_eq_cfc B hB β hβ hiso]
    intro hz
    have hf : ContinuousOn (fun w : ℂ => if w = (β : ℂ) then (1 : ℂ) else 0)
        (spectrum ℂ B) :=
      continuousOn_isolated_ite B β hiso 1 (fun _ => 0) (by intros; fun_prop)
    have he := eqOn_of_cfc_eq_cfc (hz.trans (cfc_const_zero ℂ B).symm)
      hf continuousOn_const hB.isStarNormal hiso.1
    simpa using he
  · have he := congrArg star hmul
    simpa only [star_mul, hP.star_eq, hB.star_eq, star_smul, Complex.star_def,
      Complex.conj_ofReal] using he

theorem projection_finiteRank
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (β : ℝ) [FiniteDimensional ℂ (eigenspace B β)] :
    FiniteDimensional ℂ (projection B β).range := by
  rw [projection, Submodule.range_starProjection]
  infer_instance

theorem isUnit_gap_add_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (β : ℝ)
    (hβ : β ≠ 0) (hiso : IsIsolatedSpectralPoint B β) :
    IsUnit (1 - (β : ℂ)⁻¹ • B + projection B β) := by
  classical
  let f : ℂ → ℂ := fun w => if w = (β : ℂ) then 1 else 0
  have hn : IsStarNormal B := hB.isStarNormal
  have hf : ContinuousOn f (spectrum ℂ B) :=
    continuousOn_isolated_ite B β hiso 1 (fun _ => 0) (by intros; fun_prop)
  have he : cfc (fun w => 1 - (β : ℂ)⁻¹ * w + f w) B =
      1 - (β : ℂ)⁻¹ • B + projection B β := by
    rw [cfc_add B (fun w : ℂ => 1 - (β : ℂ)⁻¹ * w) f (by fun_prop) hf,
      cfc_sub (fun _ : ℂ => 1) (fun w : ℂ => (β : ℂ)⁻¹ * w) B
        continuousOn_const (by fun_prop), cfc_const_one ℂ B hn]
    rw [← projection_eq_cfc B hB β hβ hiso]
    congr 2
    exact cfc_smul_id (β : ℂ)⁻¹ B hn
  rw [← he]
  apply (isUnit_cfc_iff _ B ((by fun_prop : ContinuousOn
    (fun w : ℂ => 1 - (β : ℂ)⁻¹ * w) (spectrum ℂ B)).add hf) hn).mpr
  intro w hw
  change 1 - (β : ℂ)⁻¹ * w + f w ≠ 0
  have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  by_cases he : w = (β : ℂ)
  · simp [f, he, hb]
  · simp only [f, if_neg he, add_zero]
    intro hz
    apply he
    have hz' : (β : ℂ)⁻¹ * w = 1 := (sub_eq_zero.mp hz).symm
    have := congrArg (fun z : ℂ => (β : ℂ) * z) hz'
    simpa [← mul_assoc, hb] using this

end
end DedekindZetaZeroFree.KPIsolatedProjection

end
