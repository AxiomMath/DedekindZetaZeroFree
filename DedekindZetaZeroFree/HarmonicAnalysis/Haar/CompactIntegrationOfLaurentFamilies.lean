module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeBaseChartNumerator

open MeasureTheory
open scoped Classical

def complexUnitLaurentLinearEvaluation (u : ℂˣ) : (ℤ →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun n : ℤ => (u : ℂ) ^ n)

private lemma laurentValue_eq (u : ℂˣ) (p : ℤ →₀ ℂ) :
    complexUnitLaurentLinearEvaluation u p = p.sum (fun n c => (u : ℂ) ^ n * c) := by
  simp [complexUnitLaurentLinearEvaluation, Finsupp.linearCombination_apply, smul_eq_mul, mul_comm]

private theorem finite_family_integral {X T : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X] [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (H : X → T → ℂ) (hH : IsLocallyConstant H) (t : T) :
    ∫ x, H x t ∂μ = ∑ y ∈ hH.range_finite.toFinset, μ.real (H ⁻¹' {y}) • y t := by
  classical
  let D := hH.range_finite.toFinset
  have hm (y : T → ℂ) : MeasurableSet (H ⁻¹' {y}) := (hH.isOpen_fiber y).measurableSet
  have hi (y : T → ℂ) : Integrable ((H ⁻¹' {y}).indicator (fun _ => y t)) μ :=
    (integrable_const _).indicator (hm y)
  have he (x : X) : H x t = ∑ y ∈ D, (H ⁻¹' {y}).indicator (fun _ => y t) x := by
    rw [Finset.sum_eq_single (H x)]
    · simp
    · intro y hy hne
      simp [Set.indicator_of_notMem, hne.symm]
    · intro hx
      exact False.elim (hx (hH.range_finite.mem_toFinset.mpr ⟨x, rfl⟩))
  simp_rw [he]
  rw [integral_finsetSum D (fun y _ => hi y)]
  exact Finset.sum_congr rfl (fun y _ => integral_indicator_const _ (hm y))

theorem compact_set_integral_laurent_family
    {X T : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (μ : Measure X) (A : Set X) (hAc : IsCompact A) (hAm : MeasurableSet A)
    (hAf : μ A ≠ ⊤) (u : T → ℂˣ) (H : X → T → ℂ)
    (hH : IsLocallyConstant (fun x : A => H x.val))
    (hp : ∀ x ∈ A, ∃ p : ℤ →₀ ℂ, ∀ t : T,
      H x t = p.sum (fun n c => (u t : ℂ) ^ n * c)) :
    ∃ p : ℤ →₀ ℂ, ∀ t : T,
      (∫ x in A, H x t ∂μ) = p.sum (fun n c => (u t : ℂ) ^ n * c) := by
  classical
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hAc
  let ν := μ.comap (Subtype.val : A → X)
  letI : IsFiniteMeasure ν := ⟨by
    change μ.comap (Subtype.val : A → X) Set.univ < ⊤
    rw [comap_subtype_coe_apply hAm μ Set.univ]
    simpa using hAf.lt_top⟩
  let G : A → T → ℂ := fun x => H x.val
  have hG : IsLocallyConstant G := hH
  let D := hG.range_finite.toFinset
  have hQ (y : T → ℂ) (hy : y ∈ D) :
      ∃ Q : ℤ →₀ ℂ, ∀ t, y t = complexUnitLaurentLinearEvaluation (u t) Q := by
    obtain ⟨x, rfl⟩ := hG.range_finite.mem_toFinset.mp hy
    obtain ⟨Q, hQ⟩ := hp x.val x.property
    exact ⟨Q, fun t => (hQ t).trans (laurentValue_eq (u t) Q).symm⟩
  choose Q hQ using hQ
  let p : ℤ →₀ ℂ := ∑ y : D, ν.real (G ⁻¹' {(y : T → ℂ)}) • Q y y.property
  refine ⟨p, fun t => ?_⟩
  rw [← laurentValue_eq]
  simp only [p, map_sum]
  have he : (∑ y : D, complexUnitLaurentLinearEvaluation (u t)
      (ν.real (G ⁻¹' {(y : T → ℂ)}) • Q y y.property)) =
      ∑ y : D, ν.real (G ⁻¹' {(y : T → ℂ)}) • (y : T → ℂ) t := by
    apply Finset.sum_congr rfl
    intro y hy
    change complexUnitLaurentLinearEvaluation (u t)
      ((ν.real (G ⁻¹' {(y : T → ℂ)}) : ℂ) • Q y y.property) = _
    rw [map_smul, ← hQ y y.property t]
    rfl
  rw [he]
  change _ = ∑ y ∈ D.attach, ν.real (G ⁻¹' {y.val}) • y.val t
  rw [Finset.sum_attach D (fun y : T → ℂ => ν.real (G ⁻¹' {y}) • y t)]
  rw [← finite_family_integral ν G hG t]
  exact (integral_subtype_comap hAm (fun x => H x t)).symm

end DedekindZetaZeroFree.KPTameTransposeBaseChartNumerator

end
