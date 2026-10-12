module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneMellinShellReassembly

open MeasureTheory
open scoped Topology

theorem shell_reassembly {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (e : X → ℤ) (g : X → ℂ) (r : ℂ) (nmin : ℤ)
    (hlower : ∀ y, e y < nmin → g y = 0)
    (hmeas : ∀ k : ℕ, MeasurableSet {y | e y = nmin + (k : ℤ)})
    (hint : ∀ k : ℕ, IntegrableOn (fun y => g y * r ^ e y)
      {y | e y = nmin + (k : ℤ)} ν)
    (hsum : Summable (fun k : ℕ => ∫ y in {y | e y = nmin + (k : ℤ)},
      ‖g y * r ^ e y‖ ∂ν)) :
    Integrable (fun y => g y * r ^ e y) ν ∧
    HasSum (fun k : ℕ =>
      (∫ y in {y | e y = nmin + (k : ℤ)}, g y ∂ν) * r ^ (nmin + (k : ℤ)))
      (∫ y, g y * r ^ e y ∂ν) := by
  set s : ℕ → Set X := fun k => {y | e y = nmin + (k : ℤ)} with hs
  have hmeas' : ∀ k : ℕ, MeasurableSet (s k) := fun k => hmeas k

  have hdisj : Pairwise fun k k' => Disjoint (s k) (s k') := by
    intro k k' hkk'
    rw [Set.disjoint_left]
    intro y hk hk'
    simp only [s, Set.mem_setOf_eq] at hk hk'
    have hcast : (k : ℤ) = (k' : ℤ) := by omega
    exact hkk' (Nat.cast_injective hcast)

  have hIntOn : IntegrableOn (fun y => g y * r ^ e y) (⋃ k, s k) ν :=
    integrableOn_iUnion_of_summable_integral_norm (s := s) (fun k => hint k)
      (by simpa only [hs] using hsum)
  have hU : MeasurableSet (⋃ k, s k) := MeasurableSet.iUnion hmeas'

  have hzero : ∀ x, x ∉ ⋃ k, s k → g x * r ^ e x = 0 := by
    intro x hx
    have he : e x < nmin := by
      by_contra h
      push Not at h
      refine hx (Set.mem_iUnion.2 ⟨(e x - nmin).toNat, ?_⟩)
      simp only [s, Set.mem_setOf_eq]
      have : ((e x - nmin).toNat : ℤ) = e x - nmin := Int.toNat_of_nonneg (by omega)
      omega
    rw [hlower x he, zero_mul]
  have hInt : Integrable (fun y => g y * r ^ e y) ν := by
    have hind : Integrable ((⋃ k, s k).indicator (fun y => g y * r ^ e y)) ν :=
      (integrable_indicator_iff hU).2 hIntOn
    refine hind.congr (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ⋃ k, s k
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hzero x hx]
  refine ⟨hInt, ?_⟩
  have hHS := hasSum_integral_iUnion (μ := ν) (f := fun y => g y * r ^ e y) hmeas' hdisj hIntOn
  simp only [hs] at hHS

  have hterm : ∀ k : ℕ,
      (∫ x in {y | e y = nmin + (k : ℤ)}, g x * r ^ e x ∂ν) =
        (∫ x in {y | e y = nmin + (k : ℤ)}, g x ∂ν) * r ^ (nmin + (k : ℤ)) := by
    intro k
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (hmeas k) ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    show g x * r ^ e x = g x * r ^ (nmin + (k : ℤ))
    rw [hx]
  have hlim : (∫ x in ⋃ k : ℕ, {y | e y = nmin + (k : ℤ)}, g x * r ^ e x ∂ν) =
      ∫ x, g x * r ^ e x ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      refine hzero x ?_
      simpa only [hs] using hx
  simpa only [hterm, hlim] using hHS

end DedekindZetaZeroFree.KPRankOneMellinShellReassembly
