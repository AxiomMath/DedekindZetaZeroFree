module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import DedekindZetaZeroFree.Analysis.StretchedExponentialDecay

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open MeasureTheory

theorem existsWeakFEPair_weight_one
    (f g : ℝ → ℂ) (a b w : ℂ) (C B p : ℝ)
    (hf : LocallyIntegrableOn f (Set.Ioi 0))
    (hg : LocallyIntegrableOn g (Set.Ioi 0))
    (hw : w ≠ 0) (hC : 0 ≤ C) (hB : 0 < B) (hp : 0 < p)
    (hfe : ∀ t : ℝ, 0 < t → f (1 / t) = w * (t : ℂ) * g t)
    (hdecay : ∀ t : ℝ, 1 ≤ t →
      ‖f t - a‖ ≤ C * Real.exp (-B * Real.rpow t p) ∧
      ‖g t - b‖ ≤ C * Real.exp (-B * Real.rpow t p)) :
    ∃ P : WeakFEPair ℂ,
      P.f = f ∧ P.g = g ∧ P.k = 1 ∧ P.ε = w ∧ P.f₀ = a ∧ P.g₀ = b := by
  let P : WeakFEPair ℂ :=
    { f := f
      g := g
      k := 1
      ε := w
      f₀ := a
      g₀ := b
      hf_int := hf
      hg_int := hg
      hk := by norm_num
      hε := hw
      h_feq := by
        intro t ht
        simpa only [Real.rpow_one, smul_eq_mul] using hfe t ht
      hf_top := DedekindZetaZeroFree.thetaStretchedExponentialPower_bound
        p B hp hB (fun t => f t - a) C hC (fun t ht => (hdecay t ht).1)
      hg_top := DedekindZetaZeroFree.thetaStretchedExponentialPower_bound
        p B hp hB (fun t => g t - b) C hC (fun t ht => (hdecay t ht).2) }
  exact ⟨P, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem existsStrongFEPair_weight_one
    (f g : ℝ → ℂ) (w : ℂ) (C B p : ℝ)
    (hf : LocallyIntegrableOn f (Set.Ioi 0))
    (hg : LocallyIntegrableOn g (Set.Ioi 0))
    (hw : w ≠ 0) (hC : 0 ≤ C) (hB : 0 < B) (hp : 0 < p)
    (hfe : ∀ t : ℝ, 0 < t → f (1 / t) = w * (t : ℂ) * g t)
    (hdecay : ∀ t : ℝ, 1 ≤ t →
      ‖f t‖ ≤ C * Real.exp (-B * Real.rpow t p) ∧
      ‖g t‖ ≤ C * Real.exp (-B * Real.rpow t p)) :
    ∃ P : WeakFEPair ℂ,
      P.f = f ∧ P.g = g ∧ P.k = 1 ∧ P.ε = w ∧
        P.f₀ = 0 ∧ P.g₀ = 0 ∧ IsStrongFEPair P := by
  obtain ⟨P, hfP, hgP, hkP, hwP, haP, hbP⟩ :=
    existsWeakFEPair_weight_one f g 0 0 w C B p hf hg hw hC hB hp hfe
      (by simpa only [sub_zero] using hdecay)
  exact ⟨P, hfP, hgP, hkP, hwP, haP, hbP, ⟨haP, hbP⟩⟩

end DedekindZetaZeroFree.Hecke
