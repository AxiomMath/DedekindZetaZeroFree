module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.ConjugacyClasses
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.SymmetricPower

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Completeness.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open Matrix Polynomial

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

private theorem trace_mul_character_symPower_torusHom (d : ℕ) (z : Circle) :
    Matrix.trace ((torusHom z : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
        * (symPower (d + 1)).character (torusHom z)
      = (symPower (d + 2)).character (torusHom z) + (symPower d).character (torusHom z) := by
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  have hstep : ∀ i : ℕ, ((z : ℂ) + ((z : ℂ))⁻¹) * (z : ℂ) ^ (2 * (i : ℤ) - ((d : ℤ) + 1))
      = (z : ℂ) ^ (2 * (i : ℤ) - (d : ℤ)) + (z : ℂ) ^ (2 * (i : ℤ) - ((d : ℤ) + 2)) := by
    intro i
    have hsucc : 2 * (i : ℤ) - (d : ℤ) = (2 * (i : ℤ) - ((d : ℤ) + 1)) + 1 := by ring
    have hpred : 2 * (i : ℤ) - ((d : ℤ) + 2) = (2 * (i : ℤ) - ((d : ℤ) + 1)) - 1 := by ring
    rw [hsucc, hpred, zpow_add_one₀ hz, zpow_sub_one₀ hz]
    field_simp
  rw [coe_torusHom, trace_torusMatrix, character_symPower_torusHom_zpow,
    character_symPower_torusHom_zpow, character_symPower_torusHom_zpow]
  push_cast
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
    Finset.sum_range_succ (fun i : ℕ => (z : ℂ) ^ (2 * (i : ℤ) - (d : ℤ))) (d + 1),
    Finset.sum_range_succ (fun i : ℕ => (z : ℂ) ^ (2 * (i : ℤ) - ((d : ℤ) + 2))) (d + 2)]
  push_cast

  have hlast : 2 * ((d : ℤ) + 1) - (d : ℤ) = (d : ℤ) + 2 := by ring
  have hlast' : 2 * ((d : ℤ) + 2) - ((d : ℤ) + 2) = (d : ℤ) + 2 := by ring
  rw [hlast, hlast']
  ring

theorem trace_mul_character_symPower (d : ℕ) (g : SU2) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) * (symPower (d + 1)).character g
      = (symPower (d + 2)).character g + (symPower d).character g := by
  have h : (fun g : SU2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
        * (symPower (d + 1)).character g)
      = fun g : SU2 => (symPower (d + 2)).character g + (symPower d).character g := by
    refine eq_of_conjInvariant_of_eqOn_torus (fun u g => ?_) (fun u g => ?_) fun x hx => ?_
    · rw [(trace_eq_of_isConj (isConj_iff.mpr ⟨u, rfl⟩)).symm, Representation.char_conj]
    · rw [Representation.char_conj, Representation.char_conj]
    · obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hx
      exact trace_mul_character_symPower_torusHom d z
  exact congrFun h g

@[simp]
theorem character_symPower_zero (g : SU2) : (symPower 0).character g = 1 := by
  have h : (fun g : SU2 => (symPower 0).character g) = fun _ : SU2 => (1 : ℂ) := by
    refine eq_of_conjInvariant_of_eqOn_torus (fun u g => Representation.char_conj _ g u)
      (fun _ _ => rfl) fun x hx => ?_
    obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hx
    simp [character_symPower_torusHom]
  exact congrFun h g

@[simp]
theorem character_symPower_one_eq_trace (g : SU2) :
    (symPower 1).character g = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h : (fun g : SU2 => (symPower 1).character g)
      = fun g : SU2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
    refine eq_of_conjInvariant_of_eqOn_torus (fun u g => Representation.char_conj _ g u)
      (fun u g => (trace_eq_of_isConj (isConj_iff.mpr ⟨u, rfl⟩)).symm) fun x hx => ?_
    obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hx
    rw [character_symPower_torusHom_zpow, coe_torusHom, trace_torusMatrix,
      Finset.sum_range_succ, Finset.sum_range_one]
    push_cast
    rw [_root_.zpow_neg_one, zpow_one]
    ring
  exact congrFun h g

theorem character_symPower_eq_chebyshevU_eval (d : ℕ) (g : SU2) :
    (symPower d).character g
      = (Chebyshev.U ℂ d).eval (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) := by
  induction d using Nat.twoStepInduction with
  | zero => simp [character_symPower_zero]
  | one => simp [character_symPower_one_eq_trace, Chebyshev.U_one]; ring
  | more n ihn ihn1 =>
    have hrec := trace_mul_character_symPower n g
    have hU : (Chebyshev.U ℂ ((n : ℤ) + 2))
        = 2 * X * Chebyshev.U ℂ ((n : ℤ) + 1) - Chebyshev.U ℂ (n : ℤ) :=
      Chebyshev.U_add_two ℂ (n : ℤ)
    have hcast : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have hcast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast, hU, ← hcast1]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [← ihn, ← ihn1]
    linear_combination -hrec

private theorem continuous_trace :
    Continuous fun g : SU2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) :=
  Continuous.matrix_trace continuous_subtype_val

theorem continuous_character_symPower (d : ℕ) :
    Continuous fun g : SU2 => (symPower d).character g := by
  have h : (fun g : SU2 => (symPower d).character g)
      = fun g : SU2 => (Chebyshev.U ℂ d).eval (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) :=
    funext (character_symPower_eq_chebyshevU_eval d)
  rw [h]
  exact (Chebyshev.U ℂ d).continuous.comp (continuous_trace.div_const 2)

noncomputable def symPowerCharacter (d : ℕ) : C(SU2, ℂ) :=
  ⟨fun g => (symPower d).character g, continuous_character_symPower d⟩

@[simp]
theorem symPowerCharacter_apply (d : ℕ) (g : SU2) :
    symPowerCharacter d g = (symPower d).character g := (rfl)

@[simp]
theorem symPowerCharacter_zero : symPowerCharacter 0 = 1 :=
  ContinuousMap.ext fun g => character_symPower_zero g

noncomputable def characterSpan : Submodule ℂ C(SU2, ℂ) :=
  Submodule.span ℂ (Set.range symPowerCharacter)

theorem symPowerCharacter_mem_characterSpan (d : ℕ) :
    symPowerCharacter d ∈ characterSpan :=
  Submodule.subset_span ⟨d, rfl⟩

theorem characterSpan_le_iff {p : Submodule ℂ C(SU2, ℂ)} :
    characterSpan ≤ p ↔ ∀ d : ℕ, symPowerCharacter d ∈ p := by
  rw [characterSpan, Submodule.span_le, Set.range_subset_iff]
  rfl

private theorem symPowerCharacter_one_mul_symPowerCharacter_mem (d : ℕ) :
    symPowerCharacter 1 * symPowerCharacter d ∈ characterSpan := by
  match d with
  | 0 =>
    rw [symPowerCharacter_zero, mul_one]
    exact symPowerCharacter_mem_characterSpan 1
  | (e + 1) =>
    have : symPowerCharacter 1 * symPowerCharacter (e + 1)
        = symPowerCharacter (e + 2) + symPowerCharacter e := by
      refine ContinuousMap.ext fun g => ?_
      simpa [character_symPower_one_eq_trace] using trace_mul_character_symPower e g
    rw [this]
    exact Submodule.add_mem _ (symPowerCharacter_mem_characterSpan _)
      (symPowerCharacter_mem_characterSpan _)

private theorem symPowerCharacter_one_mul_mem {f : C(SU2, ℂ)} (hf : f ∈ characterSpan) :
    symPowerCharacter 1 * f ∈ characterSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    exact symPowerCharacter_one_mul_symPowerCharacter_mem d
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa [mul_smul_comm] using Submodule.smul_mem _ a hx

theorem pow_symPowerCharacter_one_mem_characterSpan (n : ℕ) :
    symPowerCharacter 1 ^ n ∈ characterSpan := by
  induction n with
  | zero => simpa [← symPowerCharacter_zero] using symPowerCharacter_mem_characterSpan 0
  | succ n ih => rw [pow_succ']; exact symPowerCharacter_one_mul_mem ih

noncomputable def polyTrace (p : Polynomial ℝ) : C(SU2, ℂ) :=
  aeval (symPowerCharacter 1) p

private theorem polyTrace_mem_characterSpan (p : Polynomial ℝ) :
    polyTrace p ∈ characterSpan := by
  rw [polyTrace, aeval_eq_sum_range]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (pow_symPowerCharacter_one_mem_characterSpan i)

private theorem polyTrace_apply (p : Polynomial ℝ) {g : SU2} {t : ℝ}
    (ht : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) = (t : ℂ)) :
    polyTrace p g = ((p.eval t : ℝ) : ℂ) := by
  rw [polyTrace, aeval_eq_sum_range, p.eval_eq_sum_range]
  push_cast
  simp [ContinuousMap.sum_apply, ht, Complex.real_smul]

theorem exists_mem_characterSpan_norm_sub_lt {f : C(SU2, ℂ)}
    (hf : ∀ u g : SU2, f (u * g * u⁻¹) = f g) {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ characterSpan, ‖f - h‖ < ε := by

  set F : ℝ → ℂ := fun t => f (torusExp (Real.arccos (t / 2))) with hF
  have hFc : Continuous F :=
    f.continuous.comp (continuous_torusExp.comp
      (Real.continuous_arccos.comp (continuous_id.div_const 2)))
  obtain ⟨p₁, hp₁⟩ := exists_polynomial_near_of_continuousOn (-2) 2 (fun t => (F t).re)
    (Complex.continuous_re.comp hFc).continuousOn (ε / 3) (by positivity)
  obtain ⟨p₂, hp₂⟩ := exists_polynomial_near_of_continuousOn (-2) 2 (fun t => (F t).im)
    (Complex.continuous_im.comp hFc).continuousOn (ε / 3) (by positivity)
  refine ⟨polyTrace p₁ + Complex.I • polyTrace p₂,
    Submodule.add_mem _ (polyTrace_mem_characterSpan p₁)
      (Submodule.smul_mem _ _ (polyTrace_mem_characterSpan p₂)), ?_⟩
  refine (ContinuousMap.norm_lt_iff _ hε).mpr fun g => ?_

  obtain ⟨θ, hθ, hconj⟩ := exists_isConj_torusExp_mem_Icc g
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj
  have harc : Real.arccos (2 * Real.cos θ / 2) = θ := by
    have hhalf : (2 : ℝ) * Real.cos θ / 2 = Real.cos θ := by ring
    rw [hhalf, Real.arccos_cos hθ.1 hθ.2]
  have hfg : f g = F (2 * Real.cos θ) := by
    rw [hF]
    simp only [harc]
    rw [← hu, hf]
  have htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) = ((2 * Real.cos θ : ℝ) : ℂ) := by
    rw [trace_eq_of_isConj hconj, trace_torusExp]
    push_cast
    ring
  have hmem : (2 * Real.cos θ) ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have h₁ := hp₁ _ hmem
  have h₂ := hp₂ _ hmem

  have hval : (polyTrace p₁ + Complex.I • polyTrace p₂) g
      = ((p₁.eval (2 * Real.cos θ) : ℝ) : ℂ)
        + Complex.I * ((p₂.eval (2 * Real.cos θ) : ℝ) : ℂ) := by
    simp [polyTrace_apply p₁ htr, polyTrace_apply p₂ htr]
  rw [ContinuousMap.sub_apply, hfg, hval]
  have hsplit : F (2 * Real.cos θ)
        - (((p₁.eval (2 * Real.cos θ) : ℝ) : ℂ)
          + Complex.I * ((p₂.eval (2 * Real.cos θ) : ℝ) : ℂ))
      = ((((F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ) : ℝ)) : ℂ)
        + Complex.I * ((((F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ) : ℝ)) : ℂ) := by
    push_cast
    linear_combination -Complex.re_add_im (F (2 * Real.cos θ))
  have h₁' : |(F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ)| < ε / 3 := by
    rw [abs_sub_comm]; exact h₁
  have h₂' : |(F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ)| < ε / 3 := by
    rw [abs_sub_comm]; exact h₂
  rw [hsplit]
  calc ‖((((F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ) : ℝ)) : ℂ)
          + Complex.I * ((((F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ) : ℝ)) : ℂ)‖
      ≤ |(F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ)|
        + |(F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ)| := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ < ε := by linarith

theorem mem_topologicalClosure_characterSpan_iff {f : C(SU2, ℂ)} :
    f ∈ characterSpan.topologicalClosure ↔ ∀ u g : SU2, f (u * g * u⁻¹) = f g := by
  constructor
  · intro hf u g
    have hspan : Set.EqOn (fun h : C(SU2, ℂ) => h (u * g * u⁻¹)) (fun h : C(SU2, ℂ) => h g)
        (characterSpan : Set C(SU2, ℂ)) := by
      intro h hh
      induction hh using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨d, rfl⟩ := hx
        exact Representation.char_conj _ g u
      | zero => rfl
      | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
      | smul a x _ hx => simpa using congrArg (a * ·) hx
    refine hspan.closure (continuous_eval_const _) (continuous_eval_const _) ?_
    rwa [← Submodule.topologicalClosure_coe]
  · intro hf
    have hclosure : f ∈ closure (characterSpan : Set C(SU2, ℂ)) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨h, hh, hlt⟩ := exists_mem_characterSpan_norm_sub_lt hf hε
      exact ⟨h, hh, by rwa [dist_eq_norm]⟩
    rwa [← Submodule.topologicalClosure_coe] at hclosure

end SU2

end DedekindZetaZeroFree.TauCeti
