module

public import DedekindZetaZeroFree.LFunctions.Dedekind.PrimeIdealFactor
public import DedekindZetaZeroFree.LFunctions.Dedekind.DirichletSeriesConvergence

@[expose] public section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/PrimeIdealSummability.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

noncomputable section

open Ideal IsDedekindDomain

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem summable_ideal_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (absNorm : Ideal (𝓞 K) → ℕ)
  rw [← e.summable_iff]
  apply (summable_sigma_of_nonneg (fun x ↦
    Real.rpow_nonneg (Nat.cast_nonneg (absNorm (e x))) _)).2
  constructor
  · intro n
    let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).fintype
    exact Summable.of_finite
  · have hseries :=
      (lSeriesSummable_idealNormCount K (s := (σ : ℂ)) (by simpa using hσ)).norm
    convert hseries using 1
    ext n
    simp only [e, Equiv.sigmaFiberEquiv_apply, LSeries.norm_term_eq]
    split_ifs with hn
    · subst n
      have hzero :
          (fun y : {I : Ideal (𝓞 K) // absNorm I = 0} ↦
            (absNorm (y : Ideal (𝓞 K)) : ℝ) ^ (-σ)) = 0 := by
        funext y
        rw [y.2]
        simp [ne_of_gt (zero_lt_one.trans hσ)]
      rw [hzero]
      change (∑' _ : {I : Ideal (𝓞 K) // absNorm I = 0}, (0 : ℝ)) = 0
      simp
    · have hconst :
          (fun y : {I : Ideal (𝓞 K) // absNorm I = n} ↦
            (absNorm (y : Ideal (𝓞 K)) : ℝ) ^ (-σ)) =
            fun _ ↦ (n : ℝ) ^ (-σ) := by grind
      rw [hconst, tsum_const]
      simp only [idealNormCount, nsmul_eq_mul, norm_natCast]
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
      simp [div_eq_mul_inv]

end DedekindZetaZeroFree.Odlyzko

end
