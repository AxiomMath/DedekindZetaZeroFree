module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformConductorControl
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.PrincipalProductsAndMultiplicity

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

theorem initial_family_conductor_growth (hc : c ≠ ⊥) (Q : QuadraticHeckeFamily F c) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ b : Ideal (𝓞 F),
      Squarefree b → b ⊔ c = ⊤ →
      (Ideal.absNorm (Q.cond b) : ℝ) ≤ L * (Ideal.absNorm b : ℝ) := by
  obtain ⟨q, hq, -, hmain, -, -⟩ := allIndexConductorControl hc Q
  refine ⟨max 1 (Ideal.absNorm q : ℝ), le_max_left _ _, ?_⟩
  intro b hb hbc
  have hdvd : Ideal.absNorm (Q.cond b) ∣ Ideal.absNorm (b * q) :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp (hmain b hb hbc).1)
  have hbq : b * q ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hb.ne_zero hq
  have hle : Ideal.absNorm (Q.cond b) ≤ Ideal.absNorm b * Ideal.absNorm q := by
    rw [← map_mul Ideal.absNorm b q]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h =>
      hbq (Ideal.absNorm_eq_zero_iff.mp h)) hdvd
  have hleR : (Ideal.absNorm (Q.cond b) : ℝ) ≤
      (Ideal.absNorm b : ℝ) * (Ideal.absNorm q : ℝ) := by
    exact_mod_cast hle
  calc (Ideal.absNorm (Q.cond b) : ℝ)
      ≤ (Ideal.absNorm b : ℝ) * (Ideal.absNorm q : ℝ) := hleR
    _ ≤ (Ideal.absNorm b : ℝ) * max 1 (Ideal.absNorm q : ℝ) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
    _ = max 1 (Ideal.absNorm q : ℝ) * (Ideal.absNorm b : ℝ) := by ring

theorem initial_family_sameClass_nonprincipal (hc : c ≠ ⊥)
    (Q : QuadraticHeckeFamily F c) :
    ∀ b1 b2 : Ideal (𝓞 F),
      Squarefree b1 → b1 ⊔ c = ⊤ →
      Squarefree b2 → b2 ⊔ c = ⊤ →
      Q.cls b1 = Q.cls b2 → b1 ≠ b2 →
      ¬ (RayOperations.mul (Q.χ b1) (RayOperations.conjugate (Q.χ b2))).IsPrincipal := by
  intro b1 b2 hb1 hb1c hb2 hb2c hclass hne hprin
  refine hne ((quadraticFamily_principal_product_iff Q hc hb1 hb1c hb2 hb2c hclass).mp ?_)
  intro I hI hIcop
  have h := hprin I hI hIcop
  rw [RayOperations.mul_apply, RayOperations.conjugate_apply,
    quadraticFamily_conj Q hb2 hb2c I] at h
  rwa [RayOperations.mul_apply]

end DedekindZetaZeroFree.LargeSieve
