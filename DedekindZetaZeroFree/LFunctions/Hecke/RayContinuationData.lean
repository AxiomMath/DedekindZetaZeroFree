module

public import DedekindZetaZeroFree.LFunctions.Hecke.CompletionFactor

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

structure NonprincipalRayHeckeData (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (η : RayClassCharacter F 𝔪) where
  L : ℂ → ℂ
  Λ : ℂ → ℂ
  Λdual : ℂ → ℂ
  W : ℂ
  L_holo : DifferentiableOn ℂ L {s | 0 < s.re}
  Λ_entire : Differentiable ℂ Λ
  Λdual_entire : Differentiable ℂ Λdual
  series : ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s)) (L s)
  completed : ∀ s : ℂ, 0 < s.re → Λ s = heckeCompletionFactor F 𝔪 s * L s
  dual_series : ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : Ideal (𝓞 F) => heckeCompletionFactor F 𝔪 s *
      ((starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s))) (Λdual s)
  root_norm : ‖W‖ = 1
  reflection : ∀ s : ℂ, Λ s = W * Λdual (1 - s)
  order_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
    ‖Λ s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε))

structure PrincipalRayHeckeData (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (η : RayClassCharacter F 𝔪) where
  L : ℂ → ℂ
  R : ℂ → ℂ
  Λ : ℂ → ℂ
  E : ℂ → ℂ
  L_holo : DifferentiableOn ℂ L {s | 0 < s.re ∧ s ≠ 1}
  R_holo : DifferentiableOn ℂ R {s | 0 < s.re}
  Λ_holo : DifferentiableOn ℂ Λ {s | s ≠ 0 ∧ s ≠ 1}
  E_entire : Differentiable ℂ E
  series : ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s)) (L s)
  completed : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
    Λ s = heckeCompletionFactor F 𝔪 s * L s
  regularized : ∀ s : ℂ, 0 < s.re → s ≠ 1 → R s = (s - 1) * L s
  E_eq : ∀ s : ℂ, 0 < s.re → E s = s * heckeCompletionFactor F 𝔪 s * R s
  reflection : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ s = Λ (1 - s)
  order_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
    ‖E s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε))

end
end DedekindZetaZeroFree
