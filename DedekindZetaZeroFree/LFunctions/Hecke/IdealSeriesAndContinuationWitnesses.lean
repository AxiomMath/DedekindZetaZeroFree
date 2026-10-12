module

public import DedekindZetaZeroFree.LFunctions.Hecke.FunctionalEquation

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

noncomputable section
open scoped NumberField Classical

def heckeCompletionFactor (F : Type) [Field F] [NumberField F]
    (f : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm f : ℂ)) ^ (s / 2) *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F

def idealHeckeL {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 F), η I * (Ideal.absNorm I : ℂ) ^ (-s)

structure EntireHeckeWitness {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F f) where
  Λ : ℂ → ℂ
  Λdual : ℂ → ℂ
  W : ℂ
  differentiable : Differentiable ℂ Λ
  differentiable_dual : Differentiable ℂ Λdual
  norm_W : ‖W‖ = 1
  hasSum : ∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
    heckeCompletionFactor F f s * (η I * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ s)
  hasSum_dual : ∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
    heckeCompletionFactor F f s *
      ((starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s))) (Λdual s)
  functionalEquation : ∀ s : ℂ, Λ s = W * Λdual (1 - s)
  growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
    ‖Λ s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε))

structure PrincipalHeckeWitness {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F f) where
  Λ : ℂ → ℂ
  U : ℂ → ℂ
  differentiableOn : DifferentiableOn ℂ Λ {s | s ≠ 0 ∧ s ≠ 1}
  differentiable_U : Differentiable ℂ U
  hasSum : ∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 F) =>
    heckeCompletionFactor F f s * (η I * (Ideal.absNorm I : ℂ) ^ (-s))) (Λ s)
  functionalEquation : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ s = Λ (1 - s)
  poleClearing : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → U s = s * (s - 1) * Λ s
  growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
    ‖U s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε))

theorem exists_entireHeckeWitness
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {f : Ideal (𝓞 F)} (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hp : η.IsPrimitive)
    (hn : ¬ η.IsPrincipal) : Nonempty (EntireHeckeWitness η) := by
  obtain ⟨Λ, Λdual, W, hdiff, hdiff_dual, hW, hsum, hsum_dual, hfe, hgrowth⟩ :=
    (DedekindZetaZeroFree.Hecke.heckeFunctionalEquation F hF f hf η hp).1 hn
  exact ⟨{ Λ := Λ, Λdual := Λdual, W := W, differentiable := hdiff,
           differentiable_dual := hdiff_dual, norm_W := hW, hasSum := hsum,
           hasSum_dual := hsum_dual, functionalEquation := hfe, growth := hgrowth }⟩

theorem exists_principalHeckeWitness
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {f : Ideal (𝓞 F)} (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hp : η.IsPrimitive)
    (hn : η.IsPrincipal) : Nonempty (PrincipalHeckeWitness η) := by
  obtain ⟨Λ, U, hdiffOn, hdiffU, hsum, hfe, hpole, hgrowth⟩ :=
    (DedekindZetaZeroFree.Hecke.heckeFunctionalEquation F hF f hf η hp).2 hn
  exact ⟨{ Λ := Λ, U := U, differentiableOn := hdiffOn, differentiable_U := hdiffU,
           hasSum := hsum, functionalEquation := hfe, poleClearing := hpole,
           growth := hgrowth }⟩

end

end DedekindZetaZeroFree.LargeSieve
