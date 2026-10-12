module

public import DedekindZetaZeroFree.LFunctions.Hecke.CompletedRayZetaRegularization

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient

theorem partialRayZetaRegularization
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    ∃ (ρ : ℂ) (F : RayIdealClass K m hm → ℂ → ℂ),
      (∀ c, Differentiable ℂ (F c)) ∧
      ∀ (c : RayIdealClass K m hm) (s : ℂ), 1 < s.re →
        HasSum
          (fun I : Ideal (𝓞 K) =>
            if rayIdealClass K m hm I = some c then
              (Ideal.absNorm I : ℂ) ^ (-s)
            else 0)
          (F c s + ρ / (s - 1)) := by
  classical

  choose a ha using fun c => exists_integral_inverse_rayIdealClass K m hm c
  choose b hb using fun c => exists_ray_congruence_basepoint K m (a c) (ha c).2.1

  let D : RayIdealClass K m hm → RayCoset.Data K := fun c =>
    { m := m
      modulus_ne_bot := hm
      a := a c
      ideal_ne_bot := (ha c).1
      coprime := (ha c).2.1
      b := b c
      basepoint_mem := (hb c).1
      basepoint_congruent_one := (hb c).2 }

  refine ⟨RayCompletedRegularization.residue K m hm,
    fun c => RayCompletedRegularization.entirePart (D c), ?_, ?_⟩
  · intro c
    exact (rayCompletedRegularization K m hm (D c) rfl c (ha c).2.2).1
  · intro c s hs
    exact (rayCompletedRegularization K m hm (D c) rfl c (ha c).2.2).2 s hs

end DedekindZetaZeroFree.AbelianQuotient
