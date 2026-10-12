module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ProductConductorComparison

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

open scoped NumberField Classical
open DedekindZetaZeroFree

noncomputable section

variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

def cube {m : Ideal (𝓞 F)} (ψ : RayClassCharacter F m) :
    RayClassCharacter F m where
  toFun I := (ψ I) ^ 3
  map_mul' := fun I J => by rw [ψ.map_mul', mul_pow]
  map_top' := by rw [ψ.map_top', one_pow]
  eq_zero_iff' := fun I => by
    rw [pow_eq_zero_iff (show (3 : ℕ) ≠ 0 by norm_num), ψ.eq_zero_iff' I]
  map_span' := fun α hα hmem hpos => by
    rw [ψ.map_span' α hα hmem hpos, one_pow]

private lemma cube_apply {m : Ideal (𝓞 F)} (ψ : RayClassCharacter F m)
    (I : Ideal (𝓞 F)) : cube ψ I = (ψ I) ^ 3 := rfl

private lemma cube_eq_self_mem {z : ℂ} (h : z ^ 3 = z) :
    z ∈ ({0, 1, -1} : Set ℂ) := by
  have hfac : z * (z - 1) * (z + 1) = z ^ 3 - z := by ring
  have hzero : z * (z - 1) * (z + 1) = 0 := by rw [hfac, sub_eq_zero.mpr h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases mul_eq_zero.mp hzero with h' | h'
  · rcases mul_eq_zero.mp h' with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (sub_eq_zero.mp h'))
  · exact Or.inr (Or.inr (add_eq_zero_iff_eq_neg.mp h'))

theorem primitiveProductQuadratic
    (Q : QuadraticHeckeFamily F c)
    {u v : Ideal (𝓞 F)} (hu0 : u ≠ ⊥) (hv0 : v ≠ ⊥)
    (hu : Squarefree u) (hv : Squarefree v)
    (huc : u ⊔ c = ⊤) (hvc : v ⊔ c = ⊤) (huv : u ⊔ v = ⊤)
    (hclass : Q.cls u = Q.cls v)
    (ψ : RayClassCharacter F (u * v))
    (hagrees : ∀ I : Ideal (𝓞 F), I ⊔ (Q.cond u * Q.cond v) = ⊤ →
      ψ I = (Q.χ u) I * starRingEnd ℂ ((Q.χ v) I)) :
    (∀ I : Ideal (𝓞 F), starRingEnd ℂ (ψ I) = ψ I ∧
      ψ I ∈ ({0, 1, -1} : Set ℂ) ∧ (ψ I) ^ 3 = ψ I ∧ ‖ψ I‖ ≤ 1) ∧
      (∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (u * v) = ⊤ → (ψ I) ^ 2 = 1) := by
  have huv0 : u * v ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hu0 hv0
  have hcu0 : Q.cond u ≠ ⊥ := (Q.primitive u hu huc).1
  have hcv0 : Q.cond v ≠ ⊥ := (Q.primitive v hv hvc).1
  have hcond0 : Q.cond u * Q.cond v ≠ ⊥ := fun h =>
    (Ideal.mul_eq_bot.mp h).elim hcu0 hcv0

  have hcube_eq : ∀ I : Ideal (𝓞 F), (cube ψ) I = ψ I :=
    RayComparison.away_uniqueness huv0 hcond0 (cube ψ) ψ (by
      intro I _ hsup
      have hle : (u * v) * (Q.cond u * Q.cond v) ≤ Q.cond u * Q.cond v :=
        Ideal.dvd_iff_le.mp ⟨u * v, mul_comm _ _⟩
      have hcI : I ⊔ (Q.cond u * Q.cond v) = ⊤ :=
        le_antisymm le_top (hsup ▸ sup_le_sup_left hle I)
      have hv3 : (starRingEnd ℂ ((Q.χ v) I)) ^ 3 = starRingEnd ℂ ((Q.χ v) I) := by
        rw [← map_pow, Q.quadratic v I hv hvc]
      rw [cube_apply, hagrees I hcI, mul_pow, hv3, Q.quadratic u I hu huc])
  have hquad : ∀ I : Ideal (𝓞 F), (ψ I) ^ 3 = ψ I := fun I =>
    (cube_apply ψ I).symm.trans (hcube_eq I)
  refine ⟨fun I => ?_, fun I hI hcop => ?_⟩
  · have h3 := hquad I
    have hmem := cube_eq_self_mem h3
    refine ⟨?_, hmem, h3, ?_⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> rw [h] <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h <;> rw [h] <;> norm_num
  · have hmem := cube_eq_self_mem (hquad I)
    have hne : ψ I ≠ 0 := fun h0 =>
      (ψ.eq_zero_iff' I).mp h0 |>.elim hI (fun hc => hc hcop)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h hne
    · rw [h]; norm_num
    · rw [h]; norm_num

end

end DedekindZetaZeroFree.LargeSieve.Bilinear
