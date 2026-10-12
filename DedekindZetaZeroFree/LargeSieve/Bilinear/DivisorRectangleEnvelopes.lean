module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SevenTermApproximation
public import DedekindZetaZeroFree.LargeSieve.Bilinear.TwoOrientationPrefixEnvelope

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

namespace ErrorRectangles

def U (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (B X : ℝ) : ℝ :=
  let R := Sieve.idealAdmissibleFinset F c (2 * B)
  let S := Sieve.idealAdmissibleFinset F c (2 * X)
  sSup ({0} ∪ {z : ℝ | ∃ lam : Ideal (𝓞 F) → ℂ,
    (∑ b ∈ S, ‖lam b‖ ^ 2) ≤ 1 ∧
    z = ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2})

theorem U_le_of_exponent
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (hc : c ≠ ⊥)
    (hreciprocity : ∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ c = ⊤ →
      Squarefree b → b ⊔ c = ⊤ →
      (Q.χ a) b = (Q.χ b) a * Q.C (Q.cls a) (Q.cls b))
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hE : Sieve.HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ A : ℝ, 1 ≤ A ∧
      ∀ B X : ℝ, 1 ≤ B → 0 < X →
        U Q B X ≤ A * Real.rpow (B * max 1 X) η *
          min (B + Real.rpow (max 1 X) α) (max 1 X + Real.rpow B α) := by
  intro η hη
  obtain ⟨A, hA, hbound⟩ := Sieve.bilinear_prefix_two_orientation_envelope
    F c Q c hc (dvd_refl c) hreciprocity α hα hE η hη
  refine ⟨A, hA, ?_⟩
  intro B X hB hX
  have hp : 0 ≤ A * Real.rpow (B * max 1 X) η *
      min (B + Real.rpow (max 1 X) α) (max 1 X + Real.rpow B α) := by
    have ha : 0 ≤ A := by linarith
    have hb : 0 ≤ B := by linarith
    have hx : 0 ≤ max 1 X := le_trans (by norm_num) (le_max_left _ _)
    exact mul_nonneg (mul_nonneg ha (Real.rpow_nonneg (mul_nonneg hb hx) _))
      (le_min (add_nonneg hb (Real.rpow_nonneg hx _))
        (add_nonneg hx (Real.rpow_nonneg hb _)))
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  intro z hz
  rcases hz with hz | ⟨lam, hlam, rfl⟩
  · have hz0 : z = 0 := hz
    simpa only [hz0] using hp
  · have hh := hbound B X hB hX
      (Sieve.idealAdmissibleFinset F c (2 * B))
      (Sieve.idealAdmissibleFinset F c (2 * X))
      (Finset.Subset.refl _) (Finset.Subset.refl _)
      (fun _ => 1) (fun _ => 1) lam (by simp) (by simp)
    simp only [one_mul, mul_one] at hh
    calc
      _ ≤ _ := hh
      _ ≤ _ := mul_le_of_le_one_right hp hlam

def scales (X : ℝ) : Finset ℝ :=
  insert 1 ((Finset.range (Vendor.dyadicLength (2 * max 1 X))).image
    (fun i => (2 : ℝ) ^ i))

def InBin (P : ℝ) (f : Ideal (𝓞 F)) : Prop :=
  f ≠ ⊥ ∧ (if P = 1 then 1 ≤ norm f else P < norm f) ∧ norm f ≤ 2 * P

def rectangles (C : Context Q) : Finset (ℝ × ℝ) :=
  ((scales (C.N / norm C.d)) ×ˢ (scales (C.N / norm C.d))).filter
    (fun P => 1 ≤ P.1 ∧ 1 ≤ P.2 ∧
      P.1 ≤ 2 * C.N / norm C.d ∧ P.2 ≤ 2 * C.N / norm C.d ∧
      ∃ p ∈ C.pairs, ∃ f₁ f₂ : Ideal (𝓞 F),
        f₁ ∣ p.1 ∧ f₂ ∣ p.2 ∧ InBin P.1 f₁ ∧ InBin P.2 f₂)

def lowerConstant (c : Ideal (𝓞 F)) : ℝ := 1 / (4 * max 1 (norm c))

def largeScore (C : Context Q) (B : ℝ) (P : ℝ × ℝ) : ℝ :=
  Real.sqrt (U Q B (C.N / (norm C.d * P.1)) *
    U Q B (C.N / (norm C.d * P.2))) / Real.sqrt (P.1 * P.2)

def finiteSup (S : Finset (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : ℝ :=
  sSup ({0} ∪ {x : ℝ | ∃ P ∈ S, x = f P})

def directRectangles (C : Context Q) (B : ℝ) : Finset (ℝ × ℝ) :=
  (rectangles C).filter (fun P =>
    lowerConstant c * Real.sqrt (C.M / B) * Real.rpow (C.M * C.N) C.δ /
      norm C.d ≤ P.1 * P.2)

def directEnvelope (C : Context Q) (B : ℝ) : ℝ :=
  finiteSup (directRectangles C B) (largeScore C B)

theorem rectangle_endpoints (C : Context Q) (P : ℝ × ℝ)
    (hP : P ∈ rectangles C) :
    1 ≤ P.1 ∧ 1 ≤ P.2 ∧ P.1 ≤ 2 * C.N / norm C.d ∧
      P.2 ≤ 2 * C.N / norm C.d := by
  have h := (Finset.mem_filter.mp hP).2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end ErrorRectangles

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end
