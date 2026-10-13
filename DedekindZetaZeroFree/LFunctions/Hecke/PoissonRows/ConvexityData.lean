module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Identification

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ConvexBridge

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem conductor_bound' :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, 1 ≤ D.q u →
      (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ) ≤ C * D.q u) ∧
      (1 + (Ideal.absNorm (D.omega u).conductor : ℝ) ≤ C * D.q u) := by
  obtain ⟨C, hC, h⟩ := RowHeckeBridge.conductor_bound D
  exact ⟨C, hC, fun u hu => ⟨(h u hu).1, (h u hu).2⟩⟩

theorem entire_eq_mask_mul (u : D.Row)
    (hnp : ¬ (D.inducers u).plus.character.IsPrincipal)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h : ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) :
    ∀ s : ℂ, 0 < s.re → g s =
      Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) s *
        (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnp).L s :=
  RowHeckeBridge.entire_eq_mask_mul_Lpsi D u hnp hg h

end

end DedekindZetaZeroFree.Quantitative.ConvexBridge
