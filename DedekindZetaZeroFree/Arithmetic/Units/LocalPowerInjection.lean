module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LocallyPowerSUnitExtensionDegree
public import DedekindZetaZeroFree.Arithmetic.Kummer.DegreeOneSUnitRoots

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SArithmeticData

theorem local_power_injection (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R))
    (ℓ : ℕ) (hℓ : ℓ ∈ ({2, 3, 6} : Finset ℕ)) (ε : A.U)
    (hlocal :
      (∀ w : InfinitePlace F, ∃ b : w.Completionˣ,
        b ^ ℓ = (A.diagonal ε.val).1 w) ∧
      (∀ v : {v // v ∈ A.Sf}, ∃ b : (v.val.adicCompletion F)ˣ,
        b ^ ℓ = (A.diagonal ε.val).2 v)) :
    ∃ b : A.U, b ^ ℓ = ε := by
  have hℓpos : 0 < ℓ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
    omega
  let n : ℕ+ := ⟨ℓ, hℓpos⟩
  have hn : (n : ℕ) ∈ ({2, 3, 6} : Finset ℕ) := hℓ
  have hnF : ((n : ℕ) : F) ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hℓ with h | h | h <;> (subst h; norm_num)
  have hlocal' : ∀ v : A.Place,
      match v with
      | Sum.inl w =>
          (A.diagonal (ε : Fˣ)).1 w ∈ (powMonoidHom (n : ℕ)).range
      | Sum.inr w =>
          (A.diagonal (ε : Fˣ)).2 w ∈ (powMonoidHom (n : ℕ)).range := by
    intro v
    match v with
    | Sum.inl w =>
        obtain ⟨b, hb⟩ := hlocal.1 w
        exact ⟨b, hb⟩
    | Sum.inr w =>
        obtain ⟨b, hb⟩ := hlocal.2 w
        exact ⟨b, hb⟩
  have hdeg := arith_sunit_kummer_degree_one F A hCl n hn ε hlocal' hnF
  exact sunit_root_of_simpleKummerExtension_finrank_one F A n ε hnF hdeg

end SArithmeticData
end DedekindZetaZeroFree
