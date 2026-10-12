module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

theorem quadraticCharacter_quotient_card_two
    {G : Type*} [Group G] (ψ : G →* ℂˣ)
    (hsq : ∀ g, ψ g ^ 2 = 1) (hn : ψ ≠ 1) :
    Nat.card (G ⧸ ψ.ker) = 2 := by
  have hval : ∀ g, ((ψ g : ℂ)) ^ 2 = 1 := by
    intro g
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hsq g)
    simpa using this
  have hmem : ∀ g, ψ g = 1 ∨ ψ g = -1 := by
    intro g
    rcases sq_eq_one_iff.mp (hval g) with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  obtain ⟨g₀, hg₀⟩ : ∃ g, ψ g ≠ 1 := by
    obtain ⟨g, hg⟩ := DFunLike.exists_ne hn
    exact ⟨g, by simpa using hg⟩
  have hg₀' : ψ g₀ = -1 := (hmem g₀).resolve_left hg₀
  have hrange : Set.range ψ = ({1, -1} : Set ℂˣ) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      rcases hmem g with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨1, map_one ψ⟩
      · exact ⟨g₀, hg₀'⟩
  have hne : (1 : ℂˣ) ≠ -1 := fun h => by
    have h' : (1 : ℂ) = -1 := congrArg Units.val h
    norm_num at h'
  have hcard : Nat.card (Set.range ψ) = 2 := by
    rw [Nat.card_coe_set_eq, hrange, Set.ncard_pair hne]
  calc Nat.card (G ⧸ ψ.ker) = Nat.card (Set.range ψ) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    _ = 2 := hcard

end DedekindZetaZeroFree.LargeSieve
