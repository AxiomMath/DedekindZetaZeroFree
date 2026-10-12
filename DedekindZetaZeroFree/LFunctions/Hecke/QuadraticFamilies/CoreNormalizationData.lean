module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

structure NormalizedFamilyData {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) where
  bad : Ideal (𝓞 F)
  bad_ne_bot : bad ≠ ⊥
  original_dvd_bad : c ∣ bad
  index_dvd_conductor : ∀ a, Squarefree a → a ⊔ bad = ⊤ → a ∣ Q.cond a
  conductor_dvd_index_bad : ∀ a, Squarefree a → a ⊔ bad = ⊤ → Q.cond a ∣ a * bad

end DedekindZetaZeroFree.LargeSieve.Sieve
