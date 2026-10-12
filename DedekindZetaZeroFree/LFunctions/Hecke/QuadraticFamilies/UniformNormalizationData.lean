module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformConductorControl
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CoreNormalizationData

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

structure AllIndexNormalizedFamilyData {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    extends NormalizedFamilyData Q where
  original_ne_bot : c ≠ ⊥
  all_conductor_dvd : ∀ a, Squarefree a → a ⊔ c = ⊤ → Q.cond a ∣ a * bad
  all_index_dvd : ∀ a, Squarefree a → a ⊔ c = ⊤ → a ∣ Q.cond a * bad

end DedekindZetaZeroFree.LargeSieve.Sieve
