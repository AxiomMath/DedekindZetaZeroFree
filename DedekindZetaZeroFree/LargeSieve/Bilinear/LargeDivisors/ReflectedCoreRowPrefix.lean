module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEnvelopes

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem reflected_core_rows_subset (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hB : 1 ≤ B) :
    C.reflectedCoreRows B unit ⊆ Sieve.idealAdmissibleFinset F c (2 * B) := by
  intro r hr
  cases unit with
  | false =>
    have hm := (Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1
    exact (Sieve.mem_idealAdmissibleFinset F c (2 * B) r).mpr
      ⟨hm.1, hm.2.1, hm.2.2.2⟩
  | true =>
    have hr' : r = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp hr).1
    subst r
    exact (Sieve.top_mem_idealAdmissibleFinset_iff F c (2 * B)).mpr (by linarith)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows

end
