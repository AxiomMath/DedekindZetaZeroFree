module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDiskBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectEuler

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem idealLSeries_ne_zero_of_one_lt (ω : Detector.PrimitiveFrequencyCharacter F) (s : ℂ)
    (hs : 1 < s.re) : Detector.idealLSeries F ω.character s ≠ 0 := by
  obtain ⟨_, -, hf⟩ := ReciprocalLogDiskAux.euler_log_facts F
  obtain ⟨-, hexp, -⟩ := hf ω
  rw [← hexp s hs]
  exact Complex.exp_ne_zero _

theorem IsLZero.re_le_one {ω : Detector.PrimitiveFrequencyCharacter F} {s : ℂ}
    (h : IsLZero ω s) : s.re ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨-, g, -, hg, hgs⟩ := h
  exact idealLSeries_ne_zero_of_one_lt ω s hlt (by rw [← hg s hlt]; exact hgs)

end

end DedekindZetaZeroFree.Quantitative.DetectEuler
