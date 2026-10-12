module

public import DedekindZetaZeroFree.LFunctions.Tate.Local.AnnularFourierMellin
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalSchwartzInversion

@[expose] public section

noncomputable section

open scoped NumberField Classical

open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

variable (F : Type) [Field F] [NumberField F]

instance unitShellFourierAdicCompletionMeasurableSpace (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

instance unitShellFourierAdicCompletionBorelSpace (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

end DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

end
