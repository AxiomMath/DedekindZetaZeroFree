module

public import DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases
public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.SchwartzQuadraticOperatorKernel

@[expose] public section

noncomputable section

open scoped NumberField Classical

open NumberField MeasureTheory

namespace DedekindZetaZeroFree.SArithmeticData

variable (F : Type) [Field F] [NumberField F]

instance adapterCompletionMeasurable (v : InfinitePlace F) :
    MeasurableSpace v.Completion := borel _

instance adapterCompletionBorel (v : InfinitePlace F) :
    BorelSpace v.Completion := ⟨rfl⟩

end DedekindZetaZeroFree.SArithmeticData

end
