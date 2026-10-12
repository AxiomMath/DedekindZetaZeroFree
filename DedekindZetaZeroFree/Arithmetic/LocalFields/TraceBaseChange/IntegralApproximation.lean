module

public import DedekindZetaZeroFree.Adeles.Approximation.IntegralLocalCongruences
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralCompletionCRT
public import ClassFieldTheory.All

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TraceBaseChange

variable (F : Type*) [Field F] [NumberField F]

theorem integralProduct_dense :
    DenseRange (DedekindZetaZeroFree.integralDiagonal F) := by
  exact DedekindZetaZeroFree.integralCompletion_dense F

end DedekindZetaZeroFree.TraceBaseChange

end
