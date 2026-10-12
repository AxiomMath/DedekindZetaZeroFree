module

public import Mathlib
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralProductCRTDensity

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open NumberField IsDedekindDomain

abbrev finiteIntegralAdeles (F : Type*) [Field F] [NumberField F] :=
  (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F

def integralDiagonal (F : Type*) [Field F] [NumberField F] :
    𝓞 F →+* finiteIntegralAdeles F :=
  Pi.ringHom (fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F))

theorem integralCompletion_dense (F : Type*) [Field F] [NumberField F] :
    DenseRange (integralDiagonal F) := by
  exact denseRange_ringOfIntegers_integralDiagonal F

end
end DedekindZetaZeroFree
