module

public import DedekindZetaZeroFree.Metaplectic.Weil.GlobalPhaseExtension

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem finiteQuadraticStabilizes_free (A : SArithmeticData F) :
    ∀ (v : {v // v ∈ A.Sf}) (a : (v.val.adicCompletion F)ˣ),
      A.FiniteQuadraticStabilizes v.val a :=
  fun v a => A.finiteQuadratic_stabilizes v.val a

theorem finiteGamma_one_ne_zero_free (A : SArithmeticData F) :
    ∀ v : {v // v ∈ A.Sf}, A.finiteGamma v.val 1 ≠ 0 := by
  intro v h
  have hv := A.norm_finiteGamma v.val 1
  rw [h, norm_zero] at hv
  norm_num at hv

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
