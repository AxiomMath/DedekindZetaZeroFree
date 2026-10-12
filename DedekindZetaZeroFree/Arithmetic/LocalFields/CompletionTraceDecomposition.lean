module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.FinitePlacesAbovePrime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

theorem adicCompletion_trace_eq_sum
    (K : Type*) (L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : HeightOneSpectrum (𝓞 K)) (x : L) :
    letI : Fintype (FinitePlacesAbove K L w) := finitePlacesAboveFintype K L w
    letI : ∀ W : FinitePlacesAbove K L w,
        Algebra (w.adicCompletion K) (W.val.adicCompletion L) :=
      fun W => (finitePlaceAdicCompletionMap K L w W).toAlgebra
    algebraMap K (w.adicCompletion K) (Algebra.trace K L x) =
      ∑ W : FinitePlacesAbove K L w,
        Algebra.trace (w.adicCompletion K) (W.val.adicCompletion L)
          (algebraMap L (W.val.adicCompletion L) x) := by
  letI : Fintype (FinitePlacesAbove K L w) := finitePlacesAboveFintype K L w
  letI : ∀ W : FinitePlacesAbove K L w,
      Algebra (w.adicCompletion K) (W.val.adicCompletion L) :=
    fun W => (finitePlaceAdicCompletionMap K L w W).toAlgebra
  letI : ∀ W : FinitePlacesAbove K L w,
      Module.Finite (w.adicCompletion K) (W.val.adicCompletion L) :=
    fun W => finitePlaceAdicCompletionMap_moduleFinite K L w W
  let eRing := finitePlaceTensorRingEquivAboveAdic (K := K) (L := L) w
  let e : AlgEquiv (w.adicCompletion K) (w.adicCompletion K ⊗[K] L)
      (∀ W : FinitePlacesAbove K L w, W.val.adicCompletion L) :=
    AlgEquiv.ofRingEquiv (R := w.adicCompletion K) (f := eRing) fun a => by
      funext W
      rw [Algebra.TensorProduct.algebraMap_apply,
        finitePlaceTensorRingEquivAboveAdic_tmul, map_one, mul_one,
        Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
      rw [RingHom.algebraMap_toAlgebra]
  have h := ValuationTheory.Completion.baseChange_pi_trace_eq_sum
    (K := K) (A := w.adicCompletion K) (L := L)
    (fun W : FinitePlacesAbove K L w => W.val.adicCompletion L) e x
  rw [h]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [show e (1 ⊗ₜ[K] x) W = algebraMap L (W.val.adicCompletion L) x from
    finitePlaceTensorRingEquivAboveAdic_tmul_one (K := K) (L := L) w W x]

end DedekindZetaZeroFree

end
