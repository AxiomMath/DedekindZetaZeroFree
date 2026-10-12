module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Coinvariants

@[expose] public section

noncomputable section
open scoped TensorProduct
namespace DedekindZetaZeroFree.KPKirillovFiniteTensorProve

variable {R : Type*} [CommRing R] {I : Type*} [Fintype I]
  {S : I → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
  {E : Type*} [AddCommGroup E] [Module R E]
  {G : Type*} [Monoid G]

theorem slot_relationSpan_eq_top [DecidableEq I] (i : I) (ρ : Representation R G (S i))
    (σ : Representation R G ((⨂[R] j, S j) ⊗[R] E))
    (hσ : ∀ g f e, σ g (PiTensorProduct.tprod R f ⊗ₜ[R] e) =
      PiTensorProduct.tprod R (Function.update f i (ρ g (f i))) ⊗ₜ[R] e)
    (hρ : Representation.Coinvariants.ker ρ = ⊤) :
    Representation.Coinvariants.ker σ = ⊤ := by
  classical
  let Q := Representation.Coinvariants.ker σ
  have hpure (f : ∀ j, S j) (e : E) :
      PiTensorProduct.tprod R f ⊗ₜ[R] e ∈ Q := by
    let L : S i →ₗ[R] (⨂[R] j, S j) ⊗[R] E :=
      ((TensorProduct.mk R (⨂[R] j, S j) E).flip e).comp
        ((PiTensorProduct.tprod R).toLinearMap f i)
    have hL (x : S i) : L x =
        PiTensorProduct.tprod R (Function.update f i x) ⊗ₜ[R] e := rfl
    have hcomm (g : G) (x : S i) : σ g (L x) = L (ρ g x) := by
      rw [hL, hσ, hL]
      simp only [Function.update_self, Function.update_idem]
    have hle : Representation.Coinvariants.ker ρ ≤ Q.comap L := by
      apply Submodule.span_le.mpr
      rintro x ⟨⟨g, y⟩, rfl⟩
      change L (ρ g y - y) ∈ Q
      rw [map_sub, ← hcomm]
      exact Representation.Coinvariants.sub_mem_ker g (L y)
    have hx : f i ∈ Representation.Coinvariants.ker ρ := by rw [hρ]; trivial
    have hm := hle hx
    change L (f i) ∈ Q at hm
    simpa only [hL, Function.update_eq_self] using hm
  apply eq_top_iff.mpr
  suffices hall : ∀ x, x ∈ Q from fun x _ => hall x
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact Q.zero_mem
  | tmul f e =>
    induction f using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [TensorProduct.smul_tmul]
      exact hpure f (r • e)
    | add a b ha hb =>
      rw [TensorProduct.add_tmul]
      exact Q.add_mem ha hb
  | add a b ha hb => exact Q.add_mem ha hb

theorem relationSpan_eq_top_of_surjective
    {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (ρ : Representation R G A) (σ : Representation R G B) (L : A →ₗ[R] B)
    (hL : Function.Surjective L) (hcomm : ∀ g x, L (ρ g x) = σ g (L x))
    (hρ : Representation.Coinvariants.ker ρ = ⊤) :
    Representation.Coinvariants.ker σ = ⊤ := by
  have hle : Representation.Coinvariants.ker ρ ≤
      (Representation.Coinvariants.ker σ).comap L := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨g, y⟩, rfl⟩
    change L (ρ g y - y) ∈ Representation.Coinvariants.ker σ
    rw [map_sub, hcomm]
    exact Representation.Coinvariants.sub_mem_ker g (L y)
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨x, rfl⟩ := hL y
  apply hle
  rw [hρ]
  trivial

end DedekindZetaZeroFree.KPKirillovFiniteTensorProve

end
