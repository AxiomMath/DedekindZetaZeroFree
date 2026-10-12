module

public import DedekindZetaZeroFree.Arithmetic.Units.SUnitLagrangianComplements

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField

namespace DedekindZetaZeroFree
namespace SArithmeticData

variable {F : Type} [Field F] [NumberField F]

def weilSProduct (A : SArithmeticData F)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (x : A.G) : ℂ :=
  (∏ v : InfinitePlace F, wInf v (x.1 v)) *
    ∏ v : {v // v ∈ A.Sf}, wFin v (x.2 v)

def weilSCorrection (A : SArithmeticData F)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (x : A.G) : ℂ :=
  (A.weilSProduct wInf wFin x⁻¹)⁻¹

def WeilSStructuralLaws (A : SArithmeticData F)
    (H : A.V → A.V → Fˣ) (σ : F →+* ℂ)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ) : Prop :=
  (∀ v, wInf v 1 = 1) ∧ (∀ v, wFin v 1 = 1) ∧
  (∀ v a t, wInf v (a * t ^ 2) = wInf v a) ∧
  (∀ v a t, wFin v (a * t ^ 2) = wFin v a) ∧
  (∀ x : A.V, H x x = 1) ∧
  (∀ x y : A.G,
    A.weilSProduct wInf wFin x * A.weilSProduct wInf wFin y =
      σ ((H (QuotientGroup.mk' A.sixthPowers x)
        (QuotientGroup.mk' A.sixthPowers y) : Fˣ) : F) ^ 3 *
        A.weilSProduct wInf wFin (x * y))

private theorem weilSProduct_one (A : SArithmeticData F)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (hInf : ∀ v, wInf v 1 = 1) (hFin : ∀ v, wFin v 1 = 1) :
    A.weilSProduct wInf wFin 1 = 1 := by
  simp [weilSProduct, hInf, hFin]

private theorem weilSProduct_mul_sq (A : SArithmeticData F)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (hInf : ∀ v a t, wInf v (a * t ^ 2) = wInf v a)
    (hFin : ∀ v a t, wFin v (a * t ^ 2) = wFin v a) (x t : A.G) :
    A.weilSProduct wInf wFin (x * t ^ 2) = A.weilSProduct wInf wFin x := by
  simp [weilSProduct, hInf, hFin]

theorem weilSProduct_sign_of_structural_laws (A : SArithmeticData F)
    (H : A.V → A.V → Fˣ) (σ : F →+* ℂ)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (h : A.WeilSStructuralLaws H σ wInf wFin) (x : A.G) :
    A.weilSProduct wInf wFin x = 1 ∨ A.weilSProduct wInf wFin x = -1 := by
  rcases h with ⟨hInf, hFin, hInfSq, hFinSq, hAlt, hMul⟩
  have hSq : A.weilSProduct wInf wFin (x * x) = 1 := by
    simpa only [one_mul, pow_two] using
      (weilSProduct_mul_sq A wInf wFin hInfSq hFinSq 1 x).trans
        (weilSProduct_one A wInf wFin hInf hFin)
  apply sq_eq_one_iff.mp
  simpa [pow_two, hAlt, hSq] using hMul x x

set_option maxHeartbeats 1000000 in
private theorem weilSProduct_eq_of_mk_eq (A : SArithmeticData F)
    (H : A.V → A.V → Fˣ) (σ : F →+* ℂ)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (h : A.WeilSStructuralLaws H σ wInf wFin) (x y : A.G)
    (heq : QuotientGroup.mk' A.sixthPowers x = QuotientGroup.mk' A.sixthPowers y) :
    A.weilSProduct wInf wFin x = A.weilSProduct wInf wFin y := by
  obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' A.sixthPowers).mp heq
  obtain ⟨t, rfl⟩ := hz
  change A.weilSProduct wInf wFin x = A.weilSProduct wInf wFin (x * t ^ 6)
  rw [show t ^ (6 : ℕ) = (t ^ 3) ^ 2 by rw [← pow_mul]]
  exact (weilSProduct_mul_sq A wInf wFin h.2.2.1 h.2.2.2.1 x (t ^ 3)).symm

set_option maxHeartbeats 1500000 in

theorem exists_weilBCharacter_of_structural_laws (A : SArithmeticData F)
    (H : A.V → A.V → Fˣ) (σ : F →+* ℂ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (h : A.WeilSStructuralLaws H σ wInf wFin) :
    ∃ c : B →* ℂ,
      (∀ b : B, c b = 1 ∨ c b = -1) ∧
      (∀ (x : A.G) (hx : QuotientGroup.mk' A.sixthPowers x ∈ B),
        c ⟨QuotientGroup.mk' A.sixthPowers x, hx⟩ =
          A.weilSCorrection wInf wFin x) := by
  classical
  let r : A.V → A.G := fun v => (QuotientGroup.mk'_surjective A.sixthPowers v).choose
  have hr (v : A.V) : QuotientGroup.mk' A.sixthPowers (r v) = v :=
    (QuotientGroup.mk'_surjective A.sixthPowers v).choose_spec
  let W : A.V → ℂ := fun v => A.weilSProduct wInf wFin (r v)
  have hW (x : A.G) : W (QuotientGroup.mk' A.sixthPowers x) =
      A.weilSProduct wInf wFin x :=
    weilSProduct_eq_of_mk_eq A H σ wInf wFin h _ _ (hr _)
  have hWone : W 1 = 1 := by
    simpa only [map_one] using (hW 1).trans (weilSProduct_one A wInf wFin h.1 h.2.1)
  have hWmul (b d : B) : W ((b : A.V) * (d : A.V)) = W b * W d := by
    have hm := h.2.2.2.2.2 (r b) (r d)
    rw [hr, hr, hB.2.1 _ b.property _ d.property] at hm
    have hrep : W ((b : A.V) * (d : A.V)) =
        A.weilSProduct wInf wFin (r b * r d) := by
      simpa only [map_mul, hr] using hW (r b * r d)
    simpa only [W, Units.val_one, map_one, one_pow, one_mul, ← hrep] using hm.symm
  let c : B →* ℂ := {
    toFun := fun b => (W ((b⁻¹ : B) : A.V))⁻¹
    map_one' := by simp [hWone]
    map_mul' := by
      intro b d
      change (W (((b * d)⁻¹ : B) : A.V))⁻¹ =
        (W ((b⁻¹ : B) : A.V))⁻¹ * (W ((d⁻¹ : B) : A.V))⁻¹
      rw [mul_inv_rev, Subgroup.coe_mul, hWmul]
      exact mul_inv_rev (W (d⁻¹ : B)) (W (b⁻¹ : B)) }
  refine ⟨c, ?_, ?_⟩
  · intro b
    rcases weilSProduct_sign_of_structural_laws A H σ wInf wFin h (r ((b⁻¹ : B) : A.V))
      with hb | hb
    · exact Or.inl (by
        change (A.weilSProduct wInf wFin (r ((b⁻¹ : B) : A.V)))⁻¹ = 1
        rw [hb, inv_one])
    · exact Or.inr (by
        change (A.weilSProduct wInf wFin (r ((b⁻¹ : B) : A.V)))⁻¹ = -1
        rw [hb, inv_neg, inv_one])
  · intro x hx
    change (W ((QuotientGroup.mk' A.sixthPowers x)⁻¹))⁻¹ =
      (A.weilSProduct wInf wFin x⁻¹)⁻¹
    rw [← map_inv, hW]

end SArithmeticData
end DedekindZetaZeroFree

end
