module

public import DedekindZetaZeroFree.Arithmetic.Units.TorsionFreeDecomposition

@[expose] public section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original sources: LeanPool/Odlyzko/CompletedZeta/IdealElementDecomposition.lean;
the signature-general prefix of ConeGaussianIntegral.lean;
the idealSetElement_injective lemma of ConeGaussianInterchange.lean; and
the idealSetIntNorm definition of FundamentalConeSeries.lean.
Modifications: renamed namespace, replaced local imports, removed rc3 module
visibility syntax, and ported decomposition proofs.
Full upstream Apache-2.0 license: LICENSE.
-/

noncomputable section

open Ideal IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Theta

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

def idealSetIntNorm (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : ℕ :=
  intNorm (idealSetEquiv K J a).val

noncomputable def idealSetElement
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : K :=
  (preimageOfMemIntegerSet (idealSetEquiv K J a).val : 𝓞 K)

theorem idealSetElement_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetElement K J a ≠ 0 := by
  rw [idealSetElement]
  simp

theorem absNorm_idealSetElement
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    (((|Algebra.norm ℚ (idealSetElement K J a)| : ℚ) : ℝ)) =
      idealSetIntNorm K J a := by
  calc
    (((|Algebra.norm ℚ (idealSetElement K J a)| : ℚ) : ℝ)) =
        mixedEmbedding.norm (mixedEmbedding K (idealSetElement K J a)) := by simp
    _ = mixedEmbedding.norm (a : mixedSpace K) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]
    _ = idealSetIntNorm K J a := by
      rw [idealSetIntNorm, intNorm_idealSetEquiv_apply]

theorem idealSetElement_injective (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealSetElement K J) := by
  intro a b hab
  apply Subtype.ext
  calc
    (a : mixedSpace K) =
        mixedEmbedding K (idealSetElement K J a) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]
    _ = mixedEmbedding K (idealSetElement K J b) := congrArg _ hab
    _ = (b : mixedSpace K) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]

open Classical in

abbrev unitShiftIndex :=
  {w : InfinitePlace K // w ≠ w₀} → ℤ

open Classical in

abbrev nonzeroIdealElement (J : (Ideal (𝓞 K))⁰) :=
  {x : 𝓞 K // (x : 𝓞 K) ∈ (J : Ideal (𝓞 K)) ∧ x ≠ 0}

open Classical in

noncomputable def idealSetInteger
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : 𝓞 K :=
  preimageOfMemIntegerSet (idealSetEquiv K J a).val

open Classical in
theorem idealSetInteger_mem
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetInteger K J a ∈ (J : Ideal (𝓞 K)) := by
  exact (idealSetEquiv K J a).prop

open Classical in
theorem idealSetInteger_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetInteger K J a ≠ 0 := by
  exact mem_nonZeroDivisors_iff_ne_zero.mp
    (preimageOfMemIntegerSet (idealSetEquiv K J a).val).2

open Classical in
theorem idealSetInteger_injective (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealSetInteger K J) := by
  intro a b hab
  apply idealSetElement_injective K J
  exact congrArg (fun x : 𝓞 K ↦ (x : K)) hab

open Classical in

noncomputable def idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K → nonzeroIdealElement K J :=
  fun p ↦
    ⟨((fundamentalUnitForShift p.2)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J p.1,
      (J : Ideal (𝓞 K)).mul_mem_left _
        (idealSetInteger_mem K J p.1),
      mul_ne_zero (Units.ne_zero _) (idealSetInteger_ne_zero K J p.1)⟩

open Classical in
@[simp]
theorem idealElementDecompositionMap_coe
    (J : (Ideal (𝓞 K))⁰) (p : idealSet K J × unitShiftIndex K) :
    ((idealElementDecompositionMap K J p : 𝓞 K) : K) =
      (((fundamentalUnitForShift p.2)⁻¹ : (𝓞 K)ˣ) : K) *
        idealSetElement K J p.1 := by
  rfl

open Classical in
theorem injective_idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealElementDecompositionMap K J) := by
  rintro ⟨a, z⟩ ⟨a', z'⟩ h
  have hval := congrArg
    (fun t : nonzeroIdealElement K J ↦ (t : 𝓞 K)) h
  change
    ((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J a =
      ((fundamentalUnitForShift z')⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J a' at hval
  let v : (𝓞 K)ˣ :=
    fundamentalUnitForShift z' * (fundamentalUnitForShift z)⁻¹
  have haeq :
      (v : 𝓞 K) * idealSetInteger K J a =
        idealSetInteger K J a' := by
    calc
      (v : 𝓞 K) * idealSetInteger K J a =
          (fundamentalUnitForShift z' : 𝓞 K) *
            (((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
              idealSetInteger K J a) := by
        simp only [v, Units.val_mul]
        ring
      _ = (fundamentalUnitForShift z' : 𝓞 K) *
            (((fundamentalUnitForShift z')⁻¹ : (𝓞 K)ˣ) *
              idealSetInteger K J a') := congrArg _ hval
      _ = idealSetInteger K J a' := by simp
  have haembed :
      mixedEmbedding K ((idealSetInteger K J a : 𝓞 K) : K) =
        (a : mixedSpace K) := by
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  have haembed' :
      mixedEmbedding K ((idealSetInteger K J a' : 𝓞 K) : K) =
        (a' : mixedSpace K) := by
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  have hsmul : v • (a : mixedSpace K) = (a' : mixedSpace K) := by
    rw [unitSMul_smul]
    grind
  have hv : v ∈ torsion K :=
    (unit_smul_mem_iff_mem_torsion a.prop.1 v).mp
      (hsmul ▸ a'.prop.1)
  have hvshift :
      v = fundamentalUnitForShift (z' + -z) := by
    rw [fundamentalUnitForShift_add,
      fundamentalUnitForShift_neg]
  have hp :
      ((⟨v, hv⟩ : torsion K), (0 : unitShiftIndex K)) =
        (1, z' + -z) := by
    apply (unitDecompositionEquiv K).injective
    simp_all
  have : z' = z := by grind
  subst z'
  apply Prod.ext
  · apply idealSetInteger_injective K J
    exact mul_left_cancel₀ (Units.ne_zero _) hval
  · simp

open Classical in
theorem surjective_idealElementDecompositionMap
    (J : (Ideal (𝓞 K))⁰) :
    Function.Surjective (idealElementDecompositionMap K J) := by
  intro x
  have hxemb :
      mixedEmbedding K ((x : 𝓞 K) : K) ≠ 0 := by
    exact (map_ne_zero_iff (mixedEmbedding K)
      (mixedEmbedding_injective K)).mpr
        (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
  have hxnorm :
      mixedEmbedding.norm
          (mixedEmbedding K ((x : 𝓞 K) : K)) ≠ 0 :=
    (norm_eq_zero_iff'
      (Set.mem_range_self ((x : 𝓞 K) : K))).not.mpr hxemb
  obtain ⟨u, hu⟩ :=
    exists_unit_smul_mem hxnorm
  let a : idealSet K J :=
    ⟨u • mixedEmbedding K ((x : 𝓞 K) : K),
      mem_idealSet.mpr
        ⟨hu, ⟨(u : 𝓞 K) * x,
          (J : Ideal (𝓞 K)).mul_mem_left _ x.prop.1, by
            simp⟩⟩⟩
  have haInteger :
      idealSetInteger K J a = (u : 𝓞 K) * x := by
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
    change u • mixedEmbedding K ((x : 𝓞 K) : K) =
      mixedEmbedding K (((u : 𝓞 K) * x : 𝓞 K) : K)
    simp
  let p := (unitDecompositionEquiv K).symm u
  let ζ : torsion K := p.1
  let z : unitShiftIndex K := p.2
  have huDecomp :
      (ζ : (𝓞 K)ˣ) * fundamentalUnitForShift z = u := by
    have hp := (unitDecompositionEquiv K).apply_symm_apply u
    change unitDecompositionEquiv K (ζ, z) = u at hp
    simp_all
  have hζinv : ((ζ : (𝓞 K)ˣ)⁻¹) ∈ torsion K :=
    (torsion K).inv_mem ζ.prop
  let b : idealSet K J :=
    ⟨((ζ : (𝓞 K)ˣ)⁻¹) • (a : mixedSpace K),
      mem_idealSet.mpr
        ⟨torsion_smul_mem_of_mem a.prop.1 hζinv,
          ⟨(↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
              idealSetInteger K J a,
            (J : Ideal (𝓞 K)).mul_mem_left _
              (idealSetInteger_mem K J a), by
              rw [unitSMul_smul]
              push_cast
              rw [map_mul]
              rw [idealSetInteger,
                mixedEmbedding_preimageOfMemIntegerSet,
                idealSetEquiv_apply]⟩⟩⟩
  have hbInteger :
      idealSetInteger K J b =
        (↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          idealSetInteger K J a := by
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
    change ((ζ : (𝓞 K)ˣ)⁻¹) • (a : mixedSpace K) =
      mixedEmbedding K
        ((((↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          idealSetInteger K J a : 𝓞 K) : K))
    rw [unitSMul_smul]
    push_cast
    rw [map_mul]
    rw [idealSetInteger,
      mixedEmbedding_preimageOfMemIntegerSet,
      idealSetEquiv_apply]
  refine ⟨(b, z), ?_⟩
  apply Subtype.ext
  change
    ((fundamentalUnitForShift z)⁻¹ : (𝓞 K)ˣ) *
        idealSetInteger K J b = x
  rw [hbInteger, haInteger, ← huDecomp]
  calc
    (↑((fundamentalUnitForShift z)⁻¹) : 𝓞 K) *
        ((↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          (((ζ : (𝓞 K)ˣ) : 𝓞 K) *
            (fundamentalUnitForShift z : 𝓞 K) * x)) =
      ((↑((fundamentalUnitForShift z)⁻¹) : 𝓞 K) *
          (↑((ζ : (𝓞 K)ˣ)⁻¹) : 𝓞 K) *
          ((ζ : (𝓞 K)ˣ) : 𝓞 K) *
          (fundamentalUnitForShift z : 𝓞 K)) * x := by ring
    _ = x := by simp

open Classical in

noncomputable def idealElementDecompositionEquiv
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K ≃ nonzeroIdealElement K J :=
  Equiv.ofBijective (idealElementDecompositionMap K J)
    ⟨injective_idealElementDecompositionMap K J,
      surjective_idealElementDecompositionMap K J⟩

open Classical in
@[simp]
theorem idealElementDecompositionEquiv_apply
    (J : (Ideal (𝓞 K))⁰)
    (p : idealSet K J × unitShiftIndex K) :
    idealElementDecompositionEquiv K J p =
      idealElementDecompositionMap K J p := by
  rfl

open Classical in

def unitShiftNegEquiv : unitShiftIndex K ≃ unitShiftIndex K where
  toFun z := -z
  invFun z := -z
  left_inv z := neg_neg z
  right_inv z := neg_neg z

open Classical in

noncomputable def idealElementMulDecompositionEquiv
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J × unitShiftIndex K ≃ nonzeroIdealElement K J :=
  (Equiv.prodCongr (Equiv.refl _) (unitShiftNegEquiv K)).trans
    (idealElementDecompositionEquiv K J)

open Classical in
@[simp]
theorem idealElementMulDecompositionEquiv_coe
    (J : (Ideal (𝓞 K))⁰)
    (p : idealSet K J × unitShiftIndex K) :
    (((idealElementMulDecompositionEquiv K J p :
        nonzeroIdealElement K J) : 𝓞 K) : K) =
      ((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) *
        idealSetElement K J p.1 := by
  change
    (((idealElementDecompositionEquiv K J (p.1, -p.2) :
        nonzeroIdealElement K J) : 𝓞 K) : K) = _
  simp

theorem countable_idealSet (J : (Ideal (𝓞 K))⁰) : Countable (idealSet K J) := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  exact (idealSetInteger_injective K J).countable

theorem countable_nonzeroIdealElement (J : (Ideal (𝓞 K))⁰) :
    Countable (nonzeroIdealElement K J) := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  infer_instance

end DedekindZetaZeroFree.Theta

end
