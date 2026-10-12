module

public import DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField Pointwise

theorem frobeniusQuotientOrder
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hw : W.asIdeal.LiesOver p.asIdeal) :
    orderOf
        ((QuotientGroup.mk' (Ideal.inertia (L ≃ₐ[K] L) W.asIdeal))
          (ClassFieldTheory.arithmeticFrobeniusAt (K := K) W)) =
        W.asIdeal.inertiaDeg (𝓞 K) ∧
      Nat.card ((L ≃ₐ[K] L) ⧸ Ideal.inertia (L ≃ₐ[K] L) W.asIdeal) =
        (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L)).card *
          W.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  let P := p.asIdeal
  let Q := W.asIdeal
  let G := L ≃ₐ[K] L
  let g : G := ClassFieldTheory.arithmeticFrobeniusAt (K := K) W
  letI : Q.LiesOver P := hw
  letI : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P
  letI : Field ((𝓞 L) ⧸ Q) := Ideal.Quotient.field Q
  letI : Finite ((𝓞 K) ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  letI : Finite ((𝓞 L) ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient W.ne_bot
  letI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hg : IsArithFrobAt (𝓞 K) g Q :=
    IsArithFrobAt.arithFrobAt (𝓞 K) G Q
  let d : MulAction.stabilizer G Q := ⟨g, hg.mem_stabilizer⟩
  let φ := Ideal.Quotient.stabilizerHom Q P G
  have hφ : φ d = FiniteField.frobeniusAlgEquivOfAlgebraic
      ((𝓞 K) ⧸ P) ((𝓞 L) ⧸ Q) := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk Q (g • a) =
      Ideal.Quotient.mk Q a ^ Fintype.card ((𝓞 K) ⧸ P)
    have hQP : Q.under (𝓞 K) = P := hw.over.symm
    have h := hg.mk_apply a
    rw [hQP, Nat.card_eq_fintype_card] at h
    exact h
  have horder : orderOf ((QuotientGroup.mk' (Ideal.inertia G Q)) g) =
      orderOf (φ d) := by
    apply orderOf_eq_orderOf_iff.mpr
    intro n
    rw [← map_pow, ← map_pow]
    change ((g ^ n : G) : G ⧸ Ideal.inertia G Q) = 1 ↔ φ (d ^ n) = 1
    rw [QuotientGroup.eq_one_iff]
    change g ^ n ∈ Ideal.inertia G Q ↔ d ^ n ∈ φ.ker
    rw [Ideal.Quotient.ker_stabilizerHom]
    exact Ideal.coe_mem_inertia (I := Q) (σ := d ^ n)
  constructor
  · change orderOf ((QuotientGroup.mk' (Ideal.inertia G Q)) g) = Q.inertiaDeg (𝓞 K)
    rw [horder, hφ, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact (Ideal.inertiaDeg_eq_of_isMaximal P Q).symm
  · have hcount := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := G) P Q
    have hfinite : (P.primesOver (𝓞 L)).ncard =
        (IsDedekindDomain.primesOverFinset P (𝓞 L)).card := by
      rw [← IsDedekindDomain.coe_primesOverFinset p.ne_bot (𝓞 L), Set.ncard_coe_finset]
    rw [hfinite] at hcount
    have hindex := (Ideal.inertia G Q).card_mul_index
    rw [Subgroup.index_eq_card] at hindex
    change Nat.card (G ⧸ Ideal.inertia G Q) =
      (IsDedekindDomain.primesOverFinset P (𝓞 L)).card * Q.inertiaDeg (𝓞 K)
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Ideal.inertia G Q))
    calc
      Nat.card (Ideal.inertia G Q) * Nat.card (G ⧸ Ideal.inertia G Q) = Nat.card G := hindex
      _ = Nat.card (Ideal.inertia G Q) *
          ((IsDedekindDomain.primesOverFinset P (𝓞 L)).card * Q.inertiaDeg (𝓞 K)) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hcount.symm

end DedekindZetaZeroFree.AbelianQuotient
