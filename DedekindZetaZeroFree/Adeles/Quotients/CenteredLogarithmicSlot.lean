module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPMsFixedHaar

theorem single_slot_mean_zero
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (w : NumberField.InfinitePlace F) (t : ℝ) :
    (fun i => (if KPCusp.complexPlace F i = w then t else 0) -
      t / (KPCuspLogShape.dimension F : ℝ)) ∈
        KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F) := by

  haveI : IsEmpty {v : NumberField.InfinitePlace F // v.IsReal} := by
    rw [← Fintype.card_eq_zero_iff]
    exact hF
  have hw : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
    (fun h => isEmptyElim (⟨w, h⟩ : {v : NumberField.InfinitePlace F // v.IsReal}))
  have hdim : KPCuspLogShape.dimension F ≠ 0 := by
    haveI : Nonempty {v : NumberField.InfinitePlace F // v.IsComplex} := ⟨⟨w, hw⟩⟩
    have hc : Fintype.card {v : NumberField.InfinitePlace F // v.IsComplex} ≠ 0 :=
      Fintype.card_ne_zero
    simpa [KPCuspLogShape.dimension, NumberField.InfinitePlace.nrComplexPlaces] using hc
  have hd : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdim

  let e : {v : NumberField.InfinitePlace F // v.IsComplex} ≃ Fin (KPCuspLogShape.dimension F) :=
    Fintype.equivFin _
  have hcp : ∀ i : Fin (KPCuspLogShape.dimension F), KPCusp.complexPlace F i = (e.symm i).val :=
    fun i => rfl
  have hinj : Function.Injective (KPCusp.complexPlace F) := by
    intro i j hij
    rw [hcp i, hcp j] at hij
    have h1 : e.symm i = e.symm j := Subtype.ext hij
    exact e.symm.injective h1
  have hi₀ : KPCusp.complexPlace F (e ⟨w, hw⟩) = w := by
    rw [hcp, Equiv.symm_apply_apply]

  have hsum1 : ∑ i, (if KPCusp.complexPlace F i = w then t else 0) = t := by
    have h : ∑ i, (if KPCusp.complexPlace F i = w then t else 0) =
        (if KPCusp.complexPlace F (e ⟨w, hw⟩) = w then t else 0) :=
      Finset.sum_eq_single (e ⟨w, hw⟩)
        (fun i _ hi => by
          have hne : KPCusp.complexPlace F i ≠ w :=
            fun hh => hi (hinj (hh.trans hi₀.symm))
          rw [if_neg hne])
        (fun hmem => absurd (Finset.mem_univ _) hmem)
    rw [h, hi₀, if_pos rfl]

  have hsum2 : ∑ i : Fin (KPCuspLogShape.dimension F),
      t / (KPCuspLogShape.dimension F : ℝ) = t := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    exact div_mul_cancel₀ t hd
  rw [KPCuspLogShape.hyperplane, LinearMap.mem_ker]
  show (∑ i, ((if KPCusp.complexPlace F i = w then t else 0) -
      t / (KPCuspLogShape.dimension F : ℝ))) = 0
  rw [Finset.sum_sub_distrib, hsum1, hsum2, sub_self]

end DedekindZetaZeroFree.KPMsFixedHaar

end
