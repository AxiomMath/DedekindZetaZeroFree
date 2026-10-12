module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWordOperators
public import DedekindZetaZeroFree.Eisenstein.Residues.SpanAutomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.SharedSource
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming finite_level_exists → finite_level_exists
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem nativeSmooth_finset_sum {ι : Type*} (I : Finset ι)
    (u : ι → KPLiteralRaw.Functions F ζ hζ)
    (hu : ∀ i ∈ I, KPLiteralRaw.Smooth F ζ hζ (u i)) :
    KPLiteralRaw.Smooth F ζ hζ (∑ i ∈ I, u i) := by
  obtain ⟨U⟩ := finite_level_exists F ζ hζ
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using smooth_zero F ζ hζ U
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact smooth_add F ζ hζ _ _ (hu i (Finset.mem_insert_self i I))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem actualRightWord_finset_sum {ι : Type*} (I : Finset ι)
    (u : ι → KPLiteralRaw.Functions F ζ hζ)
    (hu : ∀ i ∈ I, KPLiteralRaw.Smooth F ζ hζ (u i))
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w (∑ i ∈ I, u i) =
      ∑ i ∈ I, KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w (u i) := by
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    induction w with
    | nil => rfl
    | cons i w ih =>
      simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, ih]
      funext g
      exact deriv_const _ _
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      actualRightWord_add _ _ (hu i (Finset.mem_insert_self i I))
        (nativeSmooth_finset_sum I u (fun j hj => hu j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]

end DedekindZetaZeroFree.SharedSource

end
