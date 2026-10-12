module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DedekindZetaZeroFree.FiniteProductDensity

theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [MeasurePreserving.lintegral_map_equiv (fun b => ∏ i, f i (b i))
        ((MeasurableEquiv.piFinSuccAbove E 0).symm)
        ((measurePreserving_piFinSuccAbove μ 0).symm)]
      simp only [Fin.prod_univ_succAbove _ 0, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove]
      have hgm : Measurable (fun y : (j : Fin n) → E (Fin.succAbove 0 j) =>
          ∏ x, f (Fin.succAbove 0 x) (y x)) := by
        simpa using Finset.measurable_prod (Finset.univ : Finset (Fin n))
          (fun i _ => (hf (Fin.succAbove 0 i)).comp (measurable_pi_apply i))
      rw [lintegral_prod_mul (hf 0).aemeasurable hgm.aemeasurable,
        ← n_ih (fun i => hf (Fin.succAbove 0 i))]

theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← MeasurePreserving.lintegral_comp_emb (measurePreserving_piCongrLeft μ e)
    (MeasurableEquiv.measurableEmbedding _) (fun b => ∏ i, f i (b i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    lintegral_fin_nat_prod_eq_prod (fun i => hf (e i))]

theorem lintegral_fintype_prod_eq_prod' {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  choose g hgm hg using fun i => hf i
  have hpi : (fun x : (i : ι) → E i => ∏ i, f i (x i)) =ᵐ[Measure.pi μ]
      fun x => ∏ i, g i (x i) := by
    have h := Measure.ae_eq_pi (μ := μ) (f := f) (f' := g) hg
    filter_upwards [h] with x hx
    exact Finset.prod_congr rfl fun i _ => congrFun hx i
  rw [lintegral_congr_ae hpi,
    lintegral_fintype_prod_eq_prod (fun i => hgm i)]
  exact Finset.prod_congr rfl fun i _ => lintegral_congr_ae (hg i).symm

end DedekindZetaZeroFree.FiniteProductDensity

end
