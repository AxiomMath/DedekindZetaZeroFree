module

public import DedekindZetaZeroFree.Arithmetic.Units.FundamentalDomainIntegration

@[expose] public section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Port of `LeanPool/Odlyzko/CompletedZeta/UnitSlabTranslation.lean`,
`UnitSlabRadial.lean`, and `UnitSlabRadialIntegral.lean` from
https://github.com/LeanPool/lean-pool at exact revision
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3, ported to rc2).
Original copyright and author attribution are retained above. Released under
Apache 2.0; full license: repository root `LICENSE`.
Source changes are imports, module visibility syntax, and namespace.
-/

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units Set
  dirichletUnitTheorem

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open DedekindZetaZeroFree.Theta
open mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open Classical in

noncomputable def unitCoordinateShiftHom :
    ({w : InfinitePlace K // w ≠ w₀} → ℤ) →+
      mixedEmbedding.realSpace K where
  toFun := unitCoordinateShift
  map_zero' := by
    ext w
    by_cases hw : w = w₀ <;> simp [unitCoordinateShift, hw]
  map_add' z z' := by
    ext w
    by_cases hw : w = w₀ <;> simp [unitCoordinateShift, hw]

open Classical in
@[simp]
theorem unitCoordinateShiftHom_apply
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitCoordinateShiftHom (K := K) z = unitCoordinateShift z :=
  rfl

open Classical in

noncomputable def unitCoordinateLattice :
    AddSubgroup (mixedEmbedding.realSpace K) :=
  (unitCoordinateShiftHom (K := K)).range

open Classical in
theorem unitCoordinateShift_mem_lattice
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitCoordinateShift z ∈ unitCoordinateLattice (K := K) :=
  ⟨z, rfl⟩

open Classical in
noncomputable instance countable_unitCoordinateLattice :
    Countable (unitCoordinateLattice (K := K)) :=
  Function.Surjective.countable
    (f := fun z : {w : InfinitePlace K // w ≠ w₀} → ℤ ↦
      (⟨unitCoordinateShift z, unitCoordinateShift_mem_lattice z⟩ :
        unitCoordinateLattice (K := K)))
    (by
      intro g
      obtain ⟨z, hz⟩ := g.prop
      refine ⟨z, Subtype.ext ?_⟩
      simpa using hz)

open Classical in

def unitAngularParamSet (K : Type*) [Field K] [NumberField K] :
    Set ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  Set.univ.pi fun _ ↦ Ico 0 1

open Classical in
theorem measurableSet_unitAngularParamSet :
    MeasurableSet (unitAngularParamSet K) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

open Classical in

def unitRadialAngularEquiv :
    mixedEmbedding.realSpace K ≃ᵐ
      (ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ)) where
  toFun y := (y w₀, fun w ↦ y w)
  invFun p w := if hw : w = w₀ then p.1 else p.2 ⟨w, hw⟩
  left_inv y := by
    ext w
    by_cases hw : w = w₀ <;> simp [hw]
  right_inv p := by
    rcases p with ⟨a, u⟩
    apply Prod.ext
    · simp
    · funext w
      simp [w.prop]
  measurable_toFun :=
    (measurable_pi_apply w₀).prodMk (measurable_pi_lambda fun w ↦ measurable_pi_apply w.val)
  measurable_invFun := by
    apply measurable_pi_lambda
    intro w
    change Measurable (fun p : ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ) ↦
      if hw : w = w₀ then p.1 else p.2 ⟨w, hw⟩)
    by_cases hw : w = w₀
    · simpa [hw] using
        (measurable_fst : Measurable (fun p : ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ) ↦ p.1))
    · simpa only [dif_neg hw, Function.comp_def] using
        ((measurable_pi_apply (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀})).comp
          (measurable_snd : Measurable (fun p : ℝ × ({w : InfinitePlace K // w ≠ w₀} → ℝ) ↦ p.2)))

open Classical in

def unitSlabCoordinates (a : ℝ) (u : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.realSpace K :=
  (unitRadialAngularEquiv (K := K)).symm (a, u)

open Classical in
@[simp] theorem unitSlabCoordinates_apply_w₀
    (a : ℝ) (u : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    unitSlabCoordinates a u w₀ = a := by
  simp [unitSlabCoordinates, unitRadialAngularEquiv]

open Classical in
@[simp] theorem unitSlabCoordinates_apply_ne
    (a : ℝ) (u : {w : InfinitePlace K // w ≠ w₀} → ℝ)
    (w : {w : InfinitePlace K // w ≠ w₀}) :
    unitSlabCoordinates a u w = u w := by
  simp [unitSlabCoordinates, unitRadialAngularEquiv, w.prop]

open Classical in
theorem measurePreserving_unitRadialAngularEquiv :
    MeasurePreserving (unitRadialAngularEquiv (K := K)) volume
      ((volume : Measure ℝ).prod
        (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) := by
  letI : Fintype {w : InfinitePlace K // w = w₀} := Unique.fintype
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
    (fun w ↦ w = w₀)
  have he := volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
    (fun w ↦ w = w₀)
  rw [Measure.volume_eq_prod] at he
  have hf := (volume_preserving_funUnique {w : InfinitePlace K // w = w₀} ℝ).prod
    (MeasurePreserving.id (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ)))
  have he' : MeasurePreserving e volume
      ((volume : Measure ({w : InfinitePlace K // w = w₀} → ℝ)).prod
        (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) := by
    convert he using 1 <;> congr 4 <;> exact Subsingleton.elim _ _
  have hdefault : (default : {w : InfinitePlace K // w = w₀}).val = w₀ :=
    (default : {w : InfinitePlace K // w = w₀}).prop
  simpa [unitRadialAngularEquiv, e, Function.comp_def,
    MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
    MeasurableEquiv.piUnique, Equiv.piEquivPiSubtypeProd, Prod.map, hdefault] using hf.comp he'

open Classical in
theorem unitRadialAngularEquiv_image_radialSlab (s : Set ℝ) :
    (unitRadialAngularEquiv (K := K)) ''
      (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}) =
        s ×ˢ unitAngularParamSet K := by
  rw [MeasurableEquiv.image_eq_preimage_symm]
  ext p
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod]
  change ((unitSlabCoordinates p.1 p.2 ∈ unitFundamentalParamSet K) ∧
    unitSlabCoordinates p.1 p.2 w₀ ∈ s) ↔ _
  rw [unitSlabCoordinates_apply_w₀, mem_unitFundamentalParamSet_iff]
  have hunit : (∀ w : InfinitePlace K, w ≠ w₀ →
      unitSlabCoordinates p.1 p.2 w ∈ Ico (0 : ℝ) 1) ↔ p.2 ∈ unitAngularParamSet K := by
    constructor
    · intro h
      change ∀ w ∈ Set.univ, p.2 w ∈ Ico (0 : ℝ) 1
      intro w _
      simpa using h w w.prop
    · intro h w hw
      have h' : ∀ i : {w : InfinitePlace K // w ≠ w₀}, p.2 i ∈ Ico (0 : ℝ) 1 := by
        simpa [unitAngularParamSet] using h
      simpa [unitSlabCoordinates, unitRadialAngularEquiv, hw] using h' ⟨w, hw⟩
  rw [hunit, and_comm]

open Classical in

theorem integrableOn_radialSlab_iff
    {E : Type*} [NormedAddCommGroup E]
    (f : mixedEmbedding.realSpace K → E) (s : Set ℝ) :
    IntegrableOn f (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}) ↔
      IntegrableOn (fun p ↦ unitSlabCoordinates (K := K) p.1 p.2 |> f)
        (s ×ˢ unitAngularParamSet K)
        ((volume : Measure ℝ).prod
          (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) := by
  let e := unitRadialAngularEquiv (K := K)
  have he := measurePreserving_unitRadialAngularEquiv (K := K)
  have hpre : e.symm ⁻¹' (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}) =
      s ×ˢ unitAngularParamSet K := by
    rw [← MeasurableEquiv.image_eq_preimage_symm]
    exact unitRadialAngularEquiv_image_radialSlab s
  have h := (he.symm e).integrableOn_comp_preimage e.symm.measurableEmbedding
    (f := f) (s := unitFundamentalParamSet K ∩ {y | y w₀ ∈ s})
  rw [hpre] at h
  exact h.symm

open Classical in

theorem setIntegral_radialSlab_eq_radialAngular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E) (s : Set ℝ)
    (hf : IntegrableOn f (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s})) :
    (∫ y in unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}, f y) =
      ∫ a in s, ∫ u in unitAngularParamSet K, f (unitSlabCoordinates a u) := by
  let e := unitRadialAngularEquiv (K := K)
  have he := measurePreserving_unitRadialAngularEquiv (K := K)
  have hchange := he.setIntegral_image_emb e.measurableEmbedding
    (fun p ↦ f (e.symm p)) (unitFundamentalParamSet K ∩ {y | y w₀ ∈ s})
  rw [unitRadialAngularEquiv_image_radialSlab] at hchange
  change (∫ p in s ×ˢ unitAngularParamSet K, f (e.symm p)
    ∂(volume : Measure ℝ).prod (volume : Measure ({w : InfinitePlace K // w ≠ w₀} → ℝ))) =
    (∫ y in unitFundamentalParamSet K ∩ {y | y w₀ ∈ s}, f (e.symm (e y))) at hchange
  simp only [MeasurableEquiv.symm_apply_apply] at hchange
  rw [← hchange]
  exact setIntegral_prod (fun p ↦ f (e.symm p)) ((integrableOn_radialSlab_iff f s).mp hf)

open Classical in

theorem setIntegral_unitFundamentalParamSet_eq_radialAngular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : IntegrableOn f (unitFundamentalParamSet K)) :
    (∫ y in unitFundamentalParamSet K, f y) =
      ∫ a : ℝ, ∫ u in unitAngularParamSet K, f (unitSlabCoordinates a u) := by
  simpa using setIntegral_radialSlab_eq_radialAngular f Set.univ (by simpa using hf)

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
