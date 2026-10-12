module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCyclicity

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration

section Algebraic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {A : ι → Type*} (op : ∀ i, A i → Module.End ℂ (V i))

def tupleOperator (a : ∀ i, A i) : Module.End ℂ (PiTensorProduct ℂ V) :=
  PiTensorProduct.map (fun i => op i (a i))

def tupleOrbitSpan (v : ∀ i, V i) : Submodule ℂ (PiTensorProduct ℂ V) :=
  Submodule.span ℂ (Set.range (fun a => tupleOperator op a (PiTensorProduct.tprod ℂ v)))

private theorem tprod_mem_of_slot_spans (v x : ∀ i, V i)
    (hx : ∀ i, x i ∈ Submodule.span ℂ (Set.range (fun a => op i a (v i)))) :
    PiTensorProduct.tprod ℂ x ∈ tupleOrbitSpan op v := by
  let P (s : Finset ι) : Prop := ∀ y : ∀ i, V i,
    (∀ i ∈ s, y i ∈ Submodule.span ℂ (Set.range (fun a => op i a (v i)))) →
    (∀ i, i ∉ s → ∃ a, y i = op i a (v i)) →
    PiTensorProduct.tprod ℂ y ∈ tupleOrbitSpan op v
  have hP : ∀ s, P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy ho
      choose a ha using fun i => ho i (by simp)
      have he : y = fun i => op i (a i) (v i) := funext ha
      rw [he]
      exact Submodule.subset_span ⟨a, PiTensorProduct.map_tprod _ _⟩
    | @insert i s hi ih =>
      intro y hy ho
      have hyi := hy i (Finset.mem_insert_self i s)
      have hm : ∀ z ∈ Submodule.span ℂ (Set.range (fun a => op i a (v i))),
          PiTensorProduct.tprod ℂ (Function.update y i z) ∈ tupleOrbitSpan op v := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨a, rfl⟩ := hz
          apply ih
          · intro j hj
            rw [Function.update_of_ne (by intro h; subst j; exact hi hj)]
            exact hy j (Finset.mem_insert_of_mem hj)
          · intro j hj
            by_cases hji : j = i
            · subst j; exact ⟨a, by simp⟩
            · rw [Function.update_of_ne hji]
              exact ho j (by simpa [hji, hj])
        | zero =>
          rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (by simp)]
          exact Submodule.zero_mem _
        | add z u hz hu ihz ihu =>
          rw [(PiTensorProduct.tprod ℂ).map_update_add]
          exact Submodule.add_mem _ ihz ihu
        | smul c z hz ihz =>
          rw [(PiTensorProduct.tprod ℂ).map_update_smul]
          exact Submodule.smul_mem _ c ihz
      simpa only [Function.update_eq_self] using hm (y i) hyi
  apply hP Finset.univ x
  · exact fun i _ => hx i
  · intro i hi
    exact (hi (Finset.mem_univ i)).elim

theorem tupleOrbitSpan_eq_top (v : ∀ i, V i)
    (hv : ∀ i, Submodule.span ℂ (Set.range (fun a => op i a (v i))) = ⊤) :
    tupleOrbitSpan op v = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    apply Submodule.smul_mem
    apply tprod_mem_of_slot_spans
    intro i
    rw [hv i]
    exact Submodule.mem_top
  | add x y hx hy => exact Submodule.add_mem _ hx hy
end Algebraic

open MomentSources KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (M : ∀ q, LocalImageData R q)

abbrev LocalOperation : KPHilbert.Place F → Type
  | Sum.inl _ => List ComplexGenerator
  | Sum.inr q => KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q

def localOperation (p : KPHilbert.Place F) :
    LocalOperation R p → Module.End ℂ (actualLocal R M p) := by
  cases p with
  | inl w => exact complexWord
  | inr q =>
    exact fun a => KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 q (M q).inducing (M q).inducing.polarization (M q).haar (M q).haar_integer a

theorem localOperation_cyclic (p : KPHilbert.Place F) (v : actualLocal R M p) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun a => localOperation R M p a v)) = ⊤ := by
  cases p with
  | inl w => exact complexWordSpan_eq_top v hv
  | inr q => exact finite_orbit_span R M q v hv

theorem actual_stage_cyclic (s : Finset (KPHilbert.Place F))
    (v : ∀ p : s, actualLocal R M p) (hv : ∀ p, v p ≠ 0) :
    tupleOrbitSpan (fun p : s => localOperation R M p) v = ⊤ := by
  apply tupleOrbitSpan_eq_top
  exact fun p => localOperation_cyclic R M p (v p) (hv p)

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
