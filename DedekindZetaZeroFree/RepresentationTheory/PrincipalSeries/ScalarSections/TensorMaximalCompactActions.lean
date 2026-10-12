module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.LocalMaximalCompactActions

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField IsDedekindDomain KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

def localMaxAction (v : KPHilbert.Place F) :
    ThetaExpansion.iwasawaCompactFactor R v → Plus R.A P C v →ₗ[ℂ] Plus R.A P C v :=
  match v with
  | Sum.inl w => archMaxAction R P C w
  | Sum.inr q => fun k => finiteMaxAction R P C q k

theorem localMax_finite_subspace (v : KPHilbert.Place F) (f : Plus R.A P C v) :
    ∃ U : Submodule ℂ (Plus R.A P C v), Module.Finite ℂ U ∧ f ∈ U ∧
      ∀ k x, x ∈ U → localMaxAction R P C v k x ∈ U := by
  cases v with
  | inl w => exact archMax_finite_subspace R P C w f
  | inr q =>
    exact ⟨finiteMaxOrbit R P C q f, finiteMaxOrbit_finite R P C q f,
      mem_finiteMaxOrbit R P C q f, finiteMaxOrbit_stable R P C q f⟩

def stageMaxAction (s : RestrictedTensorSimple.Level (bad R.A P C))
    (k : ∀ j : s.val, ThetaExpansion.iwasawaCompactFactor R j.val) :
    RestrictedTensorSimple.Stage (Plus R.A P C) s.val →ₗ[ℂ]
      RestrictedTensorSimple.Stage (Plus R.A P C) s.val :=
  PiTensorProduct.map (fun j => localMaxAction R P C j.val (k j))

theorem stageMax_finite_subspace (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    ∃ U : Submodule ℂ (RestrictedTensorSimple.Stage (Plus R.A P C) s.val),
      Module.Finite ℂ U ∧ x ∈ U ∧
        ∀ k y, y ∈ U → stageMaxAction R P C s k y ∈ U := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    choose U hfinite hx hstable using fun j : s.val => localMax_finite_subspace R P C j.val (x j)
    let : ∀ j, Module.Finite ℂ (U j) := hfinite
    refine ⟨(PiTensorProduct.mapIncl U).range, inferInstance, ?_, ?_⟩
    · apply Submodule.smul_mem
      exact ⟨PiTensorProduct.tprod ℂ (fun j => (⟨x j, hx j⟩ : U j)), by
        simp [PiTensorProduct.mapIncl, PiTensorProduct.map_tprod]⟩
    · intro k y hy
      obtain ⟨z, rfl⟩ := hy
      let act (j : s.val) : U j →ₗ[ℂ] U j :=
        (localMaxAction R P C j.val (k j)).restrict (fun y hy => hstable j (k j) y hy)
      refine ⟨PiTensorProduct.map act z, ?_⟩
      change (PiTensorProduct.map (fun j => (U j).subtype)) (PiTensorProduct.map act z) =
        (PiTensorProduct.map (fun j => localMaxAction R P C j.val (k j)))
          ((PiTensorProduct.map (fun j => (U j).subtype)) z)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
        ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl
  | add x y hx hy =>
    obtain ⟨U, hU, hxU, hUs⟩ := hx
    obtain ⟨V, hV, hyV, hVs⟩ := hy
    let : Module.Finite ℂ U := hU
    let : Module.Finite ℂ V := hV
    refine ⟨U ⊔ V, inferInstance, Submodule.add_mem_sup hxU hyV, ?_⟩
    intro k z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add]
    exact Submodule.add_mem_sup (hUs k u hu) (hVs k v hv)

theorem localMaxAction_value (v : KPHilbert.Place F)
    (k : ThetaExpansion.iwasawaCompactFactor R v)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v)
    (f : Plus R.A P C v) :
    localValue R.A P C v g (localMaxAction R P C v k f) =
      localValue R.A P C v (g * k.val) f := by
  cases v with
  | inl w => exact archMaxAction_value R P C w k g f
  | inr q => exact finiteMaxAction_value R P C q k g f

theorem rawStageValue_maxAction (s : RestrictedTensorSimple.Level (bad R.A P C))
    (k : ThetaExpansion.fullProductCompactPreimage R) (g : Raw R.A)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    rawStageValue R.A P C s g
      (stageMaxAction R P C s (fun j => ⟨k.val j.val, k.property j.val⟩) x) =
      rawStageValue R.A P C s (g * k.val) x := by
  have hm : (fun j : s.val =>
      (localValueMap R.A P C j.val (g j.val)).comp
        (localMaxAction R P C j.val ⟨k.val j.val, k.property j.val⟩)) =
      (fun j : s.val => localValueMap R.A P C j.val ((g * k.val) j.val)) := by
    funext j
    ext f
    exact localMaxAction_value R P C j.val ⟨_, k.property j.val⟩ (g j.val) f
  unfold rawStageValue stageMaxAction
  simp only [LinearMap.comp_apply]
  apply congrArg (fun y => rationalEvaluation R.A (comparison R.A P C
    (RestrictedTensorSimple.stageInclusion (Fiber R.A P C) (reference R.A P C) (bad R.A P C) s y)))
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hm]

theorem stageMaxAction_transition (s t : RestrictedTensorSimple.Level (bad R.A P C))
    (hst : s ≤ t) (k : ThetaExpansion.fullProductCompactPreimage R)
    (hfix : ∀ v, v ∉ s.val →
      localMaxAction R P C v ⟨k.val v, k.property v⟩ (plusReference R.A P C v) =
        plusReference R.A P C v)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    stageMaxAction R P C t (fun j => ⟨k.val j.val, k.property j.val⟩)
      (RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst x) =
    RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst
      (stageMaxAction R P C s (fun j => ⟨k.val j.val, k.property j.val⟩) x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    congr 1
    simp only [stageMaxAction, RestrictedTensorSimple.transition,
      RestrictedTensorSimple.insert_pure, PiTensorProduct.map_tprod]
    congr 1
    funext j
    by_cases hj : j.val ∈ s.val
    · simp only [dite_eq_left hj]
    · simpa only [dite_eq_right hj] using hfix j.val hj
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rawCoreInsertion_maxAction (s : RestrictedTensorSimple.Level (bad R.A P C))
    (k : ThetaExpansion.fullProductCompactPreimage R) (g : Raw R.A)
    (hfix : ∀ v, v ∉ s.val →
      localMaxAction R P C v ⟨k.val v, k.property v⟩ (plusReference R.A P C v) =
        plusReference R.A P C v)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    rawCoreInsertion R.A P C (RestrictedTensorSimple.stageInclusion (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C) s
      (stageMaxAction R P C s (fun j => ⟨k.val j.val, k.property j.val⟩) x)) g =
    rawCoreInsertion R.A P C (RestrictedTensorSimple.stageInclusion (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C) s x) (g * k.val) := by
  obtain ⟨u, hu⟩ := exists_reference_stage R.A P C g
  obtain ⟨v, hv⟩ := exists_reference_stage R.A P C (g * k.val)
  let t : RestrictedTensorSimple.Level (bad R.A P C) := ⟨s.val ∪ u.val ∪ v.val,
    (s.property.trans Finset.subset_union_left).trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left.trans Finset.subset_union_left
  have ht : ∀ j, j ∉ t.val → localValue R.A P C j (g j) (plusReference R.A P C j) = reference R.A P C j :=
    fun j hj => hu j (fun h => hj (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have ht' : ∀ j, j ∉ t.val → localValue R.A P C j ((g * k.val) j)
      (plusReference R.A P C j) = reference R.A P C j :=
    fun j hj => hv j (fun h => hj (Finset.mem_union_right _ h))
  have hstep (y : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s y =
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) t
        (RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst y) :=
    Module.DirectLimit.of_f.symm
  rw [hstep, hstep, rawCoreInsertion_stage R.A P C t _ g ht,
    rawCoreInsertion_stage R.A P C t _ (g * k.val) ht',
    ← stageMaxAction_transition R P C s t hst k hfix]
  exact rawStageValue_maxAction R P C t k g _

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
