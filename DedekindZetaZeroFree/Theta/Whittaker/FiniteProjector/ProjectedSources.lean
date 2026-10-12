module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FiniteSourceGeometry
public import DedekindZetaZeroFree.Eisenstein.Continuation.HolomorphicLaurentFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming level_exists → level_exists
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem finite_common_level {J : Type} [Finite J] (U : J → KPGlobalTorusFunctionData.FiniteLevel
    F R.A.zeta12 R.A.primitive_zeta12) :
    ∃ V : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12,
      ∀ j, KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 V ≤
        KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 (U j) := by
  letI := Fintype.ofFinite J
  have h (s : Finset J) : ∃ V : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12,
      ∀ j ∈ s, KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 V ≤
        KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 (U j) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Classical.choice (level_exists F R.A.zeta12 R.A.primitive_zeta12), by simp⟩
    | @insert j s hj ih =>
      obtain ⟨V,hV⟩ := ih
      let W : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12 :=
        ⟨V.toOpenSubgroup ⊓ (U j).toOpenSubgroup, V.isCompact.inter_right (U j).toOpenSubgroup.isClosed⟩
      refine ⟨W, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Subgroup.map_mono inf_le_right
      · exact (Subgroup.map_mono inf_le_left).trans (hV k hk)
  obtain ⟨V,hV⟩ := h Finset.univ
  exact ⟨V,fun j => hV j (Finset.mem_univ j)⟩

theorem canonical_family_level {J : Type} [Finite J]
    (f : J → KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
    (hf : ∀ j z g, (f j).val z g =
      Complex.exp (z * (KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 g : ℂ)) * (f j).val 0 g) :
    ∃ V : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12,
      ∀ j z g u, u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 V →
        (f j).val z (g*u) = (f j).val z g := by
  have h (j : J) (b : Bool) := ((f j).property.1 (if b then 1 else 0)).1.2.2
  choose U hU using h
  obtain ⟨V,hV⟩ := finite_common_level R (fun p : J × Bool => U p.1 p.2)
  refine ⟨V, ?_⟩
  intro j z g u hu
  have h0 := hU j false g u (hV (j,false) hu)
  have h1 := hU j true g u (hV (j,true) hu)
  simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
  rw [hf j 1, hf j 1, h0] at h1
  rw [hf j z (g*u), hf j z g, h0]
  by_cases hz : (f j).val 0 g = 0
  · simp [hz]
  · have he := mul_right_cancel₀ hz h1
    simp only [one_mul] at he
    have ha : KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 (g*u) =
        KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 g := by
      apply Real.exp_injective
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_exp] using he
    rw [ha]

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem projected_sources {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
    (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F) (l : List R.A.Sf) :
    ∃ Q : AdmissibleFlatSources R,
      Q.dq = A.sources.dq ∧
      ∀ v, ∃ B : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (Q.flat v),
        B.numerator 0 = FiniteWhittakerProjectors.rootProjectorWord R I c t l (A.realization.theta v) := by
  obtain ⟨f,B,hf,hB⟩ := selected_root_word_flat_lifts R I c t A l
  have hc := fun v => canonical_flat_residue F R.A.zeta12 R.A.primitive_zeta12 A.sources.iwasawa (f v) (B v)
  choose w C hw hC using hc
  have hw0 (v) : (w v).val 0 = (f v).val 0 := by
    funext g
    simp [hw]
  have hflat (v z g) : (w v).val z g = Complex.exp
      (z * (KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 g : ℂ)) * (w v).val 0 g := by
    rw [hw, hw0]
  letI := A.sources.finite_companions
  obtain ⟨V,hV⟩ := FiniteWhittakerProjectors.canonical_family_level R w hflat
  let Q : AdmissibleFlatSources R := {
    K := (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K
    iwasawa := PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12
    flat := w
    finite_companions := A.sources.finite_companions
    level := V
    common_level := hV
    ordinary := ?_
    exterior_spherical := ?_
    dq := A.sources.dq
    quotientHaar := A.sources.quotientHaar
    probability := A.sources.probability }
  · refine ⟨Q,rfl,?_⟩
    intro v
    refine ⟨C v, ?_⟩
    exact (funext (hC v)).trans (hB v)
  · intro v z ε g
    exact ThetaExpansion.induced_ordinary_central_covariance R z _ ((w v).property.1 z) ε g
  · intro v z p hp b hb g
    rw [hw, hw, hf v]
    have hα := KPContFlatFullProductIwasawa.alpha_mul_compact F R.A.zeta12 R.A.primitive_zeta12 g
      ⟨FiniteWhittakerProjectors.finiteInjection R p b, FiniteWhittakerProjectors.finiteInjection_compact_mem R p b hb⟩
    change KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 (g * FiniteWhittakerProjectors.finiteInjection R p b) = _ at hα
    change Complex.exp (z * (KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12
      (g * FiniteWhittakerProjectors.finiteInjection R p b) : ℂ)) * FiniteWhittakerProjectors.rootProjectorWord R I c t l ((A.sources.flat v).val 0)
      (g * FiniteWhittakerProjectors.finiteInjection R p b) = _
    rw [hα, FiniteWhittakerProjectors.rootProjectorWord_exterior R I c t l v p hp b hb]

end DedekindZetaZeroFree.RootDerivatives

end
end
