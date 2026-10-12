module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ExteriorCompactSubgroup

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPLiteralRaw SharedSource
open _root_.DedekindZetaZeroFree renaming finiteAverage_left → finiteAverage_left
open _root_.DedekindZetaZeroFree renaming finiteAverage_constant → finiteAverage_constant
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance : T2Space (Group R) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).1
local instance : IsTopologicalGroup (Group R) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1

 def exteriorSmoothAction : Representation ℂ (exteriorCompact R)
    (nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12) :=
  Representation.subrepresentation
    ((rightAction F R.A.zeta12 R.A.primitive_zeta12).comp (exteriorCompact R).subtype)
    (nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12)
    (by
      intro a f hf
      exact KPLiteralPeriod.NonzeroResidue.smooth_right_translate
        F R.A.zeta12 R.A.primitive_zeta12 f hf a.val)

 theorem exterior_flat_preimage
    (f : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
    (C : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 f)
    (hf : ∀ s g, f.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (f.val 0) g)
    (hC : ExteriorFixed R (C.numerator 0)) :
    ∃ (v : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
      (Cv : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 v),
      (∀ s g, v.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (v.val 0) g) ∧
      ExteriorFixed R (v.val 0) ∧ Cv.numerator 0 = C.numerator 0 := by
  let H := exteriorCompact R
  letI : CompactSpace H := isCompact_iff_compactSpace.mp (exteriorCompact_compact R)
  let U : CompactOpenLevel H := ⟨⊤,by simpa using (isCompact_univ : IsCompact (Set.univ : Set H))⟩
  let ρ := exteriorSmoothAction R
  let u : nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12 := ⟨f.val 0,(f.property.1 0).1⟩
  obtain ⟨L,hL⟩ := (f.property.1 0).1.2.2
  let incl : U.toOpenSubgroup →* KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 :=
    ((H.subtype.comp U.toOpenSubgroup.subtype).codRestrict _ (fun a => exteriorCompact_le_finite R a.val.property))
  have hincl : Continuous incl := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val : Continuous (fun a : H => (a : Group R))).comp
      (continuous_subtype_val : Continuous (fun a : U.toOpenSubgroup => (a : H)))
  let J : OpenSubgroup U.toOpenSubgroup := L.toOpenSubgroup.comap incl hincl
  have hJ : ∀ a : J, ρ (a.val.val : H) u = u := by
    intro a
    apply Subtype.ext
    ext g
    exact hL g _ ⟨incl a.val,a.property,rfl⟩
  obtain ⟨ho,hn,hfix⟩ := compactOpen_stabilizer_core ρ U u J hJ
  let K : FiniteAveragingLevel ρ U u := ⟨J.toSubgroup.normalCore,ho,inferInstance,hn,hfix⟩
  letI := K.finite
  letI := K.isNormal
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
  let r : (U.toOpenSubgroup ⧸ K.subgroup) → U.toOpenSubgroup := Quotient.out
  let c : ℂ := (Nat.card (U.toOpenSubgroup ⧸ K.subgroup) : ℂ)⁻¹
  have hb (i : U.toOpenSubgroup ⧸ K.subgroup) := canonical_compact_translate F R.A.zeta12
    R.A.primitive_zeta12 f C hf ⟨(r i).val.val,exteriorCompact_le_K R (r i).val.property⟩
  choose b D hb hb0 hD using hb
  let v := FiniteWhittakerProjectors.FlatFiniteSum.sum F R.A.zeta12 R.A.primitive_zeta12 Finset.univ (fun _ => c) b
  let Cv := Classical.choice (flatScalarResidue_nonempty F R.A.zeta12 R.A.primitive_zeta12 _
    (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12) v)
  have hv (s) (g) : v.val s g = ∑ i, c * (b i).val s g := FiniteWhittakerProjectors.FlatFiniteSum.sum_val _ _ _ _ _ _ _ _
  have hv0 : v.val 0 = (finiteQuotientAverage ρ U K.subgroup r u).val := by
    ext g
    rw [hv]
    simp_rw [hb0]
    unfold finiteQuotientAverage
    simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  refine ⟨v,Cv,?_,?_,?_⟩
  · intro s g
    rw [hv]
    simp_rw [hb]
    simp only [scalarWeight]
    rw [hv,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · intro q hq a ha g
    have h := finiteAverage_left ρ U u K r (fun i => Quotient.out_eq i)
      ⟨⟨finiteInjection R q a,finiteInjection_mem_exteriorCompact R q hq a ha⟩,by trivial⟩
    have hh := congrArg (fun z => z.val g) h
    change (finiteQuotientAverage ρ U K.subgroup r u).val (g * finiteInjection R q a) =
      (finiteQuotientAverage ρ U K.subgroup r u).val g at hh
    rw [← hv0] at hh
    exact hh
  · ext g
    rw [flat_sum_residue (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12)
      Finset.univ (fun _ => c) b Cv D]
    have hfixC := exteriorCompact_fixed R (C.numerator 0)
      (flatScalarResidue_smooth F R.A.zeta12 R.A.primitive_zeta12
        (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12) f C).1 hC
    simp_rw [hD,hfixC]
    simp only [Finset.sum_const,Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    have hn' : (Nat.card (U.toOpenSubgroup ⧸ K.subgroup) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    change _ • (c * C.numerator 0 g) = _
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    dsimp [c]
    simp [smul_eq_mul,← mul_assoc,hn']

end DedekindZetaZeroFree.RootDerivatives

end
