module

public import DedekindZetaZeroFree.Theta.Periods.SphericalTensor.SingleSlotNormalization
public import DedekindZetaZeroFree.Eisenstein.Residues.HarishChandraHeckePreimages

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming quotientHom → quotientHom
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming archProjection → archProjection
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming finiteProjectionHom → finiteProjectionHom
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming tuple_factorization → tuple_factorization
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming archProjection_commutes_finite → archProjection_commutes_finite
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming local_arch_mem → local_arch_mem
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming archProjection_infinite → archProjection_infinite
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming archProjection_finite → archProjection_finite
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming finiteCompactSet → finiteCompactSet
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming finiteCompact_translate_range → finiteCompact_translate_range
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

private theorem actualRightWord_eq_adelic
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (f : Functions F ζ hζ) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w f =
      AdelicRightLieWords.actualRightWord F ζ hζ w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, AdelicRightLieWords.actualRightWord]
    rw [ih]
    rfl

 theorem smooth_of_hcHeckeSpan {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η} {Q : MomentSources.AdmissibleFlatSources R}
    (T : MomentSources.Realization R Q) {u : MomentSources.Functions R} (hu : u ∈ MomentSources.hcHeckeSpan T) :
    Smooth F R.A.zeta12 R.A.primitive_zeta12 u := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v,a,w,rfl⟩ := hu
    simpa only [actualRightWord_eq_adelic F R.A.zeta12 R.A.primitive_zeta12,
      _root_.DedekindZetaZeroFree.MomentSources.Realization.theta] using
      KPLiteralPeriod.NonzeroResidue.smooth_right_translate F R.A.zeta12 R.A.primitive_zeta12 _
        (SharedSource.actualRightWord_smooth _ (T.automorphic v).1 w) a
  | zero => exact ((FiniteWhittakerProjectors.FlatFiniteSum.zero F R.A.zeta12 R.A.primitive_zeta12 ⊥).property.1 0).1
  | add u v hu hv ih ih' => exact (SharedSource.nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12).add_mem ih ih'
  | smul c u hu ih => exact (SharedSource.nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12).smul_mem c ih

 theorem kfinite_of_complex_fixed (u : Functions F ζ hζ) (hs : Smooth F ζ hζ u)
    (hfix : ∀ w k g, u (g * KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k) = u g) :
    KFinite F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K u := by
  letI : IsTopologicalGroup (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let J : Subgroup (G F ζ hζ) := {
    carrier := {a | ∀ g, u (g*a) = u g}
    one_mem' := by simp
    mul_mem' := by intro a b ha hb g; rw [← mul_assoc,hb,ha]
    inv_mem' := by intro a ha g; have h := ha (g*a⁻¹); simpa using h.symm }
  have hJ : IsClosed (J : Set (G F ζ hζ)) := by
    change IsClosed {a | ∀ g, u (g*a) = u g}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro g
    exact isClosed_eq (hs.1.comp (continuous_const.mul continuous_id)) continuous_const
  have hlocal (w : InfinitePlace F) (x : PrincipalOfKP.archimedeanLocalCompact F ζ hζ w) :
      quotientHom F ζ hζ (KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ (Sum.inl w) x.val) ∈ J := by
    have hle : PrincipalOfKP.archimedeanLocalCompact F ζ hζ w ≤
        J.comap ((quotientHom F ζ hζ).comp
          (RestrictedProduct.mulSingleMonoidHom (KPAdelicCoverRestrictedProduct.compact F ζ hζ) (Sum.inl w))) := by
      apply (Subgroup.closure_le _).mpr
      rintro a ⟨k,rfl⟩
      exact hfix w k
    exact hle x.property
  have harch (x : PrincipalOfKP.fullCompactPreimageMax F ζ hζ) :
      quotientHom F ζ hζ (archProjection F ζ hζ x.val) ∈ J := by
    rw [archProjection,map_list_prod,List.map_map]
    apply Subgroup.list_prod_mem
    rintro a ha
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp ha
    exact hlocal w ⟨x.val (Sum.inl w),x.property (Sum.inl w)⟩
  let B := Set.range (fun b : finiteCompactSet F ζ hζ => rightAction F ζ hζ b.val.val u)
  have hB : B.Finite := finiteCompact_translate_range F ζ hζ u hs
  let T := Submodule.span ℂ B
  haveI : Module.Finite ℂ T := Module.Finite.of_fg (Submodule.fg_span hB)
  let W := Submodule.span ℂ (Set.range (fun k : (KPContFlatSourceRecipe.D F ζ hζ).K => rightAction F ζ hζ k.val u))
  have hWT : W ≤ T := by
    apply Submodule.span_le.mpr
    rintro v ⟨k,rfl⟩
    obtain ⟨x,hx,hxe⟩ := Subgroup.mem_map.mp k.property
    let a := quotientHom F ζ hζ (archProjection F ζ hζ x)
    let b := finiteProjectionHom F ζ hζ x
    have he : k.val = a * b.val := by
      change k.val = quotientHom F ζ hζ (archProjection F ζ hζ x) *
        quotientHom F ζ hζ _
      rw [← map_mul,← tuple_factorization]
      exact hxe.symm
    have hv : rightAction F ζ hζ k.val u = rightAction F ζ hζ b.val u := by
      ext g
      change u (g*k.val) = u (g*b.val)
      rw [he]
      change u (g * (quotientHom F ζ hζ (archProjection F ζ hζ x) * b.val)) = _
      rw [(archProjection_commutes_finite F ζ hζ x b).eq,← mul_assoc]
      exact harch ⟨x,hx⟩ _
    change rightAction F ζ hζ k.val u ∈ T
    rw [hv]
    exact Submodule.subset_span ⟨⟨b,⟨x,hx,rfl⟩⟩,rfl⟩
  haveI : Module.Finite ℂ W := Module.Finite.of_injective (Submodule.inclusion hWT) (Submodule.inclusion_injective _)
  refine ⟨W,inferInstance,Submodule.subset_span ⟨1,?_⟩,?_⟩
  · ext g; simp [rightAction]
  · intro k v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨l,rfl⟩ := hv; exact Submodule.subset_span ⟨k*l,by ext g; simp [rightAction,mul_assoc]⟩
    | zero => simpa using W.zero_mem
    | add u v hu hv ih ih' => simpa only [map_add] using W.add_mem ih ih'
    | smul c v hv ih => simpa only [map_smul] using W.smul_mem c ih

variable {F ζ hζ}
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
open MomentSources ThetaExpansion

 theorem normalized_tensor_complex_fixed {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (D : SphericalTransportData R A) (P : NormalizedSphericalTensor R A D) :
    ∀ w k g, tensorFunction R A.factorization D.tensor.stage P.entries
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) =
      tensorFunction R A.factorization D.tensor.stage P.entries g := by
  intro w k g
  rw [P.realization_exact]
  change P.scalar * D.tensor.value _ = P.scalar * D.tensor.value g
  rw [D.tensor.complex_compact]

 theorem normalized_tensor_flat_preimage {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (D : SphericalTransportData R A) (P : NormalizedSphericalTensor R A D) :
    ∃ (f : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
      (C : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 f),
      C.numerator 0 = tensorFunction R A.factorization D.tensor.stage P.entries := by
  have hm := A.factorization.core_same_residue
    (RestrictedTensorSimple.stageInclusion _ A.factorization.references A.factorization.bad D.tensor.stage
      (PiTensorProduct.tprod ℂ P.entries))
  have hs := smooth_of_hcHeckeSpan F A.realization hm.1
  exact hcHecke_kfinite_flat_preimage R A.realization _ hm.1 hs.1
    (kfinite_of_complex_fixed F R.A.zeta12 R.A.primitive_zeta12 _ hs (normalized_tensor_complex_fixed R A D P))

end DedekindZetaZeroFree.RootDerivatives

end
