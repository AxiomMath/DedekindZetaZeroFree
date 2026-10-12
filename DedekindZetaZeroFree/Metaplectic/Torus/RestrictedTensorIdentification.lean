module

public import DedekindZetaZeroFree.Metaplectic.Torus.TensorRangesAndInducingCovariance

@[expose] public section

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

open KPAdelicCoverRestrictedProduct
private theorem raw_diagonal (g : KPGlobalTorusFunctionData.E F ζ hζ)
    (x : RestrictedCover F ζ hζ)
    (hx : scalarQuotient F ζ hζ (amalgamation F ζ hζ x) = g.val) :
    ∀ v, (x v).g 1 0 = 0 ∧ (x v).g 0 1 = 0 := by
  obtain ⟨A, hA, h10, h01⟩ := g.property
  have he : QuotientGroup.mk' (scalarSubgroup F) (restrictedProjection F ζ hζ x) =
      QuotientGroup.mk' (scalarSubgroup F) A := by
    change pglProjection F ζ hζ (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) = _
    rw [hx, hA]
  obtain ⟨s, ⟨u, hu⟩, hs⟩ := (QuotientGroup.mk'_eq_mk' (scalarSubgroup F)).mp he
  have hm : restrictedProjection F ζ hζ x = A * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by
    rw [← hu] at hs
    exact eq_mul_inv_of_mul_eq hs
  have hd : (restrictedProjection F ζ hζ x) 1 0 = 0 ∧
      (restrictedProjection F ζ hζ x) 0 1 = 0 := by
    rw [hm]
    simp [Matrix.GeneralLinearGroup.coe_mul, ← map_inv,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.scalar, h10, h01]
  intro v
  have h := congrArg (adeleEval F v) hd.1
  have h' := congrArg (adeleEval F v) hd.2
  have hev := restrictedProjection_eval F ζ hζ x v
  have hh := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 1 0) hev
  have hh' := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 0 1) hev
  exact ⟨hh.symm.trans (by simpa [matrixEval] using h),
    hh'.symm.trans (by simpa [matrixEval] using h')⟩

private theorem raw_image_torus (x : RestrictedCover F ζ hζ)
    (hd : ∀ v, (x v).g 1 0 = 0 ∧ (x v).g 0 1 = 0) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ x) ∈ KPGlobalTorusFunctionData.E F ζ hζ := by
  refine ⟨restrictedProjection F ζ hζ x, rfl, ?_, ?_⟩
  · apply Prod.ext
    · funext w; exact (hd (Sum.inl w)).1
    · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).1
  · apply Prod.ext
    · funext w; exact (hd (Sum.inl w)).2
    · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).2

private theorem arch_mem_B (x : RestrictedCover F ζ hζ)
    (hd : ∀ v, (x v).g 1 0 = 0 ∧ (x v).g 0 1 = 0)
    (hf : ∀ q, x (Sum.inr q) = 1) :
    (⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ x), raw_image_torus F ζ hζ x hd⟩ :
      KPGlobalTorusFunctionData.E F ζ hζ) ∈ KPGlobalProductPolarizationCharacter.B F ζ hζ P := by
  let e : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ x), raw_image_torus F ζ hζ x hd⟩
  change ∀ v, KPGlobalCubicIdelePairing.classComparison F
    (KPGlobalProductPolarizationCharacter.pD F ζ hζ e) v ∈ (P.localData v).L
  intro v
  cases v with
  | inl w => rw [P.complex_full]; trivial
  | inr q =>
    change KPGlobalCubicIdelePairing.localClass F (Sum.inr q)
      (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) (KPGlobalTorusFunctionData.p F ζ hζ e)) ∈ _
    have hmat : (restrictedProjection F ζ hζ x) 1 0 = 0 ∧
        (restrictedProjection F ζ hζ x) 0 1 = 0 := by
      constructor
      · apply Prod.ext
        · funext w; exact (hd (Sum.inl w)).1
        · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).1
      · apply Prod.ext
        · funext w; exact (hd (Sum.inl w)).2
        · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).2
    have hr := KPGlobalTorusFunctionData.ratio_formula F
      ⟨_, e.property⟩ (restrictedProjection F ζ hζ x) rfl hmat.1 hmat.2
    have heval : KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q)
        (KPGlobalTorusFunctionData.p F ζ hζ e) = 1 := by
      apply Units.ext
      have h := congrArg (adeleEval F (Sum.inr q)) hr
      have hev := restrictedProjection_eval F ζ hζ x (Sum.inr q)
      rw [hf q, map_one] at hev
      have h00 := congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M 0 0) hev
      have h11 := congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M 1 1) hev
      have h00' : adeleEval F (Sum.inr q) ((restrictedProjection F ζ hζ x) 0 0) = 1 := by
        simpa [matrixEval] using h00
      have h11' : adeleEval F (Sum.inr q) ((restrictedProjection F ζ hζ x) 1 1) = 1 := by
        simpa [matrixEval] using h11
      change adeleEval F (Sum.inr q)
        ((KPGlobalTorusFunctionData.torusRatio F ⟨_, e.property⟩ : Ideles F) : Adeles F) = 1
      simpa [map_mul, IsUnit.unit_spec, h00', h11'] using h
    rw [heval, map_one]
    exact (P.localData (Sum.inr q)).L.one_mem

theorem raw_unit_product_covariant_cover
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : KPGlobalTorusTensorFibers.IsUnitProductModel F ζ hζ P T Q)
    (g : KPGlobalTorusFunctionData.E F ζ hζ) :
    ∃ (b : Q.H) (a : KPGlobalTorusTensorFibers.RawEvaluationPoint F ζ hζ),
      g = b.val * a.g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) g.val
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (M F ζ hζ) u
  have hxg : scalarQuotient F ζ hζ (amalgamation F ζ hζ x) = g.val :=
    (congrArg (scalarQuotient F ζ hζ) hx).trans hu
  have hd := raw_diagonal F ζ hζ g x hxg
  let xi : RestrictedCover F ζ hζ :=
    ⟨fun v => match v with | Sum.inl w => x (Sum.inl w) | Sum.inr _ => 1,
      Filter.Eventually.of_forall (by intro v; cases v <;> simp [compact, Subgroup.one_mem])⟩
  let xf : RestrictedCover F ζ hζ :=
    ⟨fun v => match v with | Sum.inl _ => 1 | Sum.inr q => x (Sum.inr q),
      x.property.mono (by
        intro v hv
        cases v with
        | inl w => trivial
        | inr q => exact hv)⟩
  have hdi : ∀ v, (xi v).g 1 0 = 0 ∧ (xi v).g 0 1 = 0 := by
    intro v; cases v with
    | inl w => exact hd (Sum.inl w)
    | inr q => simp [xi, KPLocalCover.one_g]
  have hdf : ∀ v, (xf v).g 1 0 = 0 ∧ (xf v).g 0 1 = 0 := by
    intro v; cases v with
    | inl w => simp [xf, KPLocalCover.one_g]
    | inr q => exact hd (Sum.inr q)
  let bi : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ xi), raw_image_torus F ζ hζ xi hdi⟩
  have hb : bi ∈ Q.H := by
    rw [hQ.1]
    exact arch_mem_B F ζ hζ P xi hdi (fun _ => rfl)
  let af : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ xf), raw_image_torus F ζ hζ xf hdf⟩
  have ht : ∀ q, KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (xf (Sum.inr q)) ∈
      KPLocalExceptionalConstruction.actualTorus F ζ hζ q := by
    intro q
    refine ⟨(xf (Sum.inr q)).g, rfl, (hdf (Sum.inr q)).1, (hdf (Sum.inr q)).2⟩
  refine ⟨⟨bi, hb⟩, ⟨xf, fun q => ⟨_, ht q⟩, af, fun _ => rfl, fun _ => rfl, rfl⟩, ?_⟩
  apply Subtype.ext
  change g.val = scalarQuotient F ζ hζ (amalgamation F ζ hζ xi) *
    scalarQuotient F ζ hζ (amalgamation F ζ hζ xf)
  rw [← map_mul, ← map_mul, ← hxg]
  congr 2
  apply RestrictedProduct.ext
  intro v
  change x v = xi v * xf v
  cases v <;> simp [xi, xf]

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

end

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

theorem raw_formula_inserted_finprod
    (C : RawLocalScalarData F ζ hζ P T)
    (S U : Finset (HeightOneSpectrum (𝓞 F))) (hSU : S ⊆ U)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    (∏ᶠ q : HeightOneSpectrum (𝓞 F), C.evaluation q
        (if h : q ∈ U then
          (if h' : q ∈ S then f ⟨q, h'⟩ else C.reference q) else C.reference q) (t q)) =
      ∏ᶠ q : HeightOneSpectrum (𝓞 F), C.evaluation q
        (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q) := by
  refine finprod_congr fun q => ?_
  by_cases hqS : q ∈ S
  · have hqU : q ∈ U := hSU hqS
    simp only [dif_pos hqU, dif_pos hqS]
  · by_cases hqU : q ∈ U
    · simp only [dif_pos hqU, dif_neg hqS]
    · simp only [dif_neg hqU, dif_neg hqS]

theorem raw_tensor_formula_insertion_agrees_reachable
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (R : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S),
      RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
          KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q)
    (hR : ∀ S hS, RawTensorFormula F ζ hζ P T C Q S (R S hS))
    (S U : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) (hSU : S ⊆ U)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (g : KPGlobalTorusFunctionData.E F ζ hζ)
    (hraw : ∀ w : InfinitePlace F, raw (Sum.inl w) = 1)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (hg : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val) :
    (((R U (hS.trans hSU)).comp
        (RestrictedTensorSimple.insert
          (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q))
          C.reference S U hSU)) (PiTensorProduct.tprod ℂ f)).val.val g =
      (R S hS (PiTensorProduct.tprod ℂ f)).val.val g := by
  rw [LinearMap.comp_apply, RestrictedTensorSimple.insert_pure]
  rw [hR U (hS.trans hSU)
        (fun j : U => if h : (j : HeightOneSpectrum (𝓞 F)) ∈ S then f ⟨j, h⟩
          else C.reference j) raw t g hraw ht hg,
      hR S hS f raw t g hraw ht hg]
  exact raw_formula_inserted_finprod F ζ hζ P T C S U hSU f t

theorem raw_tensor_formula_insertion_agrees_reachable_linear
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (R : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S),
      RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
          KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q)
    (hR : ∀ S hS, RawTensorFormula F ζ hζ P T C Q S (R S hS))
    (S U : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) (hSU : S ⊆ U)
    (x : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S)
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (g : KPGlobalTorusFunctionData.E F ζ hζ)
    (hraw : ∀ w : InfinitePlace F, raw (Sum.inl w) = 1)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (hg : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val) :
    (((R U (hS.trans hSU)).comp
        (RestrictedTensorSimple.insert
          (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q))
          C.reference S U hSU)) x).val.val g = (R S hS x).val.val g := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    simpa only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun z : ℂ => c * z)
        (raw_tensor_formula_insertion_agrees_reachable F ζ hζ P T C Q hQ R hR
          S U hS hSU f raw t g hraw ht hg)
  | add x y hx hy =>
    simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

theorem scalar_functions_ext_of_covariant_cover
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Set (KPGlobalTorusFunctionData.E F ζ hζ))
    (hA : ∀ g : KPGlobalTorusFunctionData.E F ζ hζ,
      ∃ (b : Q.H) (a : KPGlobalTorusFunctionData.E F ζ hζ), a ∈ A ∧ g = b.val * a)
    (f k : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hfk : ∀ a ∈ A, f.val a = k.val a) : f = k := by
  apply Subtype.ext
  funext g
  obtain ⟨b, a, ha, rfl⟩ := hA g
  rw [f.property b a, k.property b a, hfk a ha]

def rawReachableTorus : Set (KPGlobalTorusFunctionData.E F ζ hζ) :=
  {g | ∃ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
    (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
    (∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) ∧
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val}

theorem raw_tensor_insertion_compatible_of_covariant_cover
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (R : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S),
      RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
          KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q)
    (hR : ∀ S hS, RawTensorFormula F ζ hζ P T C Q S (R S hS))
    (hcover : ∀ g : KPGlobalTorusFunctionData.E F ζ hζ,
      ∃ (b : Q.H) (a : KPGlobalTorusFunctionData.E F ζ hζ),
        a ∈ rawReachableTorus F ζ hζ ∧ g = b.val * a)
    (S U : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) (hSU : S ⊆ U) :
    (R U (hS.trans hSU)).comp
      (RestrictedTensorSimple.insert
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q))
        C.reference S U hSU) = R S hS := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply scalar_functions_ext_of_covariant_cover F ζ hζ Q
    (rawReachableTorus F ζ hζ) hcover
  intro a ha
  obtain ⟨raw, t, hraw, ht, hg⟩ := ha
  exact raw_tensor_formula_insertion_agrees_reachable_linear F ζ hζ P T C Q hQ R hR
    S U hS hSU x raw t a hraw ht hg

theorem rawEvaluation_zero_iff (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F))
    (f : KPLocalStoneVonNeumann.InducedModule (C.polarization q)) :
    (∀ t, C.evaluation q f t = 0) ↔ f = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    funext t
    have hd : (Real.rpow
        (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          ((C.canonical q).borel.coordinate t)) (1 / 6 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.rpow_pos_of_pos
        (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q) _) _)
    exact (div_eq_zero_iff.mp (by simpa only [C.evaluation_formula] using h t)).resolve_right hd
  · rintro rfl t
    simp [C.evaluation_formula]

theorem rawEvaluation_span_dual (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F)) :
    Submodule.span ℂ (Set.range (rawEvaluationLinear F ζ hζ P T C q)) = ⊤ := by
  letI := KPLocalStoneVonNeumann.tau_moduleFinite (C.canonical q).heisenberg (C.polarization q)
  apply Submodule.span_eq_top_of_ne_zero
  intro f hf
  obtain ⟨t, ht⟩ := not_forall.mp (fun h => hf ((rawEvaluation_zero_iff F ζ hζ P T C q f).mp h))
  exact ⟨rawEvaluationLinear F ζ hζ P T C q t, ⟨t, rfl⟩, ht⟩

theorem rawFiniteTensor_evaluations_separate (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S)
    (hx : ∀ t : ∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q,
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ
        (fun q : S => rawEvaluationLinear F ζ hζ P T C q.val (t q))) x = 0) : x = 0 := by
  letI := fun q : S => KPLocalStoneVonNeumann.tau_moduleFinite
    (C.canonical q.val).heisenberg (C.polarization q.val)
  let φ : MultilinearMap ℂ
      (fun q : S => Module.Dual ℂ (KPLocalStoneVonNeumann.InducedModule (C.polarization q.val))) ℂ :=
    ((LinearMap.applyₗ' ℂ x).comp PiTensorProduct.dualDistrib).compMultilinearMap
      (PiTensorProduct.tprod ℂ)
  have hφ : φ = 0 := by
    apply MultilinearMap.ext_of_span_eq_top
      (g := fun {q : S} t => rawEvaluationLinear F ζ hζ P T C q.val t)
      (fun q => rawEvaluation_span_dual F ζ hζ P T C q.val)
    intro t
    exact hx t
  letI : Module.Free ℂ (RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S) :=
    Module.Free.of_basis (Basis.piTensorProduct
      (fun q : S => Module.Free.chooseBasis ℂ
        (KPLocalStoneVonNeumann.InducedModule (C.polarization q.val))))
  letI : Module.Projective ℂ (RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S) :=
    Module.Projective.of_free
  apply (Module.forall_dual_apply_eq_zero_iff ℂ x).mp
  intro f
  obtain ⟨y, rfl⟩ := (PiTensorProduct.dualDistribEquiv
    (R := ℂ) (M := fun q : S => KPLocalStoneVonNeumann.InducedModule (C.polarization q.val))).surjective f
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c fs =>
    have h := MultilinearMap.congr_fun hφ fs
    change PiTensorProduct.dualDistrib (c • PiTensorProduct.tprod ℂ fs) x = 0
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    change c * φ fs = 0
    rw [h, MultilinearMap.zero_apply, mul_zero]
  | add a b ha hb =>
    change PiTensorProduct.dualDistrib (a + b) x = 0
    change PiTensorProduct.dualDistrib a x = 0 at ha
    change PiTensorProduct.dualDistrib b x = 0 at hb
    simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
theorem raw_reference_evaluation_one (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F)) : C.evaluation q (C.reference q) 1 = 1 := by
  rw [C.evaluation_formula, C.reference_formula]
  simp only [map_one, Subgroup.one_mem, dite_true, Units.val_one]
  rw [show (⟨1, _⟩ : (C.polarization q).L.comap (C.canonical q).heisenberg.π) = 1 from rfl, map_one]
  simp [KPGlobalCenterRationalCharacter.localAbs]

theorem rawFiniteTensorFunctional_eq_dual_of_trivial_outside (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : ∀ q, q ∉ S → t q = 1) :
    rawFiniteTensorFunctional F ζ hζ P T C S t =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ
        (fun q : S => rawEvaluationLinear F ζ hζ P T C q.val (t q.val))) := by
  apply PiTensorProduct.ext
  ext f
  have hout : (∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (t q)) = 1 := by
    have he : (fun q => if q ∈ S then (1 : ℂ) else C.evaluation q (C.reference q) (t q)) =
        fun _ => 1 := by
      funext q
      by_cases hq : q ∈ S
      · simp only [if_pos hq]
      · simp only [if_neg hq, ht q hq, raw_reference_evaluation_one F ζ hζ P T C q]
    rw [he]
    exact finprod_one
  simp only [rawFiniteTensorFunctional, PiTensorProduct.lift.tprod,
    MultilinearMap.smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, PiTensorProduct.dualDistrib_apply,
    hout, one_smul, LinearMap.compMultilinearMap_apply]

theorem raw_tensor_injective_of_finite_reachability
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (R : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q)
    (hR : RawTensorFormula F ζ hζ P T C Q S R)
    (hreach : ∀ t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q,
      (∀ q, q ∉ S → t q = 1) →
      ∃ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
        (g : KPGlobalTorusFunctionData.E F ζ hζ),
        (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
        (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) ∧
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val) :
    Function.Injective R := by
  intro a b hab
  apply sub_eq_zero.mp
  let x := a - b
  have hx : R x = 0 := by simp only [x, map_sub, hab, sub_self]
  apply rawFiniteTensor_evaluations_separate F ζ hζ P T C S x
  intro t
  let t' : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q :=
    fun q => if h : q ∈ S then t ⟨q, h⟩ else 1
  have ht' : ∀ q, q ∉ S → t' q = 1 := fun q hq => dif_neg hq
  obtain ⟨raw, g, hraw, ht, hg⟩ := hreach t' ht'
  have he := rawTensorFormula_eq_functional F ζ hζ P T C Q S hS R hR raw t' g hraw ht hg x
  rw [hx] at he
  have hz : rawFiniteTensorFunctional F ζ hζ P T C S t' x = 0 := he.symm
  rw [rawFiniteTensorFunctional_eq_dual_of_trivial_outside F ζ hζ P T C S t' ht'] at hz
  convert hz using 1
  congr 3
  funext q
  exact congrArg (rawEvaluationLinear F ζ hζ P T C q.val)
    (show t q = t' q.val by simp [t', q.property])

open KPAdelicCoverRestrictedProduct
 def localRaw (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) :=
  KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (ActualFiniteTorus.sheet F ζ hζ q t) *
    KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (ActualFiniteTorus.coordinate F ζ hζ q t)
private theorem localRaw_spec (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (localRaw F ζ hζ q t) = t.val := by
  rw [localRaw, map_mul]
  exact ((ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 t).symm
private theorem localRaw_diagonal (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    (localRaw F ζ hζ q t).g 1 0 = 0 ∧ (localRaw F ζ hζ q t).g 0 1 = 0 := by
  simp [localRaw, KPLocalCover.centralInjection, KPStandardLocalRootLifts.A,
    KPLocalCover.projection, KubotaRankTwo.d, Matrix.mul_apply,
    MonoidHom.coe_mk, OneHom.coe_mk]
  exact ⟨rfl, rfl⟩
 def finiteRawTuple (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q) : RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q => if q ∈ S then localRaw F ζ hζ q (t q) else 1,
    by
      apply Filter.eventually_cofinite.mpr
      apply (S.finite_toSet.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).subset
      intro v hv
      cases v with
      | inl w => exact False.elim (hv (Subgroup.one_mem _))
      | inr q =>
        by_cases hq : q ∈ S
        · exact ⟨q, hq, rfl⟩
        · apply False.elim
          apply hv
          change (if q ∈ S then localRaw F ζ hζ q (t q) else 1) ∈ compact F ζ hζ (Sum.inr q)
          rw [if_neg hq]
          exact (compact F ζ hζ (Sum.inr q)).one_mem⟩
private theorem finiteRawTuple_diagonal (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    restrictedProjection F ζ hζ (finiteRawTuple F ζ hζ S t) 1 0 = 0 ∧
      restrictedProjection F ζ hζ (finiteRawTuple F ζ hζ S t) 0 1 = 0 := by
  have hd (i j : Fin 2) (hij : i ≠ j) :
      restrictedProjection F ζ hζ (finiteRawTuple F ζ hζ S t) i j = 0 := by
    apply Prod.ext
    · funext w
      simp [restrictedProjection, matrixValue, KPAdelicCoverCertificatesRaw.matrixValue,
        KPAdelicCoverCertificatesRaw.matrixEntry, matrixEntry, finiteRawTuple, hij]
      rfl
    · apply RestrictedProduct.ext
      intro q
      change (if q ∈ S then localRaw F ζ hζ q (t q) else 1).g i j = 0
      by_cases hq : q ∈ S
      · rw [if_pos hq]
        fin_cases i <;> fin_cases j <;> simp_all [localRaw_diagonal F ζ hζ q (t q)]
      · simp [hq, hij]
  exact ⟨hd 1 0 (by decide), hd 0 1 (by decide)⟩
theorem raw_finite_tuple_reachable (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : ∀ q, q ∉ S → t q = 1) :
    ∃ (raw : RestrictedCover F ζ hζ) (g : KPGlobalTorusFunctionData.E F ζ hζ),
      (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
      (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) ∧
      scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) = g.val := by
  let raw := finiteRawTuple F ζ hζ S t
  let a := scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)
  have ha : a ∈ KPGlobalTorusFunctionData.torus F ζ hζ := by
    refine ⟨restrictedProjection F ζ hζ raw, ?_,
      (finiteRawTuple_diagonal F ζ hζ S t).1, (finiteRawTuple_diagonal F ζ hζ S t).2⟩
    rfl
  refine ⟨raw, ⟨a, ha⟩, fun w => rfl, ?_, rfl⟩
  intro q
  change (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
    (if q ∈ S then localRaw F ζ hζ q (t q) else 1)
  by_cases hq : q ∈ S
  · rw [if_pos hq, localRaw_spec]
  · rw [if_neg hq, map_one, ht q hq]
    rfl

theorem raw_tensor_formula_injective
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (R : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q)
    (hR : RawTensorFormula F ζ hζ P T C Q S R) : Function.Injective R := by
  exact raw_tensor_injective_of_finite_reachability F ζ hζ P T C Q S hS R hR
    (fun t ht => raw_finite_tuple_reachable F ζ hζ S t ht)

theorem raw_tensor_family_identification
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (R : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S),
      RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
          KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q)
    (hR : ∀ S hS, RawTensorFormula F ζ hζ P T C Q S (R S hS)) :
    (∀ S hS, Function.Injective (R S hS)) ∧
    (∀ f : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q,
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
        (x : RestrictedTensorSimple.Stage
          (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S),
        R S hS x = f) ∧
    (∀ (S U : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) (hSU : S ⊆ U),
      (R U (hS.trans hSU)).comp
        (RestrictedTensorSimple.insert
          (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q))
          C.reference S U hSU) = R S hS) := by
  have hcover : ∀ g : KPGlobalTorusFunctionData.E F ζ hζ,
      ∃ (b : Q.H) (a : KPGlobalTorusFunctionData.E F ζ hζ),
        a ∈ rawReachableTorus F ζ hζ ∧ g = b.val * a := by
    intro g
    obtain ⟨b, a, hg⟩ :=
      KPGlobalTorusFiniteStagesIdentification.raw_unit_product_covariant_cover
        F ζ hζ P T Q hQ g
    exact ⟨b, a.g, ⟨a.raw, a.t, a.infinite_one, a.local_lift, a.global_lift⟩, hg⟩
  refine ⟨fun S hS => raw_tensor_formula_injective F ζ hζ P T C Q S hS
    (R S hS) (hR S hS), ?_, ?_⟩
  · intro f
    obtain ⟨S, hS, x, hx⟩ :=
      KPGlobalTorusFiniteStagesIdentification.raw_smooth_restriction_finite_tensor
        F ζ hζ P T C Q hQ f
    refine ⟨S, hS, x, ?_⟩
    apply Subtype.ext
    apply scalar_functions_ext_of_covariant_cover F ζ hζ Q
      (rawReachableTorus F ζ hζ) hcover
    intro a ha
    obtain ⟨raw, t, hraw, ht, hg⟩ := ha
    rw [rawTensorFormula_eq_functional F ζ hζ P T C Q S hS
      (R S hS) (hR S hS) raw t a hraw ht hg x]
    exact congrFun hx
      (⟨raw, t, a, hraw, ht, hg⟩ : RawEvaluationPoint F ζ hζ)
  · intro S U hS hSU
    exact raw_tensor_insertion_compatible_of_covariant_cover
      F ζ hζ P T C Q hQ R hR hcover S U hS hSU

end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end
