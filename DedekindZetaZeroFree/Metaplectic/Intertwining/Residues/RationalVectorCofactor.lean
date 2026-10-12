module

public import DedekindZetaZeroFree.Adeles.Haar.FiniteRestrictedProductMeasure
public import DedekindZetaZeroFree.Metaplectic.Kubota.Induction.UnitaryRationalFiberComparison
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Global.FiniteSetEnlargement

@[expose] public section

noncomputable section
open scoped NumberField Classical
open MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPRankOneShellRepair

private theorem finite_image_at_one_nonzero
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    ∃ f : sectionSpace S.borel P .plus 0,
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ f).val 1 ≠ 0 := by
  have hn := (actual_zero_maps_nonzero F ζ hζ q S P μ hμ).1
  have hex : ∃ (f : sectionSpace S.borel P .plus 0) (g : ActualCover F ζ hζ q),
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ f).val g ≠ 0 := by
    by_contra he
    push Not at he
    apply hn
    ext f g h
    exact congrArg (fun v => v.val h) (he f g)
  obtain ⟨f,g,hg⟩ := hex
  refine ⟨IPlus S.borel P g f, ?_⟩
  have he := actualCanonicalForwardLinear_intertwines F ζ hζ q S P μ hμ g f
  change (actualCanonicalForwardLinear F ζ hζ q S P μ hμ (IPlus S.borel P g f)).val 1 ≠ 0
  rw [he]
  change (actualCanonicalForwardMap F ζ hζ q S P μ hμ f).val (1 * g) ≠ 0
  simpa only [one_mul] using hg

private theorem finite_tensor_nonzero
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (y : ∀ q : E, KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P₀ C₀ q.val)
    (hy : ∀ q, y q ≠ 0) : PiTensorProduct.tprod ℂ y ≠ 0 := by
  have hex (q : E) : ∃ t : actualTorus F ζ hζ q.val, (y q).val t ≠ 0 := by
    by_contra he
    push Not at he
    apply hy q
    apply Subtype.ext
    funext t
    exact he t
  choose t ht using hex
  let e : ∀ q : E, KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P₀ C₀ q.val →ₗ[ℂ] ℂ := fun q =>
    { toFun := fun v => v.val (t q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ E ℂ).compLinearMap e)
  intro hz
  have he := congrArg L hz
  simp only [L, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, map_zero] at he
  exact (Finset.prod_ne_zero_iff.mpr (fun q _ => ht q)) he

private theorem actual_rational_image_nonzero
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hE : C₀.exceptional ⊆ E)
    (y : ∀ q : E, KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P₀ C₀ q.val)
    (hy : ∀ q, y q ≠ 0) :
    ∃ t : KPGlobalTorusFunctionData.E F ζ hζ,
      ((PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P₀
        (KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P₀ C₀ E hE
          (PiTensorProduct.tprod ℂ y))).val.val t) ≠ 0 := by
  have hn := finite_tensor_nonzero F ζ hζ P₀ C₀ E y hy
  have hp : KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P₀ C₀ E hE
      (PiTensorProduct.tprod ℂ y) ≠ 0 := by
    intro hz
    apply hn
    exact (KPGlobalTorusFiniteStages.finiteTensorRealization_injective F ζ hζ P₀ C₀ E hE)
      (hz.trans (map_zero _).symm)
  have hr : PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P₀
      (KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P₀ C₀ E hE
        (PiTensorProduct.tprod ℂ y)) ≠ 0 := by
    intro hz
    apply hp
    exact (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational_injective F ζ hζ P₀)
      (hz.trans (map_zero _).symm)
  by_contra he
  push Not at he
  apply hr
  apply Subtype.ext
  apply Subtype.ext
  funext t
  exact he t

theorem unit_mass (F : Type) [Field F] [NumberField F]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q)
      ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1 := by
  have he : (valuation (LocalField F q)).integer = (q.adicCompletionIntegers F).toSubring := by
    let : (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    ext x
    change valuation (LocalField F q) x ≤ 1 ↔ Valued.v x ≤ 1
    exact (ValuativeRel.isEquiv (valuation (LocalField F q)) (Valued.v)).le_one_iff_le_one
  rw [he]
  exact Measure.addHaarMeasure_self (K₀ := finiteCompletionIntegersPositiveCompacts F q)

private theorem actual_finite_output_rational_nonzero
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hE : C₀.exceptional ⊆ E) :
    let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
      Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
    ∃ (f : ∀ q : E, sectionSpace (C₀.canonical q.val).borel (C₀.polarization q.val) .plus 0)
      (t : KPGlobalTorusFunctionData.E F ζ hζ),
      ((PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P₀
        (KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P₀ C₀ E hE
          (PiTensorProduct.tprod ℂ (fun q => (localHalfDifferentFactor F q.val : ℂ) •
            (actualCanonicalForwardMap F ζ hζ q.val (C₀.canonical q.val) (C₀.polarization q.val)
              (μ q) (unit_mass F q.val) (f q)).val 1)))).val.val t) ≠ 0 := by
  dsimp only
  let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
  let : ∀ q : E, (μ q).IsAddHaarMeasure := fun q => inferInstance
  have hex (q : E) := finite_image_at_one_nonzero F ζ hζ q.val (C₀.canonical q.val)
    (C₀.polarization q.val) (μ q) (unit_mass F q.val)
  choose f hf using hex
  obtain ⟨t,ht⟩ := actual_rational_image_nonzero F ζ hζ P₀ C₀ E hE
    (fun q => (localHalfDifferentFactor F q.val : ℂ) •
      (actualCanonicalForwardMap F ζ hζ q.val (C₀.canonical q.val) (C₀.polarization q.val)
        (μ q) (unit_mass F q.val) (f q)).val 1)
    (fun q => smul_ne_zero (Complex.ofReal_ne_zero.mpr (localHalfDifferentFactor_pos F q.val).ne') (hf q))
  exact ⟨f,t,ht⟩

private theorem finite_laurent_multilinear_regular
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (L : MultilinearMap ℂ V ℂ)
    (N : ι → Finset ℤ) (v : ∀ i, ℤ → V i)
    (a : ∀ _i, ℤ → ℂ → ℂ) (ha : ∀ i n, Differentiable ℂ (a i n))
    (d : ι → ℂ → ℂ) (hd : ∀ i, Differentiable ℂ (d i))
    (hd0 : ∀ i, d i 0 ≠ 0) :
    MeromorphicOn (fun s => L (fun i => (d i s)⁻¹ • ∑ n ∈ N i, a i n s • v i n)) Set.univ ∧
      AnalyticAt ℂ (fun s => L (fun i => (d i s)⁻¹ • ∑ n ∈ N i, a i n s • v i n)) 0 := by
  have he (s : ℂ) : L (fun i => (d i s)⁻¹ • ∑ n ∈ N i, a i n s • v i n) =
      (∏ i, (d i s)⁻¹) * ∑ r ∈ Fintype.piFinset N, (∏ i, a i (r i) s) * L (fun i => v i (r i)) := by
    rw [L.map_smul_univ, L.map_sum_finset, Finset.sum_congr rfl
      (fun r _ => L.map_smul_univ (fun i => a i (r i) s) (fun i => v i (r i)))]
    rfl
  simp_rw [he]
  have hn : AnalyticOnNhd ℂ
      (fun s => ∑ r ∈ Fintype.piFinset N, (∏ i, a i (r i) s) * L (fun i => v i (r i))) Set.univ := by
    intro s _
    apply Finset.analyticAt_fun_sum
    intro r _
    exact (Finset.analyticAt_fun_prod Finset.univ (fun i _ => (ha i (r i)).analyticAt s)).mul analyticAt_const
  constructor
  · intro s _
    have hm : MeromorphicAt (fun s => ∏ i, (d i s)⁻¹) s := by
      have hprod : MeromorphicAt (∏ i, (d i)⁻¹) s :=
        MeromorphicAt.prod (fun i _ => ((hd i).analyticAt s).meromorphicAt.inv)
      convert hprod using 1
      funext z
      simp
    exact hm.mul (hn s (Set.mem_univ s)).meromorphicAt
  · exact (Finset.analyticAt_fun_prod Finset.univ
      (fun i _ => ((hd i).analyticAt 0).inv (hd0 i))).mul (hn 0 (Set.mem_univ 0))

open KPRankOneShellContinuation
open _root_.DedekindZetaZeroFree.KPRankOneShellContinuation renaming eval_diff → eval_diff
open _root_.DedekindZetaZeroFree.KPRankOneShellContinuation renaming denom_diff → denom_diff

private theorem actual_local_vector_expansion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (k : S.iwasawa.compact.toOpenSubgroup) :
    ∃ (N : Finset ℤ) (v : ℤ → InducedModule P), ∀ s : ℂ,
      (actualCanonicalContinued F q ζ hζ S P μ hμ .plus s φ).val k =
        (denominator (LocalField F q) .plus s)⁻¹ •
          ∑ n ∈ N, (evaluationUnit (LocalField F q) .plus s : ℂ)^n • v n := by
  obtain ⟨J,hJ,hφ⟩ := actual_common_level F ζ hζ q S P .plus φ
  let p := actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .plus
  refine ⟨p.support,fun n => (((p n) ⟨φ,hφ⟩).val.val k),?_⟩
  intro s
  rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .plus s J hJ ⟨φ,hφ⟩]
  apply Subtype.ext
  funext t
  simp [continuedLevel,evaluate,Finsupp.sum,p]

def rationalStageEval
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hE : C₀.exceptional ⊆ E) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    MultilinearMap ℂ (fun q : E => KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P₀ C₀ q.val) ℂ :=
  let ev : smoothRationalFiber F ζ hζ →ₗ[ℂ] ℂ :=
    { toFun := fun v => v.val.val t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  (ev.comp ((PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P₀).comp
    (KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P₀ C₀ E hE))).compMultilinearMap
    (PiTensorProduct.tprod ℂ)

 theorem actual_rational_family_regular
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hE : C₀.exceptional ⊆ E)
    (μ : ∀ q : E, Measure (LocalField F q.val)) [∀ q : E, (μ q).IsAddHaarMeasure]
    (hμ : ∀ q : E, μ q ((valuation (LocalField F q.val)).integer : Set (LocalField F q.val)) = 1)
    (φ : ∀ q : E, compactPicture (C₀.canonical q.val).borel (C₀.polarization q.val)
      (C₀.canonical q.val).iwasawa .plus)
    (k : ∀ q : E, (C₀.canonical q.val).iwasawa.compact.toOpenSubgroup)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    let b : ℂ → ℂ := fun s => rationalStageEval F ζ hζ P₀ C₀ E hE t
      (fun q => (localHalfDifferentFactor F q.val : ℂ) •
        (actualCanonicalContinued F q.val ζ hζ (C₀.canonical q.val) (C₀.polarization q.val)
          (μ q) (hμ q) .plus s (φ q)).val (k q))
    MeromorphicOn b Set.univ ∧ AnalyticAt ℂ b 0 := by
  dsimp only
  have hex (q : E) := actual_local_vector_expansion F ζ hζ q.val (C₀.canonical q.val)
    (C₀.polarization q.val) (μ q) (hμ q) (φ q) (k q)
  choose N v hv using hex
  have he (s : ℂ) (q : E) : (localHalfDifferentFactor F q.val : ℂ) •
      (actualCanonicalContinued F q.val ζ hζ (C₀.canonical q.val) (C₀.polarization q.val)
        (μ q) (hμ q) .plus s (φ q)).val (k q) =
      (denominator (LocalField F q.val) .plus s)⁻¹ • ∑ n ∈ N q,
        (evaluationUnit (LocalField F q.val) .plus s : ℂ)^n •
          ((localHalfDifferentFactor F q.val : ℂ) • v q n) := by
    rw [hv, smul_comm, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact smul_comm _ _ _
  simp_rw [he]
  apply finite_laurent_multilinear_regular
  · intro q n
    exact (eval_diff (LocalField F q.val) .plus).zpow (Or.inl (fun s => Units.ne_zero _))
  · intro q
    exact denom_diff (LocalField F q.val) .plus
  · intro q
    exact denominator_ne_zero_at_zero (LocalField F q.val) .plus

private theorem compact_zero_at_one
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (f : sectionSpace S.borel P .plus 0) :
    (actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0
      ((compactTrivialization S.borel P S.iwasawa .plus 0).symm f)).val 1 =
    (actualCanonicalForwardMap F ζ hζ q S P μ hμ f).val 1 := by
  let v := actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0
    ((compactTrivialization S.borel P S.iwasawa .plus 0).symm f)
  have he := (compactTrivialization S.borel P S.iwasawa .minus 0).symm_apply_apply v
  change v.val 1 = (actualCanonicalForwardLinear F ζ hζ q S P μ hμ f).val 1
  rw [forwardIntegralLinear_eq_continuationWitness]
  exact (congrArg (fun v : compactPicture S.borel P S.iwasawa .minus => v.val 1) he).symm

theorem actual_rational_nonzero_cofactor
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hE : C₀.exceptional ⊆ E) :
    let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
      Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
    ∃ (φ : ∀ q : E, compactPicture (C₀.canonical q.val).borel (C₀.polarization q.val)
        (C₀.canonical q.val).iwasawa .plus)
      (t : KPGlobalTorusFunctionData.E F ζ hζ) (b : ℂ → ℂ),
      MeromorphicOn b Set.univ ∧ AnalyticAt ℂ b 0 ∧ b 0 ≠ 0 ∧
      ∀ s : ℂ, b s = rationalStageEval F ζ hζ P₀ C₀ E hE t
        (fun q => (localHalfDifferentFactor F q.val : ℂ) •
          (actualCanonicalContinued F q.val ζ hζ (C₀.canonical q.val) (C₀.polarization q.val)
            (μ q) (unit_mass F q.val) .plus s (φ q)).val 1) *
        ∏ _w : NumberField.InfinitePlace F, 2 * (Real.pi : ℂ) / ((1/3 : ℂ) + 2*s) := by
  let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
  let : ∀ q : E, (μ q).IsAddHaarMeasure := fun q => inferInstance
  obtain ⟨f,t,ht⟩ := actual_finite_output_rational_nonzero F ζ hζ P₀ C₀ E hE
  let φ (q : E) := (compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val)
    (C₀.canonical q.val).iwasawa .plus 0).symm (f q)
  let c : ℂ → ℂ := fun s => rationalStageEval F ζ hζ P₀ C₀ E hE t
    (fun q => (localHalfDifferentFactor F q.val : ℂ) •
      (actualCanonicalContinued F q.val ζ hζ (C₀.canonical q.val) (C₀.polarization q.val)
        (μ q) (unit_mass F q.val) .plus s (φ q)).val 1)
  have hc := actual_rational_family_regular F ζ hζ P₀ C₀ E hE μ
    (fun q => unit_mass F q.val) φ (fun _ => 1) t
  have hcn : c 0 ≠ 0 := by
    dsimp [c,φ]
    simp_rw [compact_zero_at_one]
    exact ht
  let a : ℂ → ℂ := fun s => 2 * (Real.pi : ℂ) / ((1/3 : ℂ) + 2*s)
  have ha : MeromorphicOn a Set.univ := fun s _ =>
    analyticAt_const.meromorphicAt.div (by fun_prop)
  have ha0 : AnalyticAt ℂ a 0 := analyticAt_const.div (by fun_prop) (by norm_num)
  have han : a 0 ≠ 0 := by
    dsimp [a]
    exact div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) (by norm_num)
  let b : ℂ → ℂ := fun s => c s * ∏ _w : NumberField.InfinitePlace F, a s
  refine ⟨φ,t,b,?_,?_,?_,fun _ => rfl⟩
  · intro s _
    have hp : MeromorphicAt (∏ _w : NumberField.InfinitePlace F, a) s :=
      MeromorphicAt.prod (fun _ _ => ha s (Set.mem_univ s))
    convert (hc.1 s (Set.mem_univ s)).mul hp using 1
    funext z
    simp [b,c]
  · exact hc.2.mul (Finset.analyticAt_fun_prod Finset.univ (fun _ _ => ha0))
  · exact mul_ne_zero hcn (Finset.prod_ne_zero_iff.mpr (fun _ _ => han))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor

end
