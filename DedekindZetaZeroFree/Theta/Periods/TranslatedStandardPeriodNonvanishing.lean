module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData
public import DedekindZetaZeroFree.Adeles.Characters.RationalFrequencyNontriviality
public import DedekindZetaZeroFree.Eisenstein.Residues.GenericityAndPeriodNonvanishing

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped NumberField Pointwise Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod
open KPGlobalResidualConstruction

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actual_upper_root_continuous : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
  letI : ∀ v : KPHilbert.Place F, TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : TopologicalSpace (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.restrictedTopology F ζ hζ
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hcoord (v : KPHilbert.Place F) :
      Continuous (fun x : KPGlobalTorusFunctionData.Adeles F =>
        KPStandardLocalRootLifts.N F ζ hζ v
          (KPAdelicCoverRestrictedProduct.adeleEval F v x)) := by
    cases v with
    | inl w =>
      exact (KPStandardLocalRootLifts.complex_N_continuous F ζ hζ w).comp
        ((continuous_apply w).comp continuous_fst)
    | inr q =>
      exact (KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).comp
        ((RestrictedProduct.continuous_eval q).comp continuous_snd)
  let U : Set (KPGlobalTorusFunctionData.Adeles F) :=
    {x | ∀ q, ¬ KPAdelicCoverRestrictedProduct.Bad F q →
      x.2 q ∈ q.adicCompletionIntegers F}
  have hU : IsOpen U :=
    (RestrictedProduct.isOpen_forall_imp_mem
      (fun q : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring
        (q.adicCompletion F))).preimage continuous_snd
  have h0 : (0 : KPGlobalTorusFunctionData.Adeles F) ∈ U := by
    intro q hq
    exact zero_mem _
  let S : Set (KPHilbert.Place F) :=
    {v | match v with | .inl _ => True | .inr q => ¬ KPAdelicCoverRestrictedProduct.Bad F q}
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ S
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨Set.toFinite _, by simpa [S] using KPAdelicCoverRestrictedProduct.bad_finite F⟩
  have hmem (x : U) (v : KPHilbert.Place F) (hv : v ∈ S) :
      KPStandardLocalRootLifts.N F ζ hζ v
        (KPAdelicCoverRestrictedProduct.adeleEval F v x) ∈
          KPAdelicCoverRestrictedProduct.compact F ζ hζ v := by
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q =>
      have hi (t : q.adicCompletion F) :
          t ∈ KPTameCompact.O F q ↔ t ∈ q.adicCompletionIntegers F := by
        letI : ValuativeRel (q.adicCompletion F) :=
          ClassFieldTheory.finitePlaceCompletionValuativeRel F q
        change (ValuativeRel.valuation (q.adicCompletion F)) t ≤ 1 ↔ Valued.v t ≤ 1
        rw [← Valuation.vle_one_iff]
        letI : Valued.v.Compatible := Valuation.Compatible.ofValuation
          (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))
        exact Valuation.vle_one_iff Valued.v
      have hx : x.val.2 q ∈ KPTameCompact.O F q := (hi _).mpr (x.property q hv)
      simp only [KPAdelicCoverRestrictedProduct.compact,
        KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hv]
      refine ⟨KPStandardLocalRootLifts.integralN F q ⟨_, hx⟩, ?_⟩
      exact (KPStandardLocalRootLifts.N_eq_compact F ζ hζ q
        (fun h3 => hv (Or.inr h3)) ⟨_, hx⟩).symm
  let f : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _))
      (Filter.principal S) :=
    fun x => ⟨fun v => KPStandardLocalRootLifts.N F ζ hζ v
      (KPAdelicCoverRestrictedProduct.adeleEval F v x), hmem x⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun v => (hcoord v).comp continuous_subtype_val))
  have hrt : ContinuousAt (KPGlobalTorusFunctionData.rootTuple F ζ hζ) 0 := by
    have hr : Continuous (U.domRestrict (KPGlobalTorusFunctionData.rootTuple F ζ hζ)) :=
      (RestrictedProduct.continuous_inclusion hS).comp hf
    exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hU.mem_nhds h0)
  have hN : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
    have hh : Continuous (KPGlobalTorusFunctionData.Nhom F ζ hζ) := by
      apply continuous_of_continuousAt_one
      exact QuotientGroup.continuous_mk.continuousAt.comp
        (QuotientGroup.continuous_mk.continuousAt.comp hrt)
    exact hh
  exact hN

end DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped NumberField Pointwise Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod
open KPGlobalResidualConstruction

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem global_root_continuous : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
  letI : ∀ v : KPHilbert.Place F, TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : TopologicalSpace (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.restrictedTopology F ζ hζ
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hcoord (v : KPHilbert.Place F) :
      Continuous (fun x : KPGlobalTorusFunctionData.Adeles F =>
        KPStandardLocalRootLifts.N F ζ hζ v
          (KPAdelicCoverRestrictedProduct.adeleEval F v x)) := by
    cases v with
    | inl w =>
      exact (KPStandardLocalRootLifts.complex_N_continuous F ζ hζ w).comp
        ((continuous_apply w).comp continuous_fst)
    | inr q =>
      exact (KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).comp
        ((RestrictedProduct.continuous_eval q).comp continuous_snd)
  let U : Set (KPGlobalTorusFunctionData.Adeles F) :=
    {x | ∀ q, ¬ KPAdelicCoverRestrictedProduct.Bad F q →
      x.2 q ∈ q.adicCompletionIntegers F}
  have hU : IsOpen U :=
    (RestrictedProduct.isOpen_forall_imp_mem
      (fun q : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring
        (q.adicCompletion F))).preimage continuous_snd
  have h0 : (0 : KPGlobalTorusFunctionData.Adeles F) ∈ U := by
    intro q hq
    exact zero_mem _
  let S : Set (KPHilbert.Place F) :=
    {v | match v with | .inl _ => True | .inr q => ¬ KPAdelicCoverRestrictedProduct.Bad F q}
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ S
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨Set.toFinite _, by simpa [S] using KPAdelicCoverRestrictedProduct.bad_finite F⟩
  have hmem (x : U) (v : KPHilbert.Place F) (hv : v ∈ S) :
      KPStandardLocalRootLifts.N F ζ hζ v
        (KPAdelicCoverRestrictedProduct.adeleEval F v x) ∈
          KPAdelicCoverRestrictedProduct.compact F ζ hζ v := by
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q =>
      have hi (t : q.adicCompletion F) :
          t ∈ KPTameCompact.O F q ↔ t ∈ q.adicCompletionIntegers F := by
        letI : ValuativeRel (q.adicCompletion F) :=
          ClassFieldTheory.finitePlaceCompletionValuativeRel F q
        change (ValuativeRel.valuation (q.adicCompletion F)) t ≤ 1 ↔ Valued.v t ≤ 1
        rw [← Valuation.vle_one_iff]
        letI : Valued.v.Compatible := Valuation.Compatible.ofValuation
          (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))
        exact Valuation.vle_one_iff Valued.v
      have hx : x.val.2 q ∈ KPTameCompact.O F q := (hi _).mpr (x.property q hv)
      simp only [KPAdelicCoverRestrictedProduct.compact,
        KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hv]
      refine ⟨KPStandardLocalRootLifts.integralN F q ⟨_, hx⟩, ?_⟩
      exact (KPStandardLocalRootLifts.N_eq_compact F ζ hζ q
        (fun h3 => hv (Or.inr h3)) ⟨_, hx⟩).symm
  let f : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _))
      (Filter.principal S) :=
    fun x => ⟨fun v => KPStandardLocalRootLifts.N F ζ hζ v
      (KPAdelicCoverRestrictedProduct.adeleEval F v x), hmem x⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun v => (hcoord v).comp continuous_subtype_val))
  have hrt : ContinuousAt (KPGlobalTorusFunctionData.rootTuple F ζ hζ) 0 := by
    have hr : Continuous (U.domRestrict (KPGlobalTorusFunctionData.rootTuple F ζ hζ)) :=
      (RestrictedProduct.continuous_inclusion hS).comp hf
    exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hU.mem_nhds h0)
  have hN : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
    have hh : Continuous (KPGlobalTorusFunctionData.Nhom F ζ hζ) := by
      apply continuous_of_continuousAt_one
      exact QuotientGroup.continuous_mk.continuousAt.comp
        (QuotientGroup.continuous_mk.continuousAt.comp hrt)
    exact hh
  exact hN

private theorem globalRoot_eq_pglN (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x = KPRationalAdelicSplitting.pglN F ζ hζ x := by
  rfl

 theorem globalRoot_rationalDiagonal_conjugation (t : Fˣ)
    (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x *
        KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
      KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t *
        KPGlobalTorusFunctionData.N F ζ hζ
          (algebraMap F (KPGlobalTorusFunctionData.Adeles F) (↑t⁻¹ : F) * x) := by
  let y : KPGlobalTorusFunctionData.Ideles F := Units.map
    (algebraMap F (KPGlobalTorusFunctionData.Adeles F)).toMonoidHom t
  have hy : KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
      KPRationalAdelicSplitting.pglA F ζ hζ y := by
    unfold KPRationalAdelicSplitting.pglA
    dsimp [y]
    rw [KPRationalAdelicSplitting.A_rational]
    rfl
  simp_rw [hy, globalRoot_eq_pglN]
  have h := KPRationalAdelicSplitting.quotient_upper_diagonal F ζ hζ x y
  convert h using 2
  congr 1
  rw [mul_comm]
  rfl

private theorem B_one_left (v : KPHilbert.Place F) (a : (KPHilbert.Completion F v)ˣ) :
    KPHilbert.B3 F ζ hζ v 1 a = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 a
private theorem B_one_right (v : KPHilbert.Place F) (a : (KPHilbert.Completion F v)ˣ) :
    KPHilbert.B3 F ζ hζ v a 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 a
 theorem local_weyl_upper_swap (v : KPHilbert.Place F) (x : KPHilbert.Completion F v) :
    KPStandardLocalRootLifts.W F ζ hζ v * KPStandardLocalRootLifts.N F ζ hζ v x =
    KPStandardLocalRootLifts.LowerN F ζ hζ v x * KPStandardLocalRootLifts.W F ζ hζ v := by
  unfold KPStandardLocalRootLifts.W KPStandardLocalRootLifts.N KPStandardLocalRootLifts.LowerN
  change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
  congr 1
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.weylSwap, KPStandardLocalRootLifts.lowerN,
        KubotaRankTwo.n, Matrix.mul_apply, KPLocalCover.sectionMap]
  · simp only [KPLocalCover.sectionMap_g, KPLocalCover.sectionMap_epsilon, one_mul]
    have hX : KubotaRankTwo.X (KPHilbert.Completion F v)
        (KPStandardLocalRootLifts.lowerN (KPHilbert.Completion F v) x *
          KPStandardLocalRootLifts.weylSwap (KPHilbert.Completion F v)) = 1 := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.lowerN,
        KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply]
    have hW : KubotaRankTwo.X (KPHilbert.Completion F v)
        (KPStandardLocalRootLifts.weylSwap (KPHilbert.Completion F v)) = 1 := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap]
    have hd : KubotaRankTwo.det (KPHilbert.Completion F v)
        (KPStandardLocalRootLifts.lowerN (KPHilbert.Completion F v) x) = 1 := by
      apply Units.ext
      simp [KubotaRankTwo.det, KPStandardLocalRootLifts.lowerN, Matrix.det_fin_two]
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      hX, hW, hd, B_one_left, B_one_right]
theorem adelic_weyl_upper_swap (x : KPAdelicCoverRestrictedProduct.Adeles F) :
    KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x =
    KPRationalAdelicSplitting.pglLowerN F ζ hζ x * KPRationalAdelicSplitting.pglW F ζ hζ := by
  have hh : KPRationalAdelicSplitting.W F ζ hζ * KPRationalAdelicSplitting.N F ζ hζ x =
      KPRationalAdelicSplitting.LowerN F ζ hζ x * KPRationalAdelicSplitting.W F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _ *
        KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _ =
      KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _ *
        KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _
    rw [← map_mul, ← map_mul]
    congr 1
    apply RestrictedProduct.ext
    intro v
    exact local_weyl_upper_swap F ζ hζ v _
  have hN : KPGlobalTorusFunctionData.N F ζ hζ x = KPRationalAdelicSplitting.pglN F ζ hζ x := by
    unfold KPGlobalTorusFunctionData.N KPRationalAdelicSplitting.pglN KPRationalAdelicSplitting.N
    congr 2
  rw [hN]
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ) hh

theorem adelic_lower_eq_weyl_upper (x : KPAdelicCoverRestrictedProduct.Adeles F) :
    KPRationalAdelicSplitting.pglLowerN F ζ hζ x =
      KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        (KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ := by
  rw [adelic_weyl_upper_swap, mul_inv_cancel_right]

theorem lower_invariance_of_upper (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hu : ∀ x g, θ (KPGlobalTorusFunctionData.N F ζ hζ x * g) = θ g)
    (hw : ∀ g, θ (KPRationalAdelicSplitting.pglW F ζ hζ * g) = θ g) :
    ∀ x g, θ (KPRationalAdelicSplitting.pglLowerN F ζ hζ x * g) = θ g := by
  have hwi : ∀ g, θ ((KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ * g) = θ g := by
    intro g
    simpa using (hw ((KPRationalAdelicSplitting.pglW F ζ hζ)⁻¹ * g)).symm
  intro x g
  rw [adelic_lower_eq_weyl_upper, mul_assoc, mul_assoc, hw, hu, hwi]

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
theorem actual_rational_diagonal_conjugation (t : Fˣ) (x : A F) :
    KPGlobalTorusFunctionData.N F ζ hζ x * KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
      KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t *
        KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F (A F) (↑t⁻¹ : F) * x) := by
  have h := KPRationalAdelicSplitting.quotient_upper_diagonal F ζ hζ x
    (Units.map (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)).toMonoidHom t)
  unfold KPRationalAdelicSplitting.pglA at h
  have he : KPRationalAdelicSplitting.A F ζ hζ
      (Units.map (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)).toMonoidHom t) =
        KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (KubotaRankTwo.d F t 1) := by
    exact KPRationalAdelicSplitting.A_rational F ζ hζ t
  rw [he] at h
  change KPGlobalTorusFunctionData.N F ζ hζ x * KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t =
    KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t *
      KPGlobalTorusFunctionData.N F ζ hζ (x * (algebraMap F (A F) (↑t⁻¹ : F))) at h
  simpa only [mul_comm x] using h
theorem actual_arch_single_diagonal (w : InfinitePlace F) (y : ℂˣ) :
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) =
      KPRationalAdelicSplitting.pglA F ζ hζ
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom y)) := by
  unfold KPGlobalTorusFunctionData.archDiagonalLift KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl u =>
    by_cases hu : u = w
    · subst u
      simp [KPGlobalTorusFunctionData.archDiagonalTuple, KPRationalAdelicSplitting.ATuple,
        KPRationalAdelicSplitting.ACoordinates, KPRationalAdelicSplitting.localIdele,
        KPAdelicCoverRestrictedProduct.adeleEval, y.ne_zero]
      congr 1
      apply Units.ext
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ) =
        Pi.mulSingle w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ)) w
      simp
    · simp [KPGlobalTorusFunctionData.archDiagonalTuple, KPRationalAdelicSplitting.ATuple,
        KPRationalAdelicSplitting.ACoordinates, KPRationalAdelicSplitting.localIdele,
        KPAdelicCoverRestrictedProduct.adeleEval, hu]
      rw [← KPStandardLocalRootLifts.A_one F ζ hζ (Sum.inl u)]
      congr 1
      apply Units.ext
      change 1 = Pi.mulSingle w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ)) u
      simp [hu]
  | inr q =>
    simp [KPGlobalTorusFunctionData.archDiagonalTuple, KPRationalAdelicSplitting.ATuple,
      KPRationalAdelicSplitting.ACoordinates, KPRationalAdelicSplitting.localIdele,
      KPAdelicCoverRestrictedProduct.adeleEval]
    rw [← KPStandardLocalRootLifts.A_one F ζ hζ (Sum.inr q)]
    congr 1

theorem actual_arch_single_weyl_conjugation (w : InfinitePlace F) (y : ℂˣ) :
    KPRationalAdelicSplitting.pglW F ζ hζ *
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) =
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (Function.update (fun _ => (1 : ℂ)) w (y⁻¹ : ℂˣ)) *
      KPRationalAdelicSplitting.pglW F ζ hζ := by
  rw [actual_arch_single_diagonal, actual_arch_single_diagonal]
  have h := KPRationalAdelicSplitting.quotient_weyl_diagonal F ζ hζ
    (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom y))
  simpa only [KPRationalAdelicSplitting.localIdele, map_inv] using h

end DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod

end
end
