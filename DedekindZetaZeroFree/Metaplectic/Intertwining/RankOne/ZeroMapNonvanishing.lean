module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseOperatorEvaluation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ForwardIntegralOperator

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter

set_option autoImplicit false

namespace OpenCellNonzero

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

private theorem evaluation_entire (ε : Sign) :
    Differentiable ℂ (fun s => (evaluationUnit (LocalField F q) ε s : ℂ)) := by
  have hr : Differentiable ℂ (r (LocalField F q)) := by unfold r; fun_prop
  cases ε with
  | plus => exact hr
  | minus => exact hr.inv (fun s => Complex.exp_ne_zero _)

private theorem denominator_entire (ε : Sign) :
    Differentiable ℂ (denominator (LocalField F q) ε) := by
  cases ε with
  | plus =>
    unfold denominator t r
    simp only [if_pos rfl, if_true]
    fun_prop
  | minus =>
    unfold denominator
    simp only [Sign.noConfusion, reduceCtorEq, if_false]
    exact differentiable_const 1 |>.sub ((differentiable_const _).mul
      ((evaluation_entire F q .minus).pow 6))

private theorem numerator_coordinate_entire
    (J : CompactOpenLevel (ActualCover F ζ hζ q)) (ε : Sign)
    (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    Differentiable ℂ (fun s =>
      ((evaluate (LocalField F q) S.borel P S.iwasawa J ε p
        (evaluationUnit (LocalField F q) ε s) φ).val.val k).val h) := by
  classical
  simp only [evaluate, Finsupp.sum, LinearMap.smul_apply, Submodule.coe_smul,
    Submodule.coe_sum, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Differentiable.fun_sum
  intro n hn
  exact ((evaluation_entire F q ε).zpow (Or.inl (fun s => Units.ne_zero _))).mul_const _

theorem both_actual_maps_nonzero_of_compact
    (hnonzero : ∀ ε : Sign, actualCanonicalContinued F q ζ hζ S P μ hμ ε 0 ≠ 0) :
    actualCanonicalForwardMap F ζ hζ q S P μ hμ ≠ 0 ∧
      actualCanonicalReverseMap F ζ hζ q S P μ hμ ≠ 0 := by
  constructor
  · intro hz
    have he := congrArg (fun M : (IPlus S.borel P).IntertwiningMap (IMinus S.borel P) => M.toLinearMap) hz
    change actualCanonicalForwardLinear F ζ hζ q S P μ hμ = 0 at he
    have hlinear : actualCanonicalForwardLinear F ζ hζ q S P μ hμ =
        forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g
      apply Subtype.ext
      funext h
      exact (forwardIntegralContinuationLinearWitness_eq_integral F ζ hζ q S P μ hμ
        f g h).symm
    rw [hlinear] at he
    apply hnonzero .plus
    change (actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0 :
      compactPicture S.borel P S.iwasawa .plus →ₗ[ℂ] compactPicture S.borel P S.iwasawa .minus) = 0
    apply LinearMap.ext
    intro φ
    have hv := congrArg (fun M => M (compactTrivialization S.borel P S.iwasawa .plus 0 φ)) he
    change compactTrivialization S.borel P S.iwasawa .minus 0
      (actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0
        ((compactTrivialization S.borel P S.iwasawa .plus 0).symm
          (compactTrivialization S.borel P S.iwasawa .plus 0 φ))) = 0 at hv
    have hφ := (compactTrivialization S.borel P S.iwasawa .plus 0).symm_apply_apply φ
    have hv' := (congrArg (fun ψ : compactPicture S.borel P S.iwasawa .plus =>
      compactTrivialization S.borel P S.iwasawa .minus 0
        (actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0 ψ)) hφ).symm.trans hv
    apply (compactTrivialization S.borel P S.iwasawa .minus 0).injective
    change _ = compactTrivialization S.borel P S.iwasawa .minus 0 0
    rw [LinearEquiv.map_zero]
    exact hv'
  · intro hz
    have he := congrArg (fun M : (IMinus S.borel P).IntertwiningMap (IPlus S.borel P) => M.toLinearMap) hz
    change actualCanonicalReverseLinear F ζ hζ q S P μ hμ = 0 at he
    apply hnonzero .minus
    change (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0 :
      compactPicture S.borel P S.iwasawa .minus →ₗ[ℂ] compactPicture S.borel P S.iwasawa .plus) = 0
    apply LinearMap.ext
    intro φ
    have hv := congrArg (fun M => M (compactTrivialization S.borel P S.iwasawa .minus 0 φ)) he
    change compactTrivialization S.borel P S.iwasawa .plus 0
      (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0
        ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
          (compactTrivialization S.borel P S.iwasawa .minus 0 φ))) = 0 at hv
    have hφ := (compactTrivialization S.borel P S.iwasawa .minus 0).symm_apply_apply φ
    have hv' := (congrArg (fun ψ : compactPicture S.borel P S.iwasawa .minus =>
      compactTrivialization S.borel P S.iwasawa .plus 0
        (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0 ψ)) hφ).symm.trans hv
    apply (compactTrivialization S.borel P S.iwasawa .plus 0).injective
    change _ = compactTrivialization S.borel P S.iwasawa .plus 0 0
    rw [LinearEquiv.map_zero]
    exact hv'

theorem zero_coordinate_of_holomorphic_combination
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) {ι : Type} [Fintype ι]
    (φ : ι → compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (a : ι → ℂ → ℂ) (ha : ∀ i, Differentiable ℂ (a i))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q)
    (C : ℂ)
    (hchamber : ∀ s : ℂ, convergenceHalfPlane ε s →
      ∑ i, a i s * standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
        (φ i).val k h = C) :
    ((actualCanonicalContinued F q ζ hζ S P μ hμ ε 0
      (∑ i, a i 0 • (φ i).val)).val k).val h = C := by
  classical
  let p := actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ ε
  let f : ℂ → ℂ := fun s => ∑ i, a i s *
    ((evaluate (LocalField F q) S.borel P S.iwasawa J ε p
      (evaluationUnit (LocalField F q) ε s) (φ i)).val.val k).val h
  let g : ℂ → ℂ := fun s => denominator (LocalField F q) ε s * C
  have hf : AnalyticOnNhd ℂ f Set.univ := by
    have hd : Differentiable ℂ f := Differentiable.fun_sum (fun i _ =>
      (ha i).mul (numerator_coordinate_entire F ζ hζ q S P J ε p (φ i) k h))
    exact fun z _ => hd.analyticAt z
  have hg : AnalyticOnNhd ℂ g Set.univ := fun z _ =>
    ((denominator_entire F q ε).mul_const C).analyticAt z
  have hopen : IsOpen {s : ℂ | convergenceHalfPlane ε s} := by
    cases ε with
    | plus => exact isOpen_lt continuous_const Complex.continuous_re
    | minus =>
      change IsOpen {s : ℂ | s.re < -(1 / 6 : ℝ)}
      exact isOpen_lt Complex.continuous_re continuous_const
  let z : ℂ := if ε = .plus then 0 else -1
  have hz : convergenceHalfPlane ε z := by cases ε <;> norm_num [z, convergenceHalfPlane]
  have he : f =ᶠ[nhds z] g := by
    filter_upwards [hopen.mem_nhds hz] with s hs
    dsimp [f, g]
    have hp (i : ι) :
        ((evaluate (LocalField F q) S.borel P S.iwasawa J ε p
          (evaluationUnit (LocalField F q) ε s) (φ i)).val.val k).val h =
        denominator (LocalField F q) ε s *
          standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s (φ i).val k h :=
      actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ ε s hs (φ i) k h
    simp_rw [hp]
    rw [show (∑ i, a i s * (denominator (LocalField F q) ε s *
        standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s (φ i).val k h)) =
        denominator (LocalField F q) ε s * ∑ i, a i s *
          standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s (φ i).val k h by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring, hchamber s hs]
  have hzero := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ
    (Set.mem_univ z) he (Set.mem_univ (0 : ℂ))
  have hsum : ((actualCanonicalContinued F q ζ hζ S P μ hμ ε 0
      (∑ i, a i 0 • (φ i).val)).val k).val h =
      (denominator (LocalField F q) ε 0)⁻¹ * f 0 := by
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ ε 0 J hJ]
    change (∑ i, a i 0 * ((continuedLevel (LocalField F q) S.borel P S.iwasawa J ε p 0 (φ i)).val.val k).val h) = _
    change (∑ i, a i 0 * ((denominator (LocalField F q) ε 0)⁻¹ *
      ((evaluate (LocalField F q) S.borel P S.iwasawa J ε p
        (evaluationUnit (LocalField F q) ε 0) (φ i)).val.val k).val h)) = _
    dsimp [f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, hzero]
  dsimp [g]
  rw [← mul_assoc, inv_mul_cancel₀ (denominator_ne_zero_at_zero (LocalField F q) ε), one_mul]

theorem both_actual_maps_nonzero_of_holomorphic_tests
    (htest : ∀ ε : Sign,
      ∃ (J : CompactOpenLevel (ActualCover F ζ hζ q))
        (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
        (n : ℕ) (φ : Fin n → compactLevel S.borel P S.iwasawa (sourceSign ε) J)
        (a : Fin n → ℂ → ℂ) (k : S.iwasawa.compact.toOpenSubgroup)
        (h : actualTorus F ζ hζ q) (C : ℂ),
        (∀ i, Differentiable ℂ (a i)) ∧ C ≠ 0 ∧
        ∀ s : ℂ, convergenceHalfPlane ε s →
          ∑ i, a i s * standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
            (φ i).val k h = C) :
    actualCanonicalForwardMap F ζ hζ q S P μ hμ ≠ 0 ∧
      actualCanonicalReverseMap F ζ hζ q S P μ hμ ≠ 0 := by
  apply both_actual_maps_nonzero_of_compact F ζ hζ q S P μ hμ
  intro ε hz
  obtain ⟨J, hJ, n, φ, a, k, h, C, ha, hC, hch⟩ := htest ε
  have he := zero_coordinate_of_holomorphic_combination F ζ hζ q S P μ hμ
    J hJ ε φ a ha k h C hch
  have hz' := congrArg (fun M =>
    ((M (∑ i, a i 0 • (φ i).val) : compactPicture S.borel P S.iwasawa (targetSign ε)).val k).val h) hz
  exact hC (he.symm.trans hz')

include hμ in

theorem chamber_coordinate_of_characteristic_combination
    (ε : Sign) {ι : Type} [Fintype ι]
    (φ : ι → compactPicture S.borel P S.iwasawa (sourceSign ε))
    (a : ι → ℂ → ℂ)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q)
    (U : Set (LocalField F q)) (hU : MeasurableSet U) (v : InducedModule P)
    (hcell : ∀ (s : ℂ), convergenceHalfPlane ε s → ∀ x : LocalField F q,
      ∑ i, a i s •
        (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) (φ i)).val
          (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * k) =
            U.indicator (fun _ => v) x) :
    ∀ s : ℂ, convergenceHalfPlane ε s →
      ∑ i, a i s * standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
        (φ i) k h = (μ U).toReal * v.val h := by
  classical
  intro s hs
  let b : ι → LocalField F q → ℂ := fun i x =>
    ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) (φ i)).val
      (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * k)).val h
  have hint (i : ι) : Integrable (b i) μ :=
    actualCanonicalContinued_integrable F q ζ hζ S P μ hμ ε s hs
      (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) (φ i)) k h
  have he : (fun x => ∑ i, a i s * b i x) = U.indicator (fun _ => v.val h) := by
    funext x
    have hx := congrArg (fun v : InducedModule P => v.val h) (hcell s hs x)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hx
    by_cases hxu : x ∈ U
    · simp only [Set.indicator_of_mem hxu] at hx ⊢
      exact hx
    · simp only [Set.indicator_of_notMem hxu] at hx ⊢
      exact hx
  calc
    (∑ i, a i s * standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s (φ i) k h) =
        ∑ i, ∫ x, a i s * b i x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_const_mul (a i s) (b i)).symm
    _ = ∫ x, ∑ i, a i s * b i x ∂μ :=
      (integral_finset_sum _ (fun i _ => (hint i).const_mul (a i s))).symm
    _ = ∫ x, U.indicator (fun _ => v.val h) x ∂μ := by rw [he]
    _ = (μ U).toReal * v.val h := by
      rw [integral_indicator hU, integral_const]
      simp [Measure.real, Measure.restrict_apply, Complex.real_smul]

theorem exists_nonzero_inducing_coordinate :
    ∃ (v : InducedModule P) (h : actualTorus F ζ hζ q), v.val h ≠ 0 := by
  have hfin : Module.Finite ℂ (InducedModule P) := tau_moduleFinite S.heisenberg P
  letI := hfin
  have hpos : 0 < Module.finrank ℂ (InducedModule P) := by
    rw [tau_finrank_eq_index S.heisenberg P]
    exact Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := P.L.comap S.heisenberg.π))
  letI := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : InducedModule P)
  have hh : ∃ h, v.val h ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hv
    apply Subtype.ext
    funext h
    exact hn h
  obtain ⟨h, hh⟩ := hh
  exact ⟨v, h, hh⟩

theorem both_actual_maps_nonzero_of_bruhat_families
    (htest : ∀ (ε : Sign) (v : InducedModule P),
      ∃ (J : CompactOpenLevel (ActualCover F ζ hζ q))
        (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
        (n : ℕ) (φ : Fin n → compactLevel S.borel P S.iwasawa (sourceSign ε) J)
        (a : Fin n → ℂ → ℂ) (k : S.iwasawa.compact.toOpenSubgroup)
        (U : Set (LocalField F q)),
        IsCompact U ∧ IsOpen U ∧ 0 < μ U ∧ μ U ≠ ⊤ ∧
        (∀ i, Differentiable ℂ (a i)) ∧
        ∀ (s : ℂ) (x : LocalField F q),
          ∑ i, a i s •
            (compactTrivialization S.borel P S.iwasawa (sourceSign ε)
              (sourceParameter ε s) (φ i).val).val
              (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * k) =
            U.indicator (fun _ => v) x) :
    actualCanonicalForwardMap F ζ hζ q S P μ hμ ≠ 0 ∧
      actualCanonicalReverseMap F ζ hζ q S P μ hμ ≠ 0 := by
  apply both_actual_maps_nonzero_of_holomorphic_tests F ζ hζ q S P μ hμ
  intro ε
  obtain ⟨v, h, hv⟩ := exists_nonzero_inducing_coordinate F ζ hζ q S P
  obtain ⟨J, hJ, n, φ, a, k, U, hUc, hUo, hUp, hUf, ha, hcell⟩ := htest ε v
  refine ⟨J, hJ, n, φ, a, k, h, (μ U).toReal * v.val h, ha, ?_, ?_⟩
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (ENNReal.toReal_pos hUp.ne' hUf))) hv
  · exact chamber_coordinate_of_characteristic_combination F ζ hζ q S P μ hμ ε
      (fun i => (φ i).val) a k h U hUo.measurableSet v (fun s _ => hcell s)

end OpenCellNonzero

namespace OpenCellNonzero.BruhatConstruction
open scoped NumberField Valued Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

private theorem small_subgroup : ∃ U : OpenAddSubgroup (LocalField F q),
    IsCompact (U : Set (LocalField F q)) ∧
    ∀ x ∈ U, (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
  let n : LocalField F q → ActualCover F ζ hζ q := fun x => (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q)
  have hn : Continuous n := continuous_subtype_val.comp (S.borel.upperRoot_continuous.comp continuous_ofAdd)
  let V : Set (LocalField F q) := n ⁻¹' (S.iwasawa.compact.toOpenSubgroup : Set (ActualCover F ζ hζ q)) ∩ ((valuation (LocalField F q)).integer : Set (LocalField F q))
  have hV : V ∈ nhds 0 := by
    apply Filter.inter_mem
    · apply hn.continuousAt.preimage_mem_nhds
      simpa [n] using S.iwasawa.compact.toOpenSubgroup.isOpen.mem_nhds S.iwasawa.compact.toOpenSubgroup.one_mem
    · exact (valuation (LocalField F q)).isOpen_integer.mem_nhds (by simp)
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  refine ⟨U, ?_, fun x hx => (hU hx).1⟩
  exact (IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1).of_isClosed_subset U.isClosed (fun x hx => (hU hx).2)

private theorem norm_right_compact (g : ActualCover F ζ hζ q)
    (k : S.iwasawa.compact.toOpenSubgroup) :
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (g * k)))) =
      localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))) := by
  let b := S.iwasawa.borelPart g
  let b' := S.iwasawa.borelPart (g * k)
  have hmem : ((b'⁻¹ * b : S.borel.B) : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    have he : ((b'⁻¹ * b : S.borel.B) : ActualCover F ζ hζ q) =
        (S.iwasawa.compactPart (g * k) : ActualCover F ζ hζ q) *
          ((S.iwasawa.compactPart g : ActualCover F ζ hζ q) * k)⁻¹ := by
      have h1 := S.iwasawa.decomposition g
      have h2 := S.iwasawa.decomposition (g * k)
      change g = (b : ActualCover F ζ hζ q) * _ at h1
      change g * k = (b' : ActualCover F ζ hζ q) * _ at h2
      calc
        ((b'⁻¹ * b : S.borel.B) : ActualCover F ζ hζ q) =
            (b' : ActualCover F ζ hζ q)⁻¹ * g * (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹ := by
          have hb : (b : ActualCover F ζ hζ q) = g * (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹ := (eq_mul_inv_iff_mul_eq.mpr h1.symm)
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hb, mul_assoc]
        _ = (b' : ActualCover F ζ hζ q)⁻¹ * (g * k) *
            ((S.iwasawa.compactPart g : ActualCover F ζ hζ q) * k)⁻¹ := by simp [mul_inv_rev, mul_assoc]
        _ = _ := by
          have hb : (b' : ActualCover F ζ hζ q)⁻¹ * (g * k) = (S.iwasawa.compactPart (g * k) : ActualCover F ζ hζ q) := (inv_mul_eq_iff_eq_mul.mpr h2)
          rw [hb]
    rw [he]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem (S.iwasawa.compactPart _).property
      (S.iwasawa.compact.toOpenSubgroup.inv_mem (S.iwasawa.compact.toOpenSubgroup.mul_mem (S.iwasawa.compactPart g).property k.property))
  have he := S.iwasawa.intersection_norm (b'⁻¹ * b) hmem
  have hm : localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract b')) *
      localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract (b'⁻¹ * b))) =
      localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract b)) := by
    rw [← localAbs_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]
  simpa only [he, mul_one] using hm

private theorem deformation_value (P : Polarization S.heisenberg) (ε : Sign)
    (f : sectionSpace S.borel P ε 0) (z : ℂ) (g : ActualCover F ζ hζ q) :
    (compactTrivialization S.borel P S.iwasawa ε z
      ((compactTrivialization S.borel P S.iwasawa ε 0).symm f)).val g =
      normPower (LocalField F q) (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))) z • f.val g := by
  have he := congrArg (fun f : sectionSpace S.borel P ε 0 => f.val g)
    ((compactTrivialization S.borel P S.iwasawa ε 0).apply_symm_apply f)
  change inducingAction S.borel P ε 0 (S.iwasawa.borelPart g) _ = f.val g at he
  rw [← he]
  let v := ((compactTrivialization S.borel P S.iwasawa ε 0).symm f).val (S.iwasawa.compactPart g)
  change (inducingScalar S.borel z (S.iwasawa.borelPart g)) • (borelAction S.borel P ε (S.iwasawa.borelPart g) v) =
    _ • ((inducingScalar S.borel 0 (S.iwasawa.borelPart g)) • (borelAction S.borel P ε (S.iwasawa.borelPart g) v))
  simp only [inducingScalar, normPower, zero_mul, Complex.exp_zero, mul_one, smul_smul]
  rw [mul_comm]

private theorem weyl_inverse (P : Polarization S.heisenberg) : S.borel.liftedW⁻¹ = S.borel.liftedW := by
  have hs : S.borel.liftedW ^ 2 = 1 := by
    rw [(S.openCell P).weyl_eq]
    simpa only [KPRankOneOpenCellKernel.signedWeyl,
      KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW] using
      KPPGLLocalCover.signedW_sq F ζ hζ (Sum.inr q)
  exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs)

private theorem section_common_level (P : Polarization S.heisenberg) (ε : Sign)
    (f : sectionSpace S.borel P ε 0) :
    ∃ J : CompactOpenLevel (ActualCover F ζ hζ q),
      (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup ∧
      (compactTrivialization S.borel P S.iwasawa ε 0).symm f ∈ compactLevel S.borel P S.iwasawa ε J := by
  obtain ⟨U, hU⟩ := f.property.2
  let J : CompactOpenLevel (ActualCover F ζ hζ q) :=
    ⟨U ⊓ S.iwasawa.compact.toOpenSubgroup, S.iwasawa.compact.isCompact.inter_left U.isClosed⟩
  refine ⟨J, inf_le_right, ?_⟩
  apply (compact_level_identification S.borel P S.iwasawa ε J inf_le_right 0 _).mpr
  simp only [LinearEquiv.apply_symm_apply]
  intro j
  exact Subtype.ext (hU j j.property.1)

private theorem test_section (P : Polarization S.heisenberg) (ε : Sign) (v : InducedModule P)
    (U : OpenAddSubgroup (LocalField F q)) (hUc : IsCompact (U : Set (LocalField F q))) :
    ∃ f : sectionSpace S.borel P ε 0,
      ∀ x, f.val (S.borel.liftedW * (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q)) =
        if x ∈ U then v else 0 := by
    classical
  classical
  let profile : LocalField F q → InducedModule P := fun x => if x ∈ U then v else 0
  have hl : IsLocallyConstant profile := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [U.isOpen.mem_nhds hx] with y hy
      simp [profile, hx, show y ∈ U from hy]
    · filter_upwards [U.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp [profile, hx, show y ∉ U from hy]
  have hc : HasCompactSupport profile := HasCompactSupport.intro hUc (by intro x hx; simp [profile, show x ∉ U from hx])
  obtain ⟨f, hf, _⟩ := (KPRankOneOpenCellKernel.open_cell_correspondence F ζ hζ q S.borel P (S.openCell P) ε 0).2 profile hl hc
  refine ⟨f, ?_⟩
  intro x
  have he := hf.2 x
  simpa only [KPRankOneOpenCellKernel.openCoordinate, ← (S.openCell P).weyl_eq,
    ← (S.openCell P).upper_eq, weyl_inverse F ζ hζ q S P] using he

variable (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]

private theorem corrected_test
    (ε : Sign) (v : InducedModule P)
    (U : OpenAddSubgroup (LocalField F q))
    (hU : ∀ x ∈ U, (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup)
    (f : sectionSpace S.borel P (sourceSign ε) 0)
    (hf : ∀ x, f.val (S.borel.liftedW * (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q)) = if x ∈ U then v else 0)
    (s : ℂ) (x : LocalField F q) :
    Complex.exp (-sourceParameter ε s * (Real.log (localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart S.borel.liftedW)))) : ℂ)) •
      (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)
        ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) 0).symm f)).val
        (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * 1) =
          (U : Set (LocalField F q)).indicator (fun _ => v) x := by
  have hw : kernelW (LocalField F q) S.borel ε = S.borel.liftedW := by
    cases ε <;> simp [kernelW, weyl_inverse F ζ hζ q S P]
  rw [hw, mul_one, deformation_value F ζ hζ q S P (sourceSign ε), hf]
  by_cases hx : x ∈ U
  · rw [ite_eq_left hx, Set.indicator_of_mem hx, normPower,
      norm_right_compact F ζ hζ q S S.borel.liftedW ⟨_, hU x hx⟩,
      smul_smul, ← Complex.exp_add]
    simp
  · simp [hx]

private theorem bruhat_families (ε : Sign) (v : InducedModule P) :
    ∃ (J : CompactOpenLevel (ActualCover F ζ hζ q))
      (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
      (n : ℕ) (φ : Fin n → compactLevel S.borel P S.iwasawa (sourceSign ε) J)
      (a : Fin n → ℂ → ℂ) (k : S.iwasawa.compact.toOpenSubgroup)
      (U : Set (LocalField F q)),
      IsCompact U ∧ IsOpen U ∧ 0 < μ U ∧ μ U ≠ ⊤ ∧
      (∀ i, Differentiable ℂ (a i)) ∧
      ∀ (s : ℂ) (x : LocalField F q),
        ∑ i, a i s •
          (compactTrivialization S.borel P S.iwasawa (sourceSign ε)
            (sourceParameter ε s) (φ i).val).val
            (kernelW (LocalField F q) S.borel ε * S.borel.upperRoot (Multiplicative.ofAdd x) * k) =
          U.indicator (fun _ => v) x := by
  obtain ⟨U, hUc, hU⟩ := small_subgroup F ζ hζ q S
  obtain ⟨f, hf⟩ := test_section F ζ hζ q S P (sourceSign ε) v U hUc
  obtain ⟨J, hJ, hφ⟩ := section_common_level F ζ hζ q S P (sourceSign ε) f
  let φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J := ⟨_, hφ⟩
  let a : ℂ → ℂ := fun s => Complex.exp (-sourceParameter ε s *
    (Real.log (localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart S.borel.liftedW)))) : ℂ))
  refine ⟨J, hJ, 1, fun _ => φ, fun _ => a, 1, U, hUc, U.isOpen, ?_, ?_, ?_, ?_⟩
  · exact IsOpen.measure_pos μ U.isOpen ⟨0, U.zero_mem⟩
  · exact hUc.measure_ne_top
  · intro i
    dsimp [a]
    cases ε <;> simp only [sourceParameter, reduceCtorEq, ite_true, ite_false] <;> fun_prop
  · intro s x
    simpa only [Fin.sum_univ_one, a, φ, OneMemClass.coe_one] using corrected_test F ζ hζ q S P ε v U hU f hf s x

end OpenCellNonzero.BruhatConstruction

theorem actual_zero_maps_nonzero
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    actualCanonicalForwardMap F ζ hζ q S P μ hμ ≠ 0 ∧
      actualCanonicalReverseMap F ζ hζ q S P μ hμ ≠ 0 := by
  exact OpenCellNonzero.both_actual_maps_nonzero_of_bruhat_families
    F ζ hζ q S P μ hμ
    (OpenCellNonzero.BruhatConstruction.bruhat_families F ζ hζ q S P μ)

end DedekindZetaZeroFree.KPRankOneShellRepair

end
