module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.DeformedBruhatTestScalarFormula
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.NormalizedCompactBruhatTests

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeBaseChart.CompactProfiles
open MeasureTheory Set
open scoped Classical

theorem integrable_prod_restrict_of_locallyConstant_profiles
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (C : Set X) (hC : IsCompact C) (hCm : MeasurableSet C)
    [IsFiniteMeasure (μ.restrict C)]
    (f : X → Y → ℂ) (hf : IsLocallyConstant f)
    (hi : ∀ x ∈ C, Integrable (f x) ν) :
    Integrable (fun p : X × Y => f p.1 p.2) ((μ.restrict C).prod ν) := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let R := f '' C
  have hR : R.Finite := by
    have h := (hf.comp_continuous (continuous_subtype_val : Continuous (Subtype.val : C → X))).range_finite
    simpa only [range_comp, Subtype.range_coe] using h
  letI : Fintype R := hR.fintype
  let A : R → X → ℂ := fun r => {x | f x = r.val}.indicator (fun _ => 1)
  have hA : ∀ r, Integrable (A r) (μ.restrict C) := by
    intro r
    exact (integrable_const (1 : ℂ)).indicator (hf.isOpen_fiber r.val).measurableSet
  have hB : ∀ r : R, Integrable r.val ν := by
    intro r
    obtain ⟨x, hxC, hx⟩ := r.property
    simpa only [hx] using hi x hxC
  have hs : Integrable (fun p : X × Y => ∑ r : R, A r p.1 * r.val p.2)
      ((μ.restrict C).prod ν) := by
    exact integrable_finsetSum Finset.univ (fun r _ => (hA r).mul_prod (hB r))
  apply hs.congr
  have hmem : ∀ᵐ p : X × Y ∂((μ.restrict C).prod ν), p.1 ∈ C := by
    apply (Measure.ae_prod_iff_ae_ae (hCm.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem hCm] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  filter_upwards [hmem] with p hp
  let r : R := ⟨f p.1, ⟨p.1, hp, rfl⟩⟩
  rw [Finset.sum_eq_single r]
  · simp [A, r]
  · intro b _ hbr
    have hne : f p.1 ≠ b.val := by
      intro he
      apply hbr
      exact Subtype.ext he.symm
    simp [A, hne]
  · simp

end DedekindZetaZeroFree.KPTameTransposeBaseChart.CompactProfiles

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeBaseChart.ActualJoint
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPTameValuationCoordinates KPRankOneShellContinuation KPTameTransposeLiteral
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

include S P in
private theorem root_continuous :
    Continuous (KPPGLLocalCover.N F ζ hζ (Sum.inr q)) := by
  have he : KPPGLLocalCover.N F ζ hζ (Sum.inr q) =
      fun t => (S.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ q) := by
    funext t
    exact ((S.openCell P).upper_eq t).symm
  rw [he]
  exact continuous_subtype_val.comp (S.borel.upperRoot_continuous.comp continuous_ofAdd)

private theorem section_profiles_locallyConstant
    (π : (LocalField F q)ˣ) (s : ℂ)
    (f : sectionSpace S.borel P .minus (sourceParameter .minus s)) :
    IsLocallyConstant (fun x : LocalField F q => fun u : LocalField F q =>
      (f.val (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1) := by
  obtain ⟨J, hJ⟩ := f.property.2
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous (fun y =>
      (KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)⁻¹ *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) y) :=
    continuous_const.mul (root_continuous F ζ hζ q S P)
  have hn : ∀ᶠ y in nhds x,
      (KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)⁻¹ *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) y ∈ J :=
    hc.continuousAt.preimage_mem_nhds (by simpa using J.isOpen.mem_nhds J.one_mem)
  filter_upwards [hn] with y hy
  funext u
  have he := congrFun (hJ _ hy) (kernelW (LocalField F q) S.borel .minus *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
      (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))
  have he' := congrArg (fun v : InducedModule P => v.val 1) he
  change (f.val ((_ * (_ * KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) *
    ((KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)⁻¹ *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) y))).val 1 = _ at he'
  simpa only [mul_assoc, mul_inv_cancel_left] using he'

private theorem section_fiber_integrable
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (s : ℂ) (hs : convergenceHalfPlane .minus s)
    (f : sectionSpace S.borel P .minus (sourceParameter .minus s))
    (g : ActualCover F ζ hζ q) :
    Integrable (fun u : LocalField F q =>
      (f.val (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u * g)).val 1) μ := by
  let O : TopologicalSpace.PositiveCompacts (LocalField F q) :=
    ⟨⟨((valuation (LocalField F q)).integer : Set (LocalField F q)),
      IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1⟩,
      by rw [(valuation (LocalField F q)).isOpen_integer.interior_eq]; exact ⟨0, by simp⟩⟩
  let ν := Measure.addHaarMeasure O
  have hν : ν ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1 :=
    Measure.addHaarMeasure_self
  have hi := KPRankOneShellRepair.actual_section_integrable
    F ζ hζ q S P ν hν π hπ .minus s hs f g 1
  have he : (fun u : LocalField F q =>
      (f.val (kernelW (LocalField F q) S.borel .minus *
        S.borel.upperRoot (Multiplicative.ofAdd u) * g)).val 1) =
      (fun u : LocalField F q =>
      (f.val (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u * g)).val 1) := by
    funext u
    rw [(S.openCell P).upper_eq]
    rfl
  rw [he] at hi
  rw [Measure.addHaarMeasure_unique μ O]
  exact hi.smul_measure O.isCompact.measure_lt_top.ne

theorem eventual_baseChart_joint_integrable
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ s : ℂ, convergenceHalfPlane .minus s →
      Integrable (fun z : LocalField F q × LocalField F q =>
        chartDeformedScalar F ζ hζ q S P hP
          (diagonalLift F ζ hζ q π (0, 0)) m s
          (kernelW (LocalField F q) S.borel .minus *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) z.2 *
            (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) z.1)))
        ((μ.restrict (lowShell F q)).prod μ) := by
  obtain ⟨M₁, hM₁⟩ := KPTameTransposeLiteralMass.eventual_base_minus_test_exists
    F ζ hζ q S P hP htame π hπ
  obtain ⟨M₂, hM₂⟩ := eventual_minusTest_eq_chartDeformedScalar
    F ζ hζ q S P hP htame π hπ
  refine ⟨max M₁ M₂, fun m hm s hs => ?_⟩
  obtain ⟨f, hf⟩ := hM₁ m (le_trans (le_max_left _ _) hm)
  let fₛ := deformedTest F ζ hζ q S P hP f s
  have hC : IsCompact (lowShell F q) :=
    IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1
  have hCm : MeasurableSet (lowShell F q) :=
    (valuation (LocalField F q)).isOpen_integer.measurableSet
  letI : IsFiniteMeasure (μ.restrict (lowShell F q)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hi := CompactProfiles.integrable_prod_restrict_of_locallyConstant_profiles
    μ μ (lowShell F q) hC hCm _
    (section_profiles_locallyConstant F ζ hζ q S P π s fₛ)
    (fun x _ => section_fiber_integrable F ζ hζ q S P μ π hπ s hs fₛ
      (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))
  convert hi using 1
  funext z
  exact (hM₂ m (le_trans (le_max_right _ _) hm) _ f hf s _).symm

end DedekindZetaZeroFree.KPTameTransposeBaseChart.ActualJoint

end

end

section
noncomputable section

namespace DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation
open KPTameTransposeLiteral

def expandingReverseCubeShell (F : Type) [Field F] [NumberField F]
    (q : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Set (LocalField F q) :=
  {u | IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) u) = WithZero.exp (3 * (k : ℤ))}

theorem lower_row_constraint {K : Type*} [Field K]
    (B k : GL (Fin 2) K) (u x : K) (hB10 : B 1 0 = 0)
    (hB11 : B 1 1 ≠ 0) (hk11 : k 1 1 ≠ 0)
    (h : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w K * KubotaRankTwo.n K u *
        KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.n K x) =
      Matrix.ProjGenLinGroup.mk (B * k * KPStandardLocalRootLifts.weylSwap K)) :
    u ≠ 0 ∧ x + u⁻¹ = k 1 0 / k 1 1 := by
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h10 := congrArg (fun g : GL (Fin 2) K => g 1 0) hc
  have h11 := congrArg (fun g : GL (Fin 2) K => g 1 1) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.w,
    KubotaRankTwo.n, KPStandardLocalRootLifts.weylSwap,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply,
    hB10] at h10 h11
  have hu : u ≠ 0 := by
    intro hu
    rw [hu, zero_mul] at h10
    exact mul_ne_zero hB11 hk11 h10.symm
  refine ⟨hu, ?_⟩
  have he : (1 + u * x) * k 1 1 = u * k 1 0 := by
    apply mul_left_cancel₀ hB11
    calc
      _ = (1 + u * x) * (B 1 1 * k 1 1) := by ring
      _ = (1 + u * x) * (u * (c : K)) := by rw [h10]
      _ = u * ((1 + u * x) * (c : K)) := by ring
      _ = _ := by rw [add_comm 1 (u * x), h11]; ring
  apply (eq_div_iff hk11).mpr
  apply mul_left_cancel₀ hu
  calc
    _ = (1 + u * x) * k 1 1 := by field_simp; ring
    _ = _ := he

theorem actual_support_lower_row
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (π : (LocalField F q)ˣ) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (u x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (0, 0)) m) :
    u ≠ 0 ∧ ∃ k : KPLocalCube.Gamma F q m,
      x + u⁻¹ = k.val 1 0 / k.val 1 1 := by
  obtain ⟨b, k, hk, hg⟩ := hg
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  let B : GL (Fin 2) (LocalField F q) :=
    KubotaRankTwo.d (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) 1 *
      KubotaRankTwo.n (LocalField F q) t.toAdd
  have pb : S.borel.projection b.val = Matrix.ProjGenLinGroup.mk B := by
    have he : (inBorel F ζ hζ q S P b).val =
        (S.borel.torus (S.borel.retract (inBorel F ζ hζ q S P b)) : ActualCover F ζ hζ q) *
          (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
    change S.borel.projection ((inBorel F ζ hζ q S P b).val) = _
    rw [he, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection, map_mul]
    rfl
  have pa : S.borel.projection (diagonalLift F ζ hζ q π (0, 0)) = 1 := by
    rw [diagonalLift]
    rw [(S.openCell P).projection_eq]
    have hd : KubotaRankTwo.d (LocalField F q) 1 1 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.d]
    simp [hd]
  have pe : S.borel.projection (eta F ζ hζ q π (0 : Fin 3)) = 1 := by
    have pp : S.borel.projection (eta F ζ hζ q π (0 : Fin 3)) =
        Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (π ^ (0 : Fin 3).val) 1) :=
      (S.openCell P).projection_eq _
    rw [pp]
    have hd : KubotaRankTwo.d (LocalField F q) 1 1 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.d]
    simp [hd]
  have pw : S.borel.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pn (z : LocalField F q) : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) z) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) z) :=
    (S.openCell P).projection_eq _
  have pk : S.borel.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)) = Matrix.ProjGenLinGroup.mk k.val :=
    (S.openCell P).projection_eq _
  have pkw : S.borel.projection (kernelW (LocalField F q) S.borel .minus) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)) := by
    rw [kernelW, (S.openCell P).weyl_eq, KPRankOneOpenCellKernel.signedWeyl,
      (S.openCell P).projection_eq, KPRankOneOpenCellKernel.signedWeyl_matrix]
  have hp := congrArg S.borel.projection hg
  simp only [map_mul, pb, pa, pe, pw, pn, pk, pkw, mul_one, one_mul] at hp
  have hp' : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w (LocalField F q) * KubotaRankTwo.n (LocalField F q) u *
        KPStandardLocalRootLifts.weylSwap (LocalField F q) * KubotaRankTwo.n (LocalField F q) x) =
      Matrix.ProjGenLinGroup.mk (B * k.val * KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
    simpa only [map_mul, mul_assoc] using hp
  have hB10 : B 1 0 = 0 := by
    simp [B, Matrix.mul_apply, Fin.sum_univ_two]
  have hB11 : B 1 1 ≠ 0 := by
    simp [B, Matrix.mul_apply, Fin.sum_univ_two]
  have hk11 : k.val 1 1 ≠ 0 := by
    obtain ⟨r, hr⟩ := (hm.2 k.val k.property).1 1
    rw [← hr]
    exact pow_ne_zero _ r.ne_zero
  obtain ⟨hu, he⟩ := lower_row_constraint B k.val u x hB10 hB11 hk11 hp'
  exact ⟨hu, k, he⟩

theorem actual_support_residual_in_ideal
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (π : (LocalField F q)ˣ) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (u x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (0, 0)) m) :
    u ≠ 0 ∧ ∃ y : KPLocalCube.LocalIntegers F q,
      y ∈ KPLocalCube.maximalIdeal F q ^ m ∧ (y : LocalField F q) = x + u⁻¹ := by
  obtain ⟨hu, k, hk⟩ := actual_support_lower_row F ζ hζ q S P π m hm u x hg
  obtain ⟨k₀, hk₀, he₀⟩ := k.property
  have hentries := (KPLocalCube.mem_integerCongruence_iff F q m k₀).mp hk₀
  have h11ideal : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 1
  have h10ideal : k₀ 1 0 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 0
  have hisunit : IsUnit (k₀ 1 1) := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    have hmem : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q :=
      Ideal.pow_le_self (by have := hm.1; omega) h11ideal
    change 1 - k₀ 1 1 ∈ KPLocalCube.maximalIdeal F q
    simpa only [neg_sub] using (KPLocalCube.maximalIdeal F q).neg_mem hmem
  obtain ⟨v, hv⟩ := hisunit
  let y : KPLocalCube.LocalIntegers F q := k₀ 1 0 * (↑v⁻¹)
  refine ⟨hu, y, (KPLocalCube.maximalIdeal F q ^ m).mul_mem_right _ h10ideal, ?_⟩
  rw [hk]
  have hratio : k.val 1 0 / k.val 1 1 =
      (k₀ 1 0 : LocalField F q) / (k₀ 1 1 : LocalField F q) := by
    rw [← he₀]
    rfl
  rw [hratio, ← hv]
  change ((k₀ 1 0 * (↑v⁻¹) : KPLocalCube.LocalIntegers F q) : LocalField F q) = _
  change (k₀ 1 0 : LocalField F q) * ((↑v⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) = _
  have hvinv : ((↑v⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) = ((v : KPLocalCube.LocalIntegers F q) : LocalField F q)⁻¹ := by
    exact Units.val_inv_eq_inv_val (Units.map (KPLocalCube.LocalIntegers F q).subtype.toMonoidHom v)
  rw [hvinv, div_eq_mul_inv]

theorem actual_support_inverse_mem_lowShell
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (π : (LocalField F q)ˣ) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (u x : LocalField F q) (hx : x ∈ lowShell F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (0, 0)) m) :
    u ≠ 0 ∧ u⁻¹ ∈ lowShell F q := by
  obtain ⟨hu, y, _, hy⟩ := actual_support_residual_in_ideal F ζ hζ q S P π m hm u x hg
  have hys : (y : LocalField F q) ∈ lowShell F q := y.property
  have hsub := (valuation (LocalField F q)).integer.sub_mem hys hx
  rw [hy] at hsub
  refine ⟨hu, ?_⟩
  change u⁻¹ ∈ (valuation (LocalField F q)).integer
  simpa only [add_sub_cancel_left] using hsub

private theorem unitCubeClasses_exponent_dvd
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : Kˣ)
    (hu : QuotientGroup.mk' (CubicCharacters.cubes Kˣ) u ∈
      unitCubeClasses K) : 3 ∣ KPCubicExpansion.valuationExponent K u := by
  obtain ⟨y, hy, he⟩ := hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hdiff : (KPRamifiedBeta.unitsInclusion K z * t ^ 3) / u ∈
      CubicCharacters.cubes Kˣ := (QuotientGroup.eq_iff_div_mem).mp he
  obtain ⟨r, hr⟩ := hdiff
  change r ^ 3 = _ at hr
  have hh := congrArg (KPCubicExpansion.valuationExponent K) hr
  have hu0 : KPCubicExpansion.valuationExponent K (KPRamifiedBeta.unitsInclusion K z) = 0 :=
    KPCubicExpansion.valuationExponent_unit z
  simp only [div_eq_mul_inv, KPCubicExpansion.valuationExponent_mul, hu0, zero_add] at hh
  rw [← zpow_natCast r 3, KPCubicExpansion.valuationExponent_zpow,
    ← zpow_natCast t 3, KPCubicExpansion.valuationExponent_zpow,
    ← zpow_neg_one u, KPCubicExpansion.valuationExponent_zpow] at hh
  refine ⟨KPCubicExpansion.valuationExponent K t - KPCubicExpansion.valuationExponent K r, ?_⟩
  omega

private theorem tame_base_borel_exponent_dvd
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P) (b : BL F ζ hζ q S P) :
    3 ∣ KPCubicExpansion.valuationExponent (LocalField F q)
      (S.borel.coordinate (retractL F ζ hζ q S P b)) := by
  apply unitCubeClasses_exponent_dvd
  change QuotientGroup.mk (S.borel.coordinate (retractL F ζ hζ q S P b)) ∈ _
  rw [← S.cube_class, ← hP]
  exact ⟨S.heisenberg.π (retractL F ζ hζ q S P b),
    (retractL F ζ hζ q S P b).property, rfl⟩

private theorem actual_base_support_exponent_dvd
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (u : (LocalField F q)ˣ) (x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
      (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (0, 0)) m) :
    3 ∣ KPCubicExpansion.valuationExponent (LocalField F q) u := by
  obtain ⟨b, k, hk, hg⟩ := hg
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  let z := S.borel.coordinate (retractL F ζ hζ q S P b)
  have pb : S.borel.projection b.val = Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.d (LocalField F q) z 1 * KubotaRankTwo.n (LocalField F q) t.toAdd) := by
    have he : (inBorel F ζ hζ q S P b).val =
        (S.borel.torus (S.borel.retract (inBorel F ζ hζ q S P b)) : ActualCover F ζ hζ q) *
          (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
    change S.borel.projection ((inBorel F ζ hζ q S P b).val) = _
    rw [he, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection, map_mul]
    rfl
  have pa : S.borel.projection (eta F ζ hζ q π (0 : Fin 3)) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (π ^ (0 : Fin 3).val) 1) :=
    (S.openCell P).projection_eq _
  have pw : S.borel.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pn (v : LocalField F q) : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) v) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) v) :=
    (S.openCell P).projection_eq _
  have pk : S.borel.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)) = Matrix.ProjGenLinGroup.mk k.val :=
    (S.openCell P).projection_eq _
  have pkw : S.borel.projection (kernelW (LocalField F q) S.borel .minus) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)) := by
    rw [kernelW, (S.openCell P).weyl_eq, KPRankOneOpenCellKernel.signedWeyl,
      (S.openCell P).projection_eq, KPRankOneOpenCellKernel.signedWeyl_matrix]
  have hdiag : diagonalLift F ζ hζ q π (0, 0) = eta F ζ hζ q π (0 : Fin 3) := by
    simp [diagonalLift, eta, KPPGLLocalCover.A, KPStandardLocalRootLifts.A]
  rw [hdiag] at hg
  have hp := congrArg S.borel.projection hg
  simp only [map_mul, pb, pa, pw, pn, pk, pkw] at hp
  have hp' : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w (LocalField F q) * KubotaRankTwo.n (LocalField F q) u *
        KubotaRankTwo.d (LocalField F q) (π ^ (0 : Fin 3).val) 1 *
          KPStandardLocalRootLifts.weylSwap (LocalField F q) * KubotaRankTwo.n (LocalField F q) x) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) z 1 * KubotaRankTwo.n (LocalField F q) t.toAdd *
          KubotaRankTwo.d (LocalField F q) (π ^ (0 : Fin 3).val) 1 *
          k.val * KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
    simpa only [map_mul, mul_assoc] using hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp'
  have h10 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 1 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.w, KubotaRankTwo.n,
    KubotaRankTwo.d, KPStandardLocalRootLifts.weylSwap,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply] at h10
  have hd := congrArg Matrix.GeneralLinearGroup.det hc
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hd
  have detd (v : (LocalField F q)ˣ) : Matrix.GeneralLinearGroup.det
      (KubotaRankTwo.d (LocalField F q) v 1) = v := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detn (v : LocalField F q) : Matrix.GeneralLinearGroup.det
      (KubotaRankTwo.n (LocalField F q) v) = 1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detw : Matrix.GeneralLinearGroup.det (KubotaRankTwo.w (LocalField F q)) = 1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, KubotaRankTwo.w, Matrix.det_fin_two]
  have detswap : Matrix.GeneralLinearGroup.det
      (KPStandardLocalRootLifts.weylSwap (LocalField F q)) = -1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, KPStandardLocalRootLifts.weylSwap,
      Matrix.det_fin_two]
  simp only [detd, detn, detw, detswap, one_mul, mul_one] at hd
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h10
  have hd' : c ^ 2 = z * Matrix.GeneralLinearGroup.det k.val := by
    apply mul_left_cancel (a := π ^ (0 : Fin 3).val)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hd
  obtain ⟨r, hr⟩ := (hm.2 k.val k.property).1 1
  have huc : u * c = r ^ 3 := Units.ext (h10.trans hr.symm)
  obtain ⟨d, hdv⟩ := (hm.2 k.val k.property).2
  change d ^ 3 = Matrix.GeneralLinearGroup.det k.val at hdv
  have he₁ := congrArg (KPCubicExpansion.valuationExponent (LocalField F q)) huc
  have he₂ := congrArg (KPCubicExpansion.valuationExponent (LocalField F q)) hd'
  rw [← hdv] at he₂
  simp only [KPCubicExpansion.valuationExponent_mul] at he₁ he₂
  rw [← zpow_natCast c 2, KPCubicExpansion.valuationExponent_zpow,
    ← zpow_natCast d 3, KPCubicExpansion.valuationExponent_zpow] at he₂
  rw [← zpow_natCast r 3, KPCubicExpansion.valuationExponent_zpow] at he₁
  obtain ⟨a, ha⟩ := tame_base_borel_exponent_dvd
    F ζ hζ q S P hP b
  change KPCubicExpansion.valuationExponent (LocalField F q) z = 3 * a at ha
  apply (Int.dvd_iff_emod_eq_zero).mpr
  omega

private theorem expanding_shell_pairwise
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) :
    Pairwise (fun i j => Disjoint (expandingReverseCubeShell F q i)
      (expandingReverseCubeShell F q j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hi hj
  change _ = WithZero.exp (3 * (i : ℤ)) at hi
  change _ = WithZero.exp (3 * (j : ℤ)) at hj
  have he := WithZero.exp_injective (hi.symm.trans hj)
  exact hij (by omega)

private theorem actual_base_support_mem_expanding_union
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (u x : LocalField F q) (hx : x ∈ lowShell F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
      (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (0, 0)) m) :
    u ∈ ⋃ k : ℕ, expandingReverseCubeShell F q k := by
  obtain ⟨hu, hinv⟩ := actual_support_inverse_mem_lowShell F ζ hζ q S P π m hm u x hx hg
  let v : (LocalField F q)ˣ := Units.mk0 u hu
  have hd := actual_base_support_exponent_dvd F ζ hζ q S P hP π m hm v x hg
  obtain ⟨j, hj⟩ := hd
  have hv : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) u) ≠ 0 := by simpa using hu
  have hlog : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q) (valuation (LocalField F q) u)) = -3 * j := by
    change -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q) (valuation (LocalField F q) u)) = 3 * j at hj
    omega
  have hn : j ≤ 0 := by
    have hi : valuation (LocalField F q) u⁻¹ ≤ 1 := hinv
    have he := (map_le_map_iff
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q))).mpr hi
    rw [map_one, Valuation.map_inv, map_inv₀, ← WithZero.exp_log hv,
      ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp, hlog] at he
    omega
  apply Set.mem_iUnion.mpr
  refine ⟨(-j).toNat, ?_⟩
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) u) = WithZero.exp (3 * (((-j).toNat : ℕ) : ℤ))
  rw [← WithZero.exp_log hv, hlog, Int.toNat_of_nonneg (by omega)]
  congr 1
  ring

private theorem expanding_shell_measurable
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) (k : ℕ) :
    MeasurableSet (expandingReverseCubeShell F q k) := by
  let a : LocalField F q := ((π : LocalField F q)⁻¹) ^ (3 * k)
  have ha : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) a) = WithZero.exp (3 * (k : ℤ)) := by
    simp only [a, map_pow, map_inv₀, hπ, ← WithZero.exp_neg,
      ← WithZero.exp_nsmul]
    congr 1
    push_cast
    ring
  have he : expandingReverseCubeShell F q k =
      {u | valuation (LocalField F q) u = valuation (LocalField F q) a} := by
    ext u
    change _ = _ ↔ _ = _
    rw [← ha]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).injective.eq_iff
  rw [he]
  apply IsClosed.measurableSet
  simpa only [← (valuation (LocalField F q)).restrict_inj] using
    (valuation (LocalField F q)).isClosed_sphere ((valuation (LocalField F q)).restrict a)

private theorem baseChart_decomposition_of_integrable
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) (s : ℂ)
    (H : LocalField F q → LocalField F q → ℂ)
    (hH : ∀ x u, H x u = chartDeformedScalar F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π (0, 0)) m s
      (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)))
    (hint : Integrable (Function.uncurry H) ((μ.restrict (lowShell F q)).prod μ)) :
    baseChartChamberIntegral F ζ hζ q S P hP μ π m s =
      ∑' k : ℕ, ∫ u in expandingReverseCubeShell F q k,
        ∫ x in lowShell F q, H x u ∂μ ∂μ := by
  have hs : ∀ u ∉ ⋃ k : ℕ, expandingReverseCubeShell F q k,
      ∫ x in lowShell F q, H x u ∂μ = 0 := by
    intro u hu
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [hH]
    apply dif_neg
    intro hg
    exact hu (actual_base_support_mem_expanding_union F ζ hζ q S P hP π m hm u x hx hg)
  have hi := hint.integral_prod_right
  have hswap := integral_integral_swap hint
  have hmeas := expanding_shell_measurable F q π hπ
  have hU : MeasurableSet (⋃ k : ℕ, expandingReverseCubeShell F q k) :=
    MeasurableSet.iUnion hmeas
  change (∫ x in lowShell F q, ∫ u, _ ∂μ ∂μ) = _
  simp_rw [← hH]
  rw [hswap]
  have hid : (⋃ k : ℕ, expandingReverseCubeShell F q k).indicator
      (fun u => ∫ x in lowShell F q, H x u ∂μ) =
      (fun u => ∫ x in lowShell F q, H x u ∂μ) := by
    funext u
    by_cases hu : u ∈ ⋃ k : ℕ, expandingReverseCubeShell F q k
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, hs u hu]
  have hset : (∫ u in ⋃ k : ℕ, expandingReverseCubeShell F q k,
      ∫ x in lowShell F q, H x u ∂μ ∂μ) =
      ∫ u, ∫ x in lowShell F q, H x u ∂μ ∂μ := by
    rw [← integral_indicator hU, hid]
  rw [← hset]
  exact integral_iUnion hmeas (expanding_shell_pairwise F q) hi.integrableOn

theorem eventual_baseChart_cube_shell_decomposition
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ s : ℂ, convergenceHalfPlane .minus s →
      baseChartChamberIntegral F ζ hζ q S P hP μ π m s =
        ∑' k : ℕ, ∫ u in expandingReverseCubeShell F q k,
          ∫ x in lowShell F q,
            chartDeformedScalar F ζ hζ q S P hP
          (diagonalLift F ζ hζ q π (0, 0)) m s
          (kernelW (LocalField F q) S.borel .minus *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
            (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) ∂μ ∂μ := by
  obtain ⟨D, hD⟩ :=
    KPTameJacquetBruhatTests.TestConstruction.eventually_matrixChartDepth F q
  obtain ⟨J, hJ⟩ := ActualJoint.eventual_baseChart_joint_integrable
    F ζ hζ q S P hP μ htame π hπ
  refine ⟨max D J, fun m hm s hs => ?_⟩
  exact baseChart_decomposition_of_integrable F ζ hζ q S P hP μ π hπ m
    (hD m ((le_max_left D J).trans hm)) s _ (fun _ _ => rfl)
    (hJ m ((le_max_right D J).trans hm) s hs)

end DedekindZetaZeroFree.KPTameTransposeBaseChart.AugmentationSteps.CubeShell

end

end
