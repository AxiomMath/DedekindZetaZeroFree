module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandra.ScalarWordSpan
public import DedekindZetaZeroFree.Eisenstein.Continuation.SpatialRegularity.ExponentialOrbitRegularity
public import DedekindZetaZeroFree.Adeles.Approximation.UniformConjugatedFiniteLevel

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Manifold ContDiff BigOperators
open Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources SharedSource KPContActualSphericalRightFieldIdentification
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation renaming exists_archFiniteSplit → exists_archFiniteSplit
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
local notation "ins" => KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
local notation "expA" => KPSmoothActualFlowData.exponential F
local notation "W" => actualRightWord F R.A.zeta12 R.A.primitive_zeta12

def actualLieIndexEquiv : Fin (groupDimension F) ≃ KPSmoothActualFlowData.B F :=
  (lieEnumeration F).trans (actualBasisReindex F)

private theorem actual_ray (b : Fin (groupDimension F)) (t : ℝ) :
    KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1) =
      expA (t • Pi.single (actualLieIndexEquiv (F := F) b) 1) := by
  rw [actual_frame_ray_eq_flow]
  unfold KPSmoothActualFlowData.flow
  congr 1
  funext c
  simp [actualLieIndexEquiv, Pi.single_apply, eq_comm, smul_eq_mul]

theorem actualRight_right_covariance
    (f : Functions R) (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (a : Group R) :
    ∃ x : KPSmoothActualFlowData.GInfinity F, ∀ (b : Fin (groupDimension F)) g,
      actualRight F R.A.zeta12 R.A.primitive_zeta12 b
        (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a f) g =
      ∑ j : Fin (groupDimension F),
        (KPSmoothActualFlowData.adjointMatrix F x⁻¹
          (actualLieIndexEquiv (F := F) j) (actualLieIndexEquiv (F := F) b) : ℂ) *
        actualRight F R.A.zeta12 R.A.primitive_zeta12 j f (g * a) := by
  obtain ⟨e, he⟩ := exists_archFiniteSplit F R.A.zeta12 R.A.primitive_zeta12
  let x := (e.symm a).1
  let c := (e.symm a).2
  have ha : a = ins x * c.val := (e.apply_symm_apply a).symm.trans (he x c)
  have he1 (y : KPSmoothActualFlowData.GInfinity F) : e (y, 1) = ins y := by
    simp only [he, OneMemClass.coe_one, mul_one]
  have hcomm (y : KPSmoothActualFlowData.GInfinity F) : ins y * c.val = c.val * ins y := by
    have hc : e (1, c) = c.val := by
      rw [he, (KPSmoothActualFlowData.archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).1,
        one_mul]
    rw [← he1, ← hc, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  obtain ⟨C, L, D, hD, hb, hAd⟩ := KPSmoothActualFlowData.actual_archimedean_lie_data F
  letI := C
  letI := L
  refine ⟨x, ?_⟩
  intro b g
  let q : KPSmoothActualFlowData.LieCoordinates F → ℂ := fun X => f ((g * a) * ins (D.exponential X))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := by
    simpa only [q, hD] using
      KPSpatialNativeExponentialOrbit.native_exponential_contDiff F R.A.zeta12
        R.A.primitive_zeta12 f hf.2.1 (g * a)
  have hd : HasFDerivAt q (fderiv ℝ q 0) 0 := (hq.differentiable (by simp) 0).hasFDerivAt
  have hdir (X : KPSmoothActualFlowData.LieCoordinates F) :
      HasDerivAt (fun t : ℝ => q (t • X)) (fderiv ℝ q 0 X) 0 := by
    have hd' : HasFDerivAt q (fderiv ℝ q 0) ((0 : ℝ) • X) := by simpa using hd
    convert hd'.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const X) using 1 <;>
      simp only [Function.comp_def, id_eq, one_smul]
  have hbas (j : Fin (groupDimension F)) :
      D.basis (actualLieIndexEquiv (F := F) j) = Pi.single (actualLieIndexEquiv (F := F) j) 1 := by
    funext k
    simp [hb, Pi.single_apply]
  have hval (j : Fin (groupDimension F)) :
      fderiv ℝ q 0 (D.basis (actualLieIndexEquiv (F := F) j)) =
        actualRight F R.A.zeta12 R.A.primitive_zeta12 j f (g * a) := by
    rw [← (hdir _).deriv, hbas]
    unfold actualRight
    simp only [actual_ray, q, hD]
  have hcurve (t : ℝ) :
      (g * ins (expA (t • Pi.single (actualLieIndexEquiv (F := F) b) 1))) * a =
        (g * a) * ins (D.exponential
          (t • D.adjoint x⁻¹ (D.basis (actualLieIndexEquiv (F := F) b)))) := by
    have hconj := D.exponential_conjugation x⁻¹
      (t • D.basis (actualLieIndexEquiv (F := F) b))
    rw [map_smul, inv_inv] at hconj
    rw [← hconj, hD, hbas, ha]
    simp only [(KPSmoothActualFlowData.archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.1,
      map_inv]
    have hinv : ins x⁻¹ = (ins x)⁻¹ := by
      have hh := (KPSmoothActualFlowData.archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.1 x x⁻¹
      rw [mul_inv_cancel, (KPSmoothActualFlowData.archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).1] at hh
      exact eq_inv_of_mul_eq_one_right hh.symm
    rw [hinv]
    calc
      _ = g * ((ins (expA (t • Pi.single (actualLieIndexEquiv (F := F) b) 1)) * ins x) * c.val) := by group
      _ = g * (c.val * (ins (expA (t • Pi.single (actualLieIndexEquiv (F := F) b) 1)) * ins x)) := by
        rw [← (KPSmoothActualFlowData.archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.1, hcomm]
      _ = _ := by rw [hcomm x]; group
  unfold actualRight
  simp only [actual_ray]
  have heq : (fun t : ℝ => f ((g * ins (expA (t • Pi.single (actualLieIndexEquiv (F := F) b) 1))) * a)) =
      (fun t : ℝ => q (t • D.adjoint x⁻¹ (D.basis (actualLieIndexEquiv (F := F) b)))) :=
    funext fun t => congrArg f (hcurve t)
  change deriv (fun t : ℝ => f ((g * _) * a)) 0 = _
  rw [heq, (hdir _).deriv]
  conv_lhs => rw [← D.basis.sum_equivFun (D.adjoint x⁻¹ (D.basis (actualLieIndexEquiv (F := F) b)))]
  simp only [map_sum, map_smul]
  rw [← (actualLieIndexEquiv (F := F)).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [hAd, hval, Complex.real_smul]
  simp only [actualRight, actual_ray]

variable {Q : AdmissibleFlatSources R}
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero

private theorem actualRightWord_eq_adelic (w : List (Fin (groupDimension F)))
    (f : Functions R) :
    W w f = AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord,
      AdelicRightLieWords.actualRightWord]
    rw [ih]
    rfl

theorem hcHeckeSpan_smooth (T : Realization R Q) {f : Functions R}
    (hf : f ∈ hcHeckeSpan T) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, a, w, rfl⟩ := hf
    simpa only [actualRightWord_eq_adelic] using
      KPLiteralPeriod.NonzeroResidue.smooth_right_translate F R.A.zeta12
        R.A.primitive_zeta12 _ (realization_word_smooth T v w) a
  | zero => exact smooth_zero F R.A.zeta12 R.A.primitive_zeta12 Q.level
  | add f g _ _ ih ihg => exact smooth_add F R.A.zeta12 R.A.primitive_zeta12 _ _ ih ihg
  | smul c f _ ih => exact smooth_smul F R.A.zeta12 R.A.primitive_zeta12 c f ih

theorem hcHeckeSpan_actualRight (T : Realization R Q) {f : Functions R}
    (hf : f ∈ hcHeckeSpan T) (b : Fin (groupDimension F)) :
    actualRight F R.A.zeta12 R.A.primitive_zeta12 b f ∈ hcHeckeSpan T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, a, w, rfl⟩ := hf
    obtain ⟨x, hx⟩ := actualRight_right_covariance (W w (T.theta v))
      (realization_word_smooth T v w) a
    have he : actualRight F R.A.zeta12 R.A.primitive_zeta12 b
        (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a (W w (T.theta v))) =
        ∑ j : Fin (groupDimension F),
          (KPSmoothActualFlowData.adjointMatrix F x⁻¹ (actualLieIndexEquiv (F := F) j)
            (actualLieIndexEquiv (F := F) b) : ℂ) •
            KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a
              (W (j :: w) (T.theta v)) := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change actualRight F R.A.zeta12 R.A.primitive_zeta12 b
        (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a (W w (T.theta v))) g =
          ∑ j, (KPSmoothActualFlowData.adjointMatrix F x⁻¹ (actualLieIndexEquiv (F := F) j)
            (actualLieIndexEquiv (F := F) b) : ℂ) *
            actualRight F R.A.zeta12 R.A.primitive_zeta12 j (W w (T.theta v)) (g * a)
      exact hx b g
    simp only [actualRightWord_eq_adelic] at he
    rw [he]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, a, j :: w, rfl⟩)
  | zero =>
    have he : actualRight F R.A.zeta12 R.A.primitive_zeta12 b (0 : Functions R) = 0 := by
      funext g
      exact deriv_const _ _
    rw [he]
    exact Submodule.zero_mem _
  | add f g hf hg ih ihg =>
    have he := actualRightWord_add f g (hcHeckeSpan_smooth T hf) (hcHeckeSpan_smooth T hg) [b]
    change W [b] (f + g) ∈ _
    rw [he]
    exact Submodule.add_mem _ ih ihg
  | smul c f hf ih =>
    have he := actualRightWord_smul c f (hcHeckeSpan_smooth T hf) [b]
    change W [b] (c • f) ∈ _
    rw [he]
    exact Submodule.smul_mem _ c ih

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
