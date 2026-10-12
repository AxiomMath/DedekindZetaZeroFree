module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.BottomRowRadialContraction

@[expose] public section

section
noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

private theorem action_out_mk (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPArch.action (Matrix.ProjGenLinGroup.mk g).out (0,0) = KPArch.action g (0,0) := by
  have helper (a b : Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (h : Matrix.ProjGenLinGroup.mk a = Matrix.ProjGenLinGroup.mk b) :
      KPArch.action a (0,0) = KPArch.action b (0,0) := by
    obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
    rw [(KPArch.action_laws a (Matrix.GeneralLinearGroup.scalar (Fin 2) u) (0,0)).2,
      KPArch.scalar_action]
  exact helper _ g (Quotient.out_eq _)

 def heightSq (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq g.det / (Complex.normSq (g 1 0) + Complex.normSq (g 1 1))^2

private theorem heightSq_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Real.exp (2 * (KPArch.action g (0,0)).2) = heightSq g.val := by
  rw [two_mul, Real.exp_add, ← pow_two]
  change (KPArch.height (KPArch.action g (0,0)))^2 = heightSq g.val
  rw [KPArch.action_height]
  simp [heightSq, KPArch.height, div_pow, Complex.sq_norm, add_comm]

private theorem normSq_differentiable {z : ℝ → ℂ} (hz : DifferentiableAt ℝ z 0) :
    DifferentiableAt ℝ (fun t => Complex.normSq (z t)) 0 := by
  have hre := Complex.reCLM.differentiableAt.comp 0 hz
  have him := Complex.imCLM.differentiableAt.comp 0 hz
  convert (hre.mul hre).add (him.mul him) using 1
  ext t
  simp [Complex.normSq_apply]

open scoped Matrix.Norms.Operator in
private theorem matrix_components_differentiable (g X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, DifferentiableAt ℝ (fun t : ℝ =>
      (g * NormedSpace.exp ((t : ℂ) • X)) i j) 0 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt
  have hmat := (h.const_mul g).differentiableAt
  intro i j
  exact (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).differentiableAt.comp 0
    ((ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).differentiableAt.comp 0 hmat)

open scoped Matrix.Norms.Operator in
private theorem heightSq_differentiable (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => heightSq
      (g.val * NormedSpace.exp ((t : ℂ) • X))) 0 := by
  have h := matrix_components_differentiable g.val X
  have hdet : DifferentiableAt ℝ (fun t : ℝ =>
      (g.val * NormedSpace.exp ((t : ℂ) • X)).det) 0 := by
    convert ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0)) using 1
    ext t
    simp only [Matrix.det_fin_two, Pi.sub_apply, Pi.mul_apply]
  have hden := (normSq_differentiable (h 1 0)).add (normSq_differentiable (h 1 1))
  apply (normSq_differentiable hdet).div (hden.pow 2)
  have hp := KPArch.actionDenominator_pos g (0,0)
  have hbot : Complex.normSq (g 1 0) + Complex.normSq (g 1 1) ≠ 0 := by
    simpa [KPArch.actionDenominator, KPArch.height, Complex.sq_norm, add_comm] using ne_of_gt hp
  simpa using pow_ne_zero 2 hbot

open scoped Matrix.Norms.Operator in
private theorem local_height_differentiable (g : Matrix.ProjGenLinGroup (Fin 2) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => Real.exp (2 * (KPArch.action
      (g * Matrix.ProjGenLinGroup.mk (KPSmoothActualFlowData.matrixExponential
        ((t : ℂ) • X))).out (0,0)).2)) 0 := by
  have he (t : ℝ) : Real.exp (2 * (KPArch.action
      (g * Matrix.ProjGenLinGroup.mk (KPSmoothActualFlowData.matrixExponential
        ((t : ℂ) • X))).out (0,0)).2) =
      heightSq (g.out.val * NormedSpace.exp ((t : ℂ) • X)) := by
    have ho : Matrix.ProjGenLinGroup.mk g.out = g := Quotient.out_eq g
    have hm : g * Matrix.ProjGenLinGroup.mk (KPSmoothActualFlowData.matrixExponential
        ((t : ℂ) • X)) = Matrix.ProjGenLinGroup.mk
        (g.out * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)) := by
      exact (congrArg (fun q => q * Matrix.ProjGenLinGroup.mk
        (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) ho).symm.trans
        ((Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := ℂ)).map_mul _ _).symm
    rw [hm, action_out_mk, heightSq_action]
    rfl
  simp_rw [he]
  exact heightSq_differentiable g.out X

private theorem normalRadial_product (c g : Cover F ζ hζ)
    (hd : KPCuspLogShape.dimension F ≠ 0) :
    normalRadial c g = ∏ i : Fin (KPCuspLogShape.dimension F),
      Real.exp (2 * (KPArch.action
        (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g)
          (KPCusp.complexPlace F i)).out (0,0)).2) := by
  have hdr : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast hd
  unfold normalRadial KPCuspLogShape.meanHeight
  rw [show 2 * (KPCuspLogShape.dimension F : ℝ) *
      ((∑ i, (KPArch.action
        (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g)
          (KPCusp.complexPlace F i)).out (0,0)).2) / (KPCuspLogShape.dimension F : ℝ)) =
      ∑ i, 2 * (KPArch.action
        (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g)
          (KPCusp.complexPlace F i)).out (0,0)).2 by
    rw [← Finset.mul_sum]; field_simp]
  exact Real.exp_sum _ _

theorem normalRadial_hasDerivAt (c g : Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) (l : Fin 6) :
    HasDerivAt (fun t : ℝ => normalRadial c
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F (w,l) t))) (normalRadialJet c w l g) 0 := by
  apply DifferentiableAt.hasDerivAt
  by_cases hd : KPCuspLogShape.dimension F = 0
  · simp only [normalRadial, hd, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    exact differentiableAt_const 1
  · simp_rw [normalRadial_product _ _ hd]
    apply DifferentiableAt.fun_finsetProd
    intro i hi
    have he (t : ℝ) : KPSmoothLocalQuotientCharts.archProjection F ζ hζ
        (c⁻¹ * (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPSmoothActualFlowData.flow F (w,l) t))) (KPCusp.complexPlace F i) =
        KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g) (KPCusp.complexPlace F i) *
          KPSmoothActualFlowData.flow F (w,l) t (KPCusp.complexPlace F i) := by
      rw [← mul_assoc, map_mul]
      rw [show KPSmoothLocalQuotientCharts.archProjection F ζ hζ
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,l) t)) =
          KPSmoothActualFlowData.flow F (w,l) t from
        PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ _]
      rfl
    simp_rw [he, flow_apply]
    by_cases hv : KPCusp.complexPlace F i = w
    · simp only [hv, ↓reduceIte]
      exact local_height_differentiable _ _
    · simp only [hv, ↓reduceIte, mul_one]
      exact differentiableAt_const _

end DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient

end

end

section
noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}

 theorem action_out (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : KPArch.H3) :
    KPArch.action (Matrix.ProjGenLinGroup.mk g).out z = KPArch.action g z := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (Quotient.out_eq (Matrix.ProjGenLinGroup.mk g))
  conv_rhs => rw [← hu]
  rw [(KPArch.action_laws _ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) z).2,
    KPArch.scalar_action]

 theorem su_origin (k : KPCplxCharacterHaar.ComplexSU2) :
    KPArch.action (KPCplxCharacterHaar.complexSU2Embedding k) (0,0) = (0,0) := by
  have hm := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1
  have h01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 0 1) hm
  have h11 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 1) hm
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply,
    Fin.reduceEq, if_false, if_true] at h01 h11
  have hn : ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 1 := by
    change _ * (starRingEnd ℂ) _ + _ * (starRingEnd ℂ) _ = 1 at h11
    simpa only [Complex.mul_conj, Complex.add_re, Complex.ofReal_re, Complex.one_re,
      Complex.normSq_eq_norm_sq] using congrArg Complex.re h11
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  apply Prod.ext <;>
    simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KPCplxCharacterHaar.complexSU2Embedding, hd, add_comm, hn, h01]
  exact h01

 theorem finite_projection (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPSmoothLocalQuotientCharts.archProjection F ζ hζ c.val = 1 := by
  have hc := c.property
  change KPCuspGenuineMonodromy.archProjection F ζ hζ c.val = 1 at hc
  have he (g : Cover F ζ hζ) (w : NumberField.InfinitePlace F) :
      KPSmoothLocalQuotientCharts.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by
    induction g using Quotient.inductionOn with
    | h g => rfl
  funext w
  rw [he, hc]
  exact map_one _

 theorem balanced_height (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ)
    (i : Fin (KPCuspLogShape.dimension F)) :
    (KPArch.action ((balancedArch (ζ := ζ) (hζ := hζ) p k r)
      (KPCusp.complexPlace F i)).out (0,0)).2 =
        KPMsFixedHaarDisintegration.logHeight (F := F) r + p.2.val i := by
  have hi : (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex})
      ⟨KPCusp.complexPlace F i,
        KPHilbert.infinite_isComplex F ζ hζ (KPCusp.complexPlace F i)⟩ = i := by
    simpa only [KPCusp.complexPlace] using
      (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}).apply_symm_apply i
  obtain ⟨a, ha⟩ := (k (KPCusp.complexPlace F i)).property
  change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding a) = _ at ha
  unfold balancedArch
  simp only [hi, ← ha, ← map_mul, action_out, KPArch.action_laws, su_origin]
  let t := KPMsFixedHaarDisintegration.logHeight (F := F) r + p.2.val i
  let u : ℂˣ := Units.mk0 (Real.exp t : ℂ) (by exact_mod_cast Real.exp_ne_zero t)
  have h := KPCuspLogShape.upper_action_snd
    (KPCplxCharacterHaar.upperUnipotent (p.1 i) * KPCplxCharacterHaar.diagonal u)
    (by simp [KPCplxCharacterHaar.upperUnipotent, KPCplxCharacterHaar.diagonal,
      Matrix.mul_apply, Fin.sum_univ_two]) (u : ℂ) u.ne_zero
    (by simp [KPCplxCharacterHaar.upperUnipotent, KPCplxCharacterHaar.diagonal,
      Matrix.mul_apply, Fin.sum_univ_two]) (0,0)
  rw [← (KPArch.action_laws _ _ (0,0)).2]
  change (KPArch.action (KPCplxCharacterHaar.upperUnipotent (p.1 i) *
    KPCplxCharacterHaar.diagonal u) (0,0)).2 = t
  rw [h]
  change (0 : ℝ) + Real.log ‖(Real.exp t : ℂ)‖ = t
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp, zero_add]

theorem normalRadial_cuspLift (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) (hr : 0 < r) :
    normalRadial (cuspRepresentative A j) (cuspLift A j p k r) = r := by
  have hp : KPSmoothLocalQuotientCharts.archProjection F ζ hζ
      ((cuspRepresentative A j)⁻¹ * cuspLift A j p k r) =
      balancedArch (ζ := ζ) (hζ := hζ) p k r := by
    have hi : KPSmoothLocalQuotientCharts.archProjection F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (balancedArch (ζ := ζ) (hζ := hζ) p k r)) =
          balancedArch (ζ := ζ) (hζ := hζ) p k r :=
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ _
    simp only [cuspLift, ← mul_assoc, map_mul, map_inv, inv_mul_cancel, one_mul,
      hi, finite_projection, mul_one]
  unfold normalRadial
  simp only [hp]
  have hd : 0 < KPCuspLogShape.dimension F :=
    (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2
  have hdr : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hb : ∑ i, p.2.val i = 0 := p.2.property
  unfold KPCuspLogShape.meanHeight
  simp only [balanced_height, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hb, add_zero]
  rw [mul_div_cancel_left₀ _ hdr]
  unfold KPMsFixedHaarDisintegration.logHeight
  rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hdr), Real.exp_log hr]

end DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient

end

end

section
noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsGreenFlux
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

namespace NormalCoefficientCalculus

section GlobalHeight

variable (F : Type) [Field F] [NumberField F]

open scoped Matrix.Norms.Operator in
theorem flow_apply (w v : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    KPSmoothActualFlowData.flow F (w,j) t v =
      if v = w then Matrix.ProjGenLinGroup.mk
        (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix j))
      else 1 := by
  unfold KPSmoothActualFlowData.flow KPSmoothActualFlowData.exponential
  by_cases hv : v = w
  · simp only [hv, ↓reduceIte]
    congr 2
    ext a b
    fin_cases a <;> fin_cases b <;> fin_cases j <;>
      simp [KPSmoothActualFlowData.sl2Matrix, KPSmoothActualFlowData.basisMatrix,
        Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul] <;> ring
  · simp only [hv, ↓reduceIte]
    have hz : KPSmoothActualFlowData.sl2Matrix (fun i => if (v,i) = (w,j) then t else 0) = 0 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [KPSmoothActualFlowData.sl2Matrix, hv]
    rw [hz]
    change Matrix.ProjGenLinGroup.mk ((NormedSpace.isUnit_exp (0 : Matrix (Fin 2) (Fin 2) ℂ)).unit) = 1
    have hunit : (NormedSpace.isUnit_exp (0 : Matrix (Fin 2) (Fin 2) ℂ)).unit = 1 := by
      apply Units.ext; simp
    rw [hunit, map_one]

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

end GlobalHeight

end NormalCoefficientCalculus

end DedekindZetaZeroFree.KPMsGreenFlux

end

end
