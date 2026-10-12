module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspCutoffBoundaryVanishing
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.CutoffIntegralConvergence
public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CubicCoveredRayCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Topology BigOperators
open MeasureTheory
open _root_.DedekindZetaZeroFree.KPBoundedCuspFrames renaming rationalHom → rationalHom
open _root_.DedekindZetaZeroFree.KPBoundedCuspFrames renaming rationalHom_out → rationalHom_out
open _root_.DedekindZetaZeroFree.KPBoundedCuspFrames renaming rationalHom_product → rationalHom_product
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes renaming normalRadial_finite_right → normalRadial_finite_right
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming finite_projection → finite_projection
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames renaming insertion_commutes → insertion_commutes
open _root_.DedekindZetaZeroFree.KPFiniteCuspAtlas renaming central_comm → central_comm
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming archRational_action → archRational_action
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming projective_action_mul → projective_action_mul
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming admissible_mono → admissible_mono
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming modulus_gt_of_not_core → modulus_gt_of_not_core
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming cutoff_bound → cutoff_bound
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology BigOperators NNReal
open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming bottomRowJet → bottomRowJet
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming normalRadialJet_eq_bottomRowJet → normalRadialJet_eq_bottomRowJet
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}

private theorem global_private_native_bottom_row_jet_bound (c d : ℂ) (r : ℝ) (hr : 0 ≤ r) (i : Fin 6)
    (h : 0 < Complex.normSq c + Complex.normSq d) :
    |bottomRowJet c d r i| ≤ 4 * r := by
  have hc := Complex.normSq_nonneg c
  have hd := Complex.normSq_nonneg d
  have hn : (c * star d).re ^ 2 + (c * star d).im ^ 2 = Complex.normSq c * Complex.normSq d := by
    simpa only [pow_two, ← Complex.normSq_apply, Complex.star_def, Complex.normSq_conj]
      using Complex.normSq_mul c (star d)
  have hre : |(c * star d).re| ≤ Complex.normSq c + Complex.normSq d := by
    nlinarith [sq_abs ((c * star d).re), sq_nonneg ((c * star d).im),
      sq_nonneg (Complex.normSq c - Complex.normSq d), abs_nonneg ((c * star d).re)]
  have him : |(c * star d).im| ≤ Complex.normSq c + Complex.normSq d := by
    nlinarith [sq_abs ((c * star d).im), sq_nonneg ((c * star d).re),
      sq_nonneg (Complex.normSq c - Complex.normSq d), abs_nonneg ((c * star d).im)]
  have hdiff : |Complex.normSq c - Complex.normSq d| ≤ Complex.normSq c + Complex.normSq d := by
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  fin_cases i <;> simp only [bottomRowJet, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk, abs_zero, abs_div, abs_mul,
    abs_of_pos h, abs_of_nonneg hr, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num), abs_neg] <;>
    try (apply (div_le_iff₀ h).mpr; nlinarith)
  positivity

private theorem global_private_native_normalRadialJet_abs_le {F : Type} [Field F] [NumberField F]
    {ζ : F} {hζ : IsPrimitiveRoot ζ 12} (c g : Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) (i : Fin 6) :
    |NormalCoefficient.normalRadialJet c w i g| ≤
      4 * NormalCoefficient.normalRadial c g := by
  rw [normalRadialJet_eq_bottomRowJet]
  apply global_private_native_bottom_row_jet_bound
  · exact (Real.exp_pos _).le
  · have h := KPArch.actionDenominator_pos
      (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g) w).out (0,0)
    simpa [KPArch.actionDenominator, KPArch.height, Complex.sq_norm, add_comm] using h
private theorem global_private_native_normalRadial_flow_hasDerivAt {F : Type} [Field F] [NumberField F]
    {ζ : F} {hζ : IsPrimitiveRoot ζ 12} (c g : Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) (i : Fin 6) (t : ℝ) :
    HasDerivAt (fun s => NormalCoefficient.normalRadial c
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,i) s)))
      (NormalCoefficient.normalRadialJet c w i
        (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,i) t))) t := by
  let a : ℝ → Cover F ζ hζ := fun s =>
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,i) s)
  have ha (s t : ℝ) : a (s + t) = a s * a t := by
    dsimp [a]
    rw [(KPSmoothActualFlowData.flow_properties F (w,i)).2.1,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  have hd := NormalCoefficient.normalRadial_hasDerivAt c (g * a t) w i
  have he : (fun s => NormalCoefficient.normalRadial c ((g * a t) * a s)) =
      (fun s => NormalCoefficient.normalRadial c (g * a (t+s))) := by
    funext s
    rw [ha, mul_assoc]
  change HasDerivAt (fun s => NormalCoefficient.normalRadial c ((g * a t) * a s)) _ 0 at hd
  rw [he] at hd
  have hd' := (show HasDerivAt (fun s => NormalCoefficient.normalRadial c (g * a (t+s)))
    (NormalCoefficient.normalRadialJet c w i (g * a t)) (t-t) by simpa using hd).comp_sub_const t t
  simpa only [sub_self, add_sub_cancel, Function.comp_def, a] using hd'

private theorem global_private_native_log_radial_flow_lipschitz {F : Type} [Field F] [NumberField F]
    {ζ : F} {hζ : IsPrimitiveRoot ζ 12} (c g : Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) (i : Fin 6) :
    LipschitzWith 4 (fun t => Real.log (NormalCoefficient.normalRadial c
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,i) t)))) := by
  let r : ℝ → ℝ := fun t => NormalCoefficient.normalRadial c
    (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,i) t))
  have hr (t : ℝ) : 0 < r t := Real.exp_pos _
  have hd (t : ℝ) := (global_private_native_normalRadial_flow_hasDerivAt c g w i t).log (hr t).ne'
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  change |NormalCoefficient.normalRadialJet c w i
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,i) t)) / r t| ≤ 4
  rw [abs_div, abs_of_pos (hr t)]
  apply (div_le_iff₀ (hr t)).mpr
  exact global_private_native_normalRadialJet_abs_le c _ w i

private theorem global_private_clipped_exp_lipschitz (R : ℝ) (hR : 0 < R) :
    LipschitzWith ⟨R, hR.le⟩ (fun x : ℝ => min R (Real.exp x)) := by
  have hb (x y : ℝ) (hxy : x ≤ y) :
      |min R (Real.exp y) - min R (Real.exp x)| ≤ R * |y-x| := by
    have hexy : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
    have hmine : min R (Real.exp x) ≤ min R (Real.exp y) := min_le_min_left _ hexy
    rw [abs_of_nonneg (sub_nonneg.mpr hmine), abs_of_nonneg (sub_nonneg.mpr hxy)]
    by_cases hx : R ≤ Real.exp x
    · rw [min_eq_left hx, min_eq_left (hx.trans hexy), sub_self]
      positivity
    · have hxR : x ≤ Real.log R := (Real.le_log_iff_exp_le hR).mpr (le_of_not_ge hx)
      let z := min y (Real.log R)
      have hxz : x ≤ z := le_min hxy hxR
      have hzR : z ≤ Real.log R := min_le_right _ _
      have hzy : z ≤ y := min_le_left _ _
      have hd (t : ℝ) (_ : t ∈ Set.Icc x z) : DifferentiableAt ℝ Real.exp t := Real.differentiable_exp t
      have hdB (t : ℝ) (ht : t ∈ Set.Icc x z) : ‖deriv Real.exp t‖ ≤ R := by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact (Real.exp_le_exp.mpr (ht.2.trans hzR)).trans (Real.exp_log hR).le
      have h := (convex_Icc x z).norm_image_sub_le_of_norm_deriv_le hd hdB (Set.left_mem_Icc.mpr hxz) (Set.right_mem_Icc.mpr hxz)
      have hez : Real.exp z = min R (Real.exp y) := by
        dsimp [z]
        by_cases hy : y ≤ Real.log R
        · rw [min_eq_left hy, min_eq_right ((Real.exp_le_exp.mpr hy).trans (Real.exp_log hR).le)]
        · rw [min_eq_right (le_of_not_ge hy), Real.exp_log hR,
            min_eq_left ((Real.exp_log hR).ge.trans (Real.exp_le_exp.mpr (le_of_not_ge hy)))]
      rw [min_eq_right (le_of_not_ge hx)]
      have h' : min R (Real.exp y) - Real.exp x ≤ R * (z-x) := by
        have h' : Real.exp z - Real.exp x ≤ R * (z-x) := by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hxz)),
            abs_of_nonneg (sub_nonneg.mpr hxz)] using h
        simpa only [hez] using h'
      exact h'.trans (mul_le_mul_of_nonneg_left (by linarith) hR.le)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |min R (Real.exp x) - min R (Real.exp y)| ≤ R * |x-y|
  rcases le_total x y with hxy | hyx
  · simpa only [abs_sub_comm] using hb x y hxy
  · exact hb y x hyx

private theorem global_private_clipped_taper_exp_lipschitz (Y ε : ℝ) (hε : 0 < ε) (hR : 0 < Y+ε) :
    LipschitzWith (⟨|ε⁻¹|, abs_nonneg _⟩ * ⟨Y+ε, hR.le⟩)
      (fun t : ℝ => max 0 (min 1 ((Y+ε-Real.exp t)/ε))) := by
  have hc := global_private_clipped_exp_lipschitz (Y+ε) hR
  have hp : LipschitzWith ⟨|ε⁻¹|, abs_nonneg _⟩
      (fun r : ℝ => max 0 (min 1 ((Y+ε-r)/ε))) := by
    apply LipschitzWith.const_max
    apply LipschitzWith.const_min
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |(Y + ε - x)/ε - (Y + ε - y)/ε| ≤ |ε⁻¹| * |x-y|
    have he : (Y+ε-x)/ε - (Y+ε-y)/ε = (y-x)*ε⁻¹ := by ring
    rw [he, abs_mul, abs_sub_comm]
    exact le_of_eq (mul_comm _ _)
  have hh := hp.comp hc
  have heq : ((fun r : ℝ => max 0 (min 1 ((Y+ε-r)/ε))) ∘
      (fun x : ℝ => min (Y+ε) (Real.exp x))) =
      (fun x : ℝ => max 0 (min 1 ((Y+ε-Real.exp x)/ε))) := by
    funext x
    simp only [Function.comp_apply]
    by_cases h : Y+ε ≤ Real.exp x
    · rw [min_eq_left h]
      simp only [sub_self, zero_div, min_eq_right (by norm_num : (0:ℝ) ≤ 1), max_self]
      have h2 : (Y+ε-Real.exp x)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
      rw [min_eq_right (h2.trans (by norm_num)), max_eq_left h2]
    · rw [min_eq_right (le_of_not_ge h)]
  rwa [heq] at hh

private theorem global_private_native_taper_flow_lipschitz (c g : Cover F ζ hζ)
    (Y ε : ℝ) (hε : 0 < ε) (hR : 0 < Y+ε)
    (w : NumberField.InfinitePlace F) (i : Fin 6) :
    LipschitzWith ((⟨|ε⁻¹|, abs_nonneg _⟩ * ⟨Y+ε, hR.le⟩) * 4)
      (fun t : ℝ => max 0 (min 1 ((Y+ε-NormalCoefficient.normalRadial c
        (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPSmoothActualFlowData.flow F (w,i) t)))/ε))) := by
  have h := (global_private_clipped_taper_exp_lipschitz Y ε hε hR).comp
    (global_private_native_log_radial_flow_lipschitz c g w i)
  have hr (a : Cover F ζ hζ) : 0 < NormalCoefficient.normalRadial c a := Real.exp_pos _
  simpa only [Function.comp_def, Real.exp_log (hr _)] using h

private theorem global_cutoff_upper_admissible
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (Y ε : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (hε : 0 < ε) :
    KPMsFixedHaarDisintegration.AdmissibleCutoff A (Y + ε) := by
  refine ⟨by linarith [hY.1], hY.2.trans ?_⟩
  unfold KPMsFixedHaarDisintegration.logHeight
  exact div_le_div_of_nonneg_right (Real.log_le_log hY.1 (by linarith)) (by positivity)

private theorem global_cutoff_zero_off_upper_core
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y ε : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (hε : 0 < ε)
    (x : X F ζ hζ) (hx : x ∉ quotientCore A P (Y + ε)) :
    CutoffApproximation.coreCutoff A R P D Y ε x = 0 := by
  have hYe := global_cutoff_upper_admissible A Y ε hY hε
  have hxe : P.projection U x ∈ KPMsFixedHaarDisintegration.cuspEnds A (Y + ε) := by
    simpa only [quotientCore, Set.mem_ofPred_eq, not_forall, not_not,
      KPMsFixedHaarDisintegration.cuspEnds, Set.mem_iUnion, endSet] using hx
  obtain ⟨⟨z,r⟩,hr⟩ := (D.chart_range (Y + ε) hYe).symm ▸ hxe
  have hm : Y + ε < D.modulus (P.projection U x) := by
    rw [← hr, D.chart_modulus]
    exact r.property
  have hn : x ∉ quotientCore A P Y := by
    intro hc
    apply hx
    exact FiniteSlabCoreShell.quotientCore_mono A P hY.1 (by linarith) hc
  simp only [CutoffApproximation.coreCutoff, ite_eq_right hn]
  have hd : (Y + ε - D.modulus (P.projection U x)) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [min_eq_right (hd.trans (by norm_num)), max_eq_left hd]

section SwitchingGeometry
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (D : KPMsFixedHaarDisintegration.Disintegration A R P)

private theorem modulus_on_literal_lift (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (j : Cusps A) (p : KPCuspCharts.Cross F) (r : ℝ) (hr : Y < r) :
    D.modulus (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      ((KPCuspSiegel.action F ((A.cuspAtlas j.1).representative j.2) (KPCuspCharts.toArch F
        (p, KPMsFixedHaarDisintegration.logHeight (F := F) r))), A.representative j.1)) = r := by
  let rr : Set.Ioi Y := ⟨r,hr⟩
  let b := KPMsFixedHaarDisintegration.sectionShape F hF D.radial.slot
    ⟨r, lt_trans hY.1 hr⟩
  let q : KPCuspCharts.Cross F := (p.1, p.2 - b)
  have hq : (q.1, q.2 + b) = p := by
    dsimp [q]
    simp
  have he := D.chart_formula Y hY j q rr
  change D.chart Y hY (⟨j, Quotient.mk _ q⟩,rr) =
    Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      ((KPCuspSiegel.action F ((A.cuspAtlas j.1).representative j.2) (KPCuspCharts.toArch F
        ((q.1, q.2 + b), KPMsFixedHaarDisintegration.logHeight (F := F) r))),
          A.representative j.1) at he
  rw [hq] at he
  rw [← he]
  exact D.chart_modulus Y hY _ rr

private theorem cusp_product_projection (j : Cusps A)
    (a : KPSmoothActualFlowData.GInfinity F) (η : rootsOfUnity 3 F)
    (u : U.toOpenSubgroup) :
    P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val)) =
    Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      (KPCuspSiegel.action F ((A.cuspAtlas j.1).representative j.2)
        (KPMsFixedHaarDisintegration.archBasepoint F a), A.representative j.1) := by
  let σ := (A.cuspAtlas j.1).representative j.2
  let σa : KPSmoothActualFlowData.GInfinity F := fun w =>
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding σ.out)
  have hσ : cuspRepresentative A j = (rationalHom (ζ := ζ) (hζ := hζ) σ).val :=
    (rationalHom_out σ).symm
  have he : cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      (KPBoundedCuspFrames.actualFiniteRepresentative A j).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (σa * a) * (A.representative j.1).val := by
    rw [hσ, rationalHom_product,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    dsimp [KPBoundedCuspFrames.actualFiniteRepresentative]
    have hi := (insertion_commutes
      (F := F) (ζ := ζ) (hζ := hζ) a
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ)).symm
    change (_ * _) * _ * (_⁻¹ * _) = _
    rw [mul_assoc _ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ).val
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a), hi.eq]
    dsimp [σa, σ]
    group
  rw [he]
  let c : KPFiniteCuspAtlas.FiniteCover F ζ hζ := A.representative j.1 *
    KPCuspGenuineMonodromy.central F ζ hζ η * u.val
  have hprod : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (σa * a) *
      (A.representative j.1).val * KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (σa * a) * c.val := by
    simp only [c, Subgroup.coe_mul, mul_assoc]
    rfl
  rw [hprod, P.formula]
  have ha : KPMsFixedHaarDisintegration.archBasepoint F (σa * a) =
      KPCuspSiegel.action F σ (KPMsFixedHaarDisintegration.archBasepoint F a) := by
    funext i
    change KPArch.action (σa (KPCusp.complexPlace F i) * a (KPCusp.complexPlace F i)).out (0,0) = _
    rw [projective_action_mul]
    exact congrFun (archRational_action F σ (KPMsFixedHaarDisintegration.archBasepoint F a)) i
  rw [ha]
  apply Quotient.sound
  refine ⟨1, η⁻¹, u⁻¹, by simp [σ], ?_⟩
  dsimp [c]
  simp only [map_one, one_mul, map_inv]
  rw [← central_comm F ζ hζ η (A.representative j.1)]
  group

private theorem cusp_product_radius (j : Cusps A)
    (a : KPSmoothActualFlowData.GInfinity F) (η : rootsOfUnity 3 F)
    (u : U.toOpenSubgroup) :
    NormalCoefficient.normalRadial (cuspRepresentative A j)
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val) =
    Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) *
      KPCuspLogShape.meanHeight _ (KPMsFixedHaarDisintegration.archBasepoint F a)) := by
  rw [normalRadial_finite_right _ _ u.val]
  have hz : KPSmoothLocalQuotientCharts.centreMap F ζ hζ η =
      (KPCuspGenuineMonodromy.central F ζ hζ η).val := rfl
  rw [hz, normalRadial_finite_right, normalRadial_finite_right]
  unfold NormalCoefficient.normalRadial
  rw [inv_mul_cancel_left]
  have hi : KPSmoothLocalQuotientCharts.archProjection F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) = a :=
    PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ a
  rw [hi]
  rfl

private theorem cusp_product_cutoff (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (ε : ℝ) (hε : 0 < ε) (j : Cusps A)
    (a : KPSmoothActualFlowData.GInfinity F) (η : rootsOfUnity 3 F)
    (u : U.toOpenSubgroup)
    (hr : Y < NormalCoefficient.normalRadial (cuspRepresentative A j)
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val)) :
    CutoffApproximation.coreCutoff A R P D Y ε (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val)) =
    max 0 (min 1 ((Y + ε - NormalCoefficient.normalRadial (cuspRepresentative A j)
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val)) / ε)) := by
  let z := (KPCuspCharts.toArchHomeomorph F (KPCuspCharts.positive_dimension F hF)).symm
    (KPMsFixedHaarDisintegration.archBasepoint F a)
  have hz : KPCuspCharts.toArch F z = KPMsFixedHaarDisintegration.archBasepoint F a :=
    (KPCuspCharts.toArchHomeomorph F (KPCuspCharts.positive_dimension F hF)).apply_symm_apply _
  let r := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * z.2)
  have he : NormalCoefficient.normalRadial (cuspRepresentative A j)
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val) = r := by
    rw [cusp_product_radius, ← hz, KPCuspCharts.toArch_meanHeight F
      (KPCuspCharts.positive_dimension F hF)]
  have hYr : Y < r := he ▸ hr
  have ht : KPMsFixedHaarDisintegration.logHeight (F := F) r = z.2 := by
    unfold KPMsFixedHaarDisintegration.logHeight r
    rw [Real.log_exp]
    have hd : 0 < (KPCuspLogShape.dimension F : ℝ) := by
      exact_mod_cast KPCuspCharts.positive_dimension F hF
    field_simp
  have hp := cusp_product_projection A P j a η u
  rw [← hz] at hp
  change P.projection U _ = Quotient.mk _
    (KPCuspSiegel.action F ((A.cuspAtlas j.1).representative j.2)
      (KPCuspCharts.toArch F (z.1,z.2)), A.representative j.1) at hp
  rw [← ht] at hp
  have hm : D.modulus (P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val))) = r := by
    rw [hp]
    exact modulus_on_literal_lift A R P D Y hY j z.1 r hYr
  have hn : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val) ∉ quotientCore A P Y := by
    simp only [quotientCore, Set.mem_ofPred_eq, not_forall, not_not]
    refine ⟨j, ?_⟩
    rw [hp]
    refine ⟨KPCuspSiegel.projection F _ _, ⟨_, ⟨KPCuspCharts.toArch F
      (z.1, KPMsFixedHaarDisintegration.logHeight (F := F) r), ?_, rfl⟩, rfl⟩, rfl⟩
    change KPMsFixedHaarDisintegration.logHeight (F := F) Y <
      KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F _)
    rw [KPCuspCharts.toArch_meanHeight F (KPCuspCharts.positive_dimension F hF), ht]
    have hd : 0 < (2 * (KPCuspLogShape.dimension F : ℝ)) := by
      have := KPCuspCharts.positive_dimension F hF
      positivity
    rw [← ht]
    exact div_lt_div_of_pos_right (Real.log_lt_log hY.1 hYr) hd
  rw [CutoffApproximation.coreCutoff, ite_eq_right hn, hm, he]
end SwitchingGeometry

private theorem global_cutoff_modulus_continuousOn_ends
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) :
    ContinuousOn D.modulus (KPMsFixedHaarDisintegration.cuspEnds A Y) := by
  rw [← D.chart_range Y hY, ← Set.image_univ]
  apply (D.chart_embedding Y hY).isInducing.continuousOn_image_iff.mpr
  have he : D.modulus ∘ D.chart Y hY = fun p => p.2.val := by
    funext p
    exact D.chart_modulus Y hY p.1 p.2
  rw [he]
  exact (continuous_subtype_val.comp continuous_snd).continuousOn
private theorem global_cutoff_continuousAt_off_core
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P) (Y ε : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (x : X F ζ hζ) (hx : x ∉ quotientCore A P Y) :
    ContinuousAt (CutoffApproximation.coreCutoff A R P D Y ε) x := by
  have hopen := (FiniteSlabCoreShell.isClosed_quotientCore A P Y).isOpen_compl
  have hmem : x ∈ (quotientCore A P Y)ᶜ := hx
  have he : ∀ᶠ y in 𝓝 x, CutoffApproximation.coreCutoff A R P D Y ε y =
      max 0 (min 1 ((Y + ε - D.modulus (P.projection U y)) / ε)) := by
    filter_upwards [hopen.mem_nhds hmem] with y hy
    exact ite_eq_right hy
  have hχ : ContinuousAt (fun y : X F ζ hζ =>
      max 0 (min 1 ((Y + ε - D.modulus (P.projection U y)) / ε))) x := by
    have hm : ContinuousAt (fun y => D.modulus (P.projection U y)) x := by
      apply ((global_cutoff_modulus_continuousOn_ends A R P D Y hY).comp (P.continuous U).continuousOn ?_).continuousAt (hopen.mem_nhds hmem)
      intro y hy
      simpa only [quotientCore, Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_not,
        KPMsFixedHaarDisintegration.cuspEnds, Set.mem_iUnion, endSet] using hy
    exact continuousAt_const.max (continuousAt_const.min
      ((continuousAt_const.sub hm).div_const ε))
  exact hχ.congr (Filter.EventuallyEq.symm he)

private theorem global_end_closure_subset_lower
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (j : Cusps A) (B Y : ℝ)
    (hB : KPMsFixedHaarDisintegration.AdmissibleCutoff A B) (hBY : B < Y) :
    closure (endSet A j Y) ⊆ endSet A j B := by
  let τ := KPMsFixedHaarDisintegration.logHeight (F := F) B
  let T := KPMsFixedHaarDisintegration.logHeight (F := F) Y
  have hτ : A.threshold ≤ τ := hB.2
  have hT : τ < T := by
    apply (div_lt_div_iff_of_pos_right ?_).mpr
    · exact Real.log_lt_log hB.1 hBY
    · exact mul_pos (by norm_num) (by exact_mod_cast KPCuspCharts.positive_dimension F hF)
  let L := fun (a : Cusps A) (z : KPCuspCharts.Coordinates F) =>
    Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      (((A.cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z), A.representative a.1)
  let t := fun (a : Cusps A) (x : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) =>
    if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ L a z = x
    then (Classical.choose h).2 else 0
  obtain ⟨hrange, hcoord, -, -, -, -⟩ :=
    KPActualCollarBuffer.actual_height_descent F ζ hζ hF U A τ hτ
  have hrangeT := (KPActualCollarBuffer.actual_height_descent F ζ hζ hF U A T
    (hτ.trans hT.le)).1
  have hm : endSet A j Y ⊆ endSet A j B := by
    apply Set.image_mono
    apply Set.image_mono
    apply Set.image_mono
    exact fun z hz => lt_of_lt_of_le hT hz.le
  intro x hx
  by_contra hxb
  have hfront : x ∈ frontier (endSet A j B) := by
    exact ⟨closure_mono hm hx, fun hi => hxb (interior_subset hi)⟩
  obtain ⟨V, hV, hxV, hbound⟩ :=
    (KPActualCollarBuffer.actual_boundary_zero_buffer F ζ hζ hF U A τ T hτ hT).1 j x hfront
  obtain ⟨y, hyV, hyY⟩ := (mem_closure_iff.mp hx V hV hxV)
  obtain ⟨z, hz, hzy⟩ := (show y ∈ L j '' {z : KPCuspCharts.Coordinates F | T < z.2} from
    (hrangeT j).symm ▸ hyY)
  have htz : t j y = z.2 := by
    rw [← hzy]
    exact hcoord j z (lt_trans hT hz)
  have hb : t j y < T := hbound y hyV (hm hyY)
  rw [htz] at hb
  exact (not_lt_of_ge hb.le) hz
private theorem global_core_upper_mem_nhds
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (Y T : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (hYT : Y < T)
    (x : X F ζ hζ) (hx : x ∈ quotientCore A P Y) :
    quotientCore A P T ∈ 𝓝 x := by
  let C := ⋃ j : Cusps A, (P.projection U) ⁻¹' closure (endSet A j T)
  have hc : IsClosed C := isClosed_iUnion_of_finite (fun j => isClosed_closure.preimage (P.continuous U))
  have hxc : x ∈ Cᶜ := by
    simp only [C, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
    intro j hj
    exact hx j (global_end_closure_subset_lower A j Y T hY hYT hj)
  apply mem_of_superset (hc.isOpen_compl.mem_nhds hxc)
  intro y hy j hj
  apply hy
  exact Set.mem_iUnion.mpr ⟨j, subset_closure hj⟩
private theorem global_cutoff_modulus_le_on_upper_core
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P) (Y T : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (hYT : Y ≤ T)
    (x : X F ζ hζ) (hx : x ∈ quotientCore A P T) (hxY : x ∉ quotientCore A P Y) :
    D.modulus (P.projection U x) ≤ T := by
  have he : P.projection U x ∈ KPMsFixedHaarDisintegration.cuspEnds A Y := by
    simpa only [quotientCore, Set.mem_ofPred_eq, not_forall, not_not,
      KPMsFixedHaarDisintegration.cuspEnds, Set.mem_iUnion, endSet] using hxY
  obtain ⟨⟨⟨j,q⟩,r⟩,hr⟩ := (D.chart_range Y hY).symm ▸ he
  rw [← hr, D.chart_modulus]
  by_contra hn
  have hTr : T < r.val := lt_of_not_ge hn
  obtain ⟨p, rfl⟩ := Quotient.exists_rep q
  have hT : 0 < T := hY.1.trans_le hYT
  have hlog : KPMsFixedHaarDisintegration.logHeight (F := F) T <
      KPMsFixedHaarDisintegration.logHeight (F := F) r.val := by
    apply (div_lt_div_iff_of_pos_right ?_).mpr
    · exact Real.log_lt_log hT hTr
    · exact mul_pos (by norm_num) (by exact_mod_cast KPCuspCharts.positive_dimension F hF)
  apply hx j
  rw [← hr, D.chart_formula]
  apply Set.mem_image_of_mem
  apply Set.mem_image_of_mem
  apply Set.mem_image_of_mem
  change KPMsFixedHaarDisintegration.logHeight (F := F) T <
    KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F _)
  rwa [KPCuspCharts.toArch_meanHeight F (KPCuspCharts.positive_dimension F hF)]
private theorem global_cutoff_continuousAt_on_core
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P) (Y ε : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (hε : 0 < ε)
    (x : X F ζ hζ) (hx : x ∈ quotientCore A P Y) :
    ContinuousAt (CutoffApproximation.coreCutoff A R P D Y ε) x := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hδ : 0 < η * ε / 2 := by positivity
  filter_upwards [global_core_upper_mem_nhds A P Y (Y + η * ε / 2) hY (by linarith) x hx] with y hy
  have hb : CutoffApproximation.coreCutoff A R P D Y ε y ≤ 1 := by
    unfold CutoffApproximation.coreCutoff
    split_ifs
    · rfl
    · exact max_le (by norm_num) (min_le_left _ _)
  have hl : 1 - η / 2 ≤ CutoffApproximation.coreCutoff A R P D Y ε y := by
    by_cases hyY : y ∈ quotientCore A P Y
    · rw [CutoffApproximation.coreCutoff, ite_eq_left hyY]
      linarith
    · have hm := global_cutoff_modulus_le_on_upper_core A R P D Y (Y + η * ε / 2) hY (by linarith) y hy hyY
      rw [CutoffApproximation.coreCutoff, ite_eq_right hyY]
      apply le_trans _ (le_max_right _ _)
      apply le_min (by linarith)
      apply (le_div_iff₀ hε).mpr
      nlinarith
  have hxχ : CutoffApproximation.coreCutoff A R P D Y ε x = 1 := ite_eq_left hx
  rw [hxχ, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hb)]
  linarith

section NativeSwitching
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (D : KPMsFixedHaarDisintegration.Disintegration A R P)

private theorem of_upper_supporting_branches {α : Type*} [PseudoMetricSpace α]
    {κ : ℝ≥0} (f : α → ℝ) (hbound : ∀ x, f x ≤ 1)
    (hsupport : ∀ x, f x < 1 → ∃ g : α → ℝ,
      LipschitzWith κ g ∧ g x = f x ∧ ∀ y, f y ≤ g y) :
    LipschitzWith κ f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  by_cases hxy : f x ≤ f y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    by_cases hx : f x < 1
    · obtain ⟨g, hg, he, hb⟩ := hsupport x hx
      have h := hg.dist_le_mul y x
      rw [Real.dist_eq] at h
      calc
        f y - f x ≤ g y - g x := by rw [he]; exact sub_le_sub_right (hb y) _
        _ ≤ |g y - g x| := le_abs_self _
        _ ≤ κ * dist x y := by simpa only [dist_comm] using h
    · have hxe : f x = 1 := le_antisymm (hbound x) (le_of_not_gt hx)
      have hye : f y = 1 := le_antisymm (hbound y) (hxe ▸ hxy)
      simp only [hxe, hye, sub_self]
      positivity
  · have hyx := lt_of_not_ge hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hyx.le)]
    have hy : f y < 1 := lt_of_lt_of_le hyx (hbound x)
    obtain ⟨g, hg, he, hb⟩ := hsupport y hy
    have h := hg.dist_le_mul x y
    rw [Real.dist_eq] at h
    calc
      f x - f y ≤ g x - g y := by rw [he]; exact sub_le_sub_right (hb x) _
      _ ≤ |g x - g y| := le_abs_self _
      _ ≤ κ * dist x y := h

private theorem native_flow_upper_branches (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (ε : ℝ) (hε : 0 < ε)
    (w : NumberField.InfinitePlace F) (i : Fin 6) (x : X F ζ hζ) :
    LipschitzWith (Real.nnabs (4 * (Y + ε) / ε))
      (fun t => CutoffApproximation.coreCutoff A R P D Y ε
        (KPSmoothActualFlowData.rightTranslate F ζ hζ
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
            (KPSmoothActualFlowData.flow F (w,i) t)) x)) := by
  let q := fun t : ℝ => KPSmoothActualFlowData.rightTranslate F ζ hζ
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,i) t))
  let χ := CutoffApproximation.coreCutoff A R P D Y ε
  have hb (y : X F ζ hζ) : χ y ≤ 1 := by
    unfold χ CutoffApproximation.coreCutoff
    split_ifs
    · rfl
    · exact max_le (by norm_num) (min_le_left _ _)
  apply of_upper_supporting_branches _ (fun t => hb (q t x))
  intro t ht
  have hx : q t x ∉ quotientCore A P Y := by
    intro hx
    have he : χ (q t x) = 1 := by simp [χ, CutoffApproximation.coreCutoff, hx]
    exact (ne_of_lt ht) he
  have hj : ∃ j : Cusps A, q t x ∈ ActualFrames.cuspEnd A P j Y := by
    change ¬ ∀ j : Cusps A, P.projection U (q t x) ∉ endSet A j Y at hx
    simpa only [not_forall, not_not, ActualFrames.cuspEnd, Set.mem_preimage] using hx
  obtain ⟨j,hj⟩ := hj
  obtain ⟨g, hg⟩ := ActualFrames.cuspLift_exists A P j Y (q t x) hj
  obtain ⟨p,k,r,η,u,hYr,hr,he⟩ :=
    ActualFrames.admissibleFrame_eq_actualCuspLift A Y hY j (q t x) g hg.2
  let a := balancedArch (ζ := ζ) (hζ := hζ) p k r
  let d := KPBoundedCuspFrames.actualFiniteRepresentative A j
  change g = cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
    d.val * KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val at he
  let α := fun s : ℝ => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F (w,i) s)
  have hzero : α 0 = 1 := by
    dsimp [α]
    rw [(KPSmoothActualFlowData.flow_properties F (w,i)).1,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1]
  have hq (s : ℝ) : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (g * α (s-t)) = q s x := by
    change KPSmoothActualFlowData.rightTranslate F ζ hζ (α (s-t))
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) = q s x
    rw [hg.1]
    change KPSmoothQuotientTranslationFlow.rightTranslation
      (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (α (s-t))
      (KPSmoothQuotientTranslationFlow.rightTranslation
        (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (α t) x) =
      KPSmoothQuotientTranslationFlow.rightTranslation
        (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (α s) x
    change (KPSmoothQuotientTranslationFlow.rightTranslation
      (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (α (s-t)) ∘
      KPSmoothQuotientTranslationFlow.rightTranslation
        (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (α t)) x = _
    rw [← congrFun (KPSmoothQuotientTranslationFlow.rightTranslation_mul
      (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (α t) (α (s-t))) x]
    have ha : α t * α (s-t) = α s := by
      dsimp [α]
      rw [← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
        ← (KPSmoothActualFlowData.flow_properties F (w,i)).2.1]
      congr 2
      ring
    rw [ha]
  have hprod (s : ℝ) : g * α (s-t) = cuspRepresentative A j *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (a * KPSmoothActualFlowData.flow F (w,i) (s-t)) * d.val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val := by
    rw [he]
    dsimp [KPBoundedCuspFrames.actualCuspLift, a, d]
    rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    have h1 := insertion_commutes (F := F) (ζ := ζ) (hζ := hζ)
      (KPSmoothActualFlowData.flow F (w,i) (s-t)) u.val
    have h2 := insertion_commutes (F := F) (ζ := ζ) (hζ := hζ)
      (KPSmoothActualFlowData.flow F (w,i) (s-t)) (KPCuspGenuineMonodromy.central F ζ hζ η)
    have h3 := insertion_commutes (F := F) (ζ := ζ) (hζ := hζ)
      (KPSmoothActualFlowData.flow F (w,i) (s-t)) d
    change _ * d.val * (KPCuspGenuineMonodromy.central F ζ hζ η).val *
      u.val.val * α (s-t) = _
    rw [mul_assoc _ u.val.val, ← h1.eq, ← mul_assoc,
      mul_assoc _ (KPCuspGenuineMonodromy.central F ζ hζ η).val, ← h2.eq, ← mul_assoc,
      mul_assoc _ d.val, ← h3.eq, ← mul_assoc]
    simp only [d, mul_assoc]
    rfl
  let b := fun s : ℝ => max 0 (min 1 ((Y + ε -
    NormalCoefficient.normalRadial (cuspRepresentative A j) (g * α (s-t))) / ε))
  have hl : LipschitzWith (Real.nnabs (4 * (Y + ε) / ε)) b := by
    have hn := global_private_native_taper_flow_lipschitz (cuspRepresentative A j) g Y ε hε
      (by linarith [hY.1]) w i
    have heK : (⟨|ε⁻¹|, abs_nonneg _⟩ * ⟨Y+ε, (by linarith [hY.1])⟩ * 4 : ℝ≥0) =
        Real.nnabs (4 * (Y + ε) / ε) := by
      apply NNReal.eq
      change |ε⁻¹| * (Y+ε) * 4 = |4*(Y+ε)/ε|
      have hpos : 0 < 4 * (Y+ε) / ε := div_pos (mul_pos (by norm_num) (by linarith [hY.1])) hε
      rw [abs_of_pos (inv_pos.mpr hε), abs_of_pos hpos]
      ring
    rw [heK] at hn
    apply LipschitzWith.of_dist_le_mul
    intro s v
    have hh := hn.dist_le_mul (s-t) (v-t)
    have heD : dist (s-t) (v-t) = dist s v := by
      simp only [Real.dist_eq]
      congr 1
      ring
    rw [heD] at hh
    exact hh
  refine ⟨b,hl,?_,?_⟩
  · have hgR : NormalCoefficient.normalRadial (cuspRepresentative A j) g = r := by
      rw [he]
      rw [normalRadial_finite_right _ _ u.val]
      change NormalCoefficient.normalRadial (cuspRepresentative A j)
        (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          d.val * (KPCuspGenuineMonodromy.central F ζ hζ η).val) = r
      rw [normalRadial_finite_right, normalRadial_finite_right]
      have hf := NormalCoefficient.normalRadial_cuspLift A j p k r hr
      simpa [cuspLift, normalRadial_finite_right, a] using hf
    have hc := cusp_product_cutoff A R P D Y hY ε hε j a η u
      (by rw [← he]; exact hgR ▸ hYr)
    dsimp [b]
    rw [sub_self, hzero, mul_one, ← hg.1]
    change χ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (cuspRepresentative A j * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        d.val * KPSmoothLocalQuotientCharts.centreMap F ζ hζ η * u.val.val)) = _ at hc
    rw [← he] at hc
    exact hc.symm
  · intro s
    by_cases hs : Y < NormalCoefficient.normalRadial (cuspRepresentative A j) (g * α (s-t))
    · have hc := cusp_product_cutoff A R P D Y hY ε hε j
        (a * KPSmoothActualFlowData.flow F (w,i) (s-t)) η u
        (by rwa [← hprod])
      rw [← hprod, hq] at hc
      exact le_of_eq hc
    · have hs' := le_of_not_gt hs
      have heB : b s = 1 := by
        dsimp [b]
        rw [min_eq_left ((le_div_iff₀ hε).mpr (by linarith)), max_eq_right (by norm_num)]
      rw [heB]
      exact hb _
end NativeSwitching

theorem global_coreCutoff_native_regular
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x : X F ζ hζ => (CutoffApproximation.coreCutoff A R P D Y ε x : ℂ)) ∧
    HasCompactSupport (fun x : X F ζ hζ => (CutoffApproximation.coreCutoff A R P D Y ε x : ℂ)) ∧
    ∀ (w : NumberField.InfinitePlace F) (i : Fin 6) (x : X F ζ hζ),
      LipschitzWith (Real.nnabs (4 * (Y + ε) / ε))
        (fun t : ℝ => (CutoffApproximation.coreCutoff A R P D Y ε
          (KPSmoothActualFlowData.rightTranslate F ζ hζ
            (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
              (KPSmoothActualFlowData.flow F (w,i) t)) x) : ℂ)) := by
  have hs : HasCompactSupport (fun x : X F ζ hζ => (CutoffApproximation.coreCutoff A R P D Y ε x : ℂ)) := by
    obtain ⟨hc,_,_⟩ := TruncatedL2Geometry.quotientCore_compact_measurable_finite A R P
      (Y+ε) (global_cutoff_upper_admissible A Y ε hY hε)
    apply HasCompactSupport.intro' hc (FiniteSlabCoreShell.isClosed_quotientCore A P (Y+ε))
    intro x hx
    rw [global_cutoff_zero_off_upper_core A R P D Y ε hY hε x hx]
    exact Complex.ofReal_zero
  refine ⟨?_, hs, ?_⟩
  · apply Complex.continuous_ofReal.comp
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ quotientCore A P Y
    · exact global_cutoff_continuousAt_on_core A R P D Y ε hY hε x hx
    · exact global_cutoff_continuousAt_off_core A R P D Y ε hY x hx
  · intro w i x
    have h := native_flow_upper_branches A R P D Y hY ε hε w i x
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [Complex.isometry_ofReal.dist_eq] using h.dist_le_mul s t

end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources

end
