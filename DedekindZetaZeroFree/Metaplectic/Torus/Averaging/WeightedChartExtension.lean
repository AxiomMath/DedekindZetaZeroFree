module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.InducedJetsAndFinalTopology

@[expose] public section

open scoped NumberField Classical NNReal BigOperators Topology
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TorusChartTransport
open KPGlobalTorusBorelNormTwistTransport
open KPGlobalTorusFiniteStagesCofinality
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def weightedChartIntegrand (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (z : GroupArch F)
    (x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C) : ℂ :=
  (((twist F ζ hζ (productModel F ζ hζ C) s).character (r.lift x))⁻¹ : ℂˣ) *
    (f.val (groupArchChart F ζ hζ z * g)).val.val (r.lift x).val

theorem weightedChartIntegrand_eq (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (z : GroupArch F) :
    weightedChartIntegrand F ζ hζ C s r f g z =
      twistedIntegrand F ζ hζ C s r (f.val (groupArchChart F ζ hζ z * g)) 1 := by
  funext x
  simp [weightedChartIntegrand, twistedIntegrand]

theorem weightedChartIntegrand_independent (C : ModelData F ζ hζ) (s : ℂ)
    (r r' : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (z : GroupArch F) :
    weightedChartIntegrand F ζ hζ C s r f g z =
      weightedChartIntegrand F ζ hζ C s r' f g z := by
  rw [weightedChartIntegrand_eq, weightedChartIntegrand_eq]
  exact twistedIntegrand_independent F ζ hζ C s r r' _ 1

theorem weightedChart_integral_eq (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (z : GroupArch F) :
    (∫ x, weightedChartIntegrand F ζ hζ C s r f g z x
      ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) =
      (twistedQ F ζ hζ C s (f.val (groupArchChart F ζ hζ z * g))).val.val 1 := by
  rw [weightedChartIntegrand_eq, twistedQ_formula F ζ hζ C s r]

 abbrev FinB (C : ModelData F ζ hζ) :=
  (finiteTorusClassProjection F ζ hζ) ⁻¹' (KPGlobalTorusPeriodizationInverse.M F ζ hζ C : Set _)
 def finBRep (C : ModelData F ζ hζ) (b : FinB F ζ hζ C) :
    KPGlobalTorusPeriodizationInverse.B F ζ hζ C := ⟨b.val.val, b.property⟩
 def finBClass (C : ModelData F ζ hζ) (b : FinB F ζ hζ C) :
    KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C :=
  KPGlobalTorusPeriodizationInverse.averagingClass F ζ hζ C (finBRep F ζ hζ C b)
private theorem finBClass_openQuotient (C : ModelData F ζ hζ) :
    IsOpenQuotientMap (finBClass F ζ hζ C) := by
  have hs := finiteTorusClassProjection_surjective F ζ hζ
  have hq : IsOpenQuotientMap (finiteTorusClassProjection F ζ hζ) :=
    ⟨hs, finiteTorusClassProjection_continuous F ζ hζ,
      finiteTorusClassProjection_open_of_surjective F ζ hζ hs⟩
  exact QuotientGroup.isOpenQuotientMap_mk.comp (hq.restrictPreimage _)
private theorem finite_commutes (a : G F ζ hζ)
    (ha : a ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ) (z : GroupArch F) :
    Commute (groupArchChart F ζ hζ z) a := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hc : Commute (groupArchTuple F ζ hζ z) b := by
    show (groupArchTuple F ζ hζ z) * b = b * (groupArchTuple F ζ hζ z)
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w =>
      have hw : b (Sum.inl w) = 1 := (Subgroup.mem_iInf.mp hb) w
      simp [hw]
    | inr q =>
      change 1 * b (Sum.inr q) = b (Sum.inr q) * 1
      simp
  exact hc.map ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))
private theorem fiber_formula (P : Polarization F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (g₀ : G F ζ hζ) (t : E F ζ hζ) :
    (f.val g₀).val.val t = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
      (f.val (t.val * g₀)).val.val 1 := by
  have hc := f.property t 0 g₀
  have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hc
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (NNReal.coe_pos.2 (pos_iff_ne_zero.2
        (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t))))))
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simp only [hn, mul_one, KPGlobalTorusPeriodizationInverse.rightAction_formula,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, one_mul] at he
  rw [he, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
private theorem rep_formula (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (y : GroupArch F) (b : FinB F ζ hζ C) :
    weightedChartIntegrand F ζ hζ C s r f g y (finBClass F ζ hζ C b) =
      ((((twist F ζ hζ (productModel F ζ hζ C) s).character (finBRep F ζ hζ C b))⁻¹ : ℂˣ) : ℂ) *
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val.val)⁻¹ *
      (f.val (groupArchChart F ζ hζ y * (b.val.val.val * g))).val.val 1 := by
  let x := finBClass F ζ hζ C b
  let r' : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C :=
    { lift := fun u => if u = x then finBRep F ζ hζ C b else r.lift u
      projects := fun u => by split_ifs with h; exact h.symm; exact r.projects u }
  have hh := congrFun (weightedChartIntegrand_independent F ζ hζ C s r r' f g y) x
  simp only [weightedChartIntegrand, r', ↓reduceIte] at hh
  unfold weightedChartIntegrand
  rw [hh, fiber_formula F ζ hζ _ f]
  have hc : Commute (groupArchChart F ζ hζ y) b.val.val.val :=
    finite_commutes F ζ hζ _ b.val.property y
  have hm : b.val.val.val * (groupArchChart F ζ hζ y * g) =
      groupArchChart F ζ hζ y * (b.val.val.val * g) := by
    rw [← mul_assoc, hc.symm.eq, mul_assoc]
  dsimp only [finBRep]
  rw [hm]
  ring
private theorem deltaHalf_continuous : Continuous (KPGlobalTorusFunctionData.deltaHalf F ζ hζ) := by
  have he (t : E F ζ hζ) :
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) =
        (((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℝ)) ^ (6 : ℕ) := by
    rw [KPGlobalCenterRationalCharacter.nu_formula]
    change _ = (_ ^ (1 / 6 : ℝ)) ^ (6 : ℕ)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    rfl
  unfold KPGlobalTorusFunctionData.deltaHalf
  simp only [he]
  exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))).pow 6))
private theorem bump_extension {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set V} (hU : IsOpen U) (η : V → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : tsupport η ⊆ U) (φ : V → ℂ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => η y • φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hη.contDiffAt.smul (hφ.contDiffAt (hU.mem_nhds hy))
  · have hyn : y ∉ tsupport η := fun h => hy (hs h)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hyn] with u hu
    simp only [Set.mem_compl_iff] at hu
    have h0 : η u = 0 := by
      by_contra h
      exact hu (subset_tsupport η h)
    simp [h0]
 def coef (C : ModelData F ζ hζ) (s : ℂ) (b : FinB F ζ hζ C) : ℂ :=
  ((((twist F ζ hζ (productModel F ζ hζ C) s).character (finBRep F ζ hζ C b))⁻¹ : ℂˣ) : ℂ) *
    (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val.val)⁻¹
private theorem coef_continuous (C : ModelData F ζ hζ) (s : ℂ) :
    Continuous (coef F ζ hζ C s) := by
  have hb : Continuous (finBRep F ζ hζ C) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hc := (Units.continuous_val.comp
    ((twist F ζ hζ (productModel F ζ hζ C) s).character.continuous.comp hb)).inv₀
      (fun b => Units.ne_zero _)
  unfold coef
  simp only [Units.val_inv_eq_inv_val]
  apply hc.mul
  apply Continuous.inv₀
  · exact (deltaHalf_continuous F ζ hζ).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · intro b
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (NNReal.coe_pos.2 (pos_iff_ne_zero.2
        (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ b.val.val))))))
private theorem source_locally_constant (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (g : G F ζ hζ) (b : FinB F ζ hζ C) :
    ∀ᶠ b' in 𝓝 b, ∀ y : GroupArch F,
      (f.val (groupArchChart F ζ hζ y * (b'.val.val.val * g))).val.val 1 =
        (f.val (groupArchChart F ζ hζ y * (b.val.val.val * g))).val.val 1 := by
  have hn : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
    rw [finitePart_eq_closure F ζ hζ]
    exact ActualFiniteFactor.finiteSubgroup_normal F ζ hζ
  let e : KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ*
      KPGlobalTorusFunctionData.finitePart F ζ hζ :=
    { toFun := fun u => ⟨g⁻¹ * u.val * g, by
        have h := hn.conj_mem u.val u.property g⁻¹
        simpa only [inv_inv, mul_assoc] using h⟩
      invFun := fun u => ⟨g * u.val * g⁻¹, hn.conj_mem u.val u.property g⟩
      left_inv := by intro u; apply Subtype.ext; dsimp; group
      right_inv := by intro u; apply Subtype.ext; dsimp; group
      map_mul' := by intro u v; apply Subtype.ext; dsimp; group
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let q : FinB F ζ hζ C → KPGlobalTorusFunctionData.finitePart F ζ hζ :=
    fun b => ⟨b.val.val.val, b.val.property⟩
  have hq : Continuous q :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hu : ∀ᶠ b' in 𝓝 b, e ((q b)⁻¹ * q b') ∈ J.toOpenSubgroup := by
    have hc : Continuous (fun b' => e ((q b)⁻¹ * q b')) :=
      e.continuous.comp (continuous_const.mul hq)
    have h1 : e ((q b)⁻¹ * q b) ∈ J.toOpenSubgroup := by simp
    exact hc.continuousAt.preimage_mem_nhds (J.toOpenSubgroup.isOpen.mem_nhds h1)
  filter_upwards [hu] with b' hb'
  let u := e ((q b)⁻¹ * q b')
  let j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J := ⟨u.val, ⟨u, hb', rfl⟩⟩
  have hj : j.val = g⁻¹ * b.val.val.val⁻¹ * b'.val.val.val * g := by
    change g⁻¹ * (b.val.val.val⁻¹ * b'.val.val.val) * g = _
    simp only [mul_assoc]
  intro y
  have hm : groupArchChart F ζ hζ y * (b'.val.val.val * g) =
      (groupArchChart F ζ hζ y * (b.val.val.val * g)) * j.val := by
    rw [hj]
    group
  rw [hm, hf.2 _ j]

theorem weightedChart_local_extension (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (g : G F ζ hζ) (z : GroupArch F) (hz : z ∈ groupArchDomain F) :
    ∃ U : Set (GroupArch F), IsOpen U ∧ z ∈ U ∧ U ⊆ groupArchDomain F ∧
      ∃ A : GroupArch F → KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C → ℂ,
        (∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun y => A y x)) ∧
        (∀ n : ℕ, Continuous
          (fun p : GroupArch F × KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C =>
            iteratedFDeriv ℝ n (fun y => A y p.2) p.1)) ∧
        ∀ y ∈ U, ∀ x, A y x = weightedChartIntegrand F ζ hζ C s r f g y x := by
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp ((groupArchDomain_open F).mem_nhds hz)
  let η : ContDiffBump z :=
    { rIn := d / 4
      rOut := d / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hηU : tsupport η ⊆ groupArchDomain F := by
    rw [η.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [η]; linarith)).trans hdU
  let A := fun y x => η y • weightedChartIntegrand F ζ hζ C s r f g y x
  let φ := fun (b : FinB F ζ hζ C) y =>
    η y • (f.val (groupArchChart F ζ hζ y * (b.val.val.val * g))).val.val 1
  have hφ (b : FinB F ζ hζ C) : ContDiff ℝ (⊤ : ℕ∞) (φ b) :=
    bump_extension (groupArchDomain_open F) η η.contDiff hηU _ (hf.1 _)
  have hA (b : FinB F ζ hζ C) : (fun y => A y (finBClass F ζ hζ C b)) =
      coef F ζ hζ C s b • φ b := by
    funext y
    simp only [A, rep_formula F ζ hζ C s r f g y b, φ, Pi.smul_apply, coef, smul_eq_mul,
      Complex.real_smul]
    ring
  refine ⟨Metric.ball z η.rIn, Metric.isOpen_ball, Metric.mem_ball_self η.rIn_pos,
    ?_, A, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball η.rIn_lt_rOut.le).trans
      (Metric.ball_subset_closedBall.trans (by rw [← η.tsupport_eq]; exact hηU))
  · intro x
    obtain ⟨b, rfl⟩ := (finBClass_openQuotient F ζ hζ C).surjective x
    rw [hA]
    exact (hφ b).const_smul (R := ℂ) _
  · intro n
    apply ((IsOpenQuotientMap.id (X := GroupArch F)).prodMap
      (finBClass_openQuotient F ζ hζ C)).isQuotientMap.continuous_iff.mpr
    rw [continuous_iff_continuousAt]
    rintro ⟨y, b⟩
    have hb := source_locally_constant F ζ hζ C s J f hf g b
    have hj : (fun p : GroupArch F × FinB F ζ hζ C =>
        iteratedFDeriv ℝ n (fun y => A y (finBClass F ζ hζ C p.2)) p.1) =ᶠ[𝓝 (y, b)]
        (fun p => coef F ζ hζ C s p.2 • iteratedFDeriv ℝ n (φ b) p.1) := by
      filter_upwards [continuous_snd.continuousAt.eventually hb] with p hp
      have hφeq : φ p.2 = φ b := by funext u; exact congrArg (fun v : ℂ => η u • v) (hp u)
      rw [hA, hφeq, iteratedFDeriv_const_smul_apply (R := ℂ)
        ((hφ b).contDiffAt.of_le (by simp))]
    exact (((coef_continuous F ζ hζ C s).comp continuous_snd).smul
      ((hφ b).continuous_iteratedFDeriv (by simp) |>.comp continuous_fst)).continuousAt.congr_of_eventuallyEq hj
  · intro y hy x
    have he := η.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp only [A, he, one_smul]

end
end DedekindZetaZeroFree.TorusChartTransport
