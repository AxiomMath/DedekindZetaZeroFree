module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.DoubleKernelFactorization
public import DedekindZetaZeroFree.Theta.Profiles.ShiftedCubicBetaIntegrability
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.CubeRatioHaarPushforward

@[expose] public section

namespace DedekindZetaZeroFree.KPActualFullKernelArithmetic

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneOpenCellKernel KPRankOneLiftedRegulatedDiagonalAlgebra
open KPRankOneCenterInducedDiagonalComparison KPActualScalarBinding

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

private lemma shifted_roots_null_generic
    (L : Type*) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [MeasurableSpace L] [BorelSpace L]
    (dx : Measure L) [dx.IsAddHaarMeasure] (c : Lˣ) :
    KPCubicHaar.multiplicativeHaar L dx {y : Lˣ | (y:L)^3+(c:L)=0} = 0 := by
  classical
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  let _ := isUniformAddGroup_of_addCommGroup (G := L)
  let _ : T2Space L := inferInstance
  let _ : BorelSpace Lˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace L) = borel Lˣ
    rw [@BorelSpace.measurable_eq L _ _ _, Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  have hp : (Polynomial.X^3 + Polynomial.C (c:L) : Polynomial L) ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : Polynomial L => p.coeff 3) h
    simp at h0
  have hf : {x : L | x^3+(c:L)=0}.Finite := by
    convert Polynomial.finite_setOfPred_isRoot hp using 1
    ext x; simp [Polynomial.IsRoot]
  have hfin : {y : Lˣ | (y:L)^3+(c:L)=0}.Finite :=
    hf.preimage (Set.injOn_of_injective Units.val_injective)
  have hz : dx {(0:L)} = 0 := by
    by_contra h
    have hi : (KPCubicUnitIndices.Integers L : Set L).Infinite := by
      exact Set.infinite_coe_iff.mp (inferInstance : Infinite (KPCubicUnitIndices.Integers L))
    have hc : IsCompact (KPCubicUnitIndices.Integers L : Set L) :=
      IsNonarchimedeanLocalField.isCompact_closedBall L 1
    have ht : dx (KPCubicUnitIndices.Integers L : Set L) = ⊤ :=
      hi.meas_eq_top ⟨dx {0}, h, fun x _ => (Measure.addHaar_singleton dx x).ge⟩
    exact hc.measure_lt_top.ne ht
  let _ : NullSingletonClass dx := ⟨fun x => (Measure.addHaar_singleton dx x).trans hz⟩
  have hs : MeasurableSet {y : Lˣ | (y:L)^3+(c:L)=0} := by
    exact (isClosed_eq (Units.continuous_val.pow 3 |>.add continuous_const)
      continuous_const).measurableSet
  unfold KPCubicHaar.multiplicativeHaar
  apply le_antisymm _ zero_le
  calc
    _ ≤ (dx.withDensity (fun x => ENNReal.ofReal ((KPCubicHaar.abs L x)⁻¹)))
      ((fun x : Lˣ => (x:L)) '' {y : Lˣ | (y:L)^3+(c:L)=0}) :=
      Measure.comap_apply_le _ _ hs.nullMeasurableSet
    _ = 0 := (hfin.image _).measure_zero _

private lemma ordinary_hilbert_norm (c x : (LocalField F q)ˣ) :
    ‖(KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ)‖ = 1 := by
  let w := KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x)
  have hpow : w^3=1 := by
    rw [← map_pow]
    have hc : KPHilbert.B3 F ζ hζ (Sum.inr q) c x ^ 3 = 1 :=
      Subtype.ext (KPHilbert.B3 F ζ hζ (Sum.inr q) c x).property
    rw [hc, map_one]
  have hn : ‖(w:ℂ)‖^3=1 := by
    have h := congrArg (fun w : ℂˣ => ‖(w:ℂ)‖) hpow
    simpa using h
  change ‖(w:ℂ)‖=1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg (w:ℂ)) (by norm_num : (3:ℕ)≠0)).mp hn

private lemma twisted_mellin_generic
    (L : Type*) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [MeasurableSpace L] [BorelSpace L]
    (dx : Measure L) [dx.IsAddHaarMeasure] (χ : Lˣ → ℂ)
    (hχ : Continuous χ) (hnχ : ∀ x, ‖χ x‖=1)
    (φ : L → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (ρ : ℂ) (hρ : 0 < ρ.re) :
    Integrable (fun x : Lˣ => φ (x:L) * χ x * normPower L x ρ)
      (KPCubicHaar.multiplicativeHaar L dx) := by
  let _ : BorelSpace Lˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace L) = borel Lˣ
    rw [@BorelSpace.measurable_eq L _ _ _, Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  have hab (x : Lˣ) : KPCubicHaar.abs L (x:L) = localAbs L x := by
    simp [KPCubicHaar.abs, localAbs, Units.ne_zero, Real.rpow_intCast]; rfl
  have hi := KPJointRegulator.MellinBetaIntegrability.mellin_integrable L dx φ hφ hcφ ρ hρ
  have hm : Continuous (fun x : Lˣ => normPower L x ρ) := by
    have he := KPJointRegulator.mellin_continuous L (fun _ => 1) (IsLocallyConstant.const (1:ℂ)) ρ
    change Continuous (fun x : Lˣ => (1:ℂ) * Complex.exp (ρ * (Real.log (KPCubicHaar.abs L (x:L)) : ℂ))) at he
    simpa only [one_mul, normPower, hab] using he
  apply hi.congr'
  · exact ((hφ.continuous.comp Units.continuous_val).mul hχ).aestronglyMeasurable.mul hm.aestronglyMeasurable
  · filter_upwards [] with x
    simp only [norm_mul, hnχ, mul_one]
    congr 1
    rw [normPower, hab]

private lemma actual_twisted_mellin_integrable
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (c : (LocalField F q)ˣ) (φ : LocalField F q → ℂ)
    (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (ρ : ℂ) (hρ : 0 < ρ.re) :
    Integrable (fun x : (LocalField F q)ˣ => φ (x:LocalField F q) *
      (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
      normPower (LocalField F q) x ρ)
      (KPCubicHaar.multiplicativeHaar (LocalField F q) dx) := by
  let _ : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  let _ : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have hc : Continuous (fun x : (LocalField F q)ˣ =>
      (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ)) := by
    have he := (KPHilbert.B3_continuous F ζ hζ (Sum.inr q)).comp
      ((continuous_const : Continuous (fun _ : (LocalField F q)ˣ => c)).prodMk continuous_id)
    have hι : Continuous (fun e : rootsOfUnity 3 F =>
        (KPExceptionalRaw.ordinaryIota F ζ hζ e : ℂ)) := continuous_of_discreteTopology
    exact hι.comp he
  exact twisted_mellin_generic (LocalField F q) dx _ hc
    (ordinary_hilbert_norm F ζ hζ q c) φ hφ hcφ ρ hρ
private lemma shifted_tensor_skew
    (L : Type*) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [MeasurableSpace L] [BorelSpace L]
    (dx : Measure L) [dx.IsAddHaarMeasure]
    (m β : Lˣ → ℂ) (hm : Integrable m (KPCubicHaar.multiplicativeHaar L dx))
    (hβ : Integrable β (KPCubicHaar.multiplicativeHaar L dx))
    (a : Lˣ → Lˣ) (ha : Measurable a) :
    let μ := KPCubicHaar.multiplicativeHaar L dx
    Integrable (fun xy : Lˣ×Lˣ => m (xy.1*a xy.2)*β xy.2) (μ.prod μ) ∧
      (∫ y : Lˣ, (∫ x : Lˣ, m (x*a y)*β y ∂μ) ∂μ) =
        (∫ x : Lˣ, m x ∂μ) * (∫ y : Lˣ, β y ∂μ) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  let _ := isUniformAddGroup_of_addCommGroup (G := L)
  let _ : BorelSpace Lˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace L) = borel Lˣ
    rw [@BorelSpace.measurable_eq L _ _ _, Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  let _ := KPJointRegulator.MellinBetaIntegrability.localField_secondCountable L
  let _ : SecondCountableTopology Lˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ := KPCubicHaar.multiplicativeHaar L dx
  let _ : SigmaFinite μ := KPJointRegulator.MellinBetaIntegrability.multiplicativeHaar_sigmaFinite L dx
  have hcompact : IsCompact (KPCubicUnitIndices.Integers L : Set L) :=
    IsNonarchimedeanLocalField.isCompact_closedBall L 1
  have hopen : IsOpen (KPCubicUnitIndices.Integers L : Set L) := Valued.isOpen_integer L
  have hpos : 0 < dx (KPCubicUnitIndices.Integers L : Set L) :=
    hopen.measure_pos (μ := dx) ⟨0, by simp⟩
  let _ : μ.IsHaarMeasure := (kp_rankone_cubic_haar_power_measure L dx _
    (ENNReal.toReal_pos hpos.ne' hcompact.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hcompact.measure_lt_top.ne).symm).1
  have hp : MeasurePreserving (fun yx : Lˣ×Lˣ => (yx.1,a yx.1*yx.2))
      (μ.prod μ) (μ.prod μ) :=
    (MeasurePreserving.id μ).skew_product
      ((ha.comp measurable_fst).mul measurable_snd)
      (Filter.Eventually.of_forall (fun y => map_mul_left_eq_self μ (a y)))
  have hi := hβ.mul_prod hm
  have hcomp := (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hswap := ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).integrable_comp
    hcomp.aestronglyMeasurable).mpr hcomp
  have hg : Integrable (fun xy : Lˣ×Lˣ => m (xy.1*a xy.2)*β xy.2) (μ.prod μ) := by
    apply hswap.congr
    filter_upwards [] with xy
    simp [Function.comp_def, mul_comm]
  refine ⟨hg, ?_⟩
  have hf : ∀ y, (∫ x : Lˣ, m (x*a y)*β y ∂μ) = (∫ x : Lˣ, m x ∂μ)*β y := by
    intro y
    rw [integral_mul_const]
    congr 1
    exact integral_mul_right_eq_self m (a y)
  change (∫ y : Lˣ, (∫ x : Lˣ, m (x*a y)*β y ∂μ) ∂μ) = _
  simp_rw [hf]
  exact integral_const_mul _ _

open scoped Classical in
private lemma shifted_unit_measurable
    (L : Type*) [Field L] [MeasurableSpace L] [MeasurableSingletonClass L] [MeasurableAdd₂ L]
    [MeasurableMul₂ L] (c : Lˣ) :
    Measurable (fun y : Lˣ => if h : (y:L)^3+(c:L)=0 then (1:Lˣ) else
      Units.mk0 ((y:L)^3+(c:L)) h) := by
  classical
  have hv : Measurable (fun y : Lˣ => (y:L)) := MeasurableSpace.le_map_comap
  have hg : Measurable (fun y : Lˣ => (y:L)^3+(c:L)) :=
    (hv.pow_const 3).add_const _
  have hi : Measurable (fun y : Lˣ =>
      ((if h : (y:L)^3+(c:L)=0 then (1:Lˣ) else Units.mk0 ((y:L)^3+(c:L)) h):L)) := by
    have he : (fun y : Lˣ => ((if h : (y:L)^3+(c:L)=0 then (1:Lˣ) else
      Units.mk0 ((y:L)^3+(c:L)) h):L)) =
      (fun y : Lˣ => if (y:L)^3+(c:L)=0 then 1 else (y:L)^3+(c:L)) := by
      funext y; split_ifs <;> rfl
    rw [he]
    exact Measurable.ite (hg (measurableSet_singleton 0)) measurable_const hg
  rw [measurable_iff_comap_le] at hi ⊢
  unfold Units.instMeasurableSpace
  rw [MeasurableSpace.comap_comp]
  convert hi using 1
  congr 1
  funext y
  dsimp [Function.comp_def]
  split_ifs <;> rfl

private lemma shifted_fiber_formula
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (χ : Lˣ →* ℂˣ) (φ : L → ℂ) (t : ℂˣ) (ρ : ℂ)
    (c x y : Lˣ) (hy : (y:L)^3+(c:L) ≠ 0)
    (hχ : χ (Units.mk0 ((y:L)^3+(c:L)) hy) = 1) :
    φ ((x:L)*((y:L)^3+(c:L))) * (χ x:ℂ) * KPCubicExpansion.omega L t y *
      normPower L x ρ =
    (φ ((x * Units.mk0 ((y:L)^3+(c:L)) hy : Lˣ):L) *
      (χ (x * Units.mk0 ((y:L)^3+(c:L)) hy):ℂ) *
      normPower L (x * Units.mk0 ((y:L)^3+(c:L)) hy) ρ) *
    (KPCubicExpansion.omega L t y * Complex.exp (-ρ *
      (Real.log (KPCubicHaar.abs L ((y:L)^3+(c:L))) : ℂ))) := by
  have hab (w : Lˣ) : KPCubicHaar.abs L (w:L) = localAbs L w := by
    simp [KPCubicHaar.abs, localAbs, Units.ne_zero, Real.rpow_intCast]; rfl
  have hn : normPower L (x * Units.mk0 ((y:L)^3+(c:L)) hy) ρ =
      normPower L x ρ * Complex.exp (ρ *
        (Real.log (KPCubicHaar.abs L ((y:L)^3+(c:L))) : ℂ)) := by
    simp only [normPower, localAbs_mul,
      Real.log_mul (ne_of_gt (localAbs_pos L x))
        (ne_of_gt (localAbs_pos L (Units.mk0 _ hy))), Complex.ofReal_add,
      mul_add, Complex.exp_add]
    rw [← hab (Units.mk0 _ hy)]; rfl
  simp only [map_mul, hχ, mul_one, Units.val_mul, Units.val_mk0, hn]
  have he : Complex.exp (ρ * (Real.log (KPCubicHaar.abs L ((y:L)^3+(c:L))) : ℂ)) *
      Complex.exp (-ρ * (Real.log (KPCubicHaar.abs L ((y:L)^3+(c:L))) : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination -(φ ((x:L)*((y:L)^3+(c:L))) * (χ x:ℂ) *
    KPCubicExpansion.omega L t y * normPower L x ρ) * he

open scoped Classical in
private lemma shifted_product_of_scalar_estimates
    (L : Type*) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [MeasurableSpace L] [BorelSpace L]
    (dx : Measure L) [dx.IsAddHaarMeasure]
    (χ : Lˣ →* ℂˣ) (φ : L → ℂ) (t : ℂˣ) (ρ : ℂ) (c : Lˣ)
    (hχ : ∀ (y : Lˣ) (hy : (y:L)^3+(c:L) ≠ 0),
      χ (Units.mk0 ((y:L)^3+(c:L)) hy) = 1)
    (hm : Integrable (fun x : Lˣ => φ (x:L)*(χ x:ℂ)*normPower L x ρ)
      (KPCubicHaar.multiplicativeHaar L dx))
    (hb : Integrable (fun y : Lˣ => if (y:L)^3+(c:L)=0 then 0 else
      KPCubicExpansion.omega L t y * Complex.exp (-ρ *
        (Real.log (KPCubicHaar.abs L ((y:L)^3+(c:L))) : ℂ)))
      (KPCubicHaar.multiplicativeHaar L dx)) :
    let μ := KPCubicHaar.multiplicativeHaar L dx
    let g : Lˣ×Lˣ → ℂ := fun xy => φ ((xy.1:L)*((xy.2:L)^3+(c:L))) *
      (χ xy.1:ℂ)*KPCubicExpansion.omega L t xy.2*normPower L xy.1 ρ
    Integrable g (μ.prod μ) ∧
      (∫ y : Lˣ, (∫ x : Lˣ, g (x,y) ∂μ) ∂μ) =
      (∫ x : Lˣ, φ (x:L)*(χ x:ℂ)*normPower L x ρ ∂μ) *
      (∫ y : Lˣ, if (y:L)^3+(c:L)=0 then 0 else
        KPCubicExpansion.omega L t y * Complex.exp (-ρ *
          (Real.log (KPCubicHaar.abs L ((y:L)^3+(c:L))) : ℂ)) ∂μ) := by
  classical
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  let _ := isUniformAddGroup_of_addCommGroup (G := L)
  let _ : BorelSpace Lˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace L) = borel Lˣ
    rw [@BorelSpace.measurable_eq L _ _ _, Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  let μ := KPCubicHaar.multiplicativeHaar L dx
  let _ : SigmaFinite μ := KPJointRegulator.MellinBetaIntegrability.multiplicativeHaar_sigmaFinite L dx
  let m := fun x : Lˣ => φ (x:L)*(χ x:ℂ)*normPower L x ρ
  let β := fun y : Lˣ => if (y:L)^3+(c:L)=0 then (0:ℂ) else
    KPCubicExpansion.omega L t y * Complex.exp (-ρ *
      (Real.log (KPCubicHaar.abs L ((y:L)^3+(c:L))) : ℂ))
  let _ := KPJointRegulator.MellinBetaIntegrability.localField_secondCountable L
  let a := fun y : Lˣ => if hy : (y:L)^3+(c:L)=0 then (1:Lˣ) else
    Units.mk0 ((y:L)^3+(c:L)) hy
  have ha : Measurable a := shifted_unit_measurable L c
  have hp := shifted_tensor_skew L dx m β hm hb a ha
  have hr : ∀ᵐ y : Lˣ ∂μ, (y:L)^3+(c:L) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using shifted_roots_null_generic L dx c
  have hform : ∀ (x y : Lˣ), (y:L)^3+(c:L) ≠ 0 →
      φ ((x:L)*((y:L)^3+(c:L)))*(χ x:ℂ)*KPCubicExpansion.omega L t y*normPower L x ρ =
        m (x*a y)*β y := by
    intro x y hy
    dsimp [m, β, a]
    rw [dite_eq_right hy, ite_eq_right hy]
    exact shifted_fiber_formula L χ φ t ρ c x y hy (hχ y hy)
  have hprod := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hr
  refine ⟨hp.1.congr ?_, ?_⟩
  · filter_upwards [hprod] with xy hxy
    exact (hform xy.1 xy.2 hxy).symm
  · change (∫ y : Lˣ, (∫ x : Lˣ,
      φ ((x:L)*((y:L)^3+(c:L)))*(χ x:ℂ)*KPCubicExpansion.omega L t y*normPower L x ρ
        ∂μ) ∂μ) = _
    rw [← hp.2]
    apply integral_congr_ae
    filter_upwards [hr] with y hy
    apply integral_congr_ae
    filter_upwards [] with x
    exact hform x y hy

open scoped Classical in
private lemma actual_shifted_product
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (c : (LocalField F q)ˣ) (φ : LocalField F q → ℂ)
    (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (t : ℂˣ) (ρ : ℂ) (hcone : KPJointRegulator.cone (LocalField F q) t ρ) :
    let μ := KPCubicHaar.multiplicativeHaar (LocalField F q) dx
    let χ := fun x : (LocalField F q)ˣ =>
      (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ)
    let g := fun xy : (LocalField F q)ˣ×(LocalField F q)ˣ =>
      φ ((xy.1:LocalField F q)*((xy.2:LocalField F q)^3+(c:LocalField F q))) *
        χ xy.1*KPCubicExpansion.omega (LocalField F q) t xy.2*
        normPower (LocalField F q) xy.1 ρ
    Integrable g (μ.prod μ) ∧
      (∫ y : (LocalField F q)ˣ, (∫ x : (LocalField F q)ˣ, g (x,y) ∂μ) ∂μ) =
      (∫ x : (LocalField F q)ˣ, φ (x:LocalField F q)*χ x*normPower (LocalField F q) x ρ ∂μ) *
      (∫ y : (LocalField F q)ˣ, if (y:LocalField F q)^3+(c:LocalField F q)=0 then 0 else
        KPCubicExpansion.omega (LocalField F q) t y * Complex.exp (-ρ *
          (Real.log (KPCubicHaar.abs (LocalField F q) ((y:LocalField F q)^3+(c:LocalField F q))) : ℂ)) ∂μ) := by
  let B : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) c
      map_one' := KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 c
      map_mul' := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 c }
  let χ := (KPExceptionalRaw.ordinaryIota F ζ hζ).comp B
  have hs : ∀ (y : (LocalField F q)ˣ) (hy : (y:LocalField F q)^3+(c:LocalField F q) ≠ 0),
      χ (Units.mk0 ((y:LocalField F q)^3+(c:LocalField F q)) hy) = 1 := by
    intro y hy
    change KPExceptionalRaw.ordinaryIota F ζ hζ
      (KPHilbert.B3 F ζ hζ (Sum.inr q) c (Units.mk0 _ hy)) = 1
    rw [steinberg_shifted_cube F ζ hζ q c y hy, map_one]
  exact shifted_product_of_scalar_estimates (LocalField F q) dx χ φ t ρ c hs
    (actual_twisted_mellin_integrable F ζ hζ q dx c φ hφ hcφ ρ hcone.1)
    (actual_shifted_beta_integrable F q dx c t ρ hcone)

private lemma units_borel_generic (L : Type*) [Field L] [TopologicalSpace L]
    [MeasurableSpace L] [BorelSpace L] [ContinuousInv₀ L] : BorelSpace Lˣ := by
  constructor
  unfold Units.instMeasurableSpace
  rw [@BorelSpace.measurable_eq L _ _ _, ← borel_comap,
    ← Units.isEmbedding_val₀.isInducing.eq_induced]

private lemma cube_shear_integrable
    (L : Type*) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [MeasurableSpace L] [BorelSpace L]
    (dx : Measure L) [dx.IsAddHaarMeasure]
    (κ : KPCubicUnitIndices.Integers L) (hκ : IsPrimitiveRoot κ 3)
    (g : Lˣ×Lˣ → ℂ) (hg : Integrable g
      ((KPCubicHaar.multiplicativeHaar L dx).prod (KPCubicHaar.multiplicativeHaar L dx)))
    (a : Lˣ) :
    Integrable (fun uv : Lˣ×Lˣ => g (a*uv.2^3,uv.1/uv.2))
      ((KPCubicHaar.multiplicativeHaar L dx).prod (KPCubicHaar.multiplicativeHaar L dx)) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  let _ := isUniformAddGroup_of_addCommGroup (G := L)
  let _ : BorelSpace Lˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace L) = borel Lˣ
    rw [@BorelSpace.measurable_eq L _ _ _, Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  let _ := KPJointRegulator.MellinBetaIntegrability.localField_secondCountable L
  let _ : SecondCountableTopology Lˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ := KPCubicHaar.multiplicativeHaar L dx
  let _ : SigmaFinite μ := KPJointRegulator.MellinBetaIntegrability.multiplicativeHaar_sigmaFinite L dx
  have hc : IsCompact (KPCubicUnitIndices.Integers L : Set L) :=
    IsNonarchimedeanLocalField.isCompact_closedBall L 1
  have ho : IsOpen (KPCubicUnitIndices.Integers L : Set L) := Valued.isOpen_integer L
  have hp : 0 < dx (KPCubicUnitIndices.Integers L : Set L) := ho.measure_pos (μ := dx) ⟨0, by simp⟩
  let _ : μ.IsHaarMeasure := (kp_rankone_cubic_haar_power_measure L dx _
    (ENNReal.toReal_pos hp.ne' hc.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hc.measure_lt_top.ne).symm).1
  let C := CubicCharacters.cubes Lˣ
  let A : Lˣ → Lˣ := fun v => a*v^3
  have hcub := KPCubicHaarTransport.cube_pushforward L κ hκ dx
  change Measure.map (fun v : Lˣ => v^3) μ =
    ENNReal.ofReal ((C.index : ℝ)/3) • μ.restrict (C : Set Lˣ) at hcub
  have hmap : Measure.map A μ = ENNReal.ofReal ((C.index : ℝ)/3) •
      Measure.map (fun v : Lˣ => a*v) (μ.restrict (C : Set Lˣ)) := by
    change Measure.map ((fun v : Lˣ => a*v) ∘ (fun v : Lˣ => v^3)) μ = _
    rw [← Measure.map_map (measurable_const_mul a) (continuous_pow 3).measurable,
      hcub, Measure.map_smul _ (measurable_const_mul a).aemeasurable]
  have hprod : Measure.map (fun xy : Lˣ×Lˣ => (A xy.1,xy.2)) (μ.prod μ) ≤
      ENNReal.ofReal ((C.index : ℝ)/3) • (μ.prod μ) := by
    change Measure.map (Prod.map A id) (μ.prod μ) ≤ _
    rw [← Measure.map_prod_map μ μ (by fun_prop) measurable_id, Measure.map_id, hmap,
      Measure.prod_smul_left]
    apply smul_le_smul_left
    have hm : Measure.map (fun v : Lˣ => a*v) (μ.restrict (C : Set Lˣ)) ≤ μ := by
      calc
        _ ≤ Measure.map (fun v : Lˣ => a*v) μ :=
          Measure.map_mono Measure.restrict_le_self (measurable_const_mul a)
        _ = μ := map_mul_left_eq_self μ a
    exact Measure.prod_mono hm le_rfl
  have htarget : Integrable g (Measure.map (fun xy : Lˣ×Lˣ => (A xy.1,xy.2)) (μ.prod μ)) :=
    (hg.smul_measure ENNReal.ofReal_ne_top).mono_measure hprod
  have hi := (integrable_map_measure htarget.aestronglyMeasurable (by fun_prop)).mp htarget
  have hs := (measurePreserving_prod_inv_mul_swap μ μ).integrable_comp hi.aestronglyMeasurable
  have hh := hs.mpr hi
  apply hh.congr
  filter_upwards [] with uv
  simp only [Function.comp_apply, A]
  congr 2
  simp [div_eq_mul_inv, mul_comm]

private lemma winv (K : Type*) [Field K] : (KubotaRankTwo.w K)⁻¹ = KubotaRankTwo.d K (-1) (-1) * KubotaRankTwo.w K := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
private lemma Xwinv (K : Type*) [Field K] : KubotaRankTwo.X K (KubotaRankTwo.w K)⁻¹ = -1 := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply]
private lemma Xwnw (K : Type*) [Field K] (v : Kˣ) :
    KubotaRankTwo.X K ((KubotaRankTwo.w K)⁻¹ * KubotaRankTwo.n K (-((v⁻¹ : Kˣ) : K)) * (KubotaRankTwo.w K)⁻¹) = -v⁻¹ := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply, Units.ne_zero]

private lemma BoneL (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) 1 a = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 a
private lemma BoneR (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) a 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 a
private lemma BnegR (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) a (-1) = 1 :=
  (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 a |>.2.1
private lemma sigmanR (g : KubotaRankTwo.GL2 (LocalField F q)) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q) g (KubotaRankTwo.n (LocalField F q) s) = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, BoneL, BoneR]
private lemma sigww : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    (KubotaRankTwo.w (LocalField F q)) (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xwinv, BoneL, BoneR]
private lemma sigwnw (v : (LocalField F q)ˣ) : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    ((KubotaRankTwo.w (LocalField F q))⁻¹ * KubotaRankTwo.n (LocalField F q) (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)))
    (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xwnw, KubotaRankTwo.X_mul_n,
    Xwinv, map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w, inv_one, one_mul,
    mul_one, one_pow]
  have hr : (-v⁻¹) / (-1) = v⁻¹ := by simp
  rw [hr, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 v⁻¹ |>.1, BoneL]
  simp
private lemma Xdnw (K : Type*) [Field K] (v : Kˣ) (s : K) :
    KubotaRankTwo.X K (KubotaRankTwo.d K (v ^ 2) 1 * KubotaRankTwo.n K s * (KubotaRankTwo.w K)⁻¹) = -1 := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply]
private lemma Bselfpow (a : (LocalField F q)ˣ) (m n : ℤ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (a ^ m) (a ^ n) = 1 := by
  let BL (b : (LocalField F q)ˣ) : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun x => KPHilbert.B3 F ζ hζ (Sum.inr q) x b
      map_one' := BoneL F ζ hζ q b
      map_mul' := fun x y => (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 x y b }
  let BR : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) a
      map_one' := BoneR F ζ hζ q a
      map_mul' := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 a }
  change BL (a ^ n) (a ^ m) = 1
  rw [map_zpow]
  change (BR (a ^ n)) ^ m = 1
  rw [map_zpow]
  change (KPHilbert.B3 F ζ hζ (Sum.inr q) a a ^ n) ^ m = 1
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 a |>.1]
  simp
private lemma BnegL (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) (-1) a = 1 := by
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1, BnegR]
  simp
private lemma sigdnw (v : (LocalField F q)ˣ) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (KubotaRankTwo.d (LocalField F q) (v ^ 2) 1 * KubotaRankTwo.n (LocalField F q) s)
      (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xdnw, KubotaRankTwo.X_mul_n,
    KubotaRankTwo.X_d, Xwinv, map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w,
    KubotaRankTwo.det_d, inv_one, mul_one, div_one, one_mul, one_pow]
  rw [BnegL, BoneR]
  simp
private lemma Xscalar (K : Type*) [Field K] (v : Kˣ) :
    KubotaRankTwo.X K (Matrix.GeneralLinearGroup.scalar (Fin 2) v) = v := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.scalar]
private lemma Xscalar_mul (K : Type*) [Field K] (v : Kˣ) (g : KubotaRankTwo.GL2 K) :
    KubotaRankTwo.X K (Matrix.GeneralLinearGroup.scalar (Fin 2) v * g) = v * KubotaRankTwo.X K g := by
  classical
  apply Units.ext
  simp only [KubotaRankTwo.X, Units.val_mk0, Units.val_mul]
  unfold KubotaRankTwo.x
  have he (i j : Fin 2) : (Matrix.GeneralLinearGroup.scalar (Fin 2) v * g) i j = (v : K) * g i j := by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.scalar]
  rw [he 1 0, he 1 1]
  simp only [mul_eq_zero, v.ne_zero, false_or]
  split_ifs <;> rfl
private lemma sigscalar (v : (LocalField F q)ˣ) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹)
      (KubotaRankTwo.d (LocalField F q) (v ^ 2) 1 * KubotaRankTwo.n (LocalField F q) ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
        (KubotaRankTwo.w (LocalField F q))⁻¹ * KubotaRankTwo.n (LocalField F q) s) = 1 := by
  change KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    ((Matrix.GeneralLinearGroup.scalar (Fin 2)) v⁻¹) _ = 1
  unfold KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
  simp only [Xscalar_mul, Xscalar,
    KubotaRankTwo.X_mul_n, Xdnw,
    KubotaRankTwo.det,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_one, mul_one]
  have h1 : v⁻¹ * (-1) / v⁻¹ = -1 := by simp
  rw [h1, BnegL]
  have hB : KPHilbert.B3 F ζ hζ (Sum.inr q) (v⁻¹ ^ 2) (v ^ 2) = 1 := by
    convert Bselfpow F ζ hζ q v (-2) 2 using 1 <;> simp
  simp only [map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w,
    KubotaRankTwo.det_d, inv_one, mul_one, ← inv_pow, hB, one_pow]
private lemma kappa_eq_one (v : (LocalField F q)ˣ) (s : LocalField F q) : kappa F ζ hζ q v s = 1 := by
  rw [kappa, bruhatLeft, bruhatRight, signedWeyl_eq_prescribed_signed]
  have he : ∀ x : (LocalField F q)ˣ,
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) x).epsilon = 1 := fun _ => rfl
  have hg : ∀ x : (LocalField F q)ˣ,
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) x).g = Matrix.GeneralLinearGroup.scalar (Fin 2) x := fun _ => rfl
  simp only [KPLocalCover.mul_epsilon, KPLocalCover.inv_epsilon, KPLocalCover.mul_g,
    KPLocalCover.inv_g, KPStandardLocalRootLifts.signedW, KPStandardLocalRootLifts.N,
    KPStandardLocalRootLifts.A, he, hg,
    KPLocalCover.sectionMap_epsilon, KPLocalCover.sectionMap_g]
  simp only [sigww F ζ hζ q, sigmanR F ζ hζ q, sigwnw F ζ hζ q,
    sigdnw F ζ hζ q, sigscalar F ζ hζ q, one_mul, mul_one,
    inv_one, div_one]

private lemma center_lc {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
    [CommGroup D] [Finite D] (T : LocalHeisenbergData H₀ D) (f : CenterModule T) : IsLocallyConstant f.val := by
 let J : Subgroup H₀ := T.ω.toMonoidHom.ker.map T.C.subtype
 have hJ : IsOpen (J : Set H₀) := by
   exact T.center_open.isOpenMap_subtype_val _ T.character_kernel_open
 rw [IsLocallyConstant.iff_eventually_eq]
 intro h
 have hc : Continuous (fun y : H₀ => y * h⁻¹) := continuous_id.mul continuous_const
 have hn : ∀ᶠ y in nhds h, y * h⁻¹ ∈ J :=
   hc.continuousAt.preimage_mem_nhds (by simpa using hJ.mem_nhds J.one_mem)
 filter_upwards [hn] with y hy
 obtain ⟨c, hc, he⟩ := hy
 have hw : T.ω c = 1 := hc
 have hf := f.property c h
 change (c : H₀) = y * h⁻¹ at he
 have hey : (c : H₀) * h = y := by rw [he]; group
 simpa [hey, hw] using hf

private lemma root_cont {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
    [CommGroup D] [Finite D] (T : LocalHeisenbergData H₀ D)
    (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T) (B : Binding F ζ hζ q A P) : Continuous B.rootTorus := by
 have hc := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
   (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2
 have ht : Continuous (fun v => A.torus (B.rootTorus v)) := by
   apply Continuous.subtype_mk
   change Continuous (fun v => (A.torus (B.rootTorus v) : Cover F ζ hζ q))
   simp_rw [B.torus_eq]
   exact hc.comp (continuous_id.pow 2)
 have he : B.rootTorus = fun v => A.retract (A.torus (B.rootTorus v)) := by
   funext v; exact (A.retract_torus _).symm
 rw [he]
 exact A.retract_continuous.comp ht
private lemma normPower_cont_units
    (L : Type*) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [MeasurableSpace L] [BorelSpace L] (ρ : ℂ) : Continuous (fun x : Lˣ => normPower L x ρ) := by
  have hab (x : Lˣ) : KPCubicHaar.abs L (x:L) = localAbs L x := by
    simp [KPCubicHaar.abs, localAbs, Units.ne_zero, Real.rpow_intCast]; rfl
  have he := KPJointRegulator.mellin_continuous L (fun _ => 1) (IsLocallyConstant.const (1:ℂ)) ρ
  change Continuous (fun x : Lˣ => (1:ℂ)*Complex.exp (ρ*(Real.log (KPCubicHaar.abs L (x:L)) : ℂ))) at he
  simpa only [one_mul,normPower,hab] using he

private lemma raw_kernel_continuous
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d)=d) (d:S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (s ρ:ℂ)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    Continuous (fun z : (LocalField F q)ˣ×(LocalField F q)ˣ =>
      doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ s ρ h z.1 z.2 1 1) := by
  let V := (centerCoordinates S.heisenberg rep hrep).symm (Pi.single d (1:ℂ))
  have hr := root_cont F ζ hζ q S.heisenberg S.borel P (S.openCell P)
  have hc := (center_lc S.heisenberg V).continuous.comp
    (((continuous_const : Continuous (fun _ : (LocalField F q)ˣ×(LocalField F q)ˣ => h)).mul (S.borel.weyl.continuous.comp (hr.comp continuous_snd))).mul
      (hr.comp continuous_fst))
  have hn1 : Continuous (fun z : (LocalField F q)ˣ×(LocalField F q)ˣ => normPower (LocalField F q) (z.2^2) (-s)) := (normPower_cont_units (LocalField F q) (-s)).comp (continuous_snd.pow 2)
  have hn2 : Continuous (fun z : (LocalField F q)ˣ×(LocalField F q)ˣ => normPower (LocalField F q) (z.1^2) s) := (normPower_cont_units (LocalField F q) s).comp (continuous_fst.pow 2)
  have hn3 : Continuous (fun z : (LocalField F q)ˣ×(LocalField F q)ˣ => normPower (LocalField F q) z.2 ρ) := (normPower_cont_units (LocalField F q) ρ).comp continuous_snd
  have hf : Continuous (fun z : (LocalField F q)ˣ×(LocalField F q)ˣ => φ ((z.1:LocalField F q)+(z.2:LocalField F q))) := hφ.continuous.comp ((Units.continuous_val.comp continuous_fst).add
    (Units.continuous_val.comp continuous_snd))
  have he : (fun z : (LocalField F q)ˣ×(LocalField F q)ˣ =>
      doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ s ρ h z.1 z.2 1 1) =
    (fun z => normPower (LocalField F q) (z.2^2) (-s)*normPower (LocalField F q) (z.1^2) s*
      (φ ((z.1:LocalField F q)+(z.2:LocalField F q)) * V.val
        (h*S.borel.weyl ((S.openCell P).rootTorus z.2)*(S.openCell P).rootTorus z.1))*
        normPower (LocalField F q) z.2 ρ) := by
    funext z
    simp only [doubleKernel,reverseIncrement,sourceTranslation,one_pow,mul_one,
      kappa_eq_one F ζ hζ q,map_one,Units.val_one,one_mul]
    simp only [map_smul]
    rfl
  rw [he]
  exact (hn1.mul hn2).mul (hf.mul hc) |>.mul hn3

private theorem actual_iterated_kernel
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    [DecidableEq S.D]
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r t : ℂˣ)
    (ht : (t : ℂ) = (residueCardinality (LocalField F q) : ℂ)⁻¹ * (r : ℂ)^6)
    (ρ : ℂ) (hcone : KPJointRegulator.cone (LocalField F q) t ρ)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    KPRankOneReverseRegulatorShells.H F ζ hζ q S.heisenberg S.borel P
      S.iwasawa dx J (S.openCell P) rep hrep d φ hφ hcφ r ρ h =
      ∫ η : (LocalField F q)ˣ, (∫ ξ : (LocalField F q)ˣ,
        doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d φ (KPRankOneReverseRegulatorShells.additiveParameter F q r) ρ
            h ξ η 1 1 ∂KPCubicHaar.multiplicativeHaar (LocalField F q) dx)
              ∂KPCubicHaar.multiplicativeHaar (LocalField F q) dx := by
  have hz := KPRankOneLiftedDiagonal.joint_cone_forward_convergence F q r t
    (by exact ht) ρ hcone
  have he (e : rootsOfUnity 3 F) : (S.openCell P).centralTorus e = (S.central e : _) := by
    apply Subtype.val_injective
    rw [← S.torus_full, (S.openCell P).central_eq, S.central_actual]
  have hm : ∀ e, (S.openCell P).centralTorus e ∈ S.heisenberg.C := by
    intro e; rw [he]; exact (S.central e).property
  have hc : ∀ e, S.heisenberg.ω ⟨(S.openCell P).centralTorus e, hm e⟩ =
      (S.openCell P).eta e := by
    intro e
    rw [S.openCell_ordinary]
    convert S.central_character e using 1
    congr 1
    apply Subtype.val_injective
    exact he e
  rw [KPRankOneLiftedDiagonal.center_iterated_kernel F ζ hζ q S.heisenberg
    S.borel P S.iwasawa dx J (S.openCell P) hm hc rep hrep d φ hφ hcφ r ρ hz h]
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [doubleKernel, reverseIncrement, sourceTranslation, one_pow, mul_one,
    Units.val_one]
  rw [add_comm]

open scoped Classical in

theorem actual_full_H_joint_factorization
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    [DecidableEq S.D]
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r t : ℂˣ)
    (ht : (t : ℂ) = (residueCardinality (LocalField F q) : ℂ)⁻¹ * (r : ℂ) ^ 6)
    (ρ : ℂ) (hcone : KPJointRegulator.cone (LocalField F q) t ρ)
    (cRep : KPLocalTorus.CubeClasses (LocalField F q)ˣ → (LocalField F q)ˣ)
    (hcRep : ∀ k, QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ)
      (cRep k) = k) :
    letI : Fintype S.D := Fintype.ofFinite S.D
    letI : Fintype (KPLocalTorus.CubeClasses (LocalField F q)ˣ) :=
      Fintype.ofEquiv S.D S.cubeClassEquiv.toEquiv
    let μ := KPCubicHaar.multiplicativeHaar (LocalField F q) dx
    let s := KPRankOneReverseRegulatorShells.additiveParameter F q r
    let M : (LocalField F q)ˣ → ℂ := fun c =>
      ∫ x : (LocalField F q)ˣ,
        φ (x : LocalField F q) *
          (KPExceptionalRaw.ordinaryIota F ζ hζ
            (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
          normPower (LocalField F q) x ρ ∂μ
    let β : (LocalField F q)ˣ → ℂ := fun c =>
      ∫ y : (LocalField F q)ˣ,
        if (y : LocalField F q) ^ 3 + (c : LocalField F q) = 0 then 0 else
          KPCubicExpansion.omega (LocalField F q) t y *
            Complex.exp (-ρ * (Real.log (KPCubicHaar.abs (LocalField F q)
              ((y : LocalField F q) ^ 3 + (c : LocalField F q))) : ℂ)) ∂μ
    let U : (LocalField F q)ˣ → KPExceptionalRaw.actualTorus F ζ hζ q → ℂ :=
      fun c h => doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d (fun _ => 1) s 0 h 1 c 1 1
    (∀ (a b : (LocalField F q)ˣ) (h : KPExceptionalRaw.actualTorus F ζ hζ q),
      Integrable (fun uv : (LocalField F q)ˣ × (LocalField F q)ˣ =>
        doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d φ s ρ h a b uv.1 uv.2) (μ.prod μ)) ∧
    ∀ h : KPExceptionalRaw.actualTorus F ζ hζ q,
      KPRankOneReverseRegulatorShells.H F ζ hζ q S.heisenberg S.borel P
          S.iwasawa dx J (S.openCell P) rep hrep d φ hφ hcφ r ρ h =
        (KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) / 3 : ℝ) *
          ∑ k : KPLocalTorus.CubeClasses (LocalField F q)ˣ,
            U (cRep k) h * normPower (LocalField F q) (cRep k) ρ *
              M (cRep k) * β (cRep k) := by
  classical
  letI : Fintype S.D := Fintype.ofFinite S.D
  letI : Fintype (KPLocalTorus.CubeClasses (LocalField F q)ˣ) :=
    Fintype.ofEquiv S.D S.cubeClassEquiv.toEquiv
  let _ : BorelSpace (LocalField F q)ˣ := units_borel_generic (LocalField F q)
  let _ := KPJointRegulator.MellinBetaIntegrability.localField_secondCountable (LocalField F q)
  let _ : SecondCountableTopology (LocalField F q)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ := KPCubicHaar.multiplicativeHaar (LocalField F q) dx
  let _ : SigmaFinite μ := KPJointRegulator.MellinBetaIntegrability.multiplicativeHaar_sigmaFinite (LocalField F q) dx
  let s := KPRankOneReverseRegulatorShells.additiveParameter F q r
  let g := fun (c : (LocalField F q)ˣ) (xy : (LocalField F q)ˣ×(LocalField F q)ˣ) =>
    φ ((xy.1:LocalField F q)*((xy.2:LocalField F q)^3+(c:LocalField F q))) *
      (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c xy.1) : ℂ) *
      KPCubicExpansion.omega (LocalField F q) t xy.2 * normPower (LocalField F q) xy.1 ρ
  let U := fun (c : (LocalField F q)ˣ) (h : KPExceptionalRaw.actualTorus F ζ hζ q) =>
    doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P) rep hrep d
      (fun _ => 1) s 0 h 1 c 1 1
  have hr : (r:ℂ) = KPRankOneRootParameter.r (LocalField F q) s :=
    (KPRankOneReverseRegulatorShells.root_parameter_additiveParameter F q r).symm
  have hg (c : (LocalField F q)ˣ) : Integrable (g c) (μ.prod μ) :=
    (actual_shifted_product F ζ hζ q dx c φ hφ hcφ t ρ hcone).1
  have hp := hζ.pow (by norm_num : 0 < 12) (by norm_num : 12 = 4*3)
  have hpK : IsPrimitiveRoot (algebraMap F (LocalField F q) (ζ^4)) 3 :=
    hp.map_of_injective (algebraMap F (LocalField F q)).injective
  have hv : ValuativeRel.valuation (LocalField F q) (algebraMap F (LocalField F q) (ζ^4)) = 1 := by
    apply (pow_eq_one_iff_of_nonneg zero_le (by norm_num : (3:ℕ)≠0)).mp
    rw [← map_pow, hpK.pow_eq_one, map_one]
  let κ : KPCubicUnitIndices.Integers (LocalField F q) := ⟨_, hv.le⟩
  have hκ : IsPrimitiveRoot κ 3 := hpK.of_map_of_injective
    (f := (KPCubicUnitIndices.Integers (LocalField F q)).subtype) Subtype.val_injective
  have hpoint (a b u v : (LocalField F q)ˣ) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
      doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ s ρ h a b u v =
      normPower (LocalField F q) (b/a) ρ * U (b/a) h * g (b/a) (a*v^3,u/v) := by
    rw [actual_doubleKernel_all_ratios F ζ hζ q S P rep hrep d φ s ρ r t hr ht]
    dsimp [g,U]
    ring
  constructor
  · intro a b h
    have hi := cube_shear_integrable (LocalField F q) dx κ hκ (g (b/a)) (hg _) a
    have hh := hi.const_mul (normPower (LocalField F q) (b/a) ρ * U (b/a) h)
    apply hh.congr
    filter_upwards [] with uv
    exact (hpoint a b uv.1 uv.2 h).symm
  · intro h
    let f : (LocalField F q)ˣ×(LocalField F q)ˣ → ℂ := fun z =>
      doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ s ρ h z.1 z.2 1 1
    let T := fun (c : (LocalField F q)ˣ) (xy : (LocalField F q)ˣ×(LocalField F q)ˣ) =>
      (xy.1*xy.2^3,c*xy.1)
    have hT (c : (LocalField F q)ˣ) : Measurable (T c) := by
      dsimp [T]; fun_prop
    have hcomp (c : (LocalField F q)ˣ) :
        (fun xy => f (T c xy)) = (fun xy => normPower (LocalField F q) c ρ * U c h * g c xy) := by
      funext xy
      have he : f (T c xy) = doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ s ρ h xy.1 (c*xy.1) xy.2 1 := by
        dsimp [f,T,doubleKernel,reverseIncrement,sourceTranslation]
        simp
      rw [he,hpoint]
      simp [U,g,div_eq_mul_inv,mul_assoc]
    have hc : Continuous f := raw_kernel_continuous F ζ hζ q S P rep hrep d φ hφ s ρ h
    have hmapint (c : (LocalField F q)ˣ) : Integrable f (Measure.map (T c) (μ.prod μ)) := by
      apply (integrable_map_measure hc.aestronglyMeasurable (hT c).aemeasurable).mpr
      change Integrable (fun xy => f (T c xy)) _
      rw [hcomp]
      exact (hg c).const_mul _
    have hpush := actual_cube_ratio_pushforward F q dx κ hκ cRep hcRep
    change μ.prod μ = ENNReal.ofReal (KPCubicHaar.abs (LocalField F q) 3/3) •
      ∑ k, Measure.map (T (cRep k)) (μ.prod μ) at hpush
    have hf : Integrable f (μ.prod μ) := by
      rw [hpush]
      apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
      exact (integrable_finsetSum_measure).mpr (fun k _ => hmapint (cRep k))
    rw [actual_iterated_kernel F ζ hζ q S P dx J rep hrep d φ hφ hcφ r t ht ρ hcone h]
    change (∫ η : (LocalField F q)ˣ, (∫ ξ : (LocalField F q)ˣ, f (ξ,η) ∂μ) ∂μ) = _
    rw [← integral_prod_symm f hf, hpush, integral_smul_measure, integral_finsetSum_measure]
    · have hδ : 0 < KPCubicHaar.abs (LocalField F q) (3:LocalField F q) := KPCubicHaar.abs_pos _ (by norm_num)
      rw [ENNReal.toReal_ofReal (by positivity)]
      simp only [Complex.real_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_map (hT _).aemeasurable hc.aestronglyMeasurable, hcomp,
        integral_const_mul, integral_prod_symm _ (hg _)]
      rw [(actual_shifted_product F ζ hζ q dx (cRep k) φ hφ hcφ t ρ hcone).2]
      dsimp [U]
      ring
    · intro k hk
      exact hmapint (cRep k)

end
end DedekindZetaZeroFree.KPActualFullKernelArithmetic
