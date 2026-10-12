module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.JointMellinBetaIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.KPActualFullKernelArithmetic

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open KPCubicExpansion KPCubicHaarTransport KPCubicUnitIndices ValuativeRel Filter Topology

section Generic
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

private theorem shifted_cube_proper : IsProperMap (fun x : Kˣ => x^3) := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
 letI := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
 haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
 have hp : IsProperMap (fun x : K => x^3) := by
   convert (Polynomial.X ^ 3 : Polynomial K).isProperMap_eval (by simp) using 1
   funext x
   simp
 have hprod : IsProperMap (fun p : K × Kᵐᵒᵖ => (p.1^3, p.2^3)) := hp.prodMap (by
   simpa only [MulOpposite.op_pow] using
     (MulOpposite.opHomeomorph.isProperMap.comp hp).comp MulOpposite.opHomeomorph.symm.isProperMap)
 have hcomm : (fun p : K × Kᵐᵒᵖ => (p.1^3, p.2^3)) ∘ Units.embedProduct K =
     Units.embedProduct K ∘ (fun x : Kˣ => x^3) := by funext x; ext <;> simp [Units.embedProduct]
 apply isProperMap_of_comp_of_inj (by fun_prop) Units.continuous_embedProduct
   (by rw [← hcomm]; exact hprod.comp Units.isClosedEmbedding_embedProduct.isProperMap)
 exact Units.embedProduct_injective K

private theorem integrable_comp_cube
    (dx : Measure K) [dx.IsAddHaarMeasure] (f : Kˣ → ℂ)
    (hf : Integrable f (KPCubicHaar.multiplicativeHaar K dx)) :
    Integrable (fun y : Kˣ => f (y^3)) (KPCubicHaar.multiplicativeHaar K dx) := by
  classical
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [@BorelSpace.measurable_eq K _ _ _,
      Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  letI := KPJointRegulator.MellinBetaIntegrability.localField_secondCountable K
  letI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ := KPCubicHaar.multiplicativeHaar K dx
  have hcompact : IsCompact (Integers K : Set K) :=
    IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have hopen : IsOpen (Integers K : Set K) := Valued.isOpen_integer K
  have hpos : 0 < dx (Integers K : Set K) := hopen.measure_pos (μ := dx) ⟨0, by simp⟩
  letI : μ.IsHaarMeasure := (haar_structure_and_unit_mass K dx _
    (ENNReal.toReal_pos hpos.ne' hcompact.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hcompact.measure_lt_top.ne).symm).1
  let p := powMonoidHom (α := Kˣ) 3
  let H := p.range
  haveI : H.FiniteIndex := by
    haveI : Finite (Kˣ ⧸ H) := ClassFieldTheory.powerClassGroup_finite K ⟨3, by decide⟩ (by norm_num)
    exact Subgroup.finiteIndex_of_finite_quotient
  have hp : Continuous p := continuous_id.pow 3
  have hproper : IsProperMap p := shifted_cube_proper K
  have hHc : IsClosed (H : Set Kˣ) := hproper.isClosed_range
  have hHo : IsOpen (H : Set Kˣ) := H.isOpen_of_isClosed_of_finiteIndex hHc
  letI : LocallyCompactSpace H := hHo.locallyCompactSpace
  letI : SecondCountableTopology H := hHo.isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let ν := μ.comap H.subtype
  have hi : IsOpenEmbedding H.subtype := hHo.isOpenEmbedding_subtypeVal
  letI : ν.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μ hi
  let g := p.rangeRestrict
  have hg : Continuous g := hp.subtype_mk _
  have hgp : IsProperMap g := isProperMap_of_comp_of_inj hg continuous_subtype_val hproper Subtype.val_injective
  let ρ := μ.map g
  letI : ρ.IsHaarMeasure := Measure.isHaarMeasure_map μ g hg p.rangeRestrict_surjective
    (isProperMap_iff_tendsto_cocompact.mp hgp).2
  let c := Measure.haarScalarFactor ρ ν
  have heq : ρ = c • ν := Measure.isMulLeftInvariant_eq_smul ρ ν
  have hmap := congrArg (Measure.map H.subtype) heq
  rw [Measure.map_map hi.continuous.measurable hg.measurable,
    Measure.map_smul _ hi.continuous.measurable.aemeasurable,
    hi.measurableEmbedding.map_comap] at hmap
  have hr : Set.range H.subtype = (H : Set Kˣ) := by ext x; simp
  rw [hr] at hmap
  have hfi : Integrable f (μ.map p) := by
    rw [show μ.map p = c • μ.restrict (H : Set Kˣ) from hmap]
    exact hf.integrableOn.smul_measure_nnreal
  exact hfi.comp_measurable hp.measurable

open scoped Classical in
private theorem shifted_linear_integrable
    (dx : Measure K) [dx.IsAddHaarMeasure] (c : Kˣ) (b : ℂˣ)
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hbs : (CubicUnitCharacters.residueCard K : ℝ).rpow (-s.re) < ‖(b : ℂ)‖)
    (hb1 : ‖(b : ℂ)‖ < 1) :
    Integrable (fun v : Kˣ => if (v : K) + (c : K) = 0 then 0 else
      omega K b v * Complex.exp (-s *
        (Real.log (KPCubicHaar.abs K ((v : K) + (c : K))) : ℂ)))
      (KPCubicHaar.multiplicativeHaar K dx) := by
  classical
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [@BorelSpace.measurable_eq K _ _ _,
      Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  let χ : Kˣ →ₜ* ℂˣ :=
    { toFun := fun v => b ^ valuationExponent K v
      map_one' := by simp [valuationExponent]
      map_mul' := by intro x y; rw [valuationExponent_mul, zpow_add]
      continuous_toFun := by
        apply continuous_iff_continuousAt.mpr
        intro x
        have hv := (valuation K).locally_const
          ((Valuation.ne_zero_iff (valuation K)).mpr x.ne_zero)
        apply Filter.EventuallyEq.continuousAt (y := b ^ valuationExponent K x)
        filter_upwards [Units.continuous_val.continuousAt.eventually hv] with y hy
        simp only [valuationExponent, hy] }
  obtain ⟨π, hπ⟩ := KPJointRegulator.MellinBetaIntegrability.exists_uniformizer_units K
  have hχ : ∀ u : ((valuation K).integer)ˣ,
      χ (Units.map ((valuation K).integer).subtype.toMonoidHom u) = ((1 : CubicUnitCharacters.Character K) u : ℂˣ) := by
    intro u
    change b ^ valuationExponent K (Units.map (valuation K).integer.subtype.toMonoidHom u) = 1
    rw [valuationExponent_unit, zpow_zero]
  have hb : χ π = b := by
    change b ^ valuationExponent K π = b
    rw [valuationExponent_uniformizer π hπ, zpow_one]
  have hi := integrable_character_beta K dx π hπ 1 χ hχ b hb s hs0 hs1 hbs hb1
  let μ := KPCubicHaar.multiplicativeHaar K dx
  have hcpt : IsCompact (Integers K : Set K) := IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have hop : IsOpen (Integers K : Set K) := Valued.isOpen_integer K
  have hpos : 0 < dx (Integers K : Set K) := hop.measure_pos (μ := dx) ⟨0, by simp⟩
  letI : μ.IsHaarMeasure := (haar_structure_and_unit_mass K dx _
    (ENNReal.toReal_pos hpos.ne' hcpt.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hcpt.measure_lt_top.ne).symm).1
  let a : Kˣ := -c
  let z : ℂ := omega K b a * Complex.exp (-s * (Real.log (KPCubicHaar.abs K (c : K)) : ℂ))
  have hj := (measurePreserving_mul_left μ a⁻¹).integrable_comp_of_integrable (hi.const_mul z)
  apply hj.congr
  filter_upwards [] with v
  let u : Kˣ := a⁻¹ * v
  have hv : v = a * u := by simp [u]
  have hr : (v : K) + (c : K) = (c : K) * (1 - (u : K)) := by
    rw [hv]
    simp only [Units.val_mul, a, Units.val_neg]
    ring
  have hu : (v : K) + (c : K) = 0 ↔ u = 1 := by
    rw [hr, mul_eq_zero, or_iff_right c.ne_zero, sub_eq_zero]
    exact ⟨fun h => Units.ext h.symm, fun h => by simp [h]⟩
  by_cases h : u = 1
  · change z * ((χ u : ℂ) * betaFunction K s u) = _
    rw [ite_eq_left (hu.mpr h)]
    simp [betaFunction, h]
  · have hn : 1 - (u : K) ≠ 0 := by
      intro he
      exact h (Units.ext (sub_eq_zero.mp he).symm)
    have hp := KPCubicHaar.abs_pos K hn
    have hcp := KPCubicHaar.abs_pos K c.ne_zero
    have he : (KPCubicHaar.abs K (1 - (u : K)) : ℂ) ^ (-s) =
        Complex.exp (-s * (Real.log (KPCubicHaar.abs K (1 - (u : K))) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_log hp.le]
      congr 1
      ring
    change z * ((χ u : ℂ) * betaFunction K s u) = _
    rw [ite_eq_right (fun hv0 => h (hu.mp hv0)), hr, KPCubicHaar.abs_mul,
      Real.log_mul hcp.ne' hp.ne', Complex.ofReal_add, mul_add, Complex.exp_add,
      betaFunction, ite_eq_right h, he, hv, omega_mul]
    change (omega K b a * Complex.exp _) * (omega K b u * Complex.exp _) = _
    ring

end Generic

variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
local instance shiftedBetaValuativeRel : ValuativeRel (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance shiftedBetaLocalField : IsNonarchimedeanLocalField (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
local instance shiftedBetaMeasurable : MeasurableSpace (q.adicCompletion F) :=
  borel (q.adicCompletion F)
local instance shiftedBetaBorel : BorelSpace (q.adicCompletion F) := ⟨rfl⟩

open scoped Classical in

theorem actual_shifted_beta_integrable
    (dx : Measure (q.adicCompletion F)) [dx.IsAddHaarMeasure]
    (c : (q.adicCompletion F)ˣ) (t : ℂˣ)
    (ρ : ℂ) (hcone : KPJointRegulator.cone (q.adicCompletion F) t ρ) :
    Integrable (fun y : (q.adicCompletion F)ˣ =>
      if (y : q.adicCompletion F) ^ 3 + (c : q.adicCompletion F) = 0 then 0 else
        KPCubicExpansion.omega (q.adicCompletion F) t y *
          Complex.exp (-ρ * (Real.log (KPCubicHaar.abs (q.adicCompletion F)
            ((y : q.adicCompletion F) ^ 3 + (c : q.adicCompletion F))) : ℂ)))
      (KPCubicHaar.multiplicativeHaar (q.adicCompletion F) dx) := by
  classical
  let K := q.adicCompletion F
  obtain ⟨b₀, hb₀⟩ := IsAlgClosed.exists_pow_nat_eq (t : ℂ) (by decide : 0 < 3)
  have hb0 : b₀ ≠ 0 := by
    intro h
    apply t.ne_zero
    rw [← hb₀, h]
    simp
  let b : ℂˣ := Units.mk0 b₀ hb0
  have hb : b ^ 3 = t := Units.ext hb₀
  have hnorm : ‖(b : ℂ)‖ ^ 3 = ‖(t : ℂ)‖ := by
    rw [← norm_pow, ← hb₀]
    rfl
  have hcone' := hcone
  change 0 < ρ.re ∧ ρ.re < 1 ∧
    (residueCard K : ℝ).rpow (-3 * ρ.re) < ‖(t : ℂ)‖ ∧
    ‖(t : ℂ)‖ < 1 at hcone'
  have hb1 : ‖(b : ℂ)‖ < 1 :=
    lt_of_pow_lt_pow_left₀ 3 (by positivity) (by simpa only [hnorm, one_pow] using hcone'.2.2.2)
  have hqpos : (0 : ℝ) < residueCard K := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (two_le_residueCard K)
  have hbs : (CubicUnitCharacters.residueCard K : ℝ).rpow (-ρ.re) < ‖(b : ℂ)‖ := by
    have hx : ((residueCard K : ℝ).rpow (-ρ.re)) ^ (3 : ℕ) < ‖(b : ℂ)‖ ^ (3 : ℕ) := by
      change ((residueCard K : ℝ) ^ (-ρ.re)) ^ (3 : ℕ) < ‖(b : ℂ)‖ ^ (3 : ℕ)
      rw [← Real.rpow_mul_natCast hqpos.le (-ρ.re) 3, hnorm]
      convert hcone'.2.2.1 using 1
      congr 1
      ring
    change (residueCard K : ℝ).rpow (-ρ.re) < ‖(b : ℂ)‖
    exact lt_of_pow_lt_pow_left₀ 3 (norm_nonneg _) hx
  have hi := shifted_linear_integrable K dx c b ρ hcone'.1 hcone'.2.1 hbs hb1
  have hc := integrable_comp_cube K dx _ hi
  apply hc.congr
  filter_upwards [] with y
  rw [omega_cube K t b hb]
  rfl

end
end DedekindZetaZeroFree.KPActualFullKernelArithmetic
