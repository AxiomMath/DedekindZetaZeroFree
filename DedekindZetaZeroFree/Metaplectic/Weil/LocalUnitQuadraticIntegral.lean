module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.ResidueTracePhases
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactSubgroupCharacterIntegral

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.ExteriorGauss
noncomputable section
variable {F : Type} [Field F] [NumberField F]

def rawCutoff (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F))
    (a : (v.adicCompletion F)ˣ) (n : ℕ) : ℂ :=
  (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) *
    ∫ x in {x : v.adicCompletion F | ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n},
      (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * x ^ 2) : ℂ) ∂μ

private theorem two_norm (v : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6) :
    ‖(2 : v.adicCompletion F)‖ = 1 := by
  have hn : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    have hz : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := by
      convert (Ideal.Quotient.eq_zero_iff_mem.mpr h) using 1
      exact (map_ofNat (Ideal.Quotient.mk v.asIdeal) 2).symm
    have hd : (ResidueTrace.rationalPrimeBelow v).val ∣ 2 := by
      exact (CharP.cast_eq_zero_iff (𝓞 F ⧸ v.asIdeal)
        (ringChar (𝓞 F ⧸ v.asIdeal)) 2).mp hz
    exact hgood (hd.trans (by decide))
  have h := (FinitePlace.norm_eq_one_iff_notMem F v (2 : 𝓞 F)).mpr hn
  have he : FinitePlace.embedding v (algebraMap (𝓞 F) F 2) = (2 : v.adicCompletion F) := by
    rw [map_ofNat, map_ofNat]
  rwa [he] at h

theorem unit_cutoff_eventually
    (v : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (u : (v.adicCompletionIntegers F)ˣ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      rawCutoff v μ (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) n = 1 := by
  let O := (v.adicCompletionIntegers F).toAddSubgroup
  let a : v.adicCompletion F := u
  let ψ := ResidueTrace.localTraceCharacter v
  have haO : a ∈ v.adicCompletionIntegers F := u.val.property
  have hainv : (a⁻¹) ∈ v.adicCompletionIntegers F := by
    have hi : ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).val = a⁻¹ := by
      change ↑↑(u⁻¹) = (↑↑u : v.adicCompletion F)⁻¹
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) u.inv_val
    rw [← hi]
    exact (u⁻¹).val.property
  have ha : ‖a‖ = 1 := by
    have h1 := norm_le_one_of_mem_adicCompletionIntegers v haO
    have h2 := norm_le_one_of_mem_adicCompletionIntegers v hainv
    have hne : a ≠ 0 := by exact Units.ne_zero (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)
    rw [norm_inv] at h2
    exact le_antisymm h1 ((inv_le_one₀ (norm_pos_iff.mpr hne)).mp h2)
  have htwo := two_norm v hgood
  have hO : (O : Set (v.adicCompletion F)) = Metric.closedBall 0 1 := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact ⟨norm_le_one_of_mem_adicCompletionIntegers v,
      mem_adicCompletionIntegers_of_norm_le_one v⟩
  have hμO : μ (O : Set (v.adicCompletion F)) = 1 := hμ
  have hOc : IsCompact (O : Set (v.adicCompletion F)) := hO ▸ isCompact_closedBall 0 1
  have hq (x : v.adicCompletion F) (hx : x ∈ O) : ψ (a * x ^ 2) = 1 := by
    exact (hzero a).mpr haO ⟨x ^ 2, (v.adicCompletionIntegers F).pow_mem hx 2⟩
  apply Filter.Eventually.of_forall
  intro n
  let R : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ n
  have hR : 1 ≤ R := one_le_pow₀ (by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le)
  let U : AddSubgroup (v.adicCompletion F) :=
    { carrier := {x | ‖x‖ ≤ R}
      zero_mem' := by simpa using (zero_le_one.trans hR)
      add_mem' := fun hx hy => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      neg_mem' := by intro x hx; simpa using hx }
  have hUc : IsCompact (U : Set (v.adicCompletion F)) := by
    change IsCompact {x : v.adicCompletion F | ‖x‖ ≤ R}
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : v.adicCompletion F) R
  have hOU : O ≤ U := fun x hx => (norm_le_one_of_mem_adicCompletionIntegers v hx).trans hR
  let f : v.adicCompletion F → ℂ := fun x => (ψ (a * x ^ 2) : ℂ)
  have hf : Continuous f := continuous_subtype_val.comp
    ((ResidueTrace.continuous_localTraceCharacter v).comp (by fun_prop))
  have hshift (h : v.adicCompletion F) (hh : h ∈ O) :
      (∫ x in (U : Set (v.adicCompletion F)), f (x + h) ∂μ) =
        ∫ x in (U : Set (v.adicCompletion F)), f x ∂μ := by
    have hm (x : v.adicCompletion F) : x + h ∈ U ↔ x ∈ U :=
      ⟨fun hx => by simpa using U.sub_mem hx (hOU hh), fun hx => U.add_mem hx (hOU hh)⟩
    have he : (fun x => (U : Set (v.adicCompletion F)).indicator f (x + h)) =
        (U : Set (v.adicCompletion F)).indicator (fun x => f (x + h)) := by
      funext x
      by_cases hx : x ∈ U <;> simp [Set.indicator, hx, hm x]
    have hi := integral_add_right_eq_self (μ := μ) ((U : Set (v.adicCompletion F)).indicator f) h
    rw [he, integral_indicator hUc.measurableSet, integral_indicator hUc.measurableSet] at hi
    exact hi
  have hphase (x h : v.adicCompletion F) (hh : h ∈ O) :
      f (x + h) = f x * (ψ ((2 * a * x) * h) : ℂ) := by
    have he : a * (x + h) ^ 2 = a * x ^ 2 + a * h ^ 2 + (2 * a * x) * h := by ring
    simp [f, he, AddChar.map_add_eq_mul, hq h hh]
  have horth (x : v.adicCompletion F) :
      (∫ h in (O : Set (v.adicCompletion F)), f (x + h) ∂μ) =
        (O : Set (v.adicCompletion F)).indicator f x := by
    let χ : AddChar (v.adicCompletion F) Circle := ψ.compAddMonoidHom
      (AddMonoidHom.mulLeft (2 * a * x))
    have hc : Continuous χ := (ResidueTrace.continuous_localTraceCharacter v).comp
      (continuous_const.mul continuous_id)
    have ht : (∀ h ∈ O, χ h = 1) ↔ x ∈ O := by
      have ht' : (∀ h ∈ O, χ h = 1) ↔ 2 * a * x ∈ O := by
        constructor
        · intro h
          exact (hzero (2 * a * x)).mp (fun o => h o o.property)
        · intro h t ht
          exact (hzero (2 * a * x)).mpr h ⟨t, ht⟩
      rw [ht']
      change 2 * a * x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F
      constructor <;> intro hx
      · apply mem_adicCompletionIntegers_of_norm_le_one v
        have hn := norm_le_one_of_mem_adicCompletionIntegers v hx
        simpa [norm_mul, htwo, ha] using hn
      · apply mem_adicCompletionIntegers_of_norm_le_one v
        simpa [norm_mul, htwo, ha] using norm_le_one_of_mem_adicCompletionIntegers v hx
    rw [setIntegral_congr_fun hOc.measurableSet (fun h hh => hphase x h hh), integral_const_mul]
    change f x * (∫ h in (O : Set (v.adicCompletion F)), (χ h : ℂ) ∂μ) = _
    rw [(compactSubgroup_character_integral μ O hOc χ hc).2]
    by_cases hx : x ∈ O
    · rw [if_pos (ht.mpr hx), hμO, Set.indicator_of_mem hx]
      simp
    · rw [if_neg (mt ht.mp hx), Set.indicator_of_notMem hx, mul_zero]
  have hp : Integrable (fun p : v.adicCompletion F × v.adicCompletion F => f (p.1 + p.2))
      ((μ.restrict U).prod (μ.restrict O)) := by
    rw [Measure.prod_restrict]
    exact (hf.comp (continuous_fst.add continuous_snd)).continuousOn.integrableOn_compact (hUc.prod hOc)
  have havg := integral_integral_swap (f := fun x h => f (x + h)) hp
  have hi : (∫ x in (U : Set (v.adicCompletion F)), f x ∂μ) = 1 := by
    change (∫ x in (U : Set (v.adicCompletion F)), (∫ h in (O : Set (v.adicCompletion F)), f (x + h) ∂μ) ∂μ) =
      (∫ h in (O : Set (v.adicCompletion F)), (∫ x in (U : Set (v.adicCompletion F)), f (x + h) ∂μ) ∂μ) at havg
    simp_rw [horth] at havg
    rw [setIntegral_congr_fun hOc.measurableSet hshift, setIntegral_const] at havg
    rw [integral_indicator hOc.measurableSet, Measure.restrict_restrict hOc.measurableSet,
      Set.inter_eq_left.mpr hOU] at havg
    have hfi : (∫ x in (O : Set (v.adicCompletion F)), f x ∂μ) = 1 := by
      calc
        _ = ∫ _ in (O : Set (v.adicCompletion F)), (1 : ℂ) ∂μ :=
          setIntegral_congr_fun hOc.measurableSet (fun x hx => by simp [f, hq x hx])
        _ = 1 := by simp [setIntegral_const, Measure.real, hμO]
    simpa [Measure.real, hμO, hfi] using havg.symm
  change (Real.sqrt ‖2 * a‖ : ℂ) * (∫ x in (U : Set (v.adicCompletion F)), f x ∂μ) = 1
  simp [norm_mul, htwo, ha, hi]

end
end DedekindZetaZeroFree.ExteriorGauss
