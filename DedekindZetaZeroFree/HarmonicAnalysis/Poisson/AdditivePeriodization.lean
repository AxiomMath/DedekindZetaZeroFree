module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.Adeles.Characters.CompactAbelianAndAdelicUniqueness
public import DedekindZetaZeroFree.Adeles.Quotients.AdditiveCompactness

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPChamberAdditivePeriodization

open MeasureTheory NumberField
open scoped ENNReal NNReal

variable (F : Type) [Field F] [NumberField F]

 abbrev A := NumberField.AdeleRing (𝓞 F) F
 abbrev Q := A F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

def CompatibleHaar (dx : Measure (A F)) (dq : Measure (Q F)) : Prop :=
  ∃ domain : Set (A F), MeasurableSet domain ∧
    IsAddFundamentalDomain
      (NumberField.AdeleRing.principalSubgroup (𝓞 F) F) domain dx ∧
    dx domain = 1 ∧ dq = (dx.restrict domain).map
      (QuotientAddGroup.mk' (NumberField.AdeleRing.principalSubgroup (𝓞 F) F))

def nonnegativePeriod (h : A F → ℝ≥0∞) (q : Q F) : ℝ≥0∞ :=
  ∑' t : F, h (algebraMap F (A F) t + Quotient.out q)

def normPeriod (h : A F → ℂ) (q : Q F) : ℝ≥0∞ :=
  nonnegativePeriod F (fun a => ENNReal.ofReal ‖h a‖) q

def complexPeriod (h : A F → ℂ) (q : Q F) : ℂ :=
  ∑' t : F, h (algebraMap F (A F) t + Quotient.out q)

theorem nonnegativePeriod_eq_sum (h : A F → ℝ≥0∞) (x : A F) :
    nonnegativePeriod F h (QuotientAddGroup.mk x) =
      ∑' t : F, h (algebraMap F (A F) t + x) := by
  classical
  have hout : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk x : Q F)) : Q F) =
      QuotientAddGroup.mk x := Quotient.out_eq _
  obtain ⟨s, hs⟩ := (QuotientAddGroup.eq_iff_sub_mem.mp hout)
  have hx : Quotient.out (QuotientAddGroup.mk x : Q F) = algebraMap F (A F) s + x := by
    rw [hs]
    abel
  unfold nonnegativePeriod
  rw [hx]
  convert (Equiv.addRight s).tsum_eq (fun t : F => h (algebraMap F (A F) t + x)) using 1
  simp only [Equiv.coe_addRight, map_add, add_assoc]

theorem complexPeriod_eq_sum (h : A F → ℂ) (x : A F) :
    complexPeriod F h (QuotientAddGroup.mk x) =
      ∑' t : F, h (algebraMap F (A F) t + x) := by
  classical
  have hout : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk x : Q F)) : Q F) =
      QuotientAddGroup.mk x := Quotient.out_eq _
  obtain ⟨s, hs⟩ := (QuotientAddGroup.eq_iff_sub_mem.mp hout)
  have hx : Quotient.out (QuotientAddGroup.mk x : Q F) = algebraMap F (A F) s + x := by
    rw [hs]
    abel
  unfold complexPeriod
  rw [hx]
  convert (Equiv.addRight s).tsum_eq (fun t : F => h (algebraMap F (A F) t + x)) using 1
  simp only [Equiv.coe_addRight, map_add, add_assoc]

private theorem adele_polish : PolishSpace (A F) := by
  letI := IsTopologicalAddGroup.rightUniformSpace (A F)
  letI := isUniformAddGroup_of_addCommGroup (G := A F)
  letI := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace (A F)
  letI := IsUniformAddGroup.uniformity_countably_generated (α := A F)
  infer_instance

private theorem measurable_nonnegativePeriod (h : A F → ℝ≥0∞) (hh : Measurable h) :
    Measurable (nonnegativePeriod F h) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI := adele_polish F
  have hm : Measurable (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) :=
    QuotientAddGroup.continuous_mk.measurable
  apply (hm.measurable_comp_iff_of_surjective
    (QuotientAddGroup.mk'_surjective _)).mp
  change Measurable (fun x : A F => nonnegativePeriod F h (QuotientAddGroup.mk x))
  simp_rw [nonnegativePeriod_eq_sum]
  exact Measurable.ennreal_tsum fun t => hh.comp (measurable_const.add measurable_id)

private theorem measurable_complexPeriod (h : A F → ℂ) (hh : Measurable h) :
    Measurable (complexPeriod F h) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI := adele_polish F
  have hm : Measurable (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) :=
    QuotientAddGroup.continuous_mk.measurable
  apply (hm.measurable_comp_iff_of_surjective
    (QuotientAddGroup.mk'_surjective _)).mp
  change Measurable (fun x : A F => complexPeriod F h (QuotientAddGroup.mk x))
  simp_rw [complexPeriod_eq_sum]
  exact Measurable.tsum fun t => hh.comp (measurable_const.add measurable_id)

theorem lintegral_nonnegativePeriod (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hnorm : CompatibleHaar F dx dq) (h : A F → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ q, nonnegativePeriod F h q ∂dq = ∫⁻ x, h x ∂dx := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let e := KPAdelicDiagonal.diagonalAddEquiv F
  letI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := e.toEquiv.countable_iff.mp inferInstance
  obtain ⟨domain, hd, hfd, _hmass, rfl⟩ := hnorm
  have hm : Measurable (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) :=
    QuotientAddGroup.continuous_mk.measurable
  rw [lintegral_map (measurable_nonnegativePeriod F h hh) hm]
  change (∫⁻ x in domain, nonnegativePeriod F h (QuotientAddGroup.mk x) ∂dx) = _
  simp_rw [nonnegativePeriod_eq_sum]
  have ht : ∀ t : F, AEMeasurable (fun x : A F => h (algebraMap F (A F) t + x)) (dx.restrict domain) :=
    fun t => (hh.comp (measurable_const.add measurable_id)).aemeasurable
  rw [lintegral_tsum ht]
  rw [hfd.lintegral_eq_tsum'' h]
  exact e.toEquiv.tsum_eq (fun t => ∫⁻ x in domain, h (t +ᵥ x) ∂dx)

theorem integral_complexPeriod (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hnorm : CompatibleHaar F dx dq) (h : A F → ℂ)
    (hh : Measurable h)
    (hfinite : ∫⁻ q, normPeriod F h q ∂dq < ⊤) :
    Integrable h dx ∧
      (∀ᵐ q ∂dq, Summable (fun t : F => h (algebraMap F (A F) t + Quotient.out q))) ∧
      Integrable (complexPeriod F h) dq ∧
      ∫ q, complexPeriod F h q ∂dq = ∫ x, h x ∂dx := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hnormmeas : Measurable (normPeriod F h) :=
    measurable_nonnegativePeriod F _ hh.norm.ennreal_ofReal
  have hup : Integrable h dx := by
    refine ⟨hh.aestronglyMeasurable, ?_⟩
    have hid := lintegral_nonnegativePeriod F dx dq hnorm _ hh.norm.ennreal_ofReal
    change (∫⁻ x, ‖h x‖ₑ ∂dx) < ⊤
    simpa only [normPeriod, ← ofReal_norm_eq_enorm, hid] using hfinite
  have hsum : ∀ᵐ q ∂dq, Summable (fun t : F => h (algebraMap F (A F) t + Quotient.out q)) := by
    filter_upwards [ae_lt_top hnormmeas hfinite.ne] with q hq
    apply Summable.of_norm
    apply (ENNReal.tsum_coe_ne_top_iff_summable_coe (f := fun t : F => ‖h (algebraMap F (A F) t + Quotient.out q)‖₊)).mp
    simpa only [normPeriod, nonnegativePeriod, ofReal_norm_eq_enorm, enorm_eq_nnnorm] using hq.ne
  have hcp := measurable_complexPeriod F h hh
  have hdown : Integrable (complexPeriod F h) dq := by
    refine ⟨hcp.aestronglyMeasurable, lt_of_le_of_lt ?_ hfinite⟩
    apply lintegral_mono
    intro q
    simpa only [complexPeriod, normPeriod, nonnegativePeriod, ofReal_norm_eq_enorm]
      using (enorm_tsum_le_tsum_enorm (f := fun t : F => h (algebraMap F (A F) t + Quotient.out q)))
  refine ⟨hup, hsum, hdown, ?_⟩
  let e := KPAdelicDiagonal.diagonalAddEquiv F
  letI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := e.toEquiv.countable_iff.mp inferInstance
  obtain ⟨domain, hd, hfd, _hmass, rfl⟩ := hnorm
  have hm : Measurable (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) :=
    QuotientAddGroup.continuous_mk.measurable
  rw [integral_map hm.aemeasurable hcp.aestronglyMeasurable]
  change (∫ x in domain, complexPeriod F h (QuotientAddGroup.mk x) ∂dx) = _
  simp_rw [complexPeriod_eq_sum]
  have ht : ∀ t : F, AEStronglyMeasurable
      (fun x : A F => h (algebraMap F (A F) t + x)) (dx.restrict domain) :=
    fun t => (hh.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  rw [integral_tsum ht]
  · rw [hfd.integral_eq_tsum'' h hup]
    exact e.toEquiv.tsum_eq (fun t => ∫ x in domain, h (t +ᵥ x) ∂dx)
  · have he := e.toEquiv.tsum_eq (fun t => ∫⁻ x in domain, ‖h (t +ᵥ x)‖ₑ ∂dx)
    have hid := hfd.lintegral_eq_tsum'' (fun x => ‖h x‖ₑ)
    have hn : (∑' t : F, ∫⁻ x in domain, ‖h (algebraMap F (A F) t + x)‖ₑ ∂dx) =
        ∫⁻ x, ‖h x‖ₑ ∂dx := he.trans hid.symm
    rw [hn]
    exact hup.2.ne

end DedekindZetaZeroFree.KPChamberAdditivePeriodization

end
