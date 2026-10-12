module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatProjection

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming kfinite_fullCompact → kfinite_fullCompact
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming cutFlat → cutFlat
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming cut → cut
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy → discrepancy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_range_finite → discrepancy_range_finite
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_borel → discrepancy_borel
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_smul → smooth_smul
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem smooth_finset {I : Type*} (s : Finset I) (u : I → Functions F ζ hζ)
    (hu : ∀ i ∈ s, Smooth F ζ hζ (u i)) : Smooth F ζ hζ (∑ i ∈ s, u i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact ((FlatFiniteSum.zero F ζ hζ ⊥).property.1 0).1
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact smooth_add F ζ hζ _ _ (hu i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem canonical_flat_lift {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ v : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K,
      ∀ z g, v.val z g = Complex.exp (z * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * f.val 0 g := by
  let v := fun z g => Complex.exp (z * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * f.val 0 g
  let C := (discrepancy_range_finite F ζ hζ K hK).toFinset
  have hv (z : ℂ) (g : G F ζ hζ) :
      v z g = ∑ a ∈ C, Complex.exp (-z * (a : ℂ)) * (cutFlat F ζ hζ K hK a f).val z g := by
    have hm : discrepancy F ζ hζ K hK g ∈ C := by
      exact Set.Finite.mem_toFinset (discrepancy_range_finite F ζ hζ K hK) |>.mpr (Set.mem_range_self g)
    rw [Finset.sum_eq_single (discrepancy F ζ hζ K hK g)]
    · change _ = _ * (if _ = _ then _ else _)
      rw [if_pos rfl, KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f,
        ← mul_assoc, ← Complex.exp_add]
      unfold v discrepancy KPContFlatSourceRecipe.alpha KPContFlatFullProductIwasawa.alpha
      push_cast
      congr 2
      ring
    · intro a ha hne
      change _ * (if discrepancy F ζ hζ K hK g = a then _ else 0) = 0
      simp [Ne.symm hne]
    · exact fun h => (h hm).elim
  have hs (z : ℂ) : Smooth F ζ hζ (v z) := by
    have he : v z = ∑ a ∈ C, Complex.exp (-z * (a : ℂ)) • (cutFlat F ζ hζ K hK a f).val z := by
      funext g
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv z g
    rw [he]
    exact smooth_finset F ζ hζ C _ (fun a ha =>
      smooth_smul F ζ hζ _ _ ((cutFlat F ζ hζ K hK a f).property.1 z).1)
  have hv0 : v 0 = f.val 0 := by ext g; simp [v]
  refine ⟨⟨v, ?_, ?_, ?_⟩, fun _ _ => rfl⟩
  · intro z
    refine ⟨hs z, ?_⟩
    intro r x g
    change Complex.exp _ * f.val 0 _ = _
    dsimp only [KPContFlatSourceRecipe.alpha]
    rw [KPContFlatFullProductIwasawa.alpha_borel_mul, (f.property.1 0).2]
    dsimp only [v]
    unfold KPGlobalExceptionalParameter.realLogPower
    push_cast
    simp only [add_mul, mul_add, Complex.exp_add, add_zero]
    ring
  · intro z t k
    have hn := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) t 0 k
    have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPAdeles F) = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    rw [hN, mul_one] at hn
    change Complex.exp _ * f.val 0 _ = _ * (Complex.exp _ * f.val 0 _)
    simp only [zero_mul, Complex.exp_zero, one_mul]
    unfold KPContFlatSourceRecipe.alpha KPContFlatFullProductIwasawa.alpha
    rw [hn]
    rfl
  · rw [hv0]
    exact kfinite_fullCompact F ζ hζ K hK _ (f.property.1 0).1 f.property.2.2

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming kfinite_fullCompact → kfinite_fullCompact
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming cutFlat → cutFlat
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming cut → cut
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy → discrepancy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_range_finite → discrepancy_range_finite
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_borel → discrepancy_borel
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_smul → smooth_smul
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem smooth_finset {I : Type*} (s : Finset I) (u : I → Functions F ζ hζ)
    (hu : ∀ i ∈ s, Smooth F ζ hζ (u i)) : Smooth F ζ hζ (∑ i ∈ s, u i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact ((FiniteWhittakerProjectors.FlatFiniteSum.zero F ζ hζ ⊥).property.1 0).1
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact smooth_add F ζ hζ _ _ (hu i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem canonical_flat_lift {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ v : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K,
      ∀ z g, v.val z g = Complex.exp (z * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * f.val 0 g := by
  let v := fun z g => Complex.exp (z * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * f.val 0 g
  let C := (discrepancy_range_finite F ζ hζ K hK).toFinset
  have hv (z : ℂ) (g : G F ζ hζ) :
      v z g = ∑ a ∈ C, Complex.exp (-z * (a : ℂ)) * (cutFlat F ζ hζ K hK a f).val z g := by
    have hm : discrepancy F ζ hζ K hK g ∈ C := by
      exact Set.Finite.mem_toFinset (discrepancy_range_finite F ζ hζ K hK) |>.mpr (Set.mem_range_self g)
    rw [Finset.sum_eq_single (discrepancy F ζ hζ K hK g)]
    · change _ = _ * (if _ = _ then _ else _)
      rw [if_pos rfl, KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f,
        ← mul_assoc, ← Complex.exp_add]
      unfold v discrepancy KPContFlatSourceRecipe.alpha KPContFlatFullProductIwasawa.alpha
      push_cast
      congr 2
      ring
    · intro a ha hne
      change _ * (if discrepancy F ζ hζ K hK g = a then _ else 0) = 0
      simp [Ne.symm hne]
    · exact fun h => (h hm).elim
  have hs (z : ℂ) : Smooth F ζ hζ (v z) := by
    have he : v z = ∑ a ∈ C, Complex.exp (-z * (a : ℂ)) • (cutFlat F ζ hζ K hK a f).val z := by
      funext g
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv z g
    rw [he]
    exact smooth_finset F ζ hζ C _ (fun a ha =>
      smooth_smul F ζ hζ _ _ ((cutFlat F ζ hζ K hK a f).property.1 z).1)
  have hv0 : v 0 = f.val 0 := by ext g; simp [v]
  refine ⟨⟨v, ?_, ?_, ?_⟩, fun _ _ => rfl⟩
  · intro z
    refine ⟨hs z, ?_⟩
    intro r x g
    change Complex.exp _ * f.val 0 _ = _
    dsimp only [KPContFlatSourceRecipe.alpha]
    rw [KPContFlatFullProductIwasawa.alpha_borel_mul, (f.property.1 0).2]
    dsimp only [v]
    unfold KPGlobalExceptionalParameter.realLogPower
    push_cast
    simp only [add_mul, mul_add, Complex.exp_add, add_zero]
    ring
  · intro z t k
    have hn := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) t 0 k
    have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPAdeles F) = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    rw [hN, mul_one] at hn
    change Complex.exp _ * f.val 0 _ = _ * (Complex.exp _ * f.val 0 _)
    simp only [zero_mul, Complex.exp_zero, one_mul]
    unfold KPContFlatSourceRecipe.alpha KPContFlatFullProductIwasawa.alpha
    rw [hn]
    rfl
  · rw [hv0]
    exact kfinite_fullCompact F ζ hζ K hK _ (f.property.1 0).1 f.property.2.2

theorem canonical_flat_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (A : FlatScalarResidue F ζ hζ f) :
    ∃ (v : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K)
      (B : FlatScalarResidue F ζ hζ v),
      (∀ z g, v.val z g = Complex.exp (z * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * f.val 0 g) ∧
      ∀ g, B.numerator 0 g = A.numerator 0 g := by
  obtain ⟨v,hv⟩ := canonical_flat_lift F ζ hζ hK f
  let B := Classical.choice (flatScalarResidue_nonempty F ζ hζ _
    (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ) v)
  let C := (discrepancy_range_finite F ζ hζ K hK).toFinset
  have hh (a : ℝ) := canonical_flat_lift F ζ hζ hK (cutFlat F ζ hζ K hK a f)
  choose w hw using hh
  let W := fun a => Classical.choice (flatScalarResidue_nonempty F ζ hζ _
    (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ) (w a))
  refine ⟨v,B,hv,?_⟩
  intro g
  have hf (z : ℂ) (g : G F ζ hζ) :
      f.val z g = ∑ a ∈ C, Complex.exp (z * (a : ℂ)) * (w a).val z g := by
    have hm : discrepancy F ζ hζ K hK g ∈ C := by
      exact Set.Finite.mem_toFinset (discrepancy_range_finite F ζ hζ K hK) |>.mpr (Set.mem_range_self g)
    rw [Finset.sum_eq_single (discrepancy F ζ hζ K hK g)]
    · rw [hw]
      change _ = Complex.exp _ * (Complex.exp _ * (if _ = _ then f.val 0 g else 0))
      rw [if_pos rfl, ← mul_assoc, ← Complex.exp_add,
        KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f]
      congr 2
      unfold discrepancy KPContFlatSourceRecipe.alpha
      push_cast
      ring
    · intro a ha hne
      rw [hw]
      change _ * (_ * (if discrepancy F ζ hζ K hK g = a then _ else 0)) = 0
      simp [Ne.symm hne]
    · exact fun h => (h hm).elim
  have hvg (z : ℂ) (g : G F ζ hζ) : v.val z g = ∑ a ∈ C, (w a).val z g := by
    rw [hv]
    have hm : discrepancy F ζ hζ K hK g ∈ C := by
      exact Set.Finite.mem_toFinset (discrepancy_range_finite F ζ hζ K hK) |>.mpr (Set.mem_range_self g)
    simp_rw [hw]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single (discrepancy F ζ hζ K hK g)]
    · change f.val 0 g = if discrepancy F ζ hζ K hK g = discrepancy F ζ hζ K hK g then f.val 0 g else 0
      rw [if_pos rfl]
    · intro a ha hne
      change (if discrepancy F ζ hζ K hK g = a then _ else 0) = 0
      simp [Ne.symm hne]
    · exact fun h => (h hm).elim
  have he : (fun z => A.E z g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ a ∈ C, Complex.exp (z * (a : ℂ)) * (W a).E z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (A.meromorphic g) (MeromorphicOn.fun_sum (fun a ha =>
        ((analyticOnNhd_id.mul analyticOnNhd_const).cexp).meromorphicOn.mul ((W a).meromorphic g)))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_
      (by norm_num [KPContinuation.spectralDomain])
    intro z hz
    change A.E z g = _
    rw [A.chamber z hz]
    unfold eisenstein
    simp_rw [hf]
    rw [Summable.tsum_finsetSum (fun a _ =>
      (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ _
        (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ) (w a) z hz g).mul_left _)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [tsum_mul_left]
    change Complex.exp (z * (a : ℂ)) * eisenstein F ζ hζ _ (w a) z g =
      Complex.exp (z * (a : ℂ)) * (W a).E z g
    rw [(W a).chamber z hz]
    rfl
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a ∈ C,
      (W a).numerator z g = z * (W a).E z g :=
    (Filter.eventually_all_finite C.finite_toSet).mpr (fun a ha => (W a).clears g)
  have hn : (fun z => A.numerator z g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ a ∈ C, Complex.exp (z * (a : ℂ)) * (W a).numerator z g) := by
    filter_upwards [A.clears g, he, hall] with z ha he hz
    rw [ha, he, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a ha => by rw [hz a ha]; ring)
  have hc : ContinuousAt (fun z => ∑ a ∈ C,
      Complex.exp (z * (a : ℂ)) * (W a).numerator z g) 0 := by
    apply tendsto_finsetSum
    intro a ha
    exact ((continuousAt_id.mul continuousAt_const).cexp).mul
      ((W a).analytic g 0 (Metric.mem_ball_self (W a).radius_pos)).continuousAt
  have ha := (A.analytic g 0 (Metric.mem_ball_self A.radius_pos)).continuousAt
  have hA := ((ha.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc).mp hn).eq_of_nhds
  have hB := flat_finite_residue
    (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ) B C w W
    (fun _ _ => 1) (fun _ _ => analyticOnNhd_const) 1
    (fun z g => by simpa using hvg z g) g
  simp only [mul_one, zero_mul, Complex.exp_zero, one_mul] at hA hB
  exact hB.trans hA.symm
end DedekindZetaZeroFree.RootDerivatives

end
end
