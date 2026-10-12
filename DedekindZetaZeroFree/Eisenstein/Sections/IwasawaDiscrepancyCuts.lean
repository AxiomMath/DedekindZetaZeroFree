module

public import DedekindZetaZeroFree.Eisenstein.Sections.IwasawaNormDiscrepancy
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.MovingCompactCharts
public import DedekindZetaZeroFree.Eisenstein.Induction.ScatteringChamberAndSmoothTorusFibers

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology NNReal
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts
open KPLiteralRaw KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy → discrepancy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_locallyConstant → discrepancy_locallyConstant
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_borel → discrepancy_borel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def cut (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (a : ℝ) (v : Functions F ζ hζ) : Functions F ζ hζ :=
  fun g => if discrepancy F ζ hζ K hK g = a then v g else 0

private theorem compact_mask_locallyConstant (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) :
    IsLocallyConstant (fun k : K => fun g => discrepancy F ζ hζ K hK (g * k.val)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro k
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  have he : ∀ᶠ l : K in 𝓝 k, ∀ v : K,
      discrepancy F ζ hζ K hK (v.val * l.val) =
        discrepancy F ζ hζ K hK (v.val * k.val) := by
    have he' : ∀ᶠ l : K in 𝓝 k, ∀ v ∈ (Set.univ : Set K),
        discrepancy F ζ hζ K hK (v.val * l.val) =
          discrepancy F ζ hζ K hK (v.val * k.val) := by
      apply IsCompact.eventually_forall_of_forall_eventually isCompact_univ
      intro v _
      have h := (discrepancy_locallyConstant F ζ hζ K hK).eventually_eq (v.val * k.val)
      have hc₁ : Continuous (fun p : K × K => p.2.val * p.1.val) :=
        (continuous_subtype_val.comp continuous_snd).mul
          (continuous_subtype_val.comp continuous_fst)
      have hc₂ : Continuous (fun p : K × K => p.2.val * k.val) :=
        (continuous_subtype_val.comp continuous_snd).mul continuous_const
      filter_upwards [hc₁.continuousAt h, hc₂.continuousAt h] with p hp₁ hp₂
      exact hp₁.trans hp₂.symm
    simpa only [Set.mem_univ, forall_true_left] using he'
  filter_upwards [he] with l hl
  funext g
  obtain ⟨t, x, v, hg⟩ := hK.2.1 g
  rw [hg, mul_assoc (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) v.val l.val,
    mul_assoc (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) v.val k.val,
    discrepancy_borel, discrepancy_borel]
  exact hl v

 def maskMap (m : G F ζ hζ → ℝ) (a : ℝ) :
    Functions F ζ hζ →ₗ[ℂ] Functions F ζ hζ where
  toFun v g := if m g = a then v g else 0
  map_add' v w := by ext g; by_cases h : m g = a <;> simp [h]
  map_smul' c v := by ext g; by_cases h : m g = a <;> simp [h]

 theorem cut_KFinite (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (a : ℝ) (v : Functions F ζ hζ)
    (hv : KFinite F ζ hζ K v) : KFinite F ζ hζ K (cut F ζ hζ K hK a v) := by
  obtain ⟨W, hW, hvW, hstable⟩ := hv
  letI : Module.Finite ℂ W := hW
  let B := Set.range (fun k : K => fun g => discrepancy F ζ hζ K hK (g * k.val))
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  letI : Finite B := (compact_mask_locallyConstant F ζ hζ K hK).range_finite.to_subtype
  let spaces : B → Submodule ℂ (Functions F ζ hζ) := fun m => W.map (maskMap F ζ hζ m.val a)
  haveI : ∀ m, FiniteDimensional ℂ (spaces m) := fun m => inferInstanceAs
    (FiniteDimensional ℂ (W.map (maskMap F ζ hζ m.val a)))
  haveI : FiniteDimensional ℂ ↥(⨆ m : B, spaces m) := inferInstance
  let S := Submodule.span ℂ (Set.range (fun k : K =>
    rightAction F ζ hζ k.val (cut F ζ hζ K hK a v)))
  have hS : S ≤ ⨆ m : B, spaces m := by
    apply Submodule.span_le.mpr
    rintro w ⟨k, rfl⟩
    let m : B := ⟨_, Set.mem_range_self k⟩
    apply Submodule.mem_iSup_of_mem m
    apply Submodule.mem_map.mpr
    exact ⟨rightAction F ζ hζ k.val v, hstable k v hvW, rfl⟩
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hS
  refine ⟨S, inferInstance, ?_, ?_⟩
  · exact Submodule.subset_span ⟨1, by ext g; simp [rightAction]⟩
  · intro k w hw
    apply Submodule.span_induction (p := fun w _ => rightAction F ζ hζ k.val w ∈ S)
      ?_ ?_ ?_ ?_ hw
    · rintro w ⟨l, rfl⟩
      apply Submodule.subset_span
      exact ⟨k * l, by ext g; simp [rightAction, mul_assoc]⟩
    · exact S.zero_mem
    · intro x y hx hy ihx ihy
      exact S.add_mem ihx ihy
    · intro c x hx ih
      exact S.smul_mem c ih

private theorem discrepancy_right_level (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ, ∀ g u,
      u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
        discrepancy F ζ hζ K hK (g * u) = discrepancy F ζ hζ K hK g := by
  obtain ⟨U, hU⟩ := KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level
    (literalIwasawa F ζ hζ K hK)
  obtain ⟨V, hV⟩ := KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level
    (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ)
  refine ⟨(⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
      U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩ : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ), ?_⟩
  intro g u hu
  have hu' : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U ∧
      u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V := by
    rcases Subgroup.mem_map.mp hu with ⟨w, hw, rfl⟩
    exact ⟨Subgroup.mem_map.mpr ⟨w, hw.1, rfl⟩, Subgroup.mem_map.mpr ⟨w, hw.2, rfl⟩⟩
  unfold discrepancy KPContFlatFullProductIwasawa.alpha
  rw [hU g ⟨u, hu'.1⟩, hV g ⟨u, hu'.2⟩]

 theorem cut_smooth (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (a : ℝ) (v : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) : Smooth F ζ hζ (cut F ζ hζ K hK a v) := by
  have he (g : G F ζ hζ) : cut F ζ hζ K hK a v =ᶠ[𝓝 g]
      (if discrepancy F ζ hζ K hK g = a then v else fun _ => 0) := by
    filter_upwards [(discrepancy_locallyConstant F ζ hζ K hK).eventually_eq g] with x hx
    simp only [cut, hx]
    split_ifs <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g
    apply ContinuousAt.congr_of_eventuallyEq _ (he g)
    split_ifs
    · exact hv.1.continuousAt
    · exact continuousAt_const
  · intro g x hx
    have hc : ContinuousOn (fun z => g * KPGlobalResidualConstruction.archChart F ζ hζ z)
        (KPGlobalResidualConstruction.archDomain F) :=
      continuousOn_const.mul (KPGlobalResidualConstruction.ActualMovingCompact.archChart_continuousOn F ζ hζ)
    have hel := (hc x hx) (he (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
    have hpoint := (he (g * KPGlobalResidualConstruction.archChart F ζ hζ x)).self_of_nhds
    split_ifs at hel hpoint
    · exact (hv.2.1 g x hx).congr_of_eventuallyEq hel hpoint
    · exact contDiffWithinAt_const.congr_of_eventuallyEq hel hpoint
  · obtain ⟨U, hU⟩ := hv.2.2
    obtain ⟨V, hV⟩ := discrepancy_right_level F ζ hζ K hK
    refine ⟨(⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
      U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩ : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ), ?_⟩
    intro g u hu
    have hu' : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U ∧
        u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V := by
      rcases Subgroup.mem_map.mp hu with ⟨w, hw, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨w, hw.1, rfl⟩, Subgroup.mem_map.mpr ⟨w, hw.2, rfl⟩⟩
    simp only [cut, hV g u hu'.2, hU g u hu'.1]

 def cutFlat (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (a : ℝ) (f : Flat F ζ hζ K) : Flat F ζ hζ K := by
  refine ⟨fun s => cut F ζ hζ K hK a (f.val s), ?_, ?_, ?_⟩
  · intro s
    refine ⟨cut_smooth F ζ hζ K hK a (f.val s) (f.property.1 s).1, ?_⟩
    intro r x g
    simp only [cut, discrepancy_borel]
    split_ifs
    · exact (f.property.1 s).2 r x g
    · simp
  · intro s t k
    simp only [cut]
    split_ifs
    · exact f.property.2.1 s t k
    · simp
  · exact cut_KFinite F ζ hζ K hK a (f.val 0) f.property.2.2

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts

end

section

noncomputable section
open scoped NumberField Classical Topology NNReal
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts
open KPLiteralRaw KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy → discrepancy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_locallyConstant → discrepancy_locallyConstant
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_borel → discrepancy_borel
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming discrepancy_range_finite → discrepancy_range_finite
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy renaming literal_reweight_finite_expansion → literal_reweight_finite_expansion
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def cutCore (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (a : ℝ) (f : Flat F ζ hζ K) :
    KPMsRationalCompactCrossPairing.Vplus F ζ hζ (literalIwasawa F ζ hζ K hK) :=
  literalCore F ζ hζ K hK (cutFlat F ζ hζ K hK a f)

 theorem cutCore_formula (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (a : ℝ) (f : Flat F ζ hζ K) (g : G F ζ hζ) :
    (cutCore F ζ hζ K hK a f).val.val g =
      if discrepancy F ζ hζ K hK g = a then f.val 0 g else 0 := rfl

 theorem reweight_expansion_in_literal_core (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ C : Finset ℝ, ∀ (s : ℂ) (g : G F ζ hζ),
      Complex.exp (-s * (KPContFlatFullProductIwasawa.alpha F ζ hζ g : ℂ)) * f.val s g =
        ∑ a ∈ C, Complex.exp (s * (a : ℂ)) * (cutCore F ζ hζ K hK a f).val.val g := by
  obtain ⟨C, hC⟩ := literal_reweight_finite_expansion F ζ hζ K hK f
  refine ⟨C, ?_⟩
  intro s g
  simpa only [cutCore_formula] using hC s g

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts

end
end
