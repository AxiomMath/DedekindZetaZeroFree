module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration

@[expose] public section

noncomputable section
open scoped NumberField
open MeasureTheory
open DedekindZetaZeroFree
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm
variable (F : Type) [Field F] [NumberField F]
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) := KPCuspSiegel.instMulActionPGL2SpaceDimension F

theorem arithmetic_dense_free (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) [Countable Γ]
    (s : Set (KPArch.Space (KPCuspLogShape.dimension F)))
    (hs : IsFundamentalDomain Γ s (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    Dense {x : KPArch.Space (KPCuspLogShape.dimension F) | ∀ g : Γ, g • x = x → g = 1} := by
  letI : MeasurableConstSMul Γ (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun γ => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F γ.val).measurable⟩
  letI : SMulInvariantMeasure Γ (KPArch.Space (KPCuspLogShape.dimension F))
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) := by
    constructor
    intro γ t ht
    exact (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F γ.val).measure_preimage ht.nullMeasurableSet
  have hden : Continuous (fun x : KPArch.Space (KPCuspLogShape.dimension F) =>
      ENNReal.ofReal (KPArch.volumeDensity _ x)) := by
    apply ENNReal.continuous_ofReal.comp
    unfold KPArch.volumeDensity KPArch.height
    apply continuous_finset_prod
    intro i hi
    apply Continuous.pow
    apply Continuous.inv₀ _ (fun x => Real.exp_ne_zero _)
    exact Real.continuous_exp.comp (continuous_snd.comp (continuous_apply i))
  have hpos (x : KPArch.Space (KPCuspLogShape.dimension F)) :
      ENNReal.ofReal (KPArch.volumeDensity _ x) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    unfold KPArch.volumeDensity KPArch.height
    positivity
  have hac : volume ≪ KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) :=
    withDensity_absolutelyContinuous' hden.measurable.aemeasurable
      (Filter.Eventually.of_forall hpos)
  exact Measure.dense_of_ae (hac.ae_le (KPFiniteAdelicCuspEnds.fd_ae_free _ s hs))

theorem high_overlap_stabilizes_cusp (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) [Countable Γ]
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (hd : 0 < KPCuspLogShape.dimension F)
    (s : Set (KPArch.Space (KPCuspLogShape.dimension F)))
    (hs : IsFundamentalDomain Γ s (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)))
    (he : Function.Injective (KPFiniteCuspAtlas.endMap F Γ q σ T))
    (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F))
    (hz : z ∈ KPCuspSiegel.highCusp F σ T)
    (hγz : γ • z ∈ KPCuspSiegel.highCusp F σ T) :
    (γ : KPCuspArithmetic.PGL2 F) • q = q := by
  let V := KPCuspSiegel.highCusp F σ T
  have hopen : IsOpen V := by
    apply (KPCuspCharts.projectiveHomeomorph F σ).isOpenMap _
    apply isOpen_lt continuous_const
    unfold KPCuspLogShape.meanHeight
    fun_prop
  have hpre : IsOpen ((fun x => γ • x) ⁻¹' V) :=
    hopen.preimage (KPCuspCharts.projectiveHomeomorph F γ.val).continuous
  obtain ⟨w, hwfree, hw, hγw⟩ := (arithmetic_dense_free F Γ s hs).exists_mem_open
    (hopen.inter hpre) ⟨z, hz, hγz⟩
  let e := KPCuspCharts.highCoordinatesHomeomorph F hd σ T
  let p := e.symm ⟨w, hw⟩
  let r := e.symm ⟨γ • w, hγw⟩
  have hp : σ • KPCuspCharts.toArch F p.val = w :=
    congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)
  have hr : σ • KPCuspCharts.toArch F r.val = γ • w :=
    congrArg Subtype.val (e.apply_symm_apply ⟨γ • w, hγw⟩)
  have hquot : KPFiniteCuspAtlas.endMap F Γ q σ T (Quotient.mk _ r) =
      KPFiniteCuspAtlas.endMap F Γ q σ T (Quotient.mk _ p) := by
    change KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F r.val) =
      KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p.val)
    rw [hr, hp]
    exact Quotient.sound ⟨γ, rfl⟩
  have hrel := Quotient.exact (he hquot)
  change ∃ t : KPCuspArithmetic.conjugatedStabilizer F Γ q σ,
    t • KPCuspCharts.toArch F p.val = KPCuspCharts.toArch F r.val at hrel
  obtain ⟨t, ht⟩ := hrel
  let δ := KPCuspGenuineMonodromy.cuspInclusion F Γ q σ t
  have hδw : δ • w = γ • w := by
    calc
      δ • w = δ • (σ • KPCuspCharts.toArch F p.val) := by rw [hp]
      _ = σ • KPCuspCharts.toArch F r.val := ?_
      _ = γ • w := hr

    change (δ : KPCuspArithmetic.PGL2 F) • (σ • KPCuspCharts.toArch F p.val) = σ • KPCuspCharts.toArch F r.val
    rw [KPCuspGenuineMonodromy.cuspInclusion_formula]
    simp only [mul_smul, inv_smul_smul]
    exact congrArg (fun x => σ • x) ht
  have hδγ : δ = γ := by
    have hfix : (δ⁻¹ * γ) • w = w := by
      rw [mul_smul, ← hδw, inv_smul_smul]
    exact inv_mul_eq_one.mp (hwfree _ hfix)
  rw [← hδγ]
  obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.mp t.property
  have hkt' : σ⁻¹ * k * σ = t.val := by
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using hkt
  change (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ t : KPCuspArithmetic.PGL2 F) • q = q
  rw [KPCuspGenuineMonodromy.cuspInclusion_formula, ← hkt']
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using (MulAction.mem_stabilizer_iff.mp hk.2)
end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm
variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
set_option maxHeartbeats 1000000 in

theorem atlas_high_overlap_stabilizes_cusp (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsFixedHaarDisintegration.CuspIndex A) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
    (z : KPArch.Space (KPCuspLogShape.dimension F))
    (hz : z ∈ KPCuspSiegel.highCusp F ((A.cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y))
    (hγz : γ • z ∈ KPCuspSiegel.highCusp F ((A.cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y)) :
    (γ : KPCuspArithmetic.PGL2 F) • (A.cuspAtlas j.1).cusp j.2 =
      (A.cuspAtlas j.1).cusp j.2 := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  have hT : (A.cuspAtlas j.1).threshold ≤ KPMsFixedHaarDisintegration.logHeight (F := F) Y := by
    rw [A.common_threshold]
    exact hY.2
  have hmono : KPCuspSiegel.highCusp F ((A.cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y) ⊆
      KPCuspSiegel.highCusp F ((A.cuspAtlas j.1).representative j.2) (A.cuspAtlas j.1).threshold := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨v, lt_of_le_of_lt hT hv, rfl⟩
  exact high_overlap_stabilizes_cusp F _ _ _ _
    ((A.cuspAtlas j.1).geometry j.2).positive_dimension
    (A.cuspAtlas j.1).fundamentalDomain (A.cuspAtlas j.1).isFundamentalDomain
    ((A.cuspAtlas j.1).end_embedding j.2).injective γ z
    (hmono hz) (hmono hγz)
end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm

end
