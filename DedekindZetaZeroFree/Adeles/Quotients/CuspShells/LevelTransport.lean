module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.CrossLevelFrameTransport
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.FullAngularSupport

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (S : NativeRecipe F ζ hζ R P)

namespace CrossLevelProof
open KPMsActualAngularSource KPMsActualAngularDescentSource KPMsActualAngularTransitionSource
open KPMsActualCuspSource
open FullSupportGeometry
open _root_.DedekindZetaZeroFree.KPMsActualAngularCrossLevelFrameSource renaming frame_change_full_angular → frame_change_full_angular
open _root_.DedekindZetaZeroFree.KPMsActualAngularCrossLevelFrameSource renaming all_level_radial_slot_eq → all_level_radial_slot_eq
open _root_.DedekindZetaZeroFree.KPMsActualAngularCrossLevelFrameSource renaming framed_iwasawaNorm_eq_of_delta_one → framed_iwasawaNorm_eq_of_delta_one
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
variable (U V : KPMsActualAngularSource.Level F ζ hζ)
private theorem nativeFrameTransport
    (j : Cusp S U) (g : KPMsActualAngularSource.G F ζ hζ) :
    ∃ (k : Cusp S V) (h : KPMsActualAngularSource.G F ζ hζ),
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g =
        KPSmoothLocalQuotientCharts.quotientMap F ζ hζ h ∧
      framedFullAngular F ζ hζ (nativeDatum F ζ hζ) (nativeDisintegration F ζ hζ R P S U).radial
        (cuspRepresentative S U j) g =
        framedFullAngular F ζ hζ (nativeDatum F ζ hζ) (nativeDisintegration F ζ hζ R P S V).radial
          (cuspRepresentative S V k) h ∧
      (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j) g).val =
        (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S V k) h).val ∧
      ∃ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
        (t : ℝ) (ε : rootsOfUnity 3 F)
        (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
        KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F
          (((nativeAtlas F ζ hζ R P S V).cuspAtlas k.1).representative k.2)
          (KPCuspCharts.toArch F (p,t)) ∧
        h = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S V).representative k.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val := by
  let σ := cuspRepresentative S U j
  obtain ⟨k,b,a,ε,u,hb,he⟩ := finite_frame S V (σ⁻¹ * g)
  let τ := cuspRepresentative S V k
  let h := τ * rationalLift F ζ hζ b * (σ⁻¹ * g)
  obtain ⟨y,n,hy⟩ := rational_upper_literal_factorization F ζ hζ b hb
  have hframe : τ⁻¹ * h = (KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ n * (σ⁻¹ * g) := by
    dsimp only [h]
    rw [hy]
    group
  have hq : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ h := by
    let δ := (((nativeAtlas F ζ hζ R P S V).cuspAtlas k.1).representative k.2) * b *
      (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)⁻¹
    apply (full_quotient_eq_iff_rational_left (F := F) (ζ := ζ) (hζ := hζ) g h).mpr
    refine ⟨δ, ?_⟩
    dsimp only [h,τ,σ,FullSupportGeometry.cuspRepresentative,δ]
    rw [KPMsActualAngularTransitionSource.rationalLift_mul,KPMsActualAngularTransitionSource.rationalLift_mul,KPMsActualAngularTransitionSource.rationalLift_inv]
    group
  let c := (KPCuspCharts.toArchHomeomorph F (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)).symm
    (KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas k.1).representative k.2)⁻¹
      (KPMsFixedHaarDisintegration.archBasepoint F a))
  have hc : KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas k.1).representative k.2) (KPCuspCharts.toArch F c) := by
    have hc₀ : KPCuspCharts.toArch F c = _ :=
      (KPCuspCharts.toArchHomeomorph F (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)).apply_symm_apply _
    rw [hc₀]
    exact (smul_inv_smul (((nativeAtlas F ζ hζ R P S V).cuspAtlas k.1).representative k.2)
      (KPMsFixedHaarDisintegration.archBasepoint F a)).symm
  refine ⟨k,h,hq,?_,?_,a,c.1,c.2,ε,u,hc,he⟩
  · exact (frame_change_full_angular (nativeDatum F ζ hζ) _ _ (all_level_radial_slot_eq (nativeFamily F ζ hζ R P) (S.atlasLevel (cofinalLevel F ζ hζ U)) (S.atlasLevel (cofinalLevel F ζ hζ V)))
      σ τ g h y n hframe).symm
  · have hr := framed_iwasawaNorm_eq_of_delta_one (D := (nativeDatum F ζ hζ)) 1
      (σ⁻¹*g) (τ⁻¹*h) _ n (by simpa only [inv_one,one_mul] using hframe)
      (KPGlobalTorusBorelNormTwistTransport.delta_rational F ζ hζ y)
    simpa only [framedRadius,inv_one,one_mul] using
      (congrArg (fun r : (ℝ≥0)ˣ => ((r : ℝ≥0) : ℝ)) hr).symm

private theorem frameCoordinate (j : Cusp S U) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y)
    (g : KPMsActualAngularSource.G F ζ hζ)
    (hg : g ∈ fullCuspDomain S U j (Y / (cuspOffset F ζ hζ R P S U j).val)) :
    fullCoordinate F ζ hζ R P S U j Y (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
      framedFullAngular F ζ hζ (nativeDatum F ζ hζ)
        (nativeDisintegration F ζ hζ R P S U).radial (cuspRepresentative S U j) g := by
  let x := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g
  have hx := quotientMap_mem_cuspEnd_of_mem_fullCuspDomain S U j _ g hg
  have hb := cuspLift_mem_fullCuspDomain S U j _ x hx
  have hq := (cuspLift_quotient S U j (Y / (cuspOffset F ζ hζ R P S U j).val) x).symm
  exact (actual_full_frame_invariant S U j _ (hY j) g _ hg hb hq).symm

private theorem pointTransport (j : Cusp S U) (Y : ℝ)
    (hU : OffsetAdmissible F ζ hζ R P S U Y)
    (hV : OffsetAdmissible F ζ hζ R P S V Y)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ)
    (hx : x ∈ cuspShell F ζ hζ R P S U j Y) :
    ∃ k : Cusp S V, x ∈ cuspShell F ζ hζ R P S V k Y ∧
      fullCoordinate F ζ hζ R P S U j Y x = fullCoordinate F ζ hζ R P S V k Y x := by
  let z := Y / (cuspOffset F ζ hζ R P S U j).val
  let g := cuspLift S U j z x
  have hg : g ∈ fullCuspDomain S U j z := cuspLift_mem_fullCuspDomain S U j z x hx.1
  have hqx : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g = x := cuspLift_quotient S U j z x
  have hrad := radius_eq_offset_modulus S U j z (hU j) x hx.1
  have hr : Y < (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j) g).val ∧
      (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j) g).val ≤ 2 * Y := by
    rw [hrad]
    constructor
    · exact (div_lt_iff₀ (cuspOffset F ζ hζ R P S U j).property).mp hx.2.1 |>.trans_eq (mul_comm _ _)
    · simpa only [mul_comm] using (le_div_iff₀ (cuspOffset F ζ hζ R P S U j).property).mp hx.2.2
  obtain ⟨k,h,hq,hang,hrad',a,p,t,ε,u,ha,he⟩ := nativeFrameTransport F ζ hζ R P S U V j g
  have hn : (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S V k) h).val =
      (cuspOffset F ζ hζ R P S V k).val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
    change ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
      ((cuspRepresentative S V k)⁻¹ * h) : ℝ≥0) : ℝ) = _
    rw [he]
    exact frame_norm S V k a p t ε u ha
  have ht : KPMsFixedHaarDisintegration.logHeight (F := F)
      (Y / (cuspOffset F ζ hζ R P S V k).val) < t := by
    have hl := hr.1
    rw [hrad',hn] at hl
    have hr' : Y / (cuspOffset F ζ hζ R P S V k).val <
        Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
      exact (div_lt_iff₀ (cuspOffset F ζ hζ R P S V k).property).mpr (by simpa only [mul_comm] using hl)
    have hd : 0 < 2 * (KPCuspLogShape.dimension F : ℝ) :=
      mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex))
    apply (div_lt_iff₀ hd).mpr
    simpa only [mul_comm] using (Real.log_lt_iff_lt_exp (hV k).1).mpr hr'
  have hh : h ∈ fullCuspDomain S V k (Y / (cuspOffset F ζ hζ R P S V k).val) :=
    ⟨a,p,t,ε,u,ht,ha,he⟩
  have hhx : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ h = x := hq.symm.trans hqx
  have hxend := quotientMap_mem_cuspEnd_of_mem_fullCuspDomain S V k _ h hh
  rw [hhx] at hxend
  have hmod := spherical_modulus_of_cusp_basepoint S V k _ (hV k) a p t ε u ht ha
  rw [← he,hhx] at hmod
  refine ⟨k,⟨hxend,?_⟩,?_⟩
  · change _ < _ ∧ _ ≤ _
    rw [hmod]
    constructor
    · exact (Real.log_lt_iff_lt_exp (hV k).1).mp ((div_lt_iff₀ (by
        exact mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)))).mp ht |>.trans_eq (mul_comm _ _))
    · apply (le_div_iff₀ (cuspOffset F ζ hζ R P S V k).property).mpr
      have hle := hr.2
      rw [hrad',hn] at hle
      simpa only [mul_comm] using hle
  · have hsrc := frameCoordinate F ζ hζ R P S U j Y hU g hg
    have htgt := frameCoordinate F ζ hζ R P S V k Y hV h hh
    rw [hqx] at hsrc
    rw [hhx] at htgt
    exact hsrc.trans (hang.trans htgt.symm)
private theorem endSet_mono_threshold (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y) :
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ U))
        ((nativeAtlas F ζ hζ R P S U).representative j.1))
      (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y) ⊆
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ U))
        ((nativeAtlas F ζ hζ R P S U).representative j.1))
      (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
      ((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).threshold := by
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨v, hv, rfl⟩ := hw
  refine ⟨(((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2) • v, ?_, rfl⟩
  refine ⟨v, ?_, rfl⟩
  have hT : ((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).threshold ≤
      KPMsFixedHaarDisintegration.logHeight (F := F) Y := by
    rw [(nativeAtlas F ζ hζ R P S U).common_threshold]
    exact hY.2
  exact lt_of_le_of_lt hT hv

private theorem shiftedEndsDisjoint (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y) :
    Pairwise (fun j l : Cusp S U => Disjoint (cuspEnd S U j (Y / (cuspOffset F ζ hζ R P S U j).val)) (cuspEnd S U l (Y / (cuspOffset F ζ hζ R P S U l).val))) := by
  intro j l hjl
  apply Set.disjoint_left.mpr
  intro x hxj hxl
  obtain ⟨a, ha, hea⟩ := hxj
  obtain ⟨b, hb, heb⟩ := hxl
  have hcomp : (nativeAtlas F ζ hζ R P S U).components ⟨j.1,a⟩ =
      (nativeAtlas F ζ hζ R P S U).components ⟨l.1,b⟩ := by
    rw [(nativeAtlas F ζ hζ R P S U).components_formula,
      (nativeAtlas F ζ hζ R P S U).components_formula, hea, heb]
  have hs := (nativeAtlas F ζ hζ R P S U).components.injective hcomp
  have hi : j.1 = l.1 := Sigma.mk.inj_iff.mp hs |>.1
  cases j with
  | mk i j =>
    cases l with
    | mk n l =>
      dsimp only at hi
      subst n
      have hab : a = b := by simpa using hs
      subst b
      have hne : j ≠ l := by
        intro he
        exact hjl (congrArg (Sigma.mk i) he)
      exact Set.disjoint_left.mp (((nativeAtlas F ζ hζ R P S U).cuspAtlas i).disjoint_ends hne)
        (endSet_mono_threshold F ζ hζ R P S U ⟨i,j⟩ _ (hY ⟨i,j⟩) ha)
        (endSet_mono_threshold F ζ hζ R P S U ⟨i,l⟩ _ (hY ⟨i,l⟩) hb)

private theorem testSet_measurable (j : Cusp S U) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y)
    (E : Set (FullOmega F ζ hζ (nativeDatum F ζ hζ))) (hE : MeasurableSet E) :
    MeasurableSet ((fullCoordinate F ζ hζ R P S U j Y ⁻¹' E) ∩
      cuspShell F ζ hζ R P S U j Y) := by
  let B := cuspEnd S U j (Y / (cuspOffset F ζ hζ R P S U j).val)
  have hB : MeasurableSet B := (cuspEnd_isOpen S U j _ (hY j)).measurableSet
  let q₀ := fullCoordinate F ζ hζ R P S U j Y (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ 1)
  letI : BorelSpace (FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩
  have hm : Measurable (B.piecewise (fullCoordinate F ζ hζ R P S U j Y) (fun _ => q₀)) :=
    (fullCoordinate_continuousOn S U j Y hY).measurable_piecewise continuousOn_const hB
  have he : ((fullCoordinate F ζ hζ R P S U j Y ⁻¹' E) ∩ cuspShell F ζ hζ R P S U j Y) =
      ((B.piecewise (fullCoordinate F ζ hζ R P S U j Y) (fun _ => q₀)) ⁻¹' E) ∩
        cuspShell F ζ hζ R P S U j Y := by
    ext x
    by_cases hx : x ∈ cuspShell F ζ hζ R P S U j Y
    · have hb : x ∈ B := hx.1
      simp only [Set.mem_inter_iff,Set.mem_preimage,Set.piecewise_eq_of_mem B _ _ hb,hx]
    · simp only [Set.mem_inter_iff,hx,and_false]
  rw [he]
  exact (hE.preimage hm).inter (cuspShell_measurable S U j Y hY)

private theorem testSet_disjoint (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y)
    (E : Set (FullOmega F ζ hζ (nativeDatum F ζ hζ))) :
    Pairwise (fun j l : Cusp S U => Disjoint
      ((fullCoordinate F ζ hζ R P S U j Y ⁻¹' E) ∩ cuspShell F ζ hζ R P S U j Y)
      ((fullCoordinate F ζ hζ R P S U l Y ⁻¹' E) ∩ cuspShell F ζ hζ R P S U l Y)) := by
  intro j l hjl
  exact (shiftedEndsDisjoint F ζ hζ R P S U Y hY hjl).mono
    (fun _ hx => hx.2.1) (fun _ hx => hx.2.1)

private theorem testUnion_eq (Y : ℝ)
    (hU : OffsetAdmissible F ζ hζ R P S U Y)
    (hV : OffsetAdmissible F ζ hζ R P S V Y)
    (E : Set (FullOmega F ζ hζ (nativeDatum F ζ hζ))) :
    (⋃ j : Cusp S U, (fullCoordinate F ζ hζ R P S U j Y ⁻¹' E) ∩
      cuspShell F ζ hζ R P S U j Y) =
    (⋃ k : Cusp S V, (fullCoordinate F ζ hζ R P S V k Y ⁻¹' E) ∩
      cuspShell F ζ hζ R P S V k Y) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨j,hE,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨k,hk,he⟩ := pointTransport F ζ hζ R P S U V j Y hU hV x hx
    exact Set.mem_iUnion.mpr ⟨k,by simpa only [Set.mem_preimage,← he] using hE,hk⟩
  · intro x hx
    obtain ⟨k,hE,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j,hj,he⟩ := pointTransport F ζ hζ R P S V U k Y hV hU x hx
    exact Set.mem_iUnion.mpr ⟨j,by simpa only [Set.mem_preimage,← he] using hE,hj⟩

private theorem fullShell_apply (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y)
    (E : Set (FullOmega F ζ hζ (nativeDatum F ζ hζ))) (hE : MeasurableSet E) :
    fullShell F ζ hζ R P S U Y E = ENNReal.ofReal (2 * Y) *
      R.quotientHaar (⋃ j : Cusp S U, (fullCoordinate F ζ hζ R P S U j Y ⁻¹' E) ∩
        cuspShell F ζ hζ R P S U j Y) := by
  rw [measure_iUnion (testSet_disjoint F ζ hζ R P S U Y hY E)
    (fun j => testSet_measurable F ζ hζ R P S U j Y hY E hE), tsum_fintype]
  unfold fullShell
  rw [Measure.finsetSum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Measure.smul_apply,smul_eq_mul,
    Measure.map_apply_of_aemeasurable (KPMsNativeOffsetMass.fullCoordinate_aemeasurable F ζ hζ R P S U j Y hY) hE,
    Measure.restrict_apply' (cuspShell_measurable S U j Y hY)]

end CrossLevelProof

theorem fullShell_cofinal_independent
    (V W : KPMsActualAngularSource.Level F ζ hζ) (Y : ℝ)
    (hV : OffsetAdmissible F ζ hζ R P S V Y)
    (hW : OffsetAdmissible F ζ hζ R P S W Y) :
    fullShell F ζ hζ R P S V Y = fullShell F ζ hζ R P S W Y := by
  apply Measure.ext
  intro E hE
  rw [CrossLevelProof.fullShell_apply F ζ hζ R P S V Y hV E hE,
    CrossLevelProof.fullShell_apply F ζ hζ R P S W Y hW E hE,
    CrossLevelProof.testUnion_eq F ζ hζ R P S V W Y hV hW E]

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
