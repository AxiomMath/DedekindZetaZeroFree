module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspDisintegration.AngularKernelsAndLevelCompatibility

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsFixedHaar.WeightedSectionGlobalization

open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming weighted_section_measure → weighted_section_measure
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming angular_measurable → angular_measurable
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming cross_section_inclusion_measurable → cross_section_inclusion_measurable
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming actualCuspLabel → actualCuspLabel
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming actualCuspLabel_preimage → actualCuspLabel_preimage
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming cuspCorrection → cuspCorrection
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming coarseLabel_mem → coarseLabel_mem
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming actual_weighted_pinned_cusp_degree_balance → actual_weighted_pinned_cusp_degree_balance
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming actual_label_transition → actual_label_transition
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming actual_transition_degree → actual_transition_degree
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming cuspCorrection_formula → cuspCorrection_formula
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming pinned_cusp_chart → pinned_cusp_chart
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming pinned_cusp_chart_formula → pinned_cusp_chart_formula

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.NormOneTransition renaming crossCoordinate_continuous → crossCoordinate_continuous

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
  {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}

structure ComponentMatching (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) where
  component : Fin AV.componentCount → Fin AU.componentCount
  rational : Fin AV.componentCount → KPCuspArithmetic.PGL2 F
  central : Fin AV.componentCount → rootsOfUnity 3 F
  level : Fin AV.componentCount → U.toOpenSubgroup
  formula : ∀ i, AU.representative (component i) =
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (rational i) *
      KPCuspGenuineMonodromy.central F ζ hζ (central i) * AV.representative i * level i

variable {AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V}
  {AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}

abbrev weightedSectionMeasure (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (w : Fin A.componentCount → ℝ≥0∞) : Measure (CrossSection A) :=
  weighted_section_measure A w

def cuspLabel (M : ComponentMatching AV AU) : CuspIndex AV → CuspIndex AU :=
  actualCuspLabel AV AU M.component M.rational

def correction (M : ComponentMatching AV AU) (j : CuspIndex AV) :
    KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative (cuspLabel M j).1) :=
  cuspCorrection
    (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative (cuspLabel M j).1))
    ((AU.cuspAtlas (cuspLabel M j).1).cusp (cuspLabel M j).2)
    (M.rational j.1 • (AV.cuspAtlas j.1).cusp j.2)
    (coarseLabel_mem _ _ (AU.cuspAtlas (M.component j.1)).exhaustive _)

def transition (M : ComponentMatching AV AU) (j : CuspIndex AV) :
    KPCuspArithmetic.PGL2 F :=
  ((AU.cuspAtlas (cuspLabel M j).1).representative (cuspLabel M j).2)⁻¹ *
    ((correction M j).val⁻¹ * M.rational j.1) * (AV.cuspAtlas j.1).representative j.2

structure NormOneMatrix (M : ComponentMatching AV AU) (j : CuspIndex AV) where
  matrix : Matrix.GeneralLinearGroup (Fin 2) F
  ratio : Fˣ
  upper : (matrix : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  ratio_formula : (matrix : Matrix (Fin 2) (Fin 2) F) 0 0 =
    (ratio : F) * (matrix : Matrix (Fin 2) (Fin 2) F) 1 1
  projective_formula : Matrix.ProjGenLinGroup.mk matrix = transition M j
  sum_log_zero : ∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ((KPCusp.complexPlace F i) (ratio : F)) = 0

 theorem transition_properties
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (j : CuspIndex AV) :
    let S := KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1))
      ((AV.cuspAtlas j.1).cusp j.2) ((AV.cuspAtlas j.1).representative j.2)
    let k := cuspLabel M j
    let T := KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1))
      ((AU.cuspAtlas k.1).cusp k.2) ((AU.cuspAtlas k.1).representative k.2)
    S.map (MulAut.conj (transition M j)).toMonoidHom ≤ T ∧
      ((S.map (MulAut.conj (transition M j)).toMonoidHom).subgroupOf T).FiniteIndex := by
  exact (actual_label_transition h AV AU M.component M.rational M.central M.level M.formula j).2

private theorem sum_sigma_fiber {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    {B : I → Type*} [∀ i, Fintype (B i)] {E : Type*} [AddCommMonoid E]
    (m : I → K) (k : K) (p : ∀ i, B i → Prop) [∀ i, DecidablePred (p i)]
    (f : (Σ i, B i) → E) :
    (∑ j : (Σ i, B i), if m j.1 = k ∧ p j.1 j.2 then f j else 0) =
      ∑ i : {i : I // m i = k}, ∑ b : {b : B i.val // p i.val b}, f ⟨i.val,b.val⟩ := by
  classical
  rw [Fintype.sum_sigma]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => m i = k)) (by simp)
    (fun i => ∑ b : {b : B i // p i b}, f ⟨i,b.val⟩), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : m i = k
  · simp only [hi, true_and, if_true]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter (p i)) (by simp) (fun b => f ⟨i,b⟩)
  · simp [hi]

private theorem cuspLabel_eq_iff (M : ComponentMatching AV AU)
    (i : Fin AV.componentCount) (b : Fin (AV.cuspAtlas i).cuspCount)
    (k : Fin AU.componentCount) (a : Fin (AU.cuspAtlas k).cuspCount) :
    cuspLabel M ⟨i,b⟩ = ⟨k,a⟩ ↔ M.component i = k ∧
      M.rational i • (AV.cuspAtlas i).cusp b ∈
        MulAction.orbit (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k))
          ((AU.cuspAtlas k).cusp a) := by
  constructor
  · intro he
    have hk : M.component i = k := congrArg Sigma.fst he
    subst k
    exact ⟨rfl, (actualCuspLabel_preimage AV AU M.component M.rational i a b).mp he⟩
  · rintro ⟨hk,hb⟩
    subst k
    exact (actualCuspLabel_preimage AV AU M.component M.rational i a b).mpr hb

def degree (M : ComponentMatching AV AU) (j : CuspIndex AV) : ℕ :=
  ((KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1))
    ((AV.cuspAtlas j.1).cusp j.2) ((AV.cuspAtlas j.1).representative j.2)).map
      (MulAut.conj (transition M j)).toMonoidHom).relIndex
    (KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative (cuspLabel M j).1))
      ((AU.cuspAtlas (cuspLabel M j).1).cusp (cuspLabel M j).2)
      ((AU.cuspAtlas (cuspLabel M j).1).representative (cuspLabel M j).2))

private theorem degree_eq_shifted (M : ComponentMatching AV AU) (j : CuspIndex AV) :
    degree M j =
      (((KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1)).map
        (MulAut.conj (M.rational j.1)).toMonoidHom) ⊓
          MulAction.stabilizer (KPCuspArithmetic.PGL2 F)
            (M.rational j.1 • (AV.cuspAtlas j.1).cusp j.2)).relIndex
      ((KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative (M.component j.1))) ⊓
          MulAction.stabilizer (KPCuspArithmetic.PGL2 F)
            (M.rational j.1 • (AV.cuspAtlas j.1).cusp j.2)) := by
  exact actual_transition_degree _ _ _ _ _ _ _ (correction M j)
    (cuspCorrection_formula _ _ _ _)

theorem exists_matching_degree_balance
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P) :
    ∃ M : ComponentMatching AV AU, ∀ k : CuspIndex AU,
      (∑ j : CuspIndex AV, if cuspLabel M j = k then
        DV.componentWeight j.1 * (degree M j : ℝ≥0∞) else 0) = DU.componentWeight k.1 := by
  obtain ⟨m,δ,ε,u,hc,hbal⟩ := actual_weighted_pinned_cusp_degree_balance R P h AV AU DV DU
  let M : ComponentMatching AV AU := ⟨m,δ,ε,u,hc⟩
  refine ⟨M,?_⟩
  rintro ⟨k,a⟩
  change (∑ j : CuspIndex AV, if cuspLabel M ⟨j.1,j.2⟩ = ⟨k,a⟩ then
    DV.componentWeight j.1 * (degree M j : ℝ≥0∞) else 0) = _
  simp_rw [cuspLabel_eq_iff]
  rw [sum_sigma_fiber M.component k
    (fun i b => M.rational i • (AV.cuspAtlas i).cusp b ∈
      MulAction.orbit (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k))
        ((AU.cuspAtlas k).cusp a))
    (fun j => DV.componentWeight j.1 * (degree M j : ℝ≥0∞))]
  convert hbal k a using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [degree_eq_shifted]
  rw [actual_transition_degree _ _ _ _ _ _ _ _ (cuspCorrection_formula _ _ _ _)]
  have hi : m i.val = k := i.property
  simp only [M, hi]

 theorem regroup_smul {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    {E : Type*} [AddCommMonoid E] [Module ℝ≥0∞ E]
    (l : I → K) (c : I → ℝ≥0∞) (μ : K → E) :
    (∑ j, c j • μ (l j)) =
      ∑ k, (∑ j, if l j = k then c j else 0) • μ k := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ l (fun j => c j • μ (l j))]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_filter, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

end DedekindZetaZeroFree.KPMsFixedHaar.WeightedSectionGlobalization

end
