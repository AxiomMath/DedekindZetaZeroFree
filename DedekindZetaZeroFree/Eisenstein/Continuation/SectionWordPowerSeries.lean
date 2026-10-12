module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ArchimedeanJetSeries
public import DedekindZetaZeroFree.Eisenstein.Induction.SmoothSections.AutomorphicLift

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open KPContActualCommonDiskRightHolomorphy KPContSectorSmoothFramesSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def sectionLift : smoothSections F ζ hζ U R P H →ₗ[ℂ] space F ζ hζ :=
  ((ActualSectionLift.scalarLift F ζ hζ U R P H).comp
    (smoothSections F ζ hζ U R P H).subtype).codRestrict (space F ζ hζ)
    (fun u => ActualSectionLift.lift_arch_smooth F ζ hζ U R P H u)

def sectionWord (w : List (Fin (groupDimension F))) :
    smoothSections F ζ hζ U R P H →ₗ[ℂ] space F ζ hζ :=
  (word F ζ hζ w).comp (sectionLift F ζ hζ U R P H)

theorem sectionWord_series
    (W : ℂ → smoothSections F ζ hζ U R P H)
    (b : ℕ → smoothSections F ζ hζ U R P H) (c : ℂ) (ρ : ℝ)
    (hseries : CoherentSeries F ζ hζ U R P H W b c ρ)
    (w : List (Fin (groupDimension F))) :
    KPGlobalEisensteinData.SmoothPowerSeriesOn (jets F ζ hζ) c ρ
      (fun n => sectionWord F ζ hζ U R P H w (b n))
      (fun s => sectionWord F ζ hζ U R P H w (W s)) := by
  intro i r hr hrρ ε hε
  let X : Set (ArchCoordinates F) := (fun p : Observation F => p.1.val) '' i.compact
  have hX : IsCompact X := i.isCompact.image (by fun_prop)
  have hXd : X ⊆ archDomain F := by
    rintro _ ⟨p,_,rfl⟩
    exact p.1.property
  have hcont : ContinuousOn (fun p : Observation F => ∏ j : Fin i.operator.2, ‖p.2 j.val‖) i.compact := by
    fun_prop
  obtain ⟨B,hB⟩ := i.isCompact.exists_bound_of_continuousOn hcont
  let A := max 0 B
  have hA : 0 ≤ A := le_max_left _ _
  let δ := ε / (A + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := ActualCoherentSpatialSeries.coherentSeries_moving_jets
    F ζ hζ U R P H W b c ρ hseries {i.operator.1} isCompact_singleton X hX hXd
    [(1,w)] i.operator.2 r hr hrρ δ hδ
  refine ⟨N, ?_⟩
  intro M hM s hs
  let u := (∑ j ∈ Finset.range M, (s-c)^j • b j) - W s
  have heq : (∑ j ∈ Finset.range M, (s-c)^j • sectionWord F ζ hζ U R P H w (b j)) -
      sectionWord F ζ hζ U R P H w (W s) = sectionWord F ζ hζ U R P H w u := by
    change _ = (sectionWord F ζ hζ U R P H w)
      ((∑ j ∈ Finset.range M, (s-c)^j • b j) - W s)
    have hh := (sectionWord F ζ hζ U R P H w).map_sub
      (∑ j ∈ Finset.range M, (s-c)^j • b j) (W s)
    rw [hh]
    congr 1
    exact (map_sum (sectionWord F ζ hζ U R P H w) _ _).trans
      (Finset.sum_congr rfl (fun j _ => (sectionWord F ζ hζ U R P H w).map_smul _ _)) |>.symm
  rw [heq]
  apply lt_of_le_of_lt (show KPGlobalEisensteinData.smoothSeminorm (jets F ζ hζ) i
      (sectionWord F ζ hζ U R P H w u) ≤ δ * A from ?_) ?_
  · apply (ContinuousMap.norm_le _ (mul_nonneg hδ.le hA)).mpr
    intro p
    have ht := hN M hM s hs i.operator.1 (Set.mem_singleton _) p.val.1.val
      ⟨p.val,p.property,rfl⟩
    have ht' : ‖iteratedFDeriv ℝ i.operator.2
        (fun x => (sectionWord F ζ hζ U R P H w u).val
          (i.operator.1 * archChart F ζ hζ x)) p.val.1.val‖ < δ := by
      change ‖iteratedFDeriv ℝ i.operator.2
        (fun x => actualRightWord F ζ hζ w (lift F ζ hζ U R P H u.val)
          (i.operator.1 * archChart F ζ hζ x)) p.val.1.val‖ < δ
      simpa only [u, rightCombination, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, one_mul, add_zero] using ht
    have hprod : (∏ j : Fin i.operator.2, ‖p.val.2 j.val‖) ≤ A := by
      have hb := hB p.val p.property
      exact (le_abs_self _).trans (hb.trans (le_max_right _ _))
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans
      (mul_le_mul ht'.le hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hδ.le)
  · have he : δ * (A+1) = ε := by dsimp [δ]; field_simp
    nlinarith

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries

end
