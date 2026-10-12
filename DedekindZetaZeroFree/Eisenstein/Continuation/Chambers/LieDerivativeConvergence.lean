module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.AffineLieDifferentiation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.RootDerivatives renaming chamber_value_majorant → chamber_value_majorant
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem generic_chamber_majorant {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1/3 : ℝ) < s.re) (T : Set (G F ζ hζ)) (hT : IsCompact T) :
    ∃ B : KPChamberBruhatTwoCells.RationalQuotient F → ℝ, Summable B ∧
      ∀ c g, g ∈ T → ‖f.val s (rationalLift F ζ hζ (Quotient.out c) * g)‖ ≤ B c := by
  obtain ⟨B,hB,hbound⟩ := KPLiteralChamber.chamber_jet_majorants F ζ hζ
    K hK f {s} isCompact_singleton (by intro z hz; subst z; exact hs) T hT ⟨0,fun i => Fin.elim0 i⟩
  refine ⟨B,hB,?_⟩
  intro c g hg
  have h := hbound c s rfl g hg
  rw [KPLiteralChamber.rightJet_compactExtension_rational_eq] at h
  simpa only [KPLiteralChamber.rightJet, iteratedFDeriv_zero_apply,
    KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] using h

theorem native_chamber_affine {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f v u : Flat F ζ hζ K)
    (b : Fin (groupDimension F))
    (hsource : ∀ s g, actualRight F ζ hζ b (f.val s) g = v.val s g + s * u.val s g)
    (s : ℂ) (hs : (1/3 : ℝ) < s.re) (g : G F ζ hζ) :
    HasDerivAt (fun t => eisenstein F ζ hζ K f s (g * nativeCurve F ζ hζ b t))
      (eisenstein F ζ hζ K v s g + s * eisenstein F ζ hζ K u s g) 0 := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let T := (fun t => g * nativeCurve F ζ hζ b t) '' Metric.closedBall (0 : ℝ) 1
  have hT : IsCompact T := (isCompact_closedBall (0 : ℝ) 1).image
    (continuous_const.mul (nativeCurve_continuous F ζ hζ b))
  obtain ⟨V,hV,hVbound⟩ := generic_chamber_majorant F ζ hζ hK v s hs T hT
  obtain ⟨U,hU,hUbound⟩ := generic_chamber_majorant F ζ hζ hK u s hs T hT
  let term := fun (c : KPChamberBruhatTwoCells.RationalQuotient F) t => f.val s
    (rationalLift F ζ hζ (Quotient.out c) * (g * nativeCurve F ζ hζ b t))
  let dterm := fun (c : KPChamberBruhatTwoCells.RationalQuotient F) t => v.val s
    (rationalLift F ζ hζ (Quotient.out c) * (g * nativeCurve F ζ hζ b t)) +
    s * u.val s (rationalLift F ζ hζ (Quotient.out c) * (g * nativeCurve F ζ hζ b t))
  have hd (c) (t : ℝ) (_ : t ∈ Metric.ball (0 : ℝ) 1) : HasDerivAt (term c) (dterm c t) t := by
    have hh := nativeCurve_hasDerivAt F ζ hζ b (f.val s) (f.property.1 s).1
      (rationalLift F ζ hζ (Quotient.out c) * g) t
    simp only [mul_assoc, hsource] at hh
    exact hh
  have hbound (c) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) : ‖dterm c t‖ ≤ V c + ‖s‖ * U c := by
    have htT : g * nativeCurve F ζ hζ b t ∈ T := ⟨t,Metric.ball_subset_closedBall ht,rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (hVbound c _ htT)
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hUbound c _ htT) (norm_nonneg _)))
  have hsum : Summable (fun c => ‖term c 0‖) := by
    simpa only [term, nativeCurve_zero, mul_one] using
      (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK f s hs g).norm
  have hh := hasDerivAt_tsum_of_isPreconnected (hV.add (hU.mul_left ‖s‖)) Metric.isOpen_ball
    (convex_ball (0 : ℝ) 1).isPreconnected hd hbound (Metric.mem_ball_self (by norm_num))
    hsum.of_norm (Metric.mem_ball_self (by norm_num))
  dsimp [term,dterm] at hh
  simp only [nativeCurve_zero, mul_one] at hh
  rw [Summable.tsum_add (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK v s hs g)
    ((KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK u s hs g).mul_left s), tsum_mul_left] at hh
  exact hh
end DedekindZetaZeroFree.RootDerivatives

end
