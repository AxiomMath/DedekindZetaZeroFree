module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.MovingCompactCharts
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff Matrix.Norms.Elementwise

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingLocal

open KPContLocalNorm

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

set_option backward.isDefEq.respectTransparency false in
private theorem partial_jets_smooth
    {A E B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : A × E → B) (S : Set (A × E)) (hS : IsOpen S)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f S) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : A × E => iteratedFDeriv ℝ n (fun y => f (p.1,y)) p.2) S := by
  induction n with
  | zero => simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E B).symm.contDiff.comp_contDiffOn hf
  | succ n ih =>
    intro p hp
    let J := fun q : A × E => iteratedFDeriv ℝ n (fun y => f (q.1,y)) q.2
    have hJ : ContDiffAt ℝ (⊤ : ℕ∞) J p := ih.contDiffAt (hS.mem_nhds hp)
    have hJJ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : (A × E) × E => J (q.1.1,q.2)) (p,p.2) := by
      simpa only [Function.comp_def] using hJ.comp (p,p.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hD : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : A × E => fderiv ℝ (fun y => J (q.1,y)) q.2) p :=
      hJJ.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, J] using
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) B).symm.contDiff.comp_contDiffAt p hD).contDiffWithinAt

private lemma domain_open : IsOpen (archDomain F) := by
  have he : archDomain F = ⋂ w, {x : ArchCoordinates F | x w 1 ≠ 0} := by
    ext x; simp [archDomain]
  rw [he]
  exact isOpen_iInter_of_finite (fun _ => isOpen_ne_fun (by fun_prop) continuous_const)

private lemma actual_split :
    ∃ e : (KPSmoothLocalQuotientCharts.ArchGroup F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* G F ζ hζ,
      ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c := by
  have hsub := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ
  have hh := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  rw [hsub] at hh
  obtain ⟨e,he,_⟩ := hh
  exact ⟨e,he⟩

open scoped Manifold

 def archParam (y : ArchCoordinates F) : KPSmoothLocalQuotientCharts.ArchGroup F :=
  fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (y w))

private lemma param_split
    (e : (KPSmoothLocalQuotientCharts.ArchGroup F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* G F ζ hζ)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c)
    (y : ArchCoordinates F) : e.symm (archChart F ζ hζ y) = (archParam F y,1) := by
  apply e.injective
  rw [e.apply_symm_apply, he, Subgroup.coe_one, mul_one]
  exact KPLiteralChamber.right_insertion F ζ hζ y

private lemma param_continuous (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : ContinuousOn (archParam F) (archDomain F) := by
  obtain ⟨e,he⟩ := actual_split F ζ hζ
  have hc := (continuous_fst.comp e.symm.continuous).comp_continuousOn
    (ActualMovingCompact.archChart_continuousOn F ζ hζ)
  exact hc.congr (fun y _ => congrArg Prod.fst (param_split F ζ hζ e he y).symm)

private lemma target_mk (M : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Matrix.ProjGenLinGroup.mk M ∈ PGLComplex.affineTarget ↔ M.val 0 0 ≠ 0 := by
  obtain ⟨z,hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp
    ((Quotient.out_eq (Matrix.ProjGenLinGroup.mk M)).symm)
  change (Matrix.ProjGenLinGroup.mk M).out.val 0 0 ≠ 0 ↔ _
  rw [← hz]
  simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal]

set_option backward.isDefEq.respectTransparency false in
private lemma param_smooth (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    letI := KPContActualSphericalRightFieldIdentification.actualLieChartedSpace F
    ContMDiffOn (𝓘(ℝ, ArchCoordinates F)) (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (⊤ : ℕ∞) (archParam F) (archDomain F) := by
  letI := KPContActualSphericalRightFieldIdentification.actualLieChartedSpace F
  intro x hx
  have hc : ContinuousAt (archParam F) x := (param_continuous F ζ hζ).continuousAt ((domain_open F).mem_nhds hx)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff.mpr
  refine ⟨hc,?_⟩
  have hchart (a : KPSmoothLocalQuotientCharts.ArchGroup F) :
      chartAt (KPSmoothLocalQuotientCharts.Coordinates F) a =
        (LocalQuotientCharts.ExponentialHaarFrame.rawAffineChart F a).symm :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F)))).2.2 a
  have hraw (a b : KPSmoothLocalQuotientCharts.ArchGroup F) :
      (LocalQuotientCharts.ExponentialHaarFrame.rawAffineChart F a).symm b =
        (LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F).symm
          ((PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F))
            (fun w => PGLComplex.affineChart.symm ((a w)⁻¹ * b w))) := rfl
  have hd : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ArchCoordinates F => fun w => PGLComplex.affineChart.symm
        ((archParam F x w)⁻¹ * archParam F y w)) x := by
    apply contDiffAt_pi.mpr
    intro w
    let a := (archParam F x w).out
    let M : ArchCoordinates F → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
      fun y => a⁻¹ * KPLiteralChamber.rightMatrix (y w)
    have hM (y) : Matrix.ProjGenLinGroup.mk (M y) = (archParam F x w)⁻¹ * archParam F y w := by
      simp only [M, map_mul, map_inv]
      rw [show Matrix.ProjGenLinGroup.mk a = archParam F x w from Quotient.out_eq _]
      rfl
    have ht : Matrix.ProjGenLinGroup.mk (M x) ∈ PGLComplex.affineTarget := by
      rw [hM]; simpa using PGLComplex.one_mem_affineTarget
    have hden : (M x).val 0 0 ≠ 0 := (target_mk _).mp ht
    let m : ArchCoordinates F → Matrix (Fin 2) (Fin 2) ℂ := fun y =>
      a⁻¹.val * !![y w 1 + y w 0 * y w 2, y w 0; y w 2, 1]
    have hm : ContDiff ℝ (⊤ : ℕ∞) m := by
      apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro j
      simp only [m, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases j <;> simp <;> fun_prop
    have hme : ∀ᶠ y in 𝓝 x, (M y).val = m y := by
      filter_upwards [(domain_open F).mem_nhds hx] with y hy
      simp only [M, Units.val_mul, m, KPLiteralChamber.rightMatrix_val _ (hy w)]
    have hmx : m x = (M x).val := hme.self_of_nhds.symm
    have hrat : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => PGLComplex.matrixRatios (m y)) x :=
      (PGLComplex.contDiffAt_matrixRatios _ (hmx ▸ hden)).comp x hm.contDiffAt
    apply hrat.congr_of_eventuallyEq
    have hmt : ∀ᶠ y in 𝓝 x, Matrix.ProjGenLinGroup.mk (M y) ∈ PGLComplex.affineTarget := by
      have hc' : ContinuousAt (fun y => (archParam F x w)⁻¹ * archParam F y w) x :=
        continuousAt_const.mul ((continuous_apply w).continuousAt.comp hc)
      have hh := hc'.preimage_mem_nhds (PGLComplex.affineChart.open_target.mem_nhds
        (by rw [PGLComplex.affineChart_target]; simpa using PGLComplex.one_mem_affineTarget))
      filter_upwards [hh] with y hy
      simpa only [hM, PGLComplex.affineChart_target, Set.mem_preimage] using hy
    filter_upwards [hme,hmt] with y hy hyt
    rw [← hM, PGLComplex.affineChart_symm_apply _ hyt, PGLComplex.matrixRatios_mk, hy]
  have hfinal := (LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F).symm.contDiff.comp_contDiffAt x
    ((PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).contDiff.comp_contDiffAt x hd)
  have hself {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
      (𝓘(ℝ,V)).toPartialEquiv = PartialEquiv.refl V := by ext <;> rfl
  simp only [extChartAt, OpenPartialHomeomorph.extend, hself, PartialEquiv.trans_refl,
    chartAt_self_eq, hchart]
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y => (LocalQuotientCharts.ExponentialHaarFrame.rawAffineChart F (archParam F x)).symm
      (archParam F y)) _ x
  simpa only [hraw, Function.comp_def] using hfinal.contDiffWithinAt

theorem moving_inverse_local (g : G F ζ hζ) (x : ArchCoordinates F)
    (hx : x ∈ archDomain F) :
    ∃ e : (KPSmoothLocalQuotientCharts.ArchGroup F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* G F ζ hζ,
      (∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c) ∧
    ∃ Q : KPContActualSphericalRightFieldIdentification.GroupChart F ζ hζ U R P H,
    ∃ W : Set (G F ζ hζ × ArchCoordinates F), IsOpen W ∧ (g,x) ∈ W ∧
      W ⊆ Set.univ ×ˢ archDomain F ∧
    ∃ τ : G F ζ hζ × ArchCoordinates F → Space (KPContActualSphericalRightFieldIdentification.groupDimension F),
      (∀ p, τ p = (KPContActualSphericalRightFieldIdentification.groupCoordinates F).symm
        (Q.exponential.chart.symm (e.symm (p.1 * archChart F ζ hζ p.2)).1)) ∧
      τ (g,x) = 0 ∧ ContinuousOn τ W ∧ Set.MapsTo τ W Q.T.carrier ∧
      (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => τ (a,y)) {y | (a,y) ∈ W}) ∧
      (∀ n, ContinuousOn (fun p : G F ζ hζ × ArchCoordinates F =>
        iteratedFDeriv ℝ n (fun y => τ (p.1,y)) p.2) W) ∧
      ∀ p ∈ W, ∃ v : U.toOpenSubgroup,
        p.1 * archChart F ζ hζ p.2 = Q.groupLift (τ p) *
          ((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨e,he⟩ := actual_split F ζ hζ
  let b := e.symm (g * archChart F ζ hζ x)
  obtain ⟨Q,hQ⟩ := KPContActualSphericalRightFieldIdentification.chart_at_split F ζ hζ U R P H b.1 b.2
  obtain ⟨O,hO,hOi⟩ := Q.inverse_smooth
  have hOf (y) : O y = Q.exponential.chart y := congrArg (fun E => E y) hO
  have hOif (a) : O.symm a = Q.exponential.chart.symm a := congrArg (fun E => E.symm a) hO
  let c := KPContActualSphericalRightFieldIdentification.groupCoordinates F
  let τ : G F ζ hζ × ArchCoordinates F → Space (KPContActualSphericalRightFieldIdentification.groupDimension F) :=
    fun p => c.symm (O.symm (e.symm (p.1 * archChart F ζ hζ p.2)).1)
  let f : G F ζ hζ × ArchCoordinates F → G F ζ hζ := fun p => p.1 * archChart F ζ hζ p.2
  let D : Set (G F ζ hζ × ArchCoordinates F) := Set.univ ×ˢ archDomain F
  have hD : IsOpen D := isOpen_univ.prod (domain_open F)
  have hf : ContinuousOn f D := continuous_fst.continuousOn.mul
    ((ActualMovingCompact.archChart_continuousOn F ζ hζ).comp continuous_snd.continuousOn
      (fun _ hp => hp.2))
  have hsource : c '' Q.T.carrier ⊆ O.source := by
    rintro _ ⟨t,ht,rfl⟩
    simpa only [← hO] using Q.closure_source ⟨t,subset_closure ht,rfl⟩
  let A := O '' (c '' Q.T.carrier)
  have hA : IsOpen A := O.isOpen_image_of_subset_source
    (c.toHomeomorph.isOpenMap _ Metric.isOpen_ball) hsource
  let L := (Homeomorph.mulLeft Q.finiteRepresentative) '' (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
  have hL : IsOpen L := (Homeomorph.mulLeft Q.finiteRepresentative).isOpenMap _ U.toOpenSubgroup.isOpen
  let W := D ∩ f ⁻¹' (e '' (A ×ˢ L))
  have hW : IsOpen W := hf.isOpen_inter_preimage hD (e.toHomeomorph.isOpenMap _ (hA.prod hL))
  have hb : e (O (c 0), Q.finiteRepresentative) = e b := by
    rw [he, hOf]
    change Q.groupLift 0 = e b
    exact hQ.trans (he b.1 b.2).symm
  have hb' : (O (c 0), Q.finiteRepresentative) = b := e.injective hb
  have hWgx : (g,x) ∈ W := by
    refine ⟨⟨Set.mem_univ _,hx⟩, ?_⟩
    refine ⟨(O (c 0),Q.finiteRepresentative),⟨?_,?_⟩,?_⟩
    · exact ⟨c 0,⟨0,Q.zero_mem,rfl⟩,rfl⟩
    · exact ⟨1,U.toOpenSubgroup.one_mem,mul_one _⟩
    · rw [hb]; exact e.apply_symm_apply _
  have hτ0 : τ (g,x) = 0 := by
    change c.symm (O.symm b.1) = 0
    rw [← hb']
    rw [O.left_inv (hsource ⟨0,Q.zero_mem,rfl⟩), c.symm_apply_apply]
  have hτmap : Set.MapsTo τ W Q.T.carrier := by
    rintro p ⟨_,z,hz,hzp⟩
    obtain ⟨a,⟨t,ht,rfl⟩,ha⟩ := hz.1
    have hep : (e.symm (f p)).1 = O (c t) := by rw [← hzp, e.symm_apply_apply]; exact ha.symm
    change c.symm (O.symm (e.symm (f p)).1) ∈ Q.T.carrier
    rw [hep, O.left_inv (hsource ⟨t,ht,rfl⟩), c.symm_apply_apply]
    exact ht
  have hτcont : ContinuousOn τ W := by
    apply c.symm.continuous.comp_continuousOn
    apply O.symm.continuousOn.comp
    · exact (continuous_fst.comp e.symm.continuous).continuousOn.comp (hf.mono Set.inter_subset_left)
        (fun _ _ => Set.mem_univ _)
    · rintro p ⟨_,z,hz,hzp⟩
      obtain ⟨a,ha,ha'⟩ := hz.1
      have hep : (e.symm (f p)).1 = O a := by rw [← hzp, e.symm_apply_apply]; exact ha'.symm
      change (e.symm (f p)).1 ∈ O.target
      rw [hep]
      exact O.map_source (hsource ha)
  have hfactor : ∀ p ∈ W, ∃ v : U.toOpenSubgroup,
      p.1 * archChart F ζ hζ p.2 = Q.groupLift (τ p) *
        ((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ) := by
    rintro p ⟨_,⟨a,k⟩,⟨ha,hk⟩,hepk⟩
    obtain ⟨z,⟨t,ht,rfl⟩,rfl⟩ := ha
    obtain ⟨v,hv,rfl⟩ := hk
    refine ⟨⟨v,hv⟩,?_⟩
    have hτ : τ p = t := by
      change c.symm (O.symm (e.symm (f p)).1) = t
      rw [← hepk, e.symm_apply_apply, O.left_inv (hsource ⟨t,ht,rfl⟩), c.symm_apply_apply]
    rw [hτ]
    change f p = Q.groupLift t * (v : G F ζ hζ)
    rw [← hepk, he]
    simp only [KPContActualSphericalRightFieldIdentification.GroupChart.groupLift,
      Subgroup.coe_mul, mul_assoc, hOf, c]
    rfl
  refine ⟨e,he,Q,W,hW,hWgx,Set.inter_subset_left,τ,?_,hτ0,hτcont,hτmap,?_,?_,hfactor⟩
  · intro p; simp only [τ, c, hOif]
  · letI := KPContActualSphericalRightFieldIdentification.actualLieChartedSpace F
    letI := KPContActualSphericalRightFieldIdentification.actualLieGroup F
    intro a y hy
    have heq (z) : (e.symm (a * archChart F ζ hζ z)).1 = (e.symm a).1 * archParam F z := by
      rw [map_mul, param_split F ζ hζ e he]; rfl
    have hin : (e.symm (f (a,y))).1 ∈ O.target := by
      obtain ⟨z,hz,hzp⟩ := hy.2
      obtain ⟨b,hb,hba⟩ := hz.1
      rw [← hzp, e.symm_apply_apply, ← hba]
      exact O.map_source (hsource hb)
    have hp : ContMDiffAt (𝓘(ℝ, ArchCoordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
        (fun z => (e.symm a).1 * archParam F z) y :=
      contMDiffAt_const.mul ((param_smooth F ζ hζ).contMDiffAt ((domain_open F).mem_nhds hy.1.2))
    have hi := hOi.contMDiffAt (O.open_target.mem_nhds (by simpa only [f,heq] using hin))
    have hh := (hi.comp y hp).contDiffAt
    simpa only [τ, Function.comp_def, heq] using (c.symm.contDiff.comp_contDiffAt y hh).contDiffWithinAt
  · letI := KPContActualSphericalRightFieldIdentification.actualLieChartedSpace F
    letI := KPContActualSphericalRightFieldIdentification.actualLieGroup F
    intro n p hp
    let ρ : G F ζ hζ → KPSmoothLocalQuotientCharts.ArchGroup F := fun a => (e.symm a).1
    have hρ : Continuous ρ := continuous_fst.comp e.symm.continuous
    have heq (a) (z) : (e.symm (a * archChart F ζ hζ z)).1 = ρ a * archParam F z := by
      rw [map_mul, param_split F ζ hζ e he]; rfl
    let E := chartAt (KPSmoothLocalQuotientCharts.Coordinates F) (ρ p.1)
    have hEp : ρ p.1 ∈ E.source := mem_chart_source _ _
    let J : KPSmoothLocalQuotientCharts.Coordinates F × ArchCoordinates F → Space (KPContActualSphericalRightFieldIdentification.groupDimension F) :=
      fun q => c.symm (O.symm (E.symm q.1 * archParam F q.2))
    let S : Set (KPSmoothLocalQuotientCharts.Coordinates F × ArchCoordinates F) :=
      (E.target ×ˢ archDomain F) ∩ {q | E.symm q.1 * archParam F q.2 ∈ O.target}
    have hS : IsOpen S := by
      have hc : ContinuousOn (fun q : KPSmoothLocalQuotientCharts.Coordinates F × ArchCoordinates F =>
          E.symm q.1 * archParam F q.2) (E.target ×ˢ archDomain F) :=
        (E.symm.continuousOn.comp continuous_fst.continuousOn (fun _ h => h.1)).mul
          ((param_continuous F ζ hζ).comp continuous_snd.continuousOn (fun _ h => h.2))
      exact hc.isOpen_inter_preimage (E.open_target.prod (domain_open F)) O.open_target
    have hJ : ContDiffOn ℝ (⊤ : ℕ∞) J S := by
      intro q hq
      have hE : ContMDiffAt (𝓘(ℝ,KPSmoothLocalQuotientCharts.Coordinates F))
          (𝓘(ℝ,KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) E.symm q.1 :=
        contMDiffOn_chart_symm.contMDiffAt (E.open_target.mem_nhds hq.1.1)
      have hP := (param_smooth F ζ hζ).contMDiffAt ((domain_open F).mem_nhds hq.1.2)
      have hmul := (hE.comp q contDiffAt_fst.contMDiffAt).mul (hP.comp q contDiffAt_snd.contMDiffAt)
      have hi := hOi.contMDiffAt (O.open_target.mem_nhds hq.2)
      exact (c.symm.contDiff.comp_contDiffAt q ((hi.comp q hmul).contDiffAt)).contDiffWithinAt
    let ψ : G F ζ hζ × ArchCoordinates F → KPSmoothLocalQuotientCharts.Coordinates F × ArchCoordinates F :=
      fun q => (E (ρ q.1),q.2)
    have hψ : ContinuousAt ψ p := by
      have hr : ContinuousAt (fun q : G F ζ hζ × ArchCoordinates F => ρ q.1) p :=
        hρ.continuousAt.comp continuousAt_fst
      have hcE : ContinuousAt E (ρ p.1) := E.continuousOn.continuousAt (E.open_source.mem_nhds hEp)
      exact (hcE.comp (f := fun q : G F ζ hζ × ArchCoordinates F => ρ q.1) hr).prodMk continuousAt_snd
    have hin : ρ p.1 * archParam F p.2 ∈ O.target := by
      obtain ⟨z,hz,hzp⟩ := hp.2
      obtain ⟨b,hb,hba⟩ := hz.1
      have hh : (e.symm (f p)).1 ∈ O.target := by
        rw [← hzp, e.symm_apply_apply, ← hba]
        exact O.map_source (hsource hb)
      simpa only [f, heq] using hh
    have hψS : ψ p ∈ S := by
      refine ⟨⟨E.map_source (mem_chart_source _ _),hp.1.2⟩,?_⟩
      change E.symm (E (ρ p.1)) * archParam F p.2 ∈ O.target
      rw [E.left_inv hEp]
      exact hin
    have hj := (partial_jets_smooth J S hS hJ n).continuousOn.continuousAt (hS.mem_nhds hψS)
    have hcomp := hj.comp hψ
    have hn : ∀ᶠ q in 𝓝 p, ρ q.1 ∈ E.source :=
      (hρ.continuousAt.comp continuousAt_fst).preimage_mem_nhds
        (E.open_source.mem_nhds (mem_chart_source _ _))
    have hn' : ∀ᶠ q in 𝓝 p,
        iteratedFDeriv ℝ n (fun y => τ (q.1,y)) q.2 =
          iteratedFDeriv ℝ n (fun y => J ((ψ q).1,y)) (ψ q).2 := by
      filter_upwards [hn] with q hq
      have hefun : (fun y => τ (q.1,y)) = (fun y => J ((ψ q).1,y)) := by
        funext y
        simp only [τ, J, ψ, heq, E.left_inv hq]
      rw [hefun]
    exact (hcomp.congr_of_eventuallyEq hn').continuousWithinAt

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingLocal

end
