module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.SectionSpaces.BoundedLiftingAndDescent

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

private theorem chart_component_eq (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count) :
    ∀ x : E (C.chart i).n,
      M.component ((C.chart i).toBase F ζ hζ hF U x) = (C.chart i).component := by
  intro x
  have h1 : A.components ⟨M.component ((C.chart i).toBase F ζ hζ hF U x),
      KPCuspSiegel.projection F _ (M.lift ((C.chart i).toBase F ζ hζ hF U x))⟩ =
      (C.chart i).toBase F ζ hζ hF U x := by
    rw [A.components_formula]
    exact M.lift_formula _
  have h2 : A.components ⟨(C.chart i).component,
      KPCuspSiegel.projection F _ ((C.chart i).coordinates x)⟩ =
      (C.chart i).toBase F ζ hζ hF U x := by
    rw [A.components_formula]
    rfl
  have := A.components.injective (h1.trans h2.symm)
  exact congrArg Sigma.fst this

private theorem phase_value (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count) (x : E (C.chart i).n)
    (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U)
    (γ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (h1 : M.lift ((C.chart i).toBase F ζ hζ hF U x) = γ • (C.chart i).coordinates x)
    (h2 : A.representative (C.chart i).component =
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ε *
          A.representative (C.chart i).component * (u : KPFiniteCuspAtlas.FiniteCover F ζ hζ)) :
    s.val ((C.chart i).coordinates x, A.representative (C.chart i).component) =
      ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂˣ) : ℂ)⁻¹ *
        (M.representative s ((C.chart i).toBase F ζ hζ hF U x) : ℂ) := by
  have hc := chart_component_eq F ζ hζ hF U A M C i x
  have hsec : (M.representative s ((C.chart i).toBase F ζ hζ hF U x) : ℂ) =
      s.val (M.lift ((C.chart i).toBase F ζ hζ hF U x),
        A.representative (C.chart i).component) := by
    have := M.section_formula s ((C.chart i).toBase F ζ hζ hF U x)
    rw [hc] at this
    exact this
  have hs1 := s.property.1
  have hs2 := s.property.2.1
  have hs3 := s.property.2.2
  have key : s.val (γ • (C.chart i).coordinates x,
        A.representative (C.chart i).component) =
      ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂˣ) : ℂ) *
        s.val ((C.chart i).coordinates x, A.representative (C.chart i).component) := by
    have e1 : s.val (γ • (C.chart i).coordinates x,
        A.representative (C.chart i).component) =
        s.val (γ • (C.chart i).coordinates x,
          KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
            (KPCuspGenuineMonodromy.central F ζ hζ ε *
              (A.representative (C.chart i).component *
                (u : KPFiniteCuspAtlas.FiniteCover F ζ hζ)))) := by
      conv_lhs => rw [h2]
      simp only [mul_assoc]
    rw [e1, hs1]
    rw [hs2, hs3]
  rw [hsec, h1, key, ← mul_assoc,
    inv_mul_cancel₀ (Units.ne_zero ((KPCuspGenuineMonodromy.chi F ζ hζ) ε)), one_mul]

private theorem transition_exists (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count) (x : E (C.chart i).n) :
    ∃ γ : KPCuspGenuineMonodromy.Component F ζ hζ U
      (A.representative (C.chart i).component),
      (γ : KPCuspArithmetic.PGL2 F) • (C.chart i).coordinates x =
        M.lift ((C.chart i).toBase F ζ hζ hF U x) := by
  have hc := chart_component_eq F ζ hζ hF U A M C i x
  have h := M.lift_formula ((C.chart i).toBase F ζ hζ hF U x)
  rw [hc] at h
  have he : A.components ⟨(C.chart i).component,
      KPCuspSiegel.projection F _ (M.lift ((C.chart i).toBase F ζ hζ hF U x))⟩ =
      A.components ⟨(C.chart i).component,
      KPCuspSiegel.projection F _ ((C.chart i).coordinates x)⟩ := by
    simpa only [A.components_formula, Chart.toBase] using h
  have hp := (Sigma.mk.inj (A.components.injective he)).2
  have hq : KPCuspSiegel.projection F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative (C.chart i).component))
      (M.lift ((C.chart i).toBase F ζ hζ hF U x)) =
      KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative (C.chart i).component))
        ((C.chart i).coordinates x) := by
    simpa using hp
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))

private theorem transition_finite (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : Fin A.componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j)) :
    ∃ u : U.toOpenSubgroup, A.representative j =
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ((A.line j).rho γ) *
          A.representative j * (u : KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
  obtain ⟨u, hu⟩ := (A.line j).finite_comparison γ⁻¹
  simp only [Subgroup.coe_inv, map_inv, inv_inv] at hu
  refine ⟨u, ?_⟩
  have hh := congrArg (fun t => KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * t) hu
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh

private theorem arithmetic_smul_continuous (γ : KPCuspArithmetic.PGL2 F) :
    Continuous (fun z : KPCuspGenuineMonodromy.SymmetricSpace F => γ • z) := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  change Continuous (fun z => KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk g) z)
  simp only [KPCuspSiegel.action_mk]
  exact (KPArch.productAction_contDiff _ _).continuous

private theorem measurable_transition (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) (i : Fin C.count) :
    ∃ γ : E (C.chart i).n → KPCuspGenuineMonodromy.Component F ζ hζ U
        (A.representative (C.chart i).component),
      (∀ f : KPCuspGenuineMonodromy.Component F ζ hζ U
        (A.representative (C.chart i).component) → ℂˣ, Measurable (f ∘ γ)) ∧
      ∀ x ∈ (C.chart i).extendedDomain,
        (γ x : KPCuspArithmetic.PGL2 F) • (C.chart i).coordinates x =
          M.lift ((C.chart i).toBase F ζ hζ hF U x) := by
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by unfold Matrix; infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  let S := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative (C.chart i).component)
  obtain ⟨e, he⟩ := exists_surjective_nat S
  let D := (C.chart i).extendedDomain
  have hd : MeasurableSet D := (C.chart i).open_extendedDomain.measurableSet
  have hz : Continuous (fun x : D => (C.chart i).coordinates x) :=
    (C.chart i).smooth_coordinates.continuousOn.restrict
  have hb : Measurable (fun x : D => (C.chart i).toBase F ζ hζ hF U x) := by
    have hh := A.components.continuous.comp (continuous_sigmaMk (i := (C.chart i).component))
    have hm : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
        (A.representative (C.chart i).component)) := by
      simpa only [Function.comp_def, A.components_formula] using hh
    exact (hm.comp (continuous_quot_mk.comp hz)).measurable
  let p (x : D) (n : ℕ) := (e n : KPCuspArithmetic.PGL2 F) • (C.chart i).coordinates x =
    M.lift ((C.chart i).toBase F ζ hζ hF U x)
  have hp : ∀ x, ∃ n, p x n := by
    intro x
    obtain ⟨g, hg⟩ := transition_exists F ζ hζ hF U A M C i x
    obtain ⟨n, rfl⟩ := he g
    exact ⟨n, hg⟩
  have hm : ∀ n, MeasurableSet {x : D | p x n} := fun n =>
    measurableSet_eq_fun ((arithmetic_smul_continuous F (e n)).comp hz).measurable
      (M.measurable_lift.comp hb)
  let g : D → S := fun x => e (Nat.find (hp x))
  let γ : E (C.chart i).n → S := fun x => if hx : x ∈ D then g ⟨x, hx⟩ else 1
  refine ⟨γ, ?_, ?_⟩
  · intro f
    apply measurable_of_restrict_of_restrict_compl hd
    · have hg : Measurable (fun x : D => f (g x)) :=
        (measurable_of_countable (fun n => f (e n))).comp (measurable_find hp hm)
      have hh : D.domRestrict (f ∘ γ) = (fun x : D => f (g x)) := by
        funext x
        simp only [Set.domRestrict, Function.comp_def, γ, dif_pos x.property]
      rw [hh]; exact hg
    · have hh : (Dᶜ.domRestrict (f ∘ γ)) = fun _ => f 1 := by
        funext x
        simp only [Set.domRestrict, Function.comp_def, γ, dif_neg x.property]
      rw [hh]; exact measurable_const
  · intro x hx
    change (γ x : KPCuspArithmetic.PGL2 F) • (C.chart i).coordinates x = _
    dsimp only [γ]
    rw [dif_pos hx]
    exact Nat.find_spec (hp ⟨x, hx⟩)

theorem frame_comparison (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) {K : Set (X F ζ hζ U)}
    (C : FiniteCutoffs F ζ hζ hF U A K) :
    Nonempty (FrameComparison F ζ hζ hF U A M C) := by
  choose γ hmeas hγ using measurable_transition F ζ hζ hF U A M C
  let phase : ∀ i, E (C.chart i).n → ℂˣ := fun i x =>
    ((KPCuspGenuineMonodromy.chi F ζ hζ) ((A.line (C.chart i).component).rho (γ i x)))⁻¹
  have hframe : ∀ i x, x ∈ (C.chart i).extendedDomain → ∀ a : V F ζ hζ U,
      (C.chart i).toLine F ζ hζ hF U x ((phase i x : ℂ) • a) =
        M.frame ((C.chart i).toBase F ζ hζ hF U x) a := by
    intro i x hx a
    rw [M.frame_formula, chart_component_eq F ζ hζ hF U A M C i x]
    unfold Chart.toLine
    apply congrArg (Sigma.mk (C.chart i).component)
    apply Quotient.sound
    refine ⟨γ i x, (hγ i x hx).symm, ?_⟩
    change (a : ℂ) = _ * ((phase i x : ℂ) * (a : ℂ))
    simp [phase, ← mul_assoc]
  refine ⟨{
    phase := phase
    measurable_phase := fun i => hmeas i (fun g =>
      ((KPCuspGenuineMonodromy.chi F ζ hζ) ((A.line (C.chart i).component).rho g))⁻¹)
    unitary_phase := fun i x => by
      simp only [phase, Units.val_inv_eq_inv_val, norm_inv,
        (A.line (C.chart i).component).unitary, inv_one]
    frame_comparison := ?_
    phase_equivariance := ?_
    phase_frame := ?_ }⟩
  · intro i s
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hd := (C.chart i).closed_ball_in_extension (subset_closure hx)
    obtain ⟨u, hu⟩ := transition_finite F ζ hζ hF U A (C.chart i).component (γ i x)
    simpa only [phase, Units.val_inv_eq_inv_val] using
      phase_value F ζ hζ hF U A M C i x s (γ i x)
        ((A.line (C.chart i).component).rho (γ i x)) u (hγ i x hd).symm hu
  · intro i g
    have hf := chartMeasure_pullback_ae F ζ hζ hF U A C i M.free_ae
    filter_upwards [hf, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hfree hx
    have hxd := (C.chart i).closed_ball_in_extension (subset_closure hx)
    have hyd : (C.chart i).orthogonal g x ∈ (C.chart i).extendedDomain := by
      rw [← (C.chart i).invariant_extension g]
      exact ⟨x, hxd, rfl⟩
    have hb : (C.chart i).toBase F ζ hζ hF U ((C.chart i).orthogonal g x) =
        (C.chart i).toBase F ζ hζ hF U x := by
      unfold Chart.toBase
      apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U _)
      rw [(C.chart i).equivariance g x hxd]
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨g.val, rfl⟩
    rw [chart_component_eq F ζ hζ hF U A M C i x] at hfree
    let δ := γ i ((C.chart i).orthogonal g x) * g.val * (γ i x)⁻¹
    have hfix : (δ : KPCuspArithmetic.PGL2 F) •
        M.lift ((C.chart i).toBase F ζ hζ hF U x) =
          M.lift ((C.chart i).toBase F ζ hζ hF U x) := by
      rw [← hγ i x hxd]
      simp only [δ, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul]
      rw [← (C.chart i).equivariance g x hxd, hγ i _ hyd, hb]
      exact (hγ i x hxd).symm
    have hd := hfree δ hfix
    have he : γ i ((C.chart i).orthogonal g x) * g.val = γ i x := by
      have hh := congrArg (fun t => t * γ i x) hd
      simpa [δ, mul_assoc] using hh
    have hm : (KPCuspGenuineMonodromy.chi F ζ hζ)
        ((A.line (C.chart i).component).rho (γ i ((C.chart i).orthogonal g x))) *
        ((C.chart i).rho F ζ hζ hF U g) =
      (KPCuspGenuineMonodromy.chi F ζ hζ)
        ((A.line (C.chart i).component).rho (γ i x)) := by
      simpa only [Chart.rho, MonoidHom.comp_apply, Subgroup.subtype_apply, ← map_mul] using
        congrArg (fun t => (KPCuspGenuineMonodromy.chi F ζ hζ)
          ((A.line (C.chart i).component).rho t)) he
    have hh := congrArg (fun t : ℂˣ => ((C.chart i).rho F ζ hζ hF U g) * t⁻¹) hm
    have hh' : phase i ((C.chart i).orthogonal g x) =
        (C.chart i).rho F ζ hζ hF U g * phase i x := by
      simpa [phase, mul_inv_rev, mul_assoc] using hh
    exact congrArg (fun t : ℂˣ => (t : ℂ)) hh'
  · intro i
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hframe i x ((C.chart i).closed_ball_in_extension (subset_closure hx))

end DedekindZetaZeroFree.CoreChartLocalizers

end
