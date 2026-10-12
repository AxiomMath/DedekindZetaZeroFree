module

public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.LocalCubicSheetLifts
public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.CuspLiftTransport
public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.OverlapMetricAndPhase

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff
open Topology MeasureTheory

namespace DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

namespace ChartAnalyticHelpers
open KPContLocalNorm
section Mixed
variable {A E Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
set_option backward.isDefEq.respectTransparency.types false in
private lemma partial_eq (h : A → E → Y) (s : A) (z : E)
 (hh : DifferentiableAt ℝ (Function.uncurry h) (s,z)) :
 fderiv ℝ (h s) z = (fderiv ℝ (Function.uncurry h) (s,z)).comp (ContinuousLinearMap.inr ℝ A E) := by
 exact (hh.hasFDerivAt.comp z (hasFDerivAt_prodMk_right s z)).fderiv
set_option backward.isDefEq.respectTransparency.types false in
private lemma mixed_partial (h : A → E → Y) (s : A) (z : E)
 (hh : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry h) (s,z)) (v : A) (w : E) :
 (fderiv ℝ (fun t => fderiv ℝ (h t) z) s) v w =
 (fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w v := by
 let H := Function.uncurry h
 let D := fderiv ℝ H
 let L := ContinuousLinearMap.inl ℝ A E
 let R := ContinuousLinearMap.inr ℝ A E
 let CR := (ContinuousLinearMap.compL ℝ E (A × E) Y).flip R
 let CL := (ContinuousLinearMap.compL ℝ A (A × E) Y).flip L
 have hD : HasFDerivAt D (fderiv ℝ D (s,z)) (s,z) :=
   (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
 have hs : (fun t => fderiv ℝ (h t) z) =ᶠ[𝓝 s]
     (fun t => CR (D (t,z))) := by
   have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
   filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hn] with t ht
   exact partial_eq h t z (ht.differentiableAt (by simp))
 have hz : (fun x => fderiv ℝ (fun t => h t x) s) =ᶠ[𝓝 z]
     (fun x => CL (D (s,x))) := by
   have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
   filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hn] with x hx
   have hd : HasFDerivAt H (D (s,x)) (s,x) := (hx.differentiableAt (by simp)).hasFDerivAt
   have hleft : HasFDerivAt (fun t : A => H (t,x)) (CL (D (s,x))) s :=
     by convert hd.comp s (hasFDerivAt_prodMk_left (𝕜 := ℝ) s x) using 1 <;> rfl
   exact hleft.fderiv
 have hsd := CR.hasFDerivAt.comp s (hD.comp s (hasFDerivAt_prodMk_left s z))
 have hzd := CL.hasFDerivAt.comp z (hD.comp z (hasFDerivAt_prodMk_right s z))
 have hsde := hsd.fderiv
 have hzde := hzd.fderiv
 dsimp only [Function.comp_def] at hsde hzde
 rw [hs.fderiv_eq, hz.fderiv_eq, hsde, hzde]
 exact (hh.isSymmSndFDerivAt (by simp)).eq (v,0) (0,w)

section Complex
variable [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
set_option backward.isDefEq.respectTransparency.types false in
private lemma partial_snd_hasDeriv (h k : ℂ → E → Y) (U : Set E) (hU : IsOpen U)
 (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U))
 (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Set.univ ×ˢ U))
 (hd : ∀ s z, z ∈ U → HasDerivAt (fun t => h t z) (k s z) s)
 (s : ℂ) (z : E) (hz : z ∈ U) :
 HasDerivAt (fun t => fderiv ℝ (h t) z) (fderiv ℝ (k s) z) s := by
 have hlocal := hh.contDiffAt ((isOpen_univ.prod hU).mem_nhds (show (s,z) ∈ Set.univ ×ˢ U from ⟨Set.mem_univ s,hz⟩))
 have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
     (fun q : ℂ × E => h q.1 q.2) (s,z) := hlocal
 have hder : DifferentiableAt ℝ (fun t => fderiv ℝ (h t) z) s := by
   have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
       (Function.uncurry (fun t x => h t x)) (s,z) := hlocal
   exact (h2.fderiv (g := fun _ : ℂ => z) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)
 have heq : (ContinuousLinearMap.toSpanSingleton ℂ (fderiv ℝ (k s) z)).restrictScalars ℝ =
     fderiv ℝ (fun t => fderiv ℝ (h t) z) s := by
   ext d w
   rw [mixed_partial h s z hlocal d w]
   have ht : (fun x => (fderiv ℝ (fun t => h t x) s) d) =ᶠ[𝓝 z]
       (fun x => d • k s x) := by
     filter_upwards [hU.mem_nhds hz] with x hx
     rw [((hd s x hx).hasFDerivAt.restrictScalars ℝ).fderiv]
     rfl
   have hp := (hk.contDiffAt ((isOpen_univ.prod hU).mem_nhds (show (s,z) ∈ Set.univ ×ˢ U from ⟨Set.mem_univ s,hz⟩))).comp
     z (contDiffAt_const.prodMk contDiffAt_id)
   have hf := hp.differentiableAt (by simp)
   have hswap : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (fun x t => h t x)) (z,s) :=
     hlocal.comp (z,s) (contDiff_snd.prodMk contDiff_fst).contDiffAt
   have happ := (ContinuousLinearMap.apply ℝ Y d).hasFDerivAt.comp z
     ((hswap.fderiv (g := fun _ : E => s) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)).hasFDerivAt
   have he : (fderiv ℝ (fun x => (fderiv ℝ (fun t => h t x) s) d) z) w =
       ((fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w) d := by
     have he := happ.fderiv
     dsimp only [Function.comp_def] at he
     convert congrArg (fun T : E →L[ℝ] Y => T w) he using 1 <;> rfl
   rw [← he, ht.fderiv_eq]
   have hf' : DifferentiableAt ℝ (k s) z := hf
   change (d • fderiv ℝ (k s) z) w = (fderiv ℝ (d • k s) z) w
   rw [fderiv_const_smul hf' d]
 exact hasFDerivAt_of_restrictScalars ℝ hder.hasFDerivAt heq
end Complex
end Mixed
section CompactDifferentiation
open scoped Topology
open Filter
variable {X Y : Type*} [UniformSpace X] [CompactSpace X]
 [NormedAddCommGroup Y] [NormedSpace ℂ Y]
set_option backward.isDefEq.respectTransparency.types false in
private lemma compact_hasDeriv (h k : ℂ → C(X,Y))
 (hk : Continuous (Function.uncurry (fun t x => k t x)))
 (hd : ∀ t x, HasDerivAt (fun r => h r x) (k t x) t) (s : ℂ) :
 HasDerivAt h (k s) s := by
 apply HasDerivAt.of_isLittleO
 rw [Asymptotics.isLittleO_iff]
 intro c hc
 have hu := Metric.tendstoUniformly_iff.mp (hk.tendstoUniformly (fun t x => k t x) s) c hc
 have hseg : ∀ᶠ t in 𝓝 s, ∀ r ∈ segment ℝ s t, ∀ x : X, ‖k r x - k s x‖ ≤ c := by
   have hs : ∀ᶠ t in 𝓝[Set.univ] s, ∀ x : X, ‖k t x - k s x‖ ≤ c := by
     simpa only [nhdsWithin_univ, dist_eq_norm_sub, norm_sub_rev] using hu.mono (fun t ht x => (ht x).le)
   simpa only [nhdsWithin_univ] using (convex_univ : Convex ℝ (Set.univ : Set ℂ)).eventually_nhdsWithin_segment (Set.mem_univ s) hs
 filter_upwards [hseg] with t ht
 apply (ContinuousMap.norm_le (h t - h s - (t-s) • k s) (mul_nonneg hc.le (norm_nonneg _))).mpr
 intro x
 have H := (convex_segment s t).norm_image_sub_le_of_norm_hasFDerivWithin_le'
   (f := fun r => h r x) (f' := fun r => ContinuousLinearMap.toSpanSingleton ℂ (k r x))
   (φ := ContinuousLinearMap.toSpanSingleton ℂ (k s x)) (C := c)
   (fun r _ => (hd r x).hasFDerivAt.hasFDerivWithinAt)
   (fun r hr => by
     have he : ContinuousLinearMap.toSpanSingleton ℂ (k r x) - ContinuousLinearMap.toSpanSingleton ℂ (k s x) =
       ContinuousLinearMap.toSpanSingleton ℂ (k r x - k s x) := by ext a; simp [smul_sub]
     rw [he, ContinuousLinearMap.norm_toSpanSingleton]
     exact ht r hr x)
   (left_mem_segment ℝ s t) (right_mem_segment ℝ s t)
 simpa using H

end CompactDifferentiation
section Coordinates
 theorem joint_coordinate {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (h : ℂ → Space n → ℂ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U))
    (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℂ × Space n => coordinateDerivativeList l (h p.1) p.2) (Set.univ ×ˢ U) := by
  induction l with
  | nil => exact hh
  | cons i l ih =>
    intro p hp
    have hl := ih.contDiffAt ((isOpen_univ.prod hU).mem_nhds hp)
    have hc : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : (ℂ × Space n) × Space n => coordinateDerivativeList l (h q.1.1) q.2) (p,p.2) :=
      hl.comp (p,p.2) (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt
    have hd := ContDiffAt.fderiv (f := fun q : ℂ × Space n => coordinateDerivativeList l (h q.1))
      (g := fun q : ℂ × Space n => q.2) (m := (⊤ : ℕ∞)) hc contDiff_snd.contDiffAt (by simp)
    exact (hd.clm_apply contDiffAt_const).contDiffWithinAt

private theorem coordinate_hasDeriv {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (h k : ℂ → Space n → ℂ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U))
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Set.univ ×ˢ U))
    (hd : ∀ s x, x ∈ U → HasDerivAt (fun t => h t x) (k s x) s)
    (l : List (Fin n)) (s : ℂ) (x : Space n) (hx : x ∈ U) :
    HasDerivAt (fun t => coordinateDerivativeList l (h t) x)
      (coordinateDerivativeList l (k s) x) s := by
  induction l generalizing s x with
  | nil => exact hd s x hx
  | cons i l ih =>
    have H := partial_snd_hasDeriv (fun t x => coordinateDerivativeList l (h t) x)
      (fun t x => coordinateDerivativeList l (k t) x) U hU
      (joint_coordinate hU h hh l) (joint_coordinate hU k hk l) ih s x hx
    let ev : (Space n →L[ℝ] ℂ) →L[ℂ] ℂ :=
      { toFun := fun L => L (EuclideanSpace.single i 1)
        map_add' := by intro L M; rfl
        map_smul' := by intro c L; rfl
        cont := (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1)).continuous }
    exact ev.hasFDerivAt.comp_hasDerivAt s H

 def jet {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (K : Set (Space n)) (hKU : K ⊆ U) (m : ℕ) (h : ℂ → Space n → ℂ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U)) (s : ℂ) : CompactJets K m :=
  fun α => ⟨fun x => coordinateDerivative α (h s) x,
    (((joint_coordinate hU h hh α.directions).continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => ⟨Set.mem_univ _,hKU hx⟩))).restrict⟩

theorem compact_coordinate_hasDeriv {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (h k : ℂ → Space n → ℂ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U))
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Set.univ ×ˢ U))
    (hd : ∀ s x, x ∈ U → HasDerivAt (fun t => h t x) (k s x) s)
    (K : Set (Space n)) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ J : ℂ → CompactJets K m, Differentiable ℂ J ∧
      ∀ s α (x : K), J s α x = coordinateDerivative α (h s) x := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let J := jet hU K hKU m h hh
  let D := jet hU K hKU m k hk
  refine ⟨J, ?_, fun s α x => rfl⟩
  have H (α : MultiIndex n m) (s : ℂ) : HasDerivAt (fun t => J t α) (D s α) s := by
    apply compact_hasDeriv (fun t => J t α) (fun t => D t α) _ _ s
    · exact (joint_coordinate hU k hk α.directions).continuousOn.comp_continuous
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
        (fun p => ⟨Set.mem_univ _,hKU p.2.property⟩)
    · intro t x
      exact coordinate_hasDeriv hU h k hh hk hd α.directions t x (hKU x.property)
  exact differentiable_pi.mpr (fun α s => (H α s).differentiableAt)

end Coordinates
private theorem spatial_coordinate_smooth {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i l ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem coordinate_const_mul {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (c : ℂ)
    (l : List (Fin n)) : Set.EqOn (coordinateDerivativeList l (fun x => c * u x))
      (fun x => c * coordinateDerivativeList l u x) U := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have hd : DifferentiableAt ℝ (coordinateDerivativeList l u) x :=
      ((spatial_coordinate_smooth hU u hu l).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have he : coordinateDerivativeList l (fun x => c * u x) =ᶠ[𝓝 x]
        (fun x => c * coordinateDerivativeList l u x) :=
      (hU.eventually_mem hx).mono (fun y hy => ih hy)
    change fderiv ℝ (coordinateDerivativeList l (fun x => c * u x)) x _ = _
    rw [he.fderiv_eq]
    simpa only [coordinateDerivativeList, ContinuousLinearMap.smul_apply, smul_eq_mul]
      using congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1))
        (fderiv_const_mul hd c)

private theorem coordinate_congr_on {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {u v : Space n → ℂ} (he : Set.EqOn u v U) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l u) (coordinateDerivativeList l v) U := by
  induction l with
  | nil => exact he
  | cons i l ih =>
    intro x hx
    have hlocal : coordinateDerivativeList l u =ᶠ[𝓝 x] coordinateDerivativeList l v :=
      (hU.eventually_mem hx).mono (fun y hy => ih hy)
    exact congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1)) hlocal.fderiv_eq

private theorem affine_exponential_compactJets {n : ℕ} {U : Set (Space n)}
    (hU : IsOpen U) (t ψ₀ ψ₁ : Space n → ℂ)
    (ht : ContDiffOn ℝ (⊤ : ℕ∞) t U)
    (hψ₀ : ContDiffOn ℝ (⊤ : ℕ∞) ψ₀ U) (hψ₁ : ContDiffOn ℝ (⊤ : ℕ∞) ψ₁ U)
    (O : Set ℂ) (a : ℂ → ℂ) (ha : DifferentiableOn ℂ a O)
    (K : Set (Space n)) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ J : ℂ → CompactJets K m, DifferentiableOn ℂ J O ∧
      ∀ s ∈ O, ∀ α (x : K), J s α x = coordinateDerivative α
        (fun y => a s * (Complex.exp (s * t y) * (ψ₀ y + s * ψ₁ y))) x := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let h := fun s y => Complex.exp (s * t y) * (ψ₀ y + s * ψ₁ y)
  let k := fun s y => t y * h s y + Complex.exp (s * t y) * ψ₁ y
  have ht' := ht.comp contDiffOn_snd (fun p : ℂ × Space n => fun hp : p ∈ Set.univ ×ˢ U => hp.2)
  have h₀ := hψ₀.comp contDiffOn_snd (fun p : ℂ × Space n => fun hp : p ∈ Set.univ ×ˢ U => hp.2)
  have h₁ := hψ₁.comp contDiffOn_snd (fun p : ℂ × Space n => fun hp : p ∈ Set.univ ×ˢ U => hp.2)
  have hx : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℂ × Space n => Complex.exp (p.1 * t p.2))
      (Set.univ ×ˢ U) := Complex.contDiff_exp.comp_contDiffOn (contDiffOn_fst.mul ht')
  have hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U) :=
    hx.mul (h₀.add (contDiffOn_fst.mul h₁))
  have hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Set.univ ×ˢ U) :=
    (ht'.mul hh).add (hx.mul h₁)
  have hd : ∀ s y, y ∈ U → HasDerivAt (fun r => h r y) (k s y) s := by
    intro s y hy
    have he := (((hasDerivAt_id s).mul_const (t y)).cexp).mul
      (hasDerivAt_const s (ψ₀ y) |>.add ((hasDerivAt_id s).mul_const (ψ₁ y)))
    convert he using 1
    · funext r; dsimp [h]
    · dsimp [k,h]; ring
  obtain ⟨J,hJ,hJspec⟩ := compact_coordinate_hasDeriv hU h k hh hk hd K hK hKU m
  refine ⟨fun s => a s • J s, ha.smul hJ.differentiableOn, ?_⟩
  intro s hs α x
  change a s * J s α x = _
  rw [hJspec]
  have hhs : ContDiffOn ℝ (⊤ : ℕ∞) (h s) U :=
    hh.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨Set.mem_univ _,hy⟩)
  exact (coordinate_const_mul hU _ hhs (a s) α.directions (hKU x.property)).symm

private theorem compact_family_holomorphic {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (O : Set ℂ) (hO : IsOpen O) (j : ℂ → C(X, ℂ))
    (hc : ContinuousOn (fun p : ℂ × X => j p.1 p.2) (O ×ˢ Set.univ))
    (hd : ∀ x : X, DifferentiableOn ℂ (fun z => j z x) O) :
    DifferentiableOn ℂ j O := by
  have hj : ContinuousOn j O := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    let a : O × X → ℂ × X := fun p => (p.1.val,p.2)
    have ha : Continuous a := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact hc.comp_continuous ha (fun p => ⟨p.1.property, Set.mem_univ _⟩)
  intro s hs
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hs)
  let R := r/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : Metric.closedBall s R ⊆ O :=
    (Metric.closedBall_subset_ball (by dsimp [R]; linarith)).trans hrO
  have hcircle : CircleIntegrable j s R :=
    (hj.mono (Metric.sphere_subset_closedBall.trans hclosed)).circleIntegrable hR.le
  let g : ℂ → C(X,ℂ) := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    circleIntegral (fun z => (z-w)⁻¹ • j z) s R
  have heq : Set.EqOn g j (Metric.ball s R) := by
    intro w hw
    ext x
    let L : C(X,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
    have hw' : w ∉ Metric.sphere s |R| := by
      rw [abs_of_pos hR]
      intro hh
      exact (ne_of_lt (Metric.mem_ball.mp hw)) hh
    have hi := hcircle.sub_zpow_smul (-1) hw'
    have hL : L (circleIntegral (fun z => (z-w)⁻¹ • j z) s R) =
        circleIntegral (fun z => (z-w)⁻¹ • j z x) s R := by
      rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm (by simpa using hi.out)]
      simp only [map_smul]
      rfl
    change L ((2 * Real.pi * Complex.I : ℂ)⁻¹ • _) = _
    rw [map_smul, hL]
    exact (((hd x).mono hclosed).mono Metric.closure_ball_subset_closedBall).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hg : DifferentiableAt ℂ g s := by
    change DifferentiableAt ℂ (fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      circleIntegral (fun z => (z-w)⁻¹ • j z) s R) s
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul (w := s) hcircle (by
      simpa [abs_of_pos hR] using (ne_of_gt hR).symm)).const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableAt
  have he : g =ᶠ[𝓝 s] j := Filter.eventually_of_mem (Metric.ball_mem_nhds s hR) (fun w hw => heq hw)
  exact (hg.congr_of_eventuallyEq he.symm).differentiableWithinAt

private theorem compact_family_of_local {E : Type*} [TopologicalSpace E]
    (O : Set ℂ) (hO : IsOpen O) (U : Set E) (f : ℂ → E → ℂ)
    (hl : ∀ x ∈ U, ∃ (K : Set E) (hK : IsCompact K), x ∈ interior K ∧ K ⊆ U ∧
      (letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
       ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ y : K, j z y = f z y.val))
    (C : Set E) (hC : IsCompact C) (hCU : C ⊆ U) :
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    ∃ j : ℂ → C(C,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : C, j z x = f z x.val := by
  have hc : ContinuousOn (fun p : ℂ × E => f p.1 p.2) (O ×ˢ U) := by
    intro p hp
    obtain ⟨K,hK,hpK,hKU,j,hj,heq⟩ := hl p.2 hp.2
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hcont : ContinuousOn (fun q : ℂ × K => j q.1 q.2) (O ×ˢ Set.univ) :=
      continuous_eval.comp_continuousOn ((hj.continuousOn.comp continuous_fst.continuousOn
        (fun _ hq => hq.1)).prodMk continuous_snd.continuousOn)
    have hfK : ContinuousOn (fun q : ℂ × E => f q.1 q.2) (O ×ˢ K) := by
      apply continuousOn_iff_continuous_restrict.mpr
      let a : (O ×ˢ K) → ℂ × K := fun q => (q.val.1, ⟨q.val.2,q.property.2⟩)
      have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      exact (hcont.comp_continuous ha (fun q => ⟨q.property.1, Set.mem_univ _⟩)).congr
        (fun q => heq q.val.1 q.property.1 ⟨q.val.2,q.property.2⟩)
    apply (hfK.continuousAt ?_).continuousWithinAt
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hO.mem_nhds hp.1) (mem_interior_iff_mem_nhds.mp hpK)
  have hd : ∀ x ∈ U, DifferentiableOn ℂ (fun z => f z x) O := by
    intro x hx
    obtain ⟨K,hK,hxK,hKU,j,hj,heq⟩ := hl x hx
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let L : C(K,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ ⟨x, interior_subset hxK⟩
    exact (L.differentiable.comp_differentiableOn hj).congr
      (fun z hz => (heq z hz ⟨x,interior_subset hxK⟩).symm)
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hcC : ContinuousOn (fun p : ℂ × C => f p.1 p.2.val) (O ×ˢ Set.univ) :=
    hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1,hCU p.2.property⟩)
  have hslice : ∀ z ∈ O, Continuous (fun x : C => f z x.val) := by
    intro z hz
    exact hcC.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hz,Set.mem_univ _⟩)
  let j : ℂ → C(C,ℂ) := fun z => if hz : z ∈ O then ⟨fun x => f z x.val, hslice z hz⟩ else 0
  have hjval : ∀ z ∈ O, ∀ x : C, j z x = f z x.val := by
    intro z hz x
    simp only [j, dif_pos hz]
    rfl
  refine ⟨j,compact_family_holomorphic O hO j ?_ ?_,hjval⟩
  · exact hcC.congr (fun p hp => hjval p.1 hp.1 p.2)
  · intro x
    exact (hd x.val (hCU x.property)).congr (fun z hz => hjval z hz x)

private theorem chartJets_of_local_affine_exponential {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (hO : IsOpen O) (g : ℂ → Space n → ℂ)
    (hl : ∀ x ∈ B.carrier, ∃ V : Set (Space n), IsOpen V ∧ x ∈ V ∧ V ⊆ B.carrier ∧
      ∃ t ψ₀ ψ₁ : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) t V ∧
        ContDiffOn ℝ (⊤ : ℕ∞) ψ₀ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) ψ₁ V ∧
        ∃ a : ℂ → ℂ, DifferentiableOn ℂ a O ∧
          ∀ s ∈ O, ∀ y ∈ V, g s y = a s * (Complex.exp (s * t y) * (ψ₀ y + s * ψ₁ y))) :
    KPCutoffSource.ChartSmoothHolomorphicOn B g O := by
  have hsp : ∀ s ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (g s) B.carrier := by
    intro s hs x hx
    obtain ⟨V,hV,hxV,hVB,t,ψ₀,ψ₁,ht,h₀,h₁,a,ha,heq⟩ := hl x hx
    have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => a s * (Complex.exp (s * t y) * (ψ₀ y + s * ψ₁ y))) V :=
      contDiffOn_const.mul ((Complex.contDiff_exp.comp_contDiffOn
      (contDiffOn_const.mul ht)).mul (h₀.add (contDiffOn_const.mul h₁)))
    exact ((hc.contDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
      ((hV.eventually_mem hxV).mono (fun y hy => heq s hs y hy))).contDiffWithinAt
  refine ⟨hsp,?_⟩
  intro C hC hCB m
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hj (α : MultiIndex n m) : ∃ J : ℂ → C(C,ℂ), DifferentiableOn ℂ J O ∧
      ∀ s ∈ O, ∀ x : C, J s x = coordinateDerivative α (g s) x := by
    apply compact_family_of_local O hO B.carrier (fun s x => coordinateDerivative α (g s) x) _ C hC hCB
    intro x hx
    obtain ⟨V,hV,hxV,hVB,t,ψ₀,ψ₁,ht,h₀,h₁,a,ha,heq⟩ := hl x hx
    obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
    let K := Metric.closedBall x (r/2)
    have hKV : K ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hrV
    have hK : IsCompact K := isCompact_closedBall _ _
    have hxK : x ∈ interior K := mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds x (by positivity))
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    obtain ⟨J,hJ,hJspec⟩ := affine_exponential_compactJets hV t ψ₀ ψ₁ ht h₀ h₁ O a ha K hK hKV m
    refine ⟨K,hK,hxK,hKV.trans hVB,fun s => J s α,?_,?_⟩
    · exact (ContinuousLinearMap.proj α).differentiable.comp_differentiableOn hJ
    · intro s hs y
      rw [hJspec s hs α y]
      exact (coordinate_congr_on hV (fun y hy => heq s hs y hy) α.directions (hKV y.property)).symm
  choose J hJ hJspec using hj
  refine ⟨fun s α => J α s, differentiableOn_pi.mpr hJ, ?_⟩
  intro s hs α x
  exact hJspec α s hs x

end ChartAnalyticHelpers

section PointwiseHolomorphy
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (a : Cusps F ζ hζ C R P H U)

theorem incoming_scalar_coefficient_holomorphic (Ω : Set ℂ) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f Ω) :
    DifferentiableOn ℂ (fun s =>
      (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
        (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s))).val 0) Ω := by
  let E : (rootsOfUnity 3 F → ℂ) →ₗ[ℂ] ℂ :=
    (KPContFlatCuspCoefficientTransition.zeroFiberEvaluation F ζ hζ C R P H U a).comp
      (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a)
  have hsheet : DifferentiableOn ℂ (fun s =>
      KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s)) Ω := by
    apply differentiableOn_pi.mpr
    intro ε
    let g := (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a ε).val
    let ev : S →ₗ[ℂ] ℂ :=
      { toFun := fun v => (ι v).val.val.val g
        map_add' := by intro v w; simp only [map_add, Submodule.coe_add, Pi.add_apply]
        map_smul' := by intro c v; simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply] }
    have he := ev.toContinuousLinearMap.differentiable.comp_differentiableOn hf
    have hx := ((differentiableOn_id.mul_const
      (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)).cexp).mul he
    apply hx.congr
    intro s hs
    change KPContFlatCommonLevelKernel.L F ζ hζ U ι s (f s) g = _
    exact KPContFlatCommonLevelKernel.L_formula F ζ hζ U ι s (f s) g
  exact E.toContinuousLinearMap.differentiable.comp_differentiableOn hsheet

theorem incomingValue_scalar_formula (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (z : KPCuspCharts.Coordinates F) :
    incomingValue F ζ hζ C R P H U ι a s v z =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s z.2 *
        (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
          (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s v)).val 0 := by
  unfold incomingValue
  rw [KPContFlatCuspIncomingEvaluation.incoming_formula F ζ hζ C R P H U a ι s hs]
  change KPIncomingCasimir.heightFactor _ s z.2 *
    ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val z.1.2).val _ = _
  rw [((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val z.1.2).property.2]
  rfl

theorem incomingValue_uniformizing_contDiff (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S) :
    ContDiff ℝ (⊤ : ℕ∞) (incomingValue F ζ hζ C R P H U ι a s v) := by
  have he : incomingValue F ζ hζ C R P H U ι a s v =
      (fun z : KPCuspCharts.Coordinates F =>
        KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s z.2 *
          (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
            (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s v)).val 0) :=
    funext (fun z => incomingValue_scalar_formula F ζ hζ C R P H U ι a s hs v z)
  rw [he]
  unfold KPIncomingCasimir.heightFactor
  have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun z : KPCuspCharts.Coordinates F => (z.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact (Complex.contDiff_exp.comp (contDiff_const.mul hcast)).mul contDiff_const

theorem incomingRealization_endLift_formula {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (level F ζ hζ C R P H U) R P H T)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (x : Covered F ζ hζ C R P H U)
    (l : EndLift F ζ hζ C R P H U buffer x) :
    incomingRealization F ζ hζ C R P H U ι buffer s v x =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ l.sheet : ℂ) *
        incomingValue F ζ hζ C R P H U ι l.cusp s v l.coordinates := by
  have hx : Nonempty (EndLift F ζ hζ C R P H U buffer x) := ⟨l⟩
  change (if h : Nonempty (EndLift F ζ hζ C R P H U buffer x) then
    (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ (Classical.choice h).sheet : ℂ) *
      incomingValue F ζ hζ C R P H U ι (Classical.choice h).cusp s v (Classical.choice h).coordinates
    else 0) = _
  rw [dif_pos hx]
  exact actual_endLift_incoming_transport F ζ hζ C R P H U ι buffer s hs v x _ l

private theorem height_of_coveredPoint {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (level F ζ hζ C R P H U) R P H T)
    (ε : rootsOfUnity 3 F) (z : KPCuspCharts.Coordinates F) (hz : buffer.τ < z.2) :
    height F ζ hζ C R P H U buffer a (coveredPoint F ζ hζ C R P H U a ε z) = z.2 := by
  have hbase : KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
      (coveredPoint F ζ hζ C R P H U a ε z) =
      KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a z := by
    unfold coveredPoint
    rw [KPContSectorCoveredQuotientVocabulary.q_mk]
    apply Quotient.sound
    refine ⟨1, ε⁻¹, 1, ?_, ?_⟩
    · simp [KPContActualCollarBuffer.chartLift, KPContSectorSmoothFramesSupport.cuspPoint]
    · simp [KPContFlatCuspIncomingEvaluation.atlas, KPContActualCollarBuffer.chartLift]
  unfold height
  rw [hbase]
  exact buffer.height_coordinates a z hz

private theorem physical_incoming_local_formula {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (level F ζ hζ C R P H U) R P H T)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPCuspGenuineMonodromy.SymmetricSpace F)
    (hy : Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
      (level F ζ hζ C R P H U)) (y,
        (H.atlas (level F ζ hζ C R P H U)).representative i) ∈
          ends F ζ hζ C R P H U buffer a) :
    ∃ V : Set (KPCuspGenuineMonodromy.SymmetricSpace F), IsOpen V ∧ y ∈ V ∧
      ∃ ε : rootsOfUnity 3 F, ∃ t : KPCuspGenuineMonodromy.SymmetricSpace F → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) t V ∧
        ∀ y' ∈ V, let x := Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U)) (y', (H.atlas (level F ζ hζ C R P H U)).representative i);
          x ∈ ends F ζ hζ C R P H U buffer a ∧
          height F ζ hζ C R P H U buffer a x = t y' ∧
          ∀ s ∈ KPContinuation.spectralDomain, ∀ v : S,
            incomingRealization F ζ hζ C R P H U ι buffer s v x =
              (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
                (KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s (t y') *
                  (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
                    (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s v)).val 0) := by
  obtain ⟨V,hV,hyV,ε,z,hz,hlift⟩ := actual_end_local_smooth_lift F ζ hζ C R P H U buffer a i y hy
  refine ⟨V,hV,hyV,ε,fun y' => (z y').2,hz.snd,?_⟩
  intro y' hy'
  dsimp only
  obtain ⟨hhigh,hpoint⟩ := hlift y' hy'
  have hheight := height_of_coveredPoint F ζ hζ C R P H U a buffer ε (z y') hhigh
  rw [hpoint] at hheight
  have hmem : Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
      (level F ζ hζ C R P H U)) (y',
        (H.atlas (level F ζ hζ C R P H U)).representative i) ∈
          ends F ζ hζ C R P H U buffer a := by
    change KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U)) (y', (H.atlas (level F ζ hζ C R P H U)).representative i)) ∈
      KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H buffer.τ a
    have hb : KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
      (coveredPoint F ζ hζ C R P H U a ε (z y')) =
      KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a (z y') := by
      unfold coveredPoint
      rw [KPContSectorCoveredQuotientVocabulary.q_mk]
      apply Quotient.sound
      refine ⟨1,ε⁻¹,1,?_,?_⟩ <;>
        simp [KPContSectorSmoothFramesSupport.cuspPoint, KPContFlatCuspIncomingEvaluation.atlas]
    rw [← hpoint,hb,← buffer.lift_range a]
    exact ⟨z y',hhigh,rfl⟩
  refine ⟨hmem,hheight,?_⟩
  intro s hs v
  rw [incomingRealization_endLift_formula F ζ hζ C R P H U ι buffer s hs v _
    (⟨a,ε,z y',hhigh,hpoint⟩ : EndLift F ζ hζ C R P H U buffer _)]
  rw [incomingValue_scalar_formula F ζ hζ C R P H U ι a s hs]

private theorem cutoff_multiplier_zero_below {T : ℝ} (χ : KPCutoffSource.SmoothCuspCutoff T)
    (d : ℕ) (b : Bool) (s : ℂ) (t : ℝ) (ht : t < T) :
    (if b then KPCutoffSource.incomingCommutatorMultiplier d χ.toFun s t
      else (χ.toFun t : ℂ)) = 0 := by
  have he : χ.toFun =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact χ.zero_below u hu.le
  have hd : deriv χ.toFun =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    simpa using he.deriv
  have hd₀ : deriv χ.toFun t = 0 := hd.eq_of_nhds
  have hd₂ : deriv (deriv χ.toFun) t = 0 := by
    simpa using hd.deriv_eq
  cases b <;> simp [KPCutoffSource.incomingCommutatorMultiplier, χ.zero_below t ht.le, hd₀, hd₂]

theorem incoming_cutoff_zero_germ {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (level F ζ hζ C R P H U) R P H T)
    (χ : KPCutoffSource.SmoothCuspCutoff T) (b : Bool)
    (x : Covered F ζ hζ C R P H U) (hx : x ∉ ends F ζ hζ C R P H U buffer a) :
    ∀ᶠ y in 𝓝 x, ∀ s : ℂ, ∀ v : S,
      (ends F ζ hζ C R P H U buffer a).indicator
        (fun y => (if b then KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
            χ.toFun s (height F ζ hζ C R P H U buffer a y)
          else (χ.toFun (height F ζ hζ C R P H U buffer a y) : ℂ)) *
          incomingRealization F ζ hζ C R P H U ι buffer s v y) y = 0 := by
  let q := KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
  let E := KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H buffer.τ a
  have hxE : q x ∉ E := hx
  have hq : Continuous q := KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ
    (level F ζ hζ C R P H U)
  by_cases hcl : q x ∈ closure E
  · have hfr : q x ∈ frontier E := by
      rw [frontier, (buffer.open_ends a).interior_eq]
      exact ⟨hcl,hxE⟩
    obtain ⟨V,hV,hxV,hVbound⟩ := buffer.boundary_height_buffer a (q x) hfr
    filter_upwards [hq.continuousAt.eventually (hV.mem_nhds hxV)] with y hy
    intro s v
    by_cases hyE : y ∈ ends F ζ hζ C R P H U buffer a
    · rw [Set.indicator_of_mem hyE]
      have ht : height F ζ hζ C R P H U buffer a y < T := hVbound (q y) hy hyE
      rw [cutoff_multiplier_zero_below χ _ b s _ ht, zero_mul]
    · exact Set.indicator_of_notMem hyE _
  · filter_upwards [hq.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hcl)] with y hy
    intro s v
    have hyE : y ∉ ends F ζ hζ C R P H U buffer a := fun h => hy (subset_closure h)
    exact Set.indicator_of_notMem hyE _

end PointwiseHolomorphy

theorem actual_incoming_cutoff_chart_jets
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (level F ζ hζ C R P H U) R P H T)
    (Ω : Set ℂ) (hopen : IsOpen Ω) (hΩspectral : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f Ω) (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (a : Cusps F ζ hζ C R P H U)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (q : KPContCotangentActualOverlap.LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := level F ζ hζ C R P H U) (R := R) (P := P) (H := H) i)
    (b : Bool) (B : KPContLocalNorm.LocalBall (KPContCotangentActualOverlap.d F * 3)) :
    let c : KPContLocalNorm.Space (KPContCotangentActualOverlap.d F * 3) →
        KPContCotangentActualOverlap.M F :=
      fun x => WithLp.toLp 2 (fun ik => x (finProdFinEquiv ik))
    Metric.closedBall B.center B.radius ⊆ c ⁻¹' q.omega →
    KPCutoffSource.ChartSmoothHolomorphicOn B
      (fun s x =>
        (KPCuspGenuineMonodromy.chi F ζ hζ (q.splitting (c x)) : ℂ) *
          (ends F ζ hζ C R P H U buffer a).indicator
            (fun y =>
              (if b then KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
                  (χ a).toFun s (height F ζ hζ C R P H U buffer a y)
                else ((χ a).toFun (height F ζ hζ C R P H U buffer a y) : ℂ)) *
              incomingRealization F ζ hζ C R P H U ι buffer s (f s) y)
            (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
                (level F ζ hζ C R P H U))
              (q.kind.representative • KPContCotangentActualOverlap.labeledA q.places (c x),
                (H.atlas (level F ζ hζ C R P H U)).representative i))) Ω := by
  dsimp only
  intro hB
  let c : KPContLocalNorm.Space (KPContCotangentActualOverlap.d F * 3) → KPContCotangentActualOverlap.M F :=
    fun x => WithLp.toLp 2 (fun ik => x (finProdFinEquiv ik))
  let Y := fun x => q.kind.representative • KPContCotangentActualOverlap.labeledA q.places (c x)
  let Q := fun x => Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
    (level F ζ hζ C R P H U)) (Y x, (H.atlas (level F ζ hζ C R P H U)).representative i)
  let phase := fun x => (KPCuspGenuineMonodromy.chi F ζ hζ (q.splitting (c x)) : ℂ)
  let β := fun s => (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
    (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s))).val 0
  have hβ : DifferentiableOn ℂ β Ω := incoming_scalar_coefficient_holomorphic F ζ hζ C R P H U ι a Ω f hf
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := by
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro ik
    exact (EuclideanSpace.proj (𝕜 := ℝ) (finProdFinEquiv ik)).contDiff
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => KPContCotangentActualOverlap.labeledA q.places (c x)) := by
    apply contDiff_pi.mpr
    intro k
    exact ((contDiff_apply ℝ (ℂ × ℝ) (q.places.symm k)).comp
      (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).contDiff).comp hc
  have hact : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspGenuineMonodromy.SymmetricSpace F => q.kind.representative • y) := by
    change ContDiff ℝ (⊤ : ℕ∞) (KPCuspSiegel.action F q.kind.representative)
    unfold KPCuspSiegel.action KPCuspSiegel.glAction
    exact (KPArch.productAction_contDiff _ _).of_le le_top
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := hact.comp hA
  have hQ : Continuous Q := continuous_quotient_mk'.comp (hY.continuous.prodMk continuous_const)
  have hdom : KPContLocalNorm.LocalBall.carrier B ⊆ c ⁻¹' q.omega :=
    Metric.ball_subset_closedBall.trans hB
  have hphaseLC : IsLocallyConstant (fun x : c ⁻¹' q.omega => phase x.val) :=
    (q.splitting_locallyConstant.comp_continuous
      ((hc.continuous.comp continuous_subtype_val).subtype_mk (fun x => x.property))).comp
        (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))
  apply ChartAnalyticHelpers.chartJets_of_local_affine_exponential B Ω hopen
  intro x hx
  have hph : phase =ᶠ[𝓝 x] (fun _ => phase x) := by
    have hdopen : IsOpen (c ⁻¹' q.omega) := q.isOpen_omega.preimage hc.continuous
    have hloc := hphaseLC.eventually_eq ⟨x,hdom hx⟩
    have he : phase =ᶠ[nhdsWithin x (c ⁻¹' q.omega)] (fun _ => phase x) := by
      rw [nhdsWithin_eq_map_subtype_coe (hdom hx)]
      exact hloc
    rwa [nhdsWithin_eq_nhds.mpr (hdopen.mem_nhds (hdom hx))] at he
  by_cases hxE : Q x ∈ ends F ζ hζ C R P H U buffer a
  · obtain ⟨W,hW,hxW,ε,t,ht,hform⟩ := physical_incoming_local_formula F ζ hζ C R P H U ι a buffer i (Y x) hxE
    obtain ⟨V,hVph,hV,hxV⟩ := eventually_nhds_iff.mp hph
    let L := B.carrier ∩ V ∩ Y ⁻¹' W
    have hL : IsOpen L := (Metric.isOpen_ball.inter hV).inter (hW.preimage hY.continuous)
    have hxL : x ∈ L := ⟨⟨hx,hxV⟩,hxW⟩
    let τ := fun y => t (Y y)
    have hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ L := ht.comp hY.contDiffOn (fun y hy => hy.2)
    let e := fun y => Complex.exp (((Module.finrank ℚ F / 2 : ℕ) : ℂ) * ((4 : ℂ)/3) * (τ y : ℂ))
    let tc := fun y => (((Module.finrank ℚ F / 2 : ℕ) : ℂ) * 2) * (τ y : ℂ)
    let u₀ := fun y => if b then
      -(((Module.finrank ℚ F / 2 : ℕ) : ℂ)⁻¹) * ((deriv (deriv (χ a).toFun) (τ y) : ℝ) : ℂ) +
        2 * ((deriv (χ a).toFun (τ y) : ℝ) : ℂ) - 2 * ((4 : ℂ)/3) * ((deriv (χ a).toFun (τ y) : ℝ) : ℂ)
      else ((χ a).toFun (τ y) : ℂ)
    let u₁ := fun y => if b then -4 * ((deriv (χ a).toFun (τ y) : ℝ) : ℂ) else 0
    have hcast : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (τ y : ℂ)) L := Complex.ofRealCLM.contDiff.comp_contDiffOn hτ
    have hχ₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((χ a).toFun (τ y) : ℂ)) L :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((χ a).smooth.comp_contDiffOn hτ)
    have hχ₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((deriv (χ a).toFun (τ y) : ℝ) : ℂ)) L :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiff_infty_iff_deriv.mp (χ a).smooth).2.comp_contDiffOn hτ)
    have hχ₂ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((deriv (deriv (χ a).toFun) (τ y) : ℝ) : ℂ)) L :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp (χ a).smooth).2).2.comp_contDiffOn hτ)
    have he : ContDiffOn ℝ (⊤ : ℕ∞) e L := Complex.contDiff_exp.comp_contDiffOn
      ((contDiffOn_const.mul contDiffOn_const).mul hcast)
    have htc : ContDiffOn ℝ (⊤ : ℕ∞) tc L := contDiffOn_const.mul hcast
    have hu₀ : ContDiffOn ℝ (⊤ : ℕ∞) u₀ L := by
      cases b
      · exact hχ₀
      · exact ((contDiffOn_const.mul hχ₂).add (contDiffOn_const.mul hχ₁)).sub
          ((contDiffOn_const.mul contDiffOn_const).mul hχ₁)
    have hu₁ : ContDiffOn ℝ (⊤ : ℕ∞) u₁ L := by
      cases b
      · exact contDiffOn_const
      · exact contDiffOn_const.mul hχ₁
    refine ⟨L,hL,hxL,fun y hy => hy.1.1,tc,fun y => e y * u₀ y,fun y => e y * u₁ y,
      htc,he.mul hu₀,he.mul hu₁,fun s => phase x * (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * β s,
      ((differentiableOn_const _).mul (differentiableOn_const _)).mul hβ,?_⟩
    intro s hs y hy
    obtain ⟨hyE,hyheight,hyincoming⟩ := hform (Y y) hy.2
    change phase y * (ends F ζ hζ C R P H U buffer a).indicator _ (Q y) = _
    rw [Set.indicator_of_mem hyE,hyheight,hyincoming s (hΩspectral hs) (f s),hVph y hy.1.2]
    have hexp : KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s (τ y) =
        Complex.exp (s * tc y) * e y := by
      unfold KPIncomingCasimir.heightFactor
      dsimp [tc,e]
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hexp]
    cases b <;> dsimp [u₀,u₁,β,τ] <;> (try unfold KPCutoffSource.incomingCommutatorMultiplier) <;> ring
  · have hzero := incoming_cutoff_zero_germ F ζ hζ C R P H U ι a buffer (χ a) b (Q x) hxE
    have hz := Filter.Tendsto.eventually hQ.continuousAt hzero
    obtain ⟨V,hVz,hV,hxV⟩ := eventually_nhds_iff.mp hz
    let L := B.carrier ∩ V
    refine ⟨L,Metric.isOpen_ball.inter hV,⟨hx,hxV⟩,fun y hy => hy.1,
      fun _ => 0,fun _ => 0,fun _ => 0,contDiffOn_const,contDiffOn_const,contDiffOn_const,
      fun _ => 0,differentiableOn_const _,?_⟩
    intro s hs y hy
    change phase y * (ends F ζ hζ C R P H U buffer a).indicator _ (Q y) = _
    rw [hVz y hy.2 s (f s)]
    simp

end DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

end
