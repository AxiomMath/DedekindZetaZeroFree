module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

open MeasureTheory Filter Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

variable (F : Type) [Field F] [NumberField F]

abbrev L := PGLComplex.AdelicSlicesRaw.ArchGroup F
abbrev X := KPGlobalTorusBorelTwistCompatibility.GroupArch F
abbrev D0 := KPGlobalTorusBorelTwistCompatibility.groupArchDomain F
abbrev G (ζ : F) (hζ : IsPrimitiveRoot ζ 12) := KPGlobalTorusFunctionData.G F ζ hζ
abbrev Y := NumberField.InfinitePlace F → PGLComplex.Coordinates

def e0 : X F := fun _ => ![0, 1, 0]

def ell (z : X F) : L F := fun w =>
  Matrix.ProjGenLinGroup.mk (KPLiteralChamber.leftMatrix (z w))

def affineDomain : Set (Y F) := {x | ∀ w, x w ∈ PGLComplex.affineSource}

def affineEll (x : Y F) : L F := fun w => PGLComplex.affinePoint (x w)

def gaussTarget : Set (L F) := {a | ∀ w, a w ∈ PGLComplex.affineTarget}

def toAffine (z : X F) : Y F := fun w =>
  PGLComplex.AffineHaarFrame.coordinatesCLE.symm
    ![(z w 1)⁻¹ + z w 0 * z w 2 - 1, z w 2, z w 0]

def fromAffine (x : Y F) : X F := fun w =>
  let t := PGLComplex.complexCoordinates (x w)
  ![t 2, (1 + t 0 - t 1 * t 2)⁻¹, t 1]

def gaussInverse (a : L F) : X F :=
  fromAffine F (fun w => PGLComplex.affineInverse (a w))

def KernelSmooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : L F → V) : Prop :=
  ∀ a : L F, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => f (ell F z * a)) (D0 F)

def AffineSmooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : L F → V) : Prop :=
  ∀ a : L F, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun x => f (a * affineEll F x)) (affineDomain F)

def rawBump (b : ContDiffBump (e0 F)) (a : L F) : ℝ :=
  if a ∈ gaussTarget F then b (gaussInverse F a) else 0

def eta (μ : Measure (L F)) (b : ContDiffBump (e0 F)) (a : L F) : ℝ :=
  rawBump F b a / ∫ y, rawBump F b y ∂μ

def BumpSequence (μ : Measure (L F))
    (b : ℕ → ContDiffBump (e0 F)) : Prop :=
  (∀ m, Metric.closedBall (e0 F) (b m).rOut ⊆ D0 F) ∧
  Tendsto (fun m => (b m).rOut) atTop (𝓝 0) ∧
  (∀ m, 0 < ∫ a, rawBump F (b m) a ∂μ) ∧
  (∀ m, Continuous (eta F μ (b m)) ∧ KernelSmooth F (eta F μ (b m)) ∧
    HasCompactSupport (eta F μ (b m)) ∧
    (∀ a, 0 ≤ eta F μ (b m) a) ∧ (∫ a, eta F μ (b m) a ∂μ) = 1) ∧
  (∀ O ∈ 𝓝 (1 : L F), ∀ᶠ m in atTop,
    tsupport (eta F μ (b m)) ⊆ O)

private theorem complex_coordinates_cle (x : PGLComplex.Coordinates) :
    PGLComplex.complexCoordinates x = PGLComplex.AffineHaarFrame.coordinatesCLE x := rfl

private theorem complex_toAffine (z : X F) (w : NumberField.InfinitePlace F) :
    PGLComplex.complexCoordinates (toAffine F z w) =
      ![(z w 1)⁻¹ + z w 0 * z w 2 - 1, z w 2, z w 0] := by
  rw [complex_coordinates_cle]
  exact PGLComplex.AffineHaarFrame.coordinatesCLE.apply_symm_apply _

private theorem delta_toAffine (z : X F) (w : NumberField.InfinitePlace F) :
    PGLComplex.delta (toAffine F z w) = (z w 1)⁻¹ := by
  rw [PGLComplex.delta, complex_toAffine]
  simp
  ring

theorem toAffine_mapsTo : MapsTo (toAffine F) (D0 F) (affineDomain F) := by
  intro z hz w
  change PGLComplex.delta (toAffine F z w) ≠ 0
  rw [delta_toAffine]
  exact inv_ne_zero (hz w)

private theorem fromAffine_mapsTo : MapsTo (fromAffine F) (affineDomain F) (D0 F) := by
  intro x hx w
  change (PGLComplex.delta (x w))⁻¹ ≠ 0
  exact inv_ne_zero (hx w)

private theorem fromAffine_toAffine (z : X F) : fromAffine F (toAffine F z) = z := by
  ext w i
  unfold fromAffine
  rw [complex_toAffine]
  fin_cases i <;> simp
  ring_nf
  simp

private theorem toAffine_fromAffine (x : Y F) : toAffine F (fromAffine F x) = x := by
  funext w
  apply PGLComplex.AffineHaarFrame.coordinatesCLE.injective
  rw [← complex_coordinates_cle, complex_toAffine, ← complex_coordinates_cle]
  unfold fromAffine
  ext i
  fin_cases i <;> simp
  ring

private theorem affinePoint_toAffine (z : X F) (hz : z ∈ D0 F)
    (w : NumberField.InfinitePlace F) :
    PGLComplex.affinePoint (toAffine F z w) =
      Matrix.ProjGenLinGroup.mk (KPLiteralChamber.leftMatrix (z w)) := by
  have hw : z w 1 ≠ 0 := hz w
  unfold PGLComplex.affinePoint
  rw [dif_pos (show PGLComplex.delta (toAffine F z w) ≠ 0 from toAffine_mapsTo F hz w)]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (z w 1) hw, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  rw [KPLiteralChamber.leftMatrix_val _ hw]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, PGLComplex.affineMatrix,
      complex_toAffine, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar]
  all_goals first | ring | skip
  all_goals rw [mul_inv_cancel₀ hw]

theorem affineEll_toAffine (z : X F) (hz : z ∈ D0 F) :
    affineEll F (toAffine F z) = ell F z := by
  funext w
  exact affinePoint_toAffine F z hz w

private theorem ell_mem_gaussTarget (z : X F) (hz : z ∈ D0 F) :
    ell F z ∈ gaussTarget F := by
  rw [← affineEll_toAffine F z hz]
  intro w
  rw [affineEll, ← PGLComplex.affineChart_apply _ (toAffine_mapsTo F hz w)]
  rw [← PGLComplex.affineChart_target]
  exact PGLComplex.affineChart.map_source (by rw [PGLComplex.affineChart_source]; exact toAffine_mapsTo F hz w)

private theorem gaussInverse_mapsTo : MapsTo (gaussInverse F) (gaussTarget F) (D0 F) := by
  intro a ha
  apply fromAffine_mapsTo F
  intro w
  change PGLComplex.affineInverse (a w) ∈ PGLComplex.affineSource
  rw [← PGLComplex.affineChart_symm_apply _ (ha w), ← PGLComplex.affineChart_source]
  apply PGLComplex.affineChart.symm.map_source
  change a w ∈ PGLComplex.affineChart.target
  rw [PGLComplex.affineChart_target]
  exact ha w

private theorem ell_gaussInverse (a : L F) (ha : a ∈ gaussTarget F) :
    ell F (gaussInverse F a) = a := by
  rw [← affineEll_toAffine F _ (gaussInverse_mapsTo F ha)]
  change affineEll F (toAffine F (fromAffine F _)) = a
  rw [toAffine_fromAffine]
  funext w
  change PGLComplex.affinePoint (PGLComplex.affineInverse (a w)) = a w
  have hs : PGLComplex.affineInverse (a w) ∈ PGLComplex.affineSource := by
    rw [← PGLComplex.affineChart_symm_apply _ (ha w), ← PGLComplex.affineChart_source]
    apply PGLComplex.affineChart.symm.map_source
    change a w ∈ PGLComplex.affineChart.target
    rw [PGLComplex.affineChart_target]
    exact ha w
  rw [← PGLComplex.affineChart_apply _ hs,
    ← PGLComplex.affineChart_symm_apply _ (ha w)]
  exact PGLComplex.affineChart.right_inv (by rw [PGLComplex.affineChart_target]; exact ha w)

private theorem e0_mem : e0 F ∈ D0 F := by
  intro w
  simp [e0]

private theorem ell_e0 : ell F (e0 F) = 1 := by
  funext w
  change Matrix.ProjGenLinGroup.mk (KPLiteralChamber.leftMatrix (e0 F w)) = 1
  have he : KPLiteralChamber.leftMatrix (e0 F w) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    rw [KPLiteralChamber.leftMatrix_val _ (e0_mem F w)]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [e0]
  rw [he, map_one]

private theorem ell_insertion (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (z : X F) :
    KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (ell F z) := by
  exact KPLiteralChamber.left_insertion F ζ hζ z

theorem gauss_domain_open : IsOpen (D0 F) :=
  KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F

theorem toAffine_contDiff : ContDiffOn ℝ (⊤ : ℕ∞) (toAffine F) (D0 F) := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro w
  unfold toAffine
  apply PGLComplex.AffineHaarFrame.coordinatesCLE.symm.contDiff.contDiffAt.comp
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp
  all_goals fun_prop (disch := exact hz w)

theorem fromAffine_contDiff :
    ContDiffOn ℝ (⊤ : ℕ∞) (fromAffine F) (affineDomain F) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro w
  unfold fromAffine
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp
  all_goals
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : Y F => PGLComplex.complexCoordinates (x w)) :=
      PGLComplex.contDiff_complexCoordinates.comp (contDiff_apply ℝ PGLComplex.Coordinates w)
    have hci (j : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : Y F => PGLComplex.complexCoordinates (x w) j) x :=
      (contDiff_pi.mp hc j).contDiffAt
    fun_prop (disch := first | exact hx w | exact hci _)

def affineProductChart : OpenPartialHomeomorph (Y F) (L F) :=
  OpenPartialHomeomorph.pi (fun _ : NumberField.InfinitePlace F => PGLComplex.affineChart)

theorem affineProductChart_source :
    (affineProductChart F).source = affineDomain F := by
  ext x
  simp [affineProductChart, OpenPartialHomeomorph.pi, PartialEquiv.pi,
    affineDomain, Set.pi]

theorem affineProductChart_target :
    (affineProductChart F).target = gaussTarget F := by
  ext a
  simp [affineProductChart, OpenPartialHomeomorph.pi, PartialEquiv.pi,
    gaussTarget, Set.pi]

theorem affineProductChart_apply (x : Y F) (hx : x ∈ affineDomain F) :
    affineProductChart F x = affineEll F x := by
  funext w
  exact PGLComplex.affineChart_apply _ (hx w)

theorem affineProductChart_symm_apply (a : L F) (ha : a ∈ gaussTarget F) :
    (affineProductChart F).symm a = fun w => PGLComplex.affineInverse (a w) := by
  funext w
  exact PGLComplex.affineChart_symm_apply _ (ha w)

theorem affineDomain_open : IsOpen (affineDomain F) := by
  rw [← affineProductChart_source F]
  exact (affineProductChart F).open_source

theorem gaussTarget_open : IsOpen (gaussTarget F) := by
  rw [← affineProductChart_target F]
  exact (affineProductChart F).open_target

theorem affineTarget_one : (1 : L F) ∈ gaussTarget F := by
  intro w
  have h := PGLComplex.affineChart.map_source (show (0 : PGLComplex.Coordinates) ∈
    PGLComplex.affineChart.source by simp)
  simpa using h

 def affineTransition (l r : L F) (x : Y F) : Y F := fun w =>
  PGLComplex.affineTranslate (l w).out (r w).out (x w)

private theorem affineTransition_eq (l r : L F) (x : Y F) (hx : x ∈ affineDomain F) :
    affineTransition F l r x = fun w => PGLComplex.affineInverse ((l * affineEll F x * r) w) := by
  funext w
  rw [affineTransition, PGLComplex.affineTranslate_eq_inverse_translate _ _ _ (hx w)]
  change PGLComplex.affineInverse
    (Matrix.ProjGenLinGroup.mk (l w).out * PGLComplex.affinePoint (x w) *
      Matrix.ProjGenLinGroup.mk (r w).out) = _
  rw [show Matrix.ProjGenLinGroup.mk (l w).out = l w from Quotient.out_eq _,
    show Matrix.ProjGenLinGroup.mk (r w).out = r w from Quotient.out_eq _]
  rfl

private theorem affineTransition_contDiffAt (l r : L F) (x : Y F)
    (hx : x ∈ affineDomain F) (ht : l * affineEll F x * r ∈ gaussTarget F) :
    ContDiffAt ℝ (⊤ : ℕ∞) (affineTransition F l r) x := by
  apply contDiffAt_pi.mpr
  intro w
  apply (PGLComplex.contDiffAt_affineTranslate (l w).out (r w).out (x w) ?_).comp
    x (contDiff_apply ℝ PGLComplex.Coordinates w).contDiffAt
  rw [PGLComplex.affineTranslate_denominator _ _ _ (hx w)]
  rw [show Matrix.ProjGenLinGroup.mk (l w).out = l w from Quotient.out_eq _,
    show Matrix.ProjGenLinGroup.mk (r w).out = r w from Quotient.out_eq _]
  exact ht w

private theorem affineTransition_reconstruct (l r : L F) (x : Y F)
    (hx : x ∈ affineDomain F) (ht : l * affineEll F x * r ∈ gaussTarget F) :
    affineTransition F l r x ∈ affineDomain F ∧
      affineEll F (affineTransition F l r x) = l * affineEll F x * r := by
  rw [affineTransition_eq F l r x hx]
  have h := (affineProductChart F).map_target (show l * affineEll F x * r ∈
    (affineProductChart F).target by rwa [affineProductChart_target F])
  rw [affineProductChart_symm_apply F _ ht, affineProductChart_source F] at h
  refine ⟨h, ?_⟩
  rw [← affineProductChart_apply F _ h, ← affineProductChart_symm_apply F _ ht]
  exact (affineProductChart F).right_inv (by rwa [affineProductChart_target F])

theorem affineEll_continuousAt (x : Y F) (hx : x ∈ affineDomain F) :
    ContinuousAt (affineEll F) x := by
  have h : (affineProductChart F : Y F → L F) =ᶠ[𝓝 x] affineEll F := by
    filter_upwards [(affineDomain_open F).mem_nhds hx] with y hy
    exact affineProductChart_apply F y hy
  apply ContinuousAt.congr_of_eventuallyEq _ h.symm
  exact (affineProductChart F).continuousAt (by rwa [affineProductChart_source F])

private theorem affine_transition_near (l r : L F) (x : Y F)
    (hx : x ∈ affineDomain F) (ht : l * affineEll F x * r ∈ gaussTarget F) :
    ∀ᶠ y in 𝓝 x, y ∈ affineDomain F ∧
      affineTransition F l r y ∈ affineDomain F ∧
      affineEll F (affineTransition F l r y) = l * affineEll F y * r := by
  have hc : ContinuousAt (fun y => l * affineEll F y * r) x := by
    exact (continuousAt_const.mul (affineEll_continuousAt F x hx)).mul continuousAt_const
  have hn := hc.preimage_mem_nhds ((gaussTarget_open F).mem_nhds ht)
  filter_upwards [(affineDomain_open F).mem_nhds hx, hn] with y hy ht'
  exact ⟨hy, affineTransition_reconstruct F l r y hy ht'⟩

private theorem affine_left_right_smooth {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : L F → V) :
    AffineSmooth F f ↔ ∀ a : L F, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => f (affineEll F x * a)) (affineDomain F) := by
  constructor
  · intro hf a x hx
    let k := affineEll F x * a
    let l := k⁻¹
    have ht : l * affineEll F x * a ∈ gaussTarget F := by
      convert affineTarget_one F using 1
      dsimp [l, k]
      group
    have htr := affineTransition_contDiffAt F l a x hx ht
    have hr := affineTransition_reconstruct F l a x hx ht
    have hs : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => f (k * affineEll F y)) (affineTransition F l a x) :=
      (hf k _ hr.1).contDiffAt ((affineDomain_open F).mem_nhds hr.1)
    apply ContDiffAt.contDiffWithinAt
    apply (hs.comp x htr).congr_of_eventuallyEq
    filter_upwards [affine_transition_near F l a x hx ht] with y hy
    change f (affineEll F y * a) = f (k * affineEll F (affineTransition F l a y))
    rw [hy.2.2]
    congr 1
    dsimp [l]
    group
  · intro hf a x hx
    let k := a * affineEll F x
    let r := k⁻¹
    have ht : a * affineEll F x * r ∈ gaussTarget F := by
      convert affineTarget_one F using 1
      dsimp [r, k]
      group
    have htr := affineTransition_contDiffAt F a r x hx ht
    have hr := affineTransition_reconstruct F a r x hx ht
    have hs : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => f (affineEll F y * k)) (affineTransition F a r x) :=
      (hf k _ hr.1).contDiffAt ((affineDomain_open F).mem_nhds hr.1)
    apply ContDiffAt.contDiffWithinAt
    apply (hs.comp x htr).congr_of_eventuallyEq
    filter_upwards [affine_transition_near F a r x hx ht] with y hy
    change f (a * affineEll F y) = f (affineEll F (affineTransition F a r y) * k)
    rw [hy.2.2]
    congr 1
    dsimp [r]
    group

 def coordinateHomeomorph
    (hmap : MapsTo (toAffine F) (D0 F) (affineDomain F))
    (hback : MapsTo (fromAffine F) (affineDomain F) (D0 F))
    (hleft : ∀ z ∈ D0 F, fromAffine F (toAffine F z) = z)
    (hright : ∀ x ∈ affineDomain F, toAffine F (fromAffine F x) = x) :
    OpenPartialHomeomorph (X F) (Y F) where
  toFun := toAffine F
  invFun := fromAffine F
  source := D0 F
  target := affineDomain F
  map_source' := hmap
  map_target' := hback
  left_inv' := hleft
  right_inv' := hright
  open_source := gauss_domain_open F
  open_target := affineDomain_open F
  continuousOn_toFun := (toAffine_contDiff F).continuousOn
  continuousOn_invFun := (fromAffine_contDiff F).continuousOn

private theorem gauss_homeomorph_of_coordinate_algebra
    (hmap : MapsTo (toAffine F) (D0 F) (affineDomain F))
    (hback : MapsTo (fromAffine F) (affineDomain F) (D0 F))
    (hleft : ∀ z ∈ D0 F, fromAffine F (toAffine F z) = z)
    (hright : ∀ x ∈ affineDomain F, toAffine F (fromAffine F x) = x)
    (hell : ∀ z ∈ D0 F, affineEll F (toAffine F z) = ell F z) :
    ∃ C : OpenPartialHomeomorph (X F) (L F),
      C.source = D0 F ∧ C.target = gaussTarget F ∧
      (∀ z ∈ D0 F, C z = ell F z) ∧
      (∀ a ∈ gaussTarget F, C.symm a = gaussInverse F a) := by
  let c := coordinateHomeomorph F hmap hback hleft hright
  let C := c.trans (affineProductChart F)
  have hsrc : C.source = D0 F := by
    ext z
    change (z ∈ D0 F ∧ toAffine F z ∈ (affineProductChart F).source) ↔ z ∈ D0 F
    rw [affineProductChart_source F]
    exact ⟨And.left, fun hz => ⟨hz, hmap hz⟩⟩
  have htar : C.target = gaussTarget F := by
    ext a
    change (a ∈ (affineProductChart F).target ∧
      (affineProductChart F).symm a ∈ affineDomain F) ↔ a ∈ gaussTarget F
    rw [affineProductChart_target F]
    exact ⟨And.left, fun ha => ⟨ha, by
      simpa only [affineProductChart_source F] using
        (affineProductChart F).map_target (by rwa [affineProductChart_target F])⟩⟩
  refine ⟨C, hsrc, htar, ?_, ?_⟩
  · intro z hz
    change affineProductChart F (toAffine F z) = ell F z
    rw [affineProductChart_apply F _ (hmap hz), hell z hz]
  · intro a ha
    change fromAffine F ((affineProductChart F).symm a) = gaussInverse F a
    rw [affineProductChart_symm_apply F a ha]
    rfl

private theorem smooth_bridge_of_coordinate_algebra
    (hmap : MapsTo (toAffine F) (D0 F) (affineDomain F))
    (hback : MapsTo (fromAffine F) (affineDomain F) (D0 F))
    (hright : ∀ x ∈ affineDomain F, toAffine F (fromAffine F x) = x)
    (hell : ∀ z ∈ D0 F, affineEll F (toAffine F z) = ell F z)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : L F → V) :
    KernelSmooth F f ↔ AffineSmooth F f := by
  rw [affine_left_right_smooth F f]
  constructor
  · intro hf a
    have hs := (hf a).comp (fromAffine_contDiff F) hback
    apply hs.congr
    intro x hx
    change f (affineEll F x * a) = f (ell F (fromAffine F x) * a)
    rw [← hell _ (hback hx), hright x hx]
  · intro hf a
    have hs := (hf a).comp (toAffine_contDiff F) hmap
    apply hs.congr
    intro z hz
    change f (ell F z * a) = f (affineEll F (toAffine F z) * a)
    rw [hell z hz]

private theorem gaussInverse_affine_contDiffAt (a : L F) (x : Y F)
    (hx : x ∈ affineDomain F) (ht : a * affineEll F x ∈ gaussTarget F) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => gaussInverse F (a * affineEll F y)) x := by
  have ht' : a * affineEll F x * 1 ∈ gaussTarget F := by simpa using ht
  have htr := affineTransition_contDiffAt F a 1 x hx ht'
  have hr := affineTransition_reconstruct F a 1 x hx ht'
  have hs := (fromAffine_contDiff F _ hr.1).contDiffAt
    ((affineDomain_open F).mem_nhds hr.1)
  apply (hs.comp x htr).congr_of_eventuallyEq
  filter_upwards [(affineDomain_open F).mem_nhds hx] with y hy
  change gaussInverse F (a * affineEll F y) = fromAffine F (affineTransition F a 1 y)
  rw [affineTransition_eq F a 1 y hy]
  simp only [mul_one, gaussInverse]

private theorem ell_continuousAt_of_coordinate_algebra
    (hmap : MapsTo (toAffine F) (D0 F) (affineDomain F))
    (hell : ∀ z ∈ D0 F, affineEll F (toAffine F z) = ell F z)
    (z : X F) (hz : z ∈ D0 F) : ContinuousAt (ell F) z := by
  have hc := (affineEll_continuousAt F _ (hmap hz)).comp
    ((toAffine_contDiff F z hz).contDiffAt ((gauss_domain_open F).mem_nhds hz)).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [(gauss_domain_open F).mem_nhds hz] with y hy
  exact (hell y hy).symm

theorem actualSmoothBridge {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : L F → V) : KernelSmooth F f ↔ AffineSmooth F f :=
  smooth_bridge_of_coordinate_algebra F (toAffine_mapsTo F) (fromAffine_mapsTo F)
    (fun x _ => toAffine_fromAffine F x) (affineEll_toAffine F) f

private theorem actualEll_continuousAt (z : X F) (hz : z ∈ D0 F) :
    ContinuousAt (ell F) z :=
  ell_continuousAt_of_coordinate_algebra F (toAffine_mapsTo F) (affineEll_toAffine F) z hz

 instance arch_t2 : T2Space (L F) := by
  letI : ChartedSpace PGLComplex.Coordinates PGLComplex.Group := PGLComplex.affineChartedSpace
  letI : T1Space PGLComplex.Group := ChartedSpace.t1Space PGLComplex.Coordinates PGLComplex.Group
  letI : T2Space PGLComplex.Group := inferInstance
  change T2Space (NumberField.InfinitePlace F → PGLComplex.Group)
  exact @Pi.t2Space (NumberField.InfinitePlace F) (fun _ => PGLComplex.Group)
    (fun _ => inferInstance) (fun _ => inferInstance)

private theorem ell_continuousOn : ContinuousOn (ell F) (D0 F) := by
  intro z hz
  exact (ell_continuousAt_of_coordinate_algebra F (toAffine_mapsTo F)
    (affineEll_toAffine F) z hz).continuousWithinAt

private theorem rawBump_support_subset (b : ContDiffBump (e0 F)) :
    Function.support (rawBump F b) ⊆ ell F '' Metric.closedBall (e0 F) b.rOut := by
  intro a ha
  have ht : a ∈ gaussTarget F := by
    by_contra h
    exact ha (by simp [rawBump, h])
  have hb : b (gaussInverse F a) ≠ 0 := by simpa [rawBump, ht] using ha
  have hball : gaussInverse F a ∈ Metric.closedBall (e0 F) b.rOut := by
    apply Metric.ball_subset_closedBall
    rw [← b.support_eq]
    exact hb
  exact ⟨gaussInverse F a, hball, ell_gaussInverse F a ht⟩

private theorem rawBump_image_compact (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) :
    IsCompact (ell F '' Metric.closedBall (e0 F) b.rOut) :=
  (isCompact_closedBall (e0 F) b.rOut).image_of_continuousOn ((ell_continuousOn F).mono hb)

private theorem rawBump_tsupport_subset (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) :
    tsupport (rawBump F b) ⊆ ell F '' Metric.closedBall (e0 F) b.rOut :=
  (rawBump_image_compact F b hb).isClosed.closure_subset_iff.mpr
    (rawBump_support_subset F b)

private theorem rawBump_compact (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) :
    HasCompactSupport (rawBump F b) :=
  (rawBump_image_compact F b hb).of_isClosed_subset (isClosed_tsupport _)
    (rawBump_tsupport_subset F b hb)

private theorem rawBump_zero_near (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) (a : L F)
    (ha : a ∉ ell F '' Metric.closedBall (e0 F) b.rOut) :
    rawBump F b =ᶠ[𝓝 a] 0 := by
  filter_upwards [(rawBump_image_compact F b hb).isClosed.compl_mem_nhds ha] with y hy
  exact Function.notMem_support.mp (fun hs => hy (rawBump_support_subset F b hs))

private theorem rawBump_affine_smooth (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) : AffineSmooth F (rawBump F b) := by
  intro a x hx
  apply ContDiffAt.contDiffWithinAt
  by_cases ht : a * affineEll F x ∈ gaussTarget F
  · have hd := b.contDiff.contDiffAt.comp x (gaussInverse_affine_contDiffAt F a x hx ht)
    apply hd.congr_of_eventuallyEq
    have hc : ContinuousAt (fun y => a * affineEll F y) x :=
      continuousAt_const.mul (affineEll_continuousAt F x hx)
    filter_upwards [hc.preimage_mem_nhds ((gaussTarget_open F).mem_nhds ht)] with y hy
    change (if a * affineEll F y ∈ gaussTarget F then b (gaussInverse F (a * affineEll F y)) else 0) = _
    change a * affineEll F y ∈ gaussTarget F at hy
    rw [if_pos hy]
    rfl
  · have hn : a * affineEll F x ∉ ell F '' Metric.closedBall (e0 F) b.rOut := by
      rintro ⟨z, hz, he⟩
      exact ht (he ▸ ell_mem_gaussTarget F z (hb hz))
    have hc : ContinuousAt (fun y => a * affineEll F y) x :=
      continuousAt_const.mul (affineEll_continuousAt F x hx)
    exact contDiffAt_const.congr_of_eventuallyEq
      ((rawBump_zero_near F b hb _ hn).comp_tendsto hc)

private theorem rawBump_continuous (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) : Continuous (rawBump F b) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha : a ∈ gaussTarget F
  · have hc : ContinuousAt (gaussInverse F) a := by
      have ht : a ∈ (affineProductChart F).target := by rwa [affineProductChart_target F]
      have hs := (affineProductChart F).map_target ht
      rw [affineProductChart_source F] at hs
      have hd := ((fromAffine_contDiff F _ hs).contDiffAt
        ((affineDomain_open F).mem_nhds hs)).continuousAt
      have hi := (affineProductChart F).symm.continuousAt ht
      apply (hd.comp hi).congr_of_eventuallyEq
      filter_upwards [(gaussTarget_open F).mem_nhds ha] with y hy
      change gaussInverse F y = fromAffine F ((affineProductChart F).symm y)
      rw [affineProductChart_symm_apply F y hy]
      rfl
    apply (b.continuous.continuousAt.comp hc).congr_of_eventuallyEq
    filter_upwards [(gaussTarget_open F).mem_nhds ha] with y hy
    simp [rawBump, hy]
  · have hn : a ∉ ell F '' Metric.closedBall (e0 F) b.rOut := by
      rintro ⟨z, hz, he⟩
      exact ha (he ▸ ell_mem_gaussTarget F z (hb hz))
    exact continuousAt_const.congr (rawBump_zero_near F b hb a hn).symm

private theorem rawBump_kernel_smooth (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) : KernelSmooth F (rawBump F b) :=
  (smooth_bridge_of_coordinate_algebra F (toAffine_mapsTo F) (fromAffine_mapsTo F)
    (fun x _ => toAffine_fromAffine F x) (affineEll_toAffine F) _).mpr
    (rawBump_affine_smooth F b hb)

private theorem closedBall_subset_D0 (r : ℝ) (hr : r < 1) :
    Metric.closedBall (e0 F) r ⊆ D0 F := by
  intro z hz w
  have hz' : dist z (e0 F) ≤ r := by simpa [Metric.mem_closedBall] using hz
  have h1 : dist (z w) ((e0 F) w) ≤ r := le_trans (dist_le_pi_dist z (e0 F) w) hz'
  have h2 : dist ((z w) 1) (((e0 F) w) 1) ≤ r :=
    le_trans (dist_le_pi_dist (z w) ((e0 F) w) 1) h1
  have h3 : ((e0 F) w) 1 = (1 : ℂ) := by simp [e0]
  rw [h3] at h2
  intro hzero
  rw [hzero] at h2
  simp [dist_eq_norm] at h2
  linarith

 def bumpB (m : ℕ) : ContDiffBump (e0 F) :=
  { rIn := 1/(2*((m:ℝ)+2))
    rOut := 1/((m:ℝ)+2)
    rIn_pos := by positivity
    rIn_lt_rOut := by
      have h : (0:ℝ) < (m:ℝ)+2 := by positivity
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith) }

private theorem bumpB_support (m : ℕ) :
    Metric.closedBall (e0 F) (bumpB F m).rOut ⊆ D0 F := by
  apply closedBall_subset_D0
  simp only [bumpB]
  have hpos : (0:ℝ) < (m:ℝ)+2 := by positivity
  rw [div_lt_one hpos]
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]

private theorem bumpB_tendsto :
    Tendsto (fun m => (bumpB F m).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have h2 : Tendsto (fun n : ℕ => ((n:ℕ)+2 : ℕ)) atTop atTop :=
    tendsto_add_atTop_nat 2
  have := h.comp h2
  simp only [bumpB]
  simpa [Function.comp_def, Nat.cast_add] using this

private theorem rawBump_nonneg (b : ContDiffBump (e0 F)) (a : L F) :
    0 ≤ rawBump F b a := by
  unfold rawBump
  split
  · exact b.nonneg
  · exact le_refl 0

private theorem eta_nonneg (μ : Measure (L F)) (b : ContDiffBump (e0 F))
    (hpos : 0 < ∫ y, rawBump F b y ∂μ) (a : L F) : 0 ≤ eta F μ b a := by
  have hden : 0 ≤ (∫ y, rawBump F b y ∂μ)⁻¹ := inv_nonneg.mpr hpos.le
  simp only [eta, div_eq_mul_inv]
  exact mul_nonneg (rawBump_nonneg F b a) hden

private theorem eta_integral_eq_one (μ : Measure (L F)) (b : ContDiffBump (e0 F))
    (hne : ∫ y, rawBump F b y ∂μ ≠ 0) : ∫ a, eta F μ b a ∂μ = 1 := by
  have h1 : ∫ a, eta F μ b a ∂μ =
      (∫ a, rawBump F b a ∂μ) / (∫ a, rawBump F b a ∂μ) := by
    simp only [eta]
    exact MeasureTheory.integral_div _ _
  rw [h1, div_self hne]

private theorem eta_eq (μ : Measure (L F)) (b : ContDiffBump (e0 F)) :
    eta F μ b = fun a => rawBump F b a * (∫ y, rawBump F b y ∂μ)⁻¹ := by
  funext a
  simp only [eta, div_eq_mul_inv]

private theorem continuous_eta (μ : Measure (L F)) (b : ContDiffBump (e0 F))
    (hc : Continuous (rawBump F b)) : Continuous (eta F μ b) := by
  rw [eta_eq F μ b]
  exact hc.mul continuous_const

private theorem hasCompactSupport_eta (μ : Measure (L F)) (b : ContDiffBump (e0 F))
    (hc : HasCompactSupport (rawBump F b)) : HasCompactSupport (eta F μ b) := by
  rw [eta_eq F μ b]
  exact hc.mul_right

private theorem kernelSmooth_eta (μ : Measure (L F)) (b : ContDiffBump (e0 F))
    (hc : KernelSmooth F (rawBump F b)) : KernelSmooth F (eta F μ b) := by
  rw [eta_eq F μ b]
  intro a
  exact (hc a).smul_const _

private theorem one_mem_gaussTarget : (1 : L F) ∈ gaussTarget F := by
  intro w
  have h := PGLComplex.affineChart.map_source
    (show (0 : PGLComplex.Coordinates) ∈ PGLComplex.affineChart.source by simp)
  simpa [gaussTarget] using h

private theorem affineInverse_one : PGLComplex.affineInverse (1 : PGLComplex.Group) = 0 := by
  have h1 : (1 : PGLComplex.Group) ∈ PGLComplex.affineTarget := by
    have h := PGLComplex.affineChart.map_source
      (show (0 : PGLComplex.Coordinates) ∈ PGLComplex.affineChart.source by simp)
    simpa using h
  rw [← PGLComplex.affineChart_symm_apply 1 h1, ← PGLComplex.affineChart_zero]
  exact PGLComplex.affineChart.left_inv (x := 0) (by simp)

private theorem fromAffine_zero : fromAffine F (0 : Y F) = e0 F := by
  funext w i
  fin_cases i <;> simp [fromAffine, e0, PGLComplex.complexCoordinates, Complex.ext_iff]

private theorem rawBump_one (b : ContDiffBump (e0 F)) : rawBump F b 1 = 1 := by
  rw [rawBump, if_pos (one_mem_gaussTarget F)]
  have hg : gaussInverse F (1 : L F) = e0 F := by
    simp only [gaussInverse]
    rw [show (fun w : NumberField.InfinitePlace F => PGLComplex.affineInverse ((1 : L F) w)) =
        (0 : Y F) from by funext w; exact affineInverse_one]
    exact fromAffine_zero F
  rw [hg]
  exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)

private theorem rawBump_integral_pos (μ : Measure (L F)) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ]
    (b : ContDiffBump (e0 F)) (hc : Continuous (rawBump F b))
    (hcomp : HasCompactSupport (rawBump F b)) : 0 < ∫ a, rawBump F b a ∂μ :=
  hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp
    (fun a => rawBump_nonneg F b a) (by rw [rawBump_one F b]; norm_num)

private theorem eta_tsupport_subset (μ : Measure (L F)) (b : ContDiffBump (e0 F))
    (hb : Metric.closedBall (e0 F) b.rOut ⊆ D0 F) :
    tsupport (eta F μ b) ⊆ ell F '' Metric.closedBall (e0 F) b.rOut := by
  rw [eta_eq F μ b]
  exact tsupport_mul_subset_left.trans (rawBump_tsupport_subset F b hb)

private theorem bumpB_shrinking (μ : Measure (L F)) :
    ∀ O ∈ 𝓝 (1 : L F), ∀ᶠ m in atTop, tsupport (eta F μ (bumpB F m)) ⊆ O := by
  intro O hO
  have hc := actualEll_continuousAt F (e0 F) (e0_mem F)
  have hn : ell F ⁻¹' O ∈ 𝓝 (e0 F) :=
    hc.preimage_mem_nhds (by simpa only [ell_e0 F] using hO)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hr : ∀ᶠ m in atTop, (bumpB F m).rOut < ε :=
    (bumpB_tendsto F).eventually (gt_mem_nhds hε)
  filter_upwards [hr] with m hm
  intro a ha
  obtain ⟨z, hz, rfl⟩ := eta_tsupport_subset F μ (bumpB F m) (bumpB_support F m) ha
  apply hball
  exact lt_of_le_of_lt hz hm

theorem actual_chart_bridge_and_normalized_bumps
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μL : Measure (L F)) [μL.IsHaarMeasure] :
  IsOpen (D0 F) ∧ e0 F ∈ D0 F ∧ ell F (e0 F) = 1 ∧
  (∀ z : X F, KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z =
    PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (ell F z)) ∧
  (∃ C : OpenPartialHomeomorph (X F) (L F),
    C.source = D0 F ∧ C.target = gaussTarget F ∧
    (∀ z ∈ D0 F, C z = ell F z) ∧
    (∀ a ∈ gaussTarget F, C.symm a = gaussInverse F a)) ∧
  ContDiffOn ℝ (⊤ : ℕ∞) (toAffine F) (D0 F) ∧
  ContDiffOn ℝ (⊤ : ℕ∞) (fromAffine F) (affineDomain F) ∧
  Set.MapsTo (toAffine F) (D0 F) (affineDomain F) ∧
  Set.MapsTo (fromAffine F) (affineDomain F) (D0 F) ∧
  (∀ z ∈ D0 F, fromAffine F (toAffine F z) = z ∧
    affineEll F (toAffine F z) = ell F z) ∧
  (∀ x ∈ affineDomain F, toAffine F (fromAffine F x) = x) ∧
  (∀ f : L F → ℝ, KernelSmooth F f ↔ AffineSmooth F f) ∧
  (∀ f : L F → ℂ, KernelSmooth F f ↔ AffineSmooth F f) ∧
  ∃ b : ℕ → ContDiffBump (e0 F), BumpSequence F μL b := by
  refine ⟨gauss_domain_open F, e0_mem F, ell_e0 F, ell_insertion F ζ hζ, ?_,
    toAffine_contDiff F, fromAffine_contDiff F, toAffine_mapsTo F, fromAffine_mapsTo F,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact gauss_homeomorph_of_coordinate_algebra F (toAffine_mapsTo F)
      (fromAffine_mapsTo F) (fun z _ => fromAffine_toAffine F z)
      (fun x _ => toAffine_fromAffine F x) (affineEll_toAffine F)
  · exact fun z hz => ⟨fromAffine_toAffine F z, affineEll_toAffine F z hz⟩
  · exact fun x _ => toAffine_fromAffine F x
  · exact fun f => smooth_bridge_of_coordinate_algebra F (toAffine_mapsTo F)
      (fromAffine_mapsTo F) (fun x _ => toAffine_fromAffine F x) (affineEll_toAffine F) f
  · exact fun f => smooth_bridge_of_coordinate_algebra F (toAffine_mapsTo F)
      (fromAffine_mapsTo F) (fun x _ => toAffine_fromAffine F x) (affineEll_toAffine F) f
  · refine ⟨bumpB F, bumpB_support F, bumpB_tendsto F, ?_, ?_, bumpB_shrinking F μL⟩
    · intro m
      exact rawBump_integral_pos F μL (bumpB F m)
        (rawBump_continuous F _ (bumpB_support F m))
        (rawBump_compact F _ (bumpB_support F m))
    · intro m
      have hc := rawBump_continuous F (bumpB F m) (bumpB_support F m)
      have hs := rawBump_kernel_smooth F (bumpB F m) (bumpB_support F m)
      have hk := rawBump_compact F (bumpB F m) (bumpB_support F m)
      have hp := rawBump_integral_pos F μL (bumpB F m) hc hk
      exact ⟨continuous_eta F μL _ hc, kernelSmooth_eta F μL _ hs,
        hasCompactSupport_eta F μL _ hk, eta_nonneg F μL _ hp,
        eta_integral_eq_one F μL _ hp.ne'⟩

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
