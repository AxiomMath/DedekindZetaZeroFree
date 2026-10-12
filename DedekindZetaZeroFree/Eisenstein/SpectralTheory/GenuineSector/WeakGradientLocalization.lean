module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CoordinateBallRestriction
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.BoundedCutoffMultiplication
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CompactCutoffDifferentialBounds
public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.ClassicalToWeakSolutions
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.ClosedGradientCutoffProduct

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentChartRestriction
open KPContActualSectorChartEquivariantInputs KPContSectorLineL2Isometry
open KPContLocalNorm
open KPContActualCotangentCountableShrinking KPContActualCotangentPieceHilbertSum

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def coordinateDomain (a : ActualChart (U := U) (H := H)) : Set (Space (3 * d F)) :=
  (baseReindex (F := F)).symm ⁻¹' omega a

def InteriorBall (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) : Prop :=
  IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ coordinateDomain a

private theorem base_direction (j : Fin (3*d F)) :
    (baseReindex (F:=F)).symm (EuclideanSpace.single j 1) =
      HyperbolicChart.coordinateVector (d F) ((coefficientIndex (F:=F)).symm j).1
        ((coefficientIndex (F:=F)).symm j).2 := by
  ext ik
  simp only [baseReindex, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.symm_symm, HyperbolicChart.coordinateVector,
    WithLp.ofLp_toLp]
  simp [EuclideanSpace.single_apply, Pi.single_apply, ← Equiv.apply_eq_iff_eq_symm_apply]
private theorem decoder_differential (a : ActualChart (U:=U) (H:=H)) (f : omega a → ℂ)
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) (j : Fin (3*d F)) :
    (let p := (baseReindex (F:=F)).symm x
     let ik := (coefficientIndex (F:=F)).symm j
     let v := chartDifferential a f ⟨p,hx⟩
     ![(Real.exp (-p (ik.1,2)):ℂ) * v (ik.1,1),
       (Real.exp (-p (ik.1,2)):ℂ) * v (ik.1,2), v (ik.1,0)] ik.2) =
    HyperbolicChart.coordinateDerivative (d F) ((coefficientIndex (F:=F)).symm j).1
      ((coefficientIndex (F:=F)).symm j).2 (liftExtension a f) ((baseReindex (F:=F)).symm x) := by
  generalize hi : (coefficientIndex (F:=F)).symm j = ik
  obtain ⟨i,k⟩ := ik
  fin_cases k <;> simp [chartDifferential, CotangentLogCoframe.j_apply,
    HyperbolicChart.differential, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    ← Complex.exp_add]

private theorem flattened_differential (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (x : Space (3 * d F)) (hx : x ∈ coordinateDomain a)
    (hf : DifferentiableAt ℝ (liftExtension a f) ((baseReindex (F := F)).symm x))
    (j : Fin (3 * d F)) :
    fderiv ℝ (fun y => liftExtension a f ((baseReindex (F := F)).symm y)) x
      (EuclideanSpace.single j 1) =
    HyperbolicChart.coordinateDerivative (d F) ((coefficientIndex (F := F)).symm j).1
      ((coefficientIndex (F := F)).symm j).2 (liftExtension a f)
        ((baseReindex (F := F)).symm x) := by
  have hd := hf.hasFDerivAt.comp x
    ((baseReindex (F := F)).symm.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y => liftExtension a f ((baseReindex (F := F)).symm y)) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [base_direction]
  rfl

private theorem coordinateDomain_isOpen (a : ActualChart (U := U) (H := H)) :
    IsOpen (coordinateDomain a) := by
  change IsOpen ((toActual (F := F) (ζ := ζ) (hζ := hζ)) ⁻¹' a.domain)
  apply a.domain_open.preimage
  unfold toActual labeledA
  fun_prop

private theorem smooth_liftExtension (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (liftExtension a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  apply hg.congr
  intro x hx
  simpa only [liftExtension, dif_pos hx] using (he ⟨x, hx⟩).symm

private theorem smooth_flattened (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => liftExtension a f ((baseReindex (F := F)).symm x))
      (coordinateDomain a) :=
  (smooth_liftExtension a f hf).comp (baseReindex (F := F)).symm.contDiff.contDiffOn
    (fun _ hx => hx)

private theorem smooth_coordinate_sobolev (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B)
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ∃ h : IntegerSobolev B 1, ∀ α,
      (fun x => h.derivatives α x) =ᵐ[volume.restrict B.carrier]
        coordinateDerivative α (fun x => liftExtension a f ((baseReindex (F := F)).symm x)) := by
  let u := fun x => liftExtension a f ((baseReindex (F := F)).symm x)
  have hu := smooth_flattened a f hf
  have hclosed : Metric.closedBall B.center B.radius ⊆ coordinateDomain a := by
    rw [← closure_ball B.center (ne_of_gt B.radius_pos)]
    exact hB.2
  have hL2 := fun α : MultiIndex (3 * d F) 1 =>
    KPContLocalEnergy.SobolevEnergyEstimates.coordinateDerivative_memLp_of_closedBall B
      (coordinateDomain_isOpen a) hclosed hu α
  obtain ⟨h, hh⟩ := smooth_has_integerSobolev_data B u
    (hu.mono (subset_closure.trans hB.2)) hL2
  exact ⟨h, fun α => (hh α).symm ▸ (hL2 α).coeFn_toLp⟩

def scalarCoordinate (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) : ℂ :=
  liftExtension a (sectionFields s.val a) ((baseReindex (F := F)).symm x)

def covariantCoordinate (W : Family (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F))
    (j : Fin (3 * d F)) : ℂ :=
  let p := (baseReindex (F := F)).symm x
  let ik := (coefficientIndex (F := F)).symm j
  let v := liftExtension a (coefficient W a) p
  ![(Real.exp (-p (ik.1, 2)) : ℂ) * v (ik.1, 1),
    (Real.exp (-p (ik.1, 2)) : ℂ) * v (ik.1, 2), v (ik.1, 0)] ik.2

def zeroIndex (n : ℕ) : MultiIndex n 1 := ⟨fun _ => 0, by simp⟩

def WeakChartData (s : BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) : Prop :=
  ∀ (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)),
    InteriorBall a B → ∀ ε : rootsOfUnity 3 F,
    ∃ h : IntegerSobolev B 1,
      (fun x => h.derivatives (zeroIndex (3 * d F)) x) =ᵐ[volume.restrict B.carrier]
        (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * scalarCoordinate s a x) ∧
      ∀ (α : MultiIndex (3 * d F) 1) (j : Fin (3 * d F)), (α.val j).val = 1 →
        (fun x => h.derivatives α x) =ᵐ[volume.restrict B.carrier]
          (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
            covariantCoordinate W a x j)

def ActualWeakH1Loc (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) : Prop :=
  ∃ (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U := U) (H := H)),
    sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s ∧ WeakChartData s W

def IsActualWeakGradient (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) : Prop :=
  ∃ (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U := U) (H := H)),
    sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s ∧
    KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = v ∧ WeakChartData s r.val

 def firstIndex {n : ℕ} (j : Fin n) : MultiIndex n 1 :=
  ⟨Pi.single j 1, by simp [Pi.single_apply, apply_ite Fin.val]⟩

private theorem firstIndex_eq_raw {n : ℕ} (j : Fin n) :
    firstIndex j = KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j := by
  apply Subtype.ext
  funext k
  simp only [firstIndex, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, Pi.single_apply]

private theorem firstIndex_directions {n : ℕ} (j : Fin n) : (firstIndex j).directions = [j] := by
  rw [firstIndex_eq_raw]
  exact KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions j

private theorem index_one_eq_first {n : ℕ} (α : MultiIndex n 1) (j : Fin n)
    (hj : (α.val j).val = 1) : α = firstIndex j := by
  have hs := Finset.sum_le_one_iff.mp α.property
  apply Subtype.ext
  funext k
  apply Fin.ext
  by_cases hkj : k = j
  · subst k
    simpa [firstIndex] using hj
  · have hk : (α.val k).val = 0 := by
      by_contra hk
      exact hkj (hs k j (Finset.mem_univ _) (Finset.mem_univ _) hk (by omega)).1
    simpa [firstIndex, Pi.single_apply, hkj] using hk

private theorem test_smooth_local_data (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) (hB : InteriorBall a B) :
    ∃ h : IntegerSobolev B 1,
      (fun x => h.derivatives (zeroIndex (3 * d F)) x) =ᵐ[volume.restrict B.carrier]
        (fun x => liftExtension a (f.val a) ((baseReindex (F := F)).symm x)) ∧
      ∀ (α : MultiIndex (3 * d F) 1) (j : Fin (3 * d F)), (α.val j).val = 1 →
        (fun x => h.derivatives α x) =ᵐ[volume.restrict B.carrier]
          (fun x => covariantCoordinate (D_U f).val a x j) := by
  obtain ⟨h, hh⟩ := smooth_coordinate_sobolev a B hB (f.val a) (f.property.1 a)
  refine ⟨h, ?_, ?_⟩
  · change (fun x => h.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex (3 * d F) 1) x) =ᵐ[_] _
    simpa only [KPContLocalEnergy.SobolevEnergyEstimates.coordinateDerivative_zeroIndex] using
      hh (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex (3 * d F) 1)
  · intro α j hj
    have heq := index_one_eq_first α j hj
    rw [heq]
    apply (hh (firstIndex j)).trans
    filter_upwards [ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hx
    have hx' : x ∈ coordinateDomain a := hB.2 (subset_closure hx)
    have hp := (smooth_liftExtension a (f.val a) (f.property.1 a)).differentiableOn
      (by simp) ((baseReindex (F := F)).symm x) hx'
    have hopen : IsOpen (omega a) := by
      change IsOpen (labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ) ⁻¹' a.domain)
      apply a.domain_open.preimage
      unfold labeledA
      fun_prop
    have hp' := hp.differentiableAt (hopen.mem_nhds hx')
    rw [coordinateDerivative, firstIndex_directions]
    change fderiv ℝ (fun y => liftExtension a (f.val a) ((baseReindex (F := F)).symm y)) x
      (EuclideanSpace.single j 1) = _
    rw [flattened_differential a (f.val a) x hx' hp' j]
    have hdecoder := decoder_differential a (f.val a) x hx' j
    unfold covariantCoordinate
    have hxomega : (baseReindex (F := F)).symm x ∈ omega a := hx'
    simp only [liftExtension, dif_pos hxomega]
    exact hdecoder.symm

private theorem scalarBall_test (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B) (f : S_U F ζ hζ U R P H) :
    (fun x => KPContActualSectorBallRestriction.scalarBall a B hB
      (KPContActualSectorTestEmbeddings.iota f) x) =ᵐ[volume.restrict B.carrier]
        (fun x => liftExtension a (f.val a) ((baseReindex (F := F)).symm x)) := by
  have hspec := (Classical.choose_spec (scalar_gluing f)).1
  have hcont : Continuous (scalarCovered f).val := by
    exact (continuous_iff F ζ hζ U R P H (scalarSections f)).mp
      (fun i => (hspec.1 i).continuous)
  let b : BorelL2Scalars F ζ hζ U R := ⟨scalarCovered f, hcont.measurable,
    KPContActualSectorTestEmbeddings.scalar_memLp f⟩
  have hb := sectorLineIsometry_representative F ζ hζ U R P H
    (KPContActualSectorTestEmbeddings.iota f) b (by rfl)
  have hae := KPContActualSectorBallRestriction.scalarBall_ae a B hB _
    (borelS F ζ hζ U R P H b) hb
  have hval : (borelS F ζ hζ U R P H b).val = scalarSections f := by
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H (scalarCovered f) = _
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
      ((KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).symm (scalarSections f)) = _
    exact (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply _
  have hfields : sectionFields (scalarSections f) = f.val := hspec.2.2
  simpa only [KPContActualSectorCoordinateNullEquivalence.scalar, hval, hfields] using hae

private theorem index_cases {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n ∨ ∃ j, α = firstIndex j := by
  by_cases hz : ∀ j, (α.val j).val = 0
  · left
    apply Subtype.ext
    funext j
    exact Fin.ext (hz j)
  · obtain ⟨j, hj⟩ := not_forall.mp hz
    have hj1 : (α.val j).val = 1 := by
      have := (α.val j).isLt
      omega
    exact Or.inr ⟨j, index_one_eq_first α j hj1⟩

private theorem first_ne_zero {n : ℕ} (j : Fin n) : firstIndex j ≠ zeroIndex n := by
  intro he
  have h := congrArg (fun α : MultiIndex n 1 => (α.val j).val) he
  simp [firstIndex, zeroIndex] at h

private theorem first_injective {n : ℕ} : Function.Injective (firstIndex (n := n)) := by
  intro i j hij
  by_contra h
  have he := congrArg (fun α : MultiIndex n 1 => (α.val i).val) hij
  simp [firstIndex, Pi.single_apply, h] at he

 def ballDerivative (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : InteriorBall a B) (α : MultiIndex (3 * d F) 1) :
    (KPContSectorClosedLpSubspace.H F ζ hζ R U × KPContActualSectorCotangentL2.V F ζ hζ U R P H)
      →L[ℂ] BallL2 B :=
  if h : ∃ j, α = firstIndex j then
    (KPContActualSectorBallRestriction.coordinateBall a B hB h.choose).comp
      (ContinuousLinearMap.snd ℂ _ _) else
    (KPContActualSectorBallRestriction.scalarBall a B hB).comp
      (ContinuousLinearMap.fst ℂ _ _)

private theorem ballDerivative_zero (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : InteriorBall a B) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) :
    ballDerivative a B hB (zeroIndex (3 * d F)) (u,v) =
      KPContActualSectorBallRestriction.scalarBall a B hB u := by
  have hn : ¬∃ j, zeroIndex (3 * d F) = firstIndex j := by
    rintro ⟨j,hj⟩
    exact first_ne_zero j hj.symm
  simp [ballDerivative, hn]

private theorem ballDerivative_first (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : InteriorBall a B) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H) (j : Fin (3 * d F)) :
    ballDerivative a B hB (firstIndex j) (u,v) =
      KPContActualSectorBallRestriction.coordinateBall a B hB j v := by
  have he : ∃ i, firstIndex j = firstIndex i := ⟨j,rfl⟩
  simp only [ballDerivative, dif_pos he, ContinuousLinearMap.comp_apply]
  rw [← first_injective he.choose_spec]
  rfl

 theorem ballDerivative_test_weak (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B) (f : S_U F ζ hζ U R P H)
    (α : MultiIndex (3 * d F) 1) :
    IsWeakDerivative B α
      (ballDerivative a B hB (zeroIndex (3 * d F))
        (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f)))
      (ballDerivative a B hB α
        (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f))) := by
  obtain ⟨h, hh0, hh1⟩ := test_smooth_local_data f a B hB
  have h0 : h.derivatives (zeroIndex (3 * d F)) =
      ballDerivative a B hB (zeroIndex (3 * d F))
        (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f)) := by
    rw [ballDerivative_zero]
    apply Lp.ext
    exact hh0.trans (scalarBall_test a B hB f).symm
  have ha : h.derivatives α = ballDerivative a B hB α
      (KPContActualSectorTestEmbeddings.iota f, KPContActualSectorTestEmbeddings.j (D_U f)) := by
    rcases index_cases α with rfl | ⟨j,rfl⟩
    · exact h0
    · rw [ballDerivative_first]
      apply Lp.ext
      exact (hh1 _ j (by simp [firstIndex])).trans
        (KPContActualSectorBallRestriction.coordinateBall_ae a B hB j _
          (KPContActualSectorTestEmbeddings.cotangentSquareFamily (D_U f)) rfl).symm
  have hw := h.weak_derivatives α
  change IsWeakDerivative B α (h.derivatives (zeroIndex (3 * d F))) (h.derivatives α) at hw
  rwa [h0, ha] at hw

private theorem base_point (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  let C := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hx : x ∈ ⋃ n, (C.chart n).baseDomain := by rw [C.covers]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := hn
  refine ⟨C.chart n, coordinates (C.chart n) y, ?_⟩
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  rw [← hy]
  simp only [q, coordinates, ShrunkChart.toBase]
  rw [hi]

private theorem masked_norm_sq (W W' : Family (U := U) (H := H)) (i : Fin (d F))
    (hW : ∀ (a : ActualChart (U := U) (H := H)) (x : omega a) (j : Fin (d F)) (k : Fin 3),
      coefficient W' a x (j,k) = if j=i then coefficient W a x (j,k) else 0)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    ‖coefficient W' a x‖ ^ 2 = ∑ k : Fin 3, ‖coefficient W a x (i,k)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp_rw [hW, apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_irrel]
  simp

private theorem descent_of_projection (W W' : Family (U := U) (H := H)) (i : Fin (d F))
    (hW : ∀ (a : ActualChart (U := U) (H := H)) (x : omega a) (j : Fin (d F)) (k : Fin 3),
      coefficient W' a x (j,k) = if j=i then coefficient W a x (j,k) else 0) :
    ∃! f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ,
      Measurable f ∧ ∀ (a : ActualChart (U := U) (H := H)) (x : omega a),
        f (q a x.val) = ∑ k : Fin 3, ‖coefficient W a x (i, k)‖ ^ 2 := by
  refine ⟨fun x => (normSquare W' x : ℝ), ⟨(measurable_normSquare W').coe_nnreal_real, ?_⟩, ?_⟩
  · intro a x
    change (normSquare W' (q a x.val) : ℝ) = _
    rw [normSquare_chart]
    exact masked_norm_sq W W' i hW a x
  · intro f hf
    funext x
    obtain ⟨a, y, hy⟩ := base_point x
    rw [← hy, hf.2 a y, normSquare_chart]
    exact (masked_norm_sq W W' i hW a y).symm

theorem placeSquare_descends (W : Family (U := U) (H := H)) (i : Fin (d F)) :
    ∃! f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ,
      Measurable f ∧ ∀ (a : ActualChart (U := U) (H := H)) (x : omega a),
        f (q a x.val) = ∑ k : Fin 3, ‖coefficient W a x (i, k)‖ ^ 2 := by
  exact descent_of_projection W (KPContActualCotangentPlaceProjection.project i W) i
    (KPContActualCotangentPlaceProjection.coefficient_project i W)

def placeSquare (W : Family (U := U) (H := H)) (i : Fin (d F)) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ := Classical.choose (placeSquare_descends W i)

private theorem place_square_nonneg (W : Family (U:=U) (H:=H)) (i : Fin (d F)) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) : 0 ≤ placeSquare W i x := by
  obtain ⟨a,y,hy⟩ := base_point x
  rw [← hy, show placeSquare W i (q a y.val) = ∑ k : Fin 3, ‖coefficient W a y (i,k)‖ ^ 2 from
    (Classical.choose_spec (placeSquare_descends W i)).1.2 a y]
  positivity
private theorem place_square_sum (W : Family (U:=U) (H:=H)) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    (∑ i, placeSquare W i x) = (normSquare W x : ℝ) := by
  obtain ⟨a,y,hy⟩ := base_point x
  rw [← hy, normSquare_chart]
  change _ = ‖coefficient W a y‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Classical.choose_spec (placeSquare_descends W i)).1.2 a y
private theorem place_square_integrable (r : SquareFiniteFamily (U:=U) (H:=H)) (i : Fin (d F)) :
    Integrable (placeSquare r.val i) (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
  apply (KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare r).mono_nonneg
    ((Classical.choose_spec (placeSquare_descends r.val i)).1.1.aestronglyMeasurable)
    (Filter.Eventually.of_forall (place_square_nonneg r.val i))
  apply Filter.Eventually.of_forall
  intro x
  rw [← place_square_sum]
  exact Finset.single_le_sum (fun j hj => place_square_nonneg r.val j x) (Finset.mem_univ i)

 def iteratedDerivativeTest {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) (φ : TestFunction B.toOpens ℂ ⊤) :
    TestFunction B.toOpens ℂ ⊤ :=
  match l with
  | [] => φ
  | i :: l => TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1)
      (iteratedDerivativeTest l φ)

private theorem iteratedDerivativeTest_apply {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) (φ : TestFunction B.toOpens ℂ ⊤) :
    (fun x => iteratedDerivativeTest l φ x) = coordinateDerivativeList l (fun x => φ x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    simp only [iteratedDerivativeTest, coordinateDerivativeList]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM]
    rw [TestFunction.fderivCLM_apply_of_le _ (by simp)]
    change fderiv ℝ (fun y => iteratedDerivativeTest l φ y) x _ = _
    rw [ih]

 def pairTest {n : ℕ} (B : LocalBall n) (φ : TestFunction B.toOpens ℂ ⊤) :
    BallL2 B →L[ℂ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict B.carrier) 2 2).flip
    ((φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).toLp φ)
private theorem pairTest_eq {n : ℕ} (B : LocalBall n) (φ : TestFunction B.toOpens ℂ ⊤)
    (u : BallL2 B) : pairTest B φ u = ∫ x in B.carrier, u x * φ x := by
  rw [pairTest, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).coeFn_toLp]
    with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

private theorem weakDerivative_isClosed {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k) :
    IsClosed {uv : BallL2 B × BallL2 B | IsWeakDerivative B α uv.1 uv.2} := by
  have heq : {uv : BallL2 B × BallL2 B | IsWeakDerivative B α uv.1 uv.2} =
      ⋂ φ : TestFunction B.toOpens ℂ ⊤,
        {uv | pairTest B (iteratedDerivativeTest α.directions φ) uv.1 =
          (-1 : ℂ) ^ α.degree * pairTest B φ uv.2} := by
    ext uv
    simp only [Set.mem_setOf_eq, Set.mem_iInter, IsWeakDerivative, pairTest_eq,
      iteratedDerivativeTest_apply, coordinateDerivative]
  rw [heq]
  apply isClosed_iInter
  intro φ
  exact isClosed_eq ((pairTest B _).continuous.comp continuous_fst)
    (continuous_const.mul ((pairTest B φ).continuous.comp continuous_snd))

 theorem weakDerivative_of_tendsto {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (us ds : ℕ → BallL2 B) (u d : BallL2 B)
    (hu : Filter.Tendsto us Filter.atTop (𝓝 u))
    (hd : Filter.Tendsto ds Filter.atTop (𝓝 d))
    (hweak : ∀ m, IsWeakDerivative B α (us m) (ds m)) :
    IsWeakDerivative B α u d := by
  exact (weakDerivative_isClosed B α).mem_of_tendsto (hu.prodMk_nhds hd)
    (Filter.Eventually.of_forall hweak)

private theorem lp_mul_test_integrable {n : ℕ} {B : LocalBall n}
    (u : BallL2 B) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => u x * φ x) (volume.restrict B.carrier) :=
  (Lp.memLp u).integrable_mul
    (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport)

private theorem lp_mul_derivative_test_integrable {n k : ℕ} {B : LocalBall n}
    (u : BallL2 B) (α : MultiIndex n k) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => u x * coordinateDerivative α (fun x => φ x) x)
      (volume.restrict B.carrier) := by
  simpa only [iteratedDerivativeTest_apply, coordinateDerivative] using
    lp_mul_test_integrable u (iteratedDerivativeTest α.directions φ)

 theorem weak_derivative_sub {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u₁ u₂ d₁ d₂ : BallL2 B)
    (h₁ : IsWeakDerivative B α u₁ d₁) (h₂ : IsWeakDerivative B α u₂ d₂) :
    IsWeakDerivative B α (u₁ - u₂) (d₁ - d₂) := by
  intro φ
  have hleft : (∫ x in B.carrier, (u₁ - u₂) x *
      coordinateDerivative α (fun y => φ y) x) =
      (∫ x in B.carrier, u₁ x * coordinateDerivative α (fun y => φ y) x) -
      (∫ x in B.carrier, u₂ x * coordinateDerivative α (fun y => φ y) x) := by
    rw [← integral_sub (lp_mul_derivative_test_integrable u₁ α φ)
      (lp_mul_derivative_test_integrable u₂ α φ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u₁ u₂] with x hx
    simp only [hx, Pi.sub_apply, sub_mul]
  have hright : (∫ x in B.carrier, (d₁ - d₂) x * φ x) =
      (∫ x in B.carrier, d₁ x * φ x) - (∫ x in B.carrier, d₂ x * φ x) := by
    rw [← integral_sub (lp_mul_test_integrable d₁ φ) (lp_mul_test_integrable d₂ φ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub d₁ d₂] with x hx
    simp only [hx, Pi.sub_apply, sub_mul]
  change _ = (-1 : ℂ) ^ α.degree * _
  rw [hleft, hright, h₁ φ, h₂ φ, mul_sub]

 theorem weak_derivative_smul {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (c : ℂ) (u d : BallL2 B) (h : IsWeakDerivative B α u d) :
    IsWeakDerivative B α (c • u) (c • d) := by
  intro φ
  have hleft : (∫ x in B.carrier, (c • u) x *
      coordinateDerivative α (fun y => φ y) x) =
      c * (∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hright : (∫ x in B.carrier, (c • d) x * φ x) =
      c * (∫ x in B.carrier, d x * φ x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c d] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  change _ = (-1 : ℂ) ^ α.degree * _
  rw [hleft, hright, h φ]
  ring

 theorem weakDerivative_zero {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k) :
    IsWeakDerivative B α (0 : BallL2 B) (0 : BallL2 B) := by
  intro φ
  have hL : (fun x => (0 : BallL2 B) x * coordinateDerivative α (fun y => φ y) x)
      =ᵐ[volume.restrict B.carrier] (fun _ => (0 : ℂ)) := by
    filter_upwards [Lp.coeFn_zero (μ := volume.restrict B.carrier) (p := 2) (E := ℂ)]
      with x hx
    rw [hx]; simp
  have hR : (fun x => (0 : BallL2 B) x * φ x)
      =ᵐ[volume.restrict B.carrier] (fun _ => (0 : ℂ)) := by
    filter_upwards [Lp.coeFn_zero (μ := volume.restrict B.carrier) (p := 2) (E := ℂ)]
      with x hx
    rw [hx]; simp
  rw [integral_congr_ae hL, integral_congr_ae hR]
  simp

def coordinateH1Submodule {n : ℕ} (B : LocalBall n) :
    Submodule ℂ (PiLp 2 (fun _ : MultiIndex n 1 => BallL2 B)) where
  carrier := {h | ∀ α, IsWeakDerivative B α (h (zeroIndex n)) (h α)}
  zero_mem' := by
    intro α
    rw [PiLp.zero_apply, PiLp.zero_apply]
    exact weakDerivative_zero B α
  add_mem' := by
    intro h g hh hg α
    rw [PiLp.add_apply, PiLp.add_apply]
    have hsm := weak_derivative_smul
      B α (-1) (g (zeroIndex n)) (g α) (hg α)
    have hsub := weak_derivative_sub
      B α (h (zeroIndex n)) ((-1 : ℂ) • g (zeroIndex n)) (h α) ((-1 : ℂ) • g α)
      (hh α) hsm
    rwa [neg_one_smul, neg_one_smul, sub_neg_eq_add, sub_neg_eq_add] at hsub
  smul_mem' := by
    intro c h hh α
    rw [PiLp.smul_apply, PiLp.smul_apply]
    exact weak_derivative_smul
      B α c (h (zeroIndex n)) (h α) (hh α)

 def mulBall {n : ℕ} (B : LocalBall n) (b : Space n → ℂ)
    (hb : MemLp b ⊤ (volume.restrict B.carrier)) : BallL2 B →L[ℂ] BallL2 B :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume.restrict B.carrier) ⊤ 2 2 (hb.toLp b)
private theorem mulBall_ae {n : ℕ} (B : LocalBall n) (b : Space n → ℂ)
    (hb : MemLp b ⊤ (volume.restrict B.carrier)) (u : BallL2 B) :
    (fun x => mulBall B b hb u x) =ᵐ[volume.restrict B.carrier] (fun x => b x * u x) := by
  have he := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hb.toLp b) u
  filter_upwards [he, hb.coeFn_toLp] with x hx hxb
  simpa only [mulBall, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hxb] using hx
private theorem memLp_top_on_ball {n : ℕ} (B : LocalBall n) (Ω : Set (Space n))
    (hΩ : IsOpen Ω) (hB : IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ Ω)
    (b : Space n → ℂ) (hb : ContinuousOn b Ω) :
    MemLp b ⊤ (volume.restrict B.carrier) := by
  obtain ⟨C,hC⟩ := hB.1.exists_bound_of_continuousOn (hb.mono hB.2)
  apply memLp_top_of_bound (hb.mono (subset_closure.trans hB.2) |>.aestronglyMeasurable B.toOpens.isOpen.measurableSet) C
  exact ae_restrict_of_forall_mem B.toOpens.isOpen.measurableSet (fun x hx => hC x (subset_closure hx))

abbrev CoordinateH1 {n : ℕ} (B : LocalBall n) := ↥(coordinateH1Submodule B)

abbrev CompactMultiplier :=
  {η : RealSmoothCutoff F ζ hζ U R P H // HasCompactSupport η.val}

def multiplierCoordinate (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3 * d F)) : ℂ :=
  liftExtension a (cutoffLift η.val a) ((baseReindex (F := F)).symm x)

def MultipliedData (η : CompactMultiplier (U := U) (H := H))
    (s t : BorelL2Sections F ζ hζ U R P H)
    (r z : SquareFiniteFamily (U := U) (H := H)) : Prop :=
  ∀ a : ActualChart (U := U) (H := H),
    (fun y : a.domain => sectionFields t.val a (KPContActualCotangentPieceHilbertSum.coordinates a y)) =ᵐ[a.liftedMeasure]
      (fun y => cutoffLift η.val a (KPContActualCotangentPieceHilbertSum.coordinates a y) *
        sectionFields s.val a (KPContActualCotangentPieceHilbertSum.coordinates a y)) ∧
    localCoefficient a z.val =ᵐ[a.liftedMeasure]
      (fun y => let x := KPContActualCotangentPieceHilbertSum.coordinates a y
        cutoffLift η.val a x • localCoefficient a r.val y +
          sectionFields s.val a x • cutoffDifferential η.val a x)

variable (F ζ hζ)
variable (U R P H)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "A" => KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
local notation "Q" => KPContActualSectorFriedrichsSynthesis.formDomain F ζ hζ U R P H μG hμG hR realization

private theorem closedGradient_weak_chart (u : Q)
    (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U := U) (H := H))
    (hs : sectorLineIsometry F ζ hζ U R P H (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) =
      mk F ζ hζ U R P H s)
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = (A).closure u) :
    WeakChartData s r.val := by
  obtain ⟨fs, hfs, hgrad, -⟩ :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization).form_core u
  have hp := hfs.prodMk_nhds hgrad
  intro a B hB ε
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ ε
  let v := (A).closure u
  have hweak : ∀ α, IsWeakDerivative B α
      (ballDerivative a B hB (zeroIndex (3 * d F)) (u.val,v))
      (ballDerivative a B hB α (u.val,v)) := by
    intro α
    apply weakDerivative_of_tendsto B α
      (fun m => ballDerivative a B hB (zeroIndex (3 * d F))
        (KPContActualSectorTestEmbeddings.iota (fs m), KPContActualSectorTestEmbeddings.j (D_U (fs m))))
      (fun m => ballDerivative a B hB α
        (KPContActualSectorTestEmbeddings.iota (fs m), KPContActualSectorTestEmbeddings.j (D_U (fs m))))
    · exact ((ballDerivative a B hB _).continuous.tendsto _).comp hp
    · exact ((ballDerivative a B hB α).continuous.tendsto _).comp hp
    · exact fun m => ballDerivative_test_weak a B hB (fs m) α
  let h : IntegerSobolev B 1 := ⟨fun α => c • ballDerivative a B hB α (u.val,v), by
    intro α
    exact weak_derivative_smul B α c _ _ (hweak α)⟩
  refine ⟨h, ?_, ?_⟩
  · have hz := ballDerivative_zero a B hB u.val v
    have heq := KPContActualSectorBallRestriction.scalarBall_ae a B hB u.val s hs
    filter_upwards [Lp.coeFn_smul c (ballDerivative a B hB (zeroIndex (3 * d F)) (u.val,v)), heq]
      with x hx he
    change (c • ballDerivative a B hB (zeroIndex (3 * d F)) (u.val,v)) x = _
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, hz, he]
    rfl
  · intro α j hj
    have hα := index_one_eq_first α j hj
    have hf := ballDerivative_first a B hB u.val v j
    have heq := KPContActualSectorBallRestriction.coordinateBall_ae a B hB j v r hr
    filter_upwards [Lp.coeFn_smul c (ballDerivative a B hB α (u.val,v)), heq] with x hx he
    change (c • ballDerivative a B hB α (u.val,v)) x = _
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, hα, hf, he]
    rfl

 def graphDomain (w : ClosedGradientSpace A) : Q :=
  ⟨closedGradientEmbedding A w, (A).closure.mem_domain_of_mem_graph w.property⟩

 theorem graphDomain_gradient (w : ClosedGradientSpace A) :
    (A).closure (graphDomain F ζ hζ U R P H μG hμG hR realization w) =
      closedGradientCoordinate A w := by
  obtain ⟨u, hu, hv⟩ := (A).closure.mem_graph_iff.mp w.property
  have he : u = graphDomain F ζ hζ U R P H μG hμG hR realization w := Subtype.ext hu
  rw [← he]
  exact hv

private theorem closedGradient_isActualWeak (u : Q) :
    IsActualWeakGradient (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) ((A).closure u) := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep
    (sectorLineIsometry F ζ hζ U R P H (u : KPContSectorClosedLpSubspace.H F ζ hζ R U))
  change mk F ζ hζ U R P H s = _ at hs
  obtain ⟨r,hr⟩ := KPContActualSectorCotangentL2.ofFamily_surjective F ζ hζ U R P H ((A).closure u)
  exact ⟨s,r,hs.symm,hr,closedGradient_weak_chart F ζ hζ U R P H μG hμG hR realization u s r hs.symm hr⟩

 def coordinateGraphMap (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B) :
    ClosedGradientSpace A →L[ℂ] CoordinateH1 B := by
  let L : ClosedGradientSpace A →L[ℂ] PiLp 2 (fun _ : MultiIndex (3 * d F) 1 => BallL2 B) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : MultiIndex (3 * d F) 1 => BallL2 B)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun α => (ballDerivative a B hB α).comp
        ((closedGradientEmbedding A).prod (closedGradientCoordinate A))))
  apply L.codRestrict (coordinateH1Submodule B)
  intro w
  obtain ⟨fs,hfs,hgrad,-⟩ :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization).form_core
      (graphDomain F ζ hζ U R P H μG hμG hR realization w)
  rw [graphDomain_gradient] at hgrad
  intro α
  change IsWeakDerivative B α
    (ballDerivative a B hB (zeroIndex (3 * d F))
      (closedGradientEmbedding A w, closedGradientCoordinate A w))
    (ballDerivative a B hB α (closedGradientEmbedding A w, closedGradientCoordinate A w))
  apply weakDerivative_of_tendsto B α
    (fun m => ballDerivative a B hB (zeroIndex (3 * d F))
      (KPContActualSectorTestEmbeddings.iota (fs m), KPContActualSectorTestEmbeddings.j (D_U (fs m))))
    (fun m => ballDerivative a B hB α
      (KPContActualSectorTestEmbeddings.iota (fs m), KPContActualSectorTestEmbeddings.j (D_U (fs m))))
  · exact ((ballDerivative a B hB _).continuous.tendsto _).comp (hfs.prodMk_nhds hgrad)
  · exact ((ballDerivative a B hB α).continuous.tendsto _).comp (hfs.prodMk_nhds hgrad)
  · exact fun m => ballDerivative_test_weak a B hB (fs m) α

private theorem graph_tests_tendsto (w : ClosedGradientSpace A) :
    ∃ fs : ℕ → S_U F ζ hζ U R P H,
      Filter.Tendsto (fun n => KPContActualFormCutoffClosedProduct.graphTestLift
        F ζ hζ U R P H μG hμG hR realization (fs n)) Filter.atTop (𝓝 w) := by
  obtain ⟨fs,hfs,hgrad,-⟩ :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization).form_core
      (graphDomain F ζ hζ U R P H μG hμG hR realization w)
  rw [graphDomain_gradient] at hgrad
  refine ⟨fs, ?_⟩
  rw [tendsto_subtype_rng]
  have hw : (w : WithLp 2 (_ × _)) = WithLp.toLp 2
      (closedGradientEmbedding A w, closedGradientCoordinate A w) := by
    apply WithLp.ofLp_injective
    rfl
  rw [hw]
  exact ((WithLp.prod_continuous_toLp 2 _ _).tendsto _).comp (hfs.prodMk_nhds hgrad)

private theorem smooth_cutoff_flat (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (multiplierCoordinate η a) (coordinateDomain a) := by
  apply smooth_flattened
  obtain ⟨g,hg,he⟩ := η.val.smooth a
  exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
    fun x => congrArg Complex.ofReal (he x)⟩

private theorem scalarBall_product_test (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) (hB : InteriorBall a B)
    (f : S_U F ζ hζ U R P H) :
    KPContActualSectorBallRestriction.scalarBall a B hB
        (KPContActualSectorTestEmbeddings.iota (scalarMultiply η.val f)) =
      mulBall B (multiplierCoordinate η a)
        (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
          (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn)
        (KPContActualSectorBallRestriction.scalarBall a B hB
          (KPContActualSectorTestEmbeddings.iota f)) := by
  apply Lp.ext
  filter_upwards [scalarBall_test a B hB (scalarMultiply η.val f),
    scalarBall_test a B hB f,
    mulBall_ae B (multiplierCoordinate η a) _
      (KPContActualSectorBallRestriction.scalarBall a B hB
        (KPContActualSectorTestEmbeddings.iota f))] with x h1 h2 h3
  rw [h1,h3,h2]
  simp only [multiplierCoordinate, scalarMultiply, liftExtension]
  split_ifs <;> simp

private theorem scalarBall_graph_product
    (η : CompactMultiplier (U := U) (H := H))
    (M : ClosedGradientSpace A →L[ℂ] ClosedGradientSpace A)
    (hM : ∀ f : S_U F ζ hζ U R P H,
      M (KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization f) =
        KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization
          (scalarMultiply η.val f))
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) (hB : InteriorBall a B)
    (w : ClosedGradientSpace A) :
    KPContActualSectorBallRestriction.scalarBall a B hB (closedGradientEmbedding A (M w)) =
      mulBall B (multiplierCoordinate η a)
        (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
          (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn)
        (KPContActualSectorBallRestriction.scalarBall a B hB (closedGradientEmbedding A w)) := by
  obtain ⟨fs,hfs⟩ := graph_tests_tendsto F ζ hζ U R P H μG hμG hR realization w
  let L := (KPContActualSectorBallRestriction.scalarBall a B hB).comp ((closedGradientEmbedding A).comp M)
  let N := (mulBall B (multiplierCoordinate η a)
    (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _ (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn)).comp
      ((KPContActualSectorBallRestriction.scalarBall a B hB).comp (closedGradientEmbedding A))
  apply tendsto_nhds_unique ((L.continuous.tendsto w).comp hfs)
    (((N.continuous.tendsto w).comp hfs).congr' ?_)
  filter_upwards with n
  dsimp [L,N]
  rw [hM]
  exact (scalarBall_product_test F ζ hζ U R P H η a B hB (fs n)).symm

 def decode (x : Space (3*d F)) (j : Fin (3*d F)) (v : KPContCotangentActualGenuineTwistIsotropy.E F) : ℂ :=
  let p := (baseReindex (F := F)).symm x
  let ik := (coefficientIndex (F := F)).symm j
  ![(Real.exp (-p (ik.1,2)) : ℂ) * v (ik.1,1),
    (Real.exp (-p (ik.1,2)) : ℂ) * v (ik.1,2), v (ik.1,0)] ik.2

private theorem decode_add_smul (x : Space (3*d F)) (j : Fin (3*d F))
    (b c : ℂ) (v w : KPContCotangentActualGenuineTwistIsotropy.E F) :
    decode F x j (b • v + c • w) = b * decode F x j v + c * decode F x j w := by
  generalize hi : (coefficientIndex (F := F)).symm j = ik
  rcases ik with ⟨i,k⟩
  fin_cases k <;> simp [decode, hi, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

 def cutoffPartial (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (j : Fin (3*d F)) (x : Space (3*d F)) : ℂ :=
  fderiv ℝ (multiplierCoordinate η a) x (EuclideanSpace.single j 1)

private theorem cutoffPartial_cont (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (j : Fin (3*d F)) :
    ContinuousOn (cutoffPartial F ζ hζ U R P H η a j) (coordinateDomain a) := by
  exact (((smooth_cutoff_flat F ζ hζ U R P H η a).fderiv_of_isOpen
    (coordinateDomain_isOpen a) (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const).continuousOn

private theorem cutoffPartial_decode (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (j : Fin (3*d F))
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) :
    cutoffPartial F ζ hζ U R P H η a j x = decode F x j
      (cutoffDifferential η.val a ⟨(baseReindex (F := F)).symm x, hx⟩) := by
  have hp := (smooth_liftExtension a (cutoffLift η.val a) (by
    obtain ⟨g,hg,he⟩ := η.val.smooth a
    exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
      fun x => congrArg Complex.ofReal (he x)⟩)).differentiableOn (by simp) _ hx
  have hpd := hp.differentiableAt ((show IsOpen (omega a) from a.domain_open.preimage (by
    unfold labeledA; fun_prop)).mem_nhds hx)
  exact (flattened_differential a _ x hx hpd j).trans (decoder_differential a _ x hx j).symm

include μG hμG hR realization in
private theorem coordinateBall_product_test
    (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3*d F)) (hB : InteriorBall a B)
    (j : Fin (3*d F)) (f : S_U F ζ hζ U R P H) :
    KPContActualSectorBallRestriction.coordinateBall a B hB j
      (KPContActualSectorTestEmbeddings.j (D_U (scalarMultiply η.val f))) =
      mulBall B (multiplierCoordinate η a)
        (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
          (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn)
        (KPContActualSectorBallRestriction.coordinateBall a B hB j (KPContActualSectorTestEmbeddings.j (D_U f))) +
      mulBall B (cutoffPartial F ζ hζ U R P H η a j)
        (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
          (cutoffPartial_cont F ζ hζ U R P H η a j))
        (KPContActualSectorBallRestriction.scalarBall a B hB (KPContActualSectorTestEmbeddings.iota f)) := by
  have hb := memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
    (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn
  have hd := memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
    (cutoffPartial_cont F ζ hζ U R P H η a j)
  apply Lp.ext
  filter_upwards [KPContActualSectorBallRestriction.coordinateBall_ae a B hB j _
      (KPContActualSectorTestEmbeddings.cotangentSquareFamily (D_U (scalarMultiply η.val f))) rfl,
    KPContActualSectorBallRestriction.coordinateBall_ae a B hB j _
      (KPContActualSectorTestEmbeddings.cotangentSquareFamily (D_U f)) rfl,
    scalarBall_test a B hB f, mulBall_ae B (multiplierCoordinate η a) hb
      (KPContActualSectorBallRestriction.coordinateBall a B hB j (KPContActualSectorTestEmbeddings.j (D_U f))),
    mulBall_ae B (cutoffPartial F ζ hζ U R P H η a j) hd
      (KPContActualSectorBallRestriction.scalarBall a B hB (KPContActualSectorTestEmbeddings.iota f)),
    Lp.coeFn_add (mulBall B (multiplierCoordinate η a) hb
      (KPContActualSectorBallRestriction.coordinateBall a B hB j (KPContActualSectorTestEmbeddings.j (D_U f))))
      (mulBall B (cutoffPartial F ζ hζ U R P H η a j) hd
        (KPContActualSectorBallRestriction.scalarBall a B hB (KPContActualSectorTestEmbeddings.iota f))),
    ae_restrict_mem B.toOpens.isOpen.measurableSet] with x h1 h2 h3 h4 h5 h6 hx
  change KPContActualSectorBallRestriction.coordinateBall a B hB j
    (KPContActualSectorTestEmbeddings.j (D_U (scalarMultiply η.val f))) x = _ at h1
  change KPContActualSectorBallRestriction.coordinateBall a B hB j
    (KPContActualSectorTestEmbeddings.j (D_U f)) x = _ at h2
  rw [h1,h6]
  simp only [Pi.add_apply]
  simp only [h4,h5,h2,h3]
  have hx' := hB.2 (subset_closure hx)
  have hp := congrArg (fun W : T_U F ζ hζ U R P H => coefficient W.val a
    ⟨(baseReindex (F := F)).symm x,hx'⟩)
    ((kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H realization).differential_product η.val f)
  change decode F x j (liftExtension a (coefficient (D_U (scalarMultiply η.val f)).val a)
    ((baseReindex (F := F)).symm x)) = _
  have hxomega : (baseReindex (F := F)).symm x ∈ omega a := hx'
  simp only [liftExtension, dif_pos hxomega]
  rw [hp]
  change decode F x j (_ • _ + _ • _) = _
  rw [decode_add_smul F, cutoffPartial_decode F ζ hζ U R P H η a j x hx']
  simp only [multiplierCoordinate, KPContActualSectorCoordinateNullEquivalence.coordinateW,
    KPContActualSectorTestEmbeddings.cotangentSquareFamily, liftExtension, dif_pos hxomega, decode]
  change _ * decode F x j (coefficient (D_U f).val a ⟨_,hxomega⟩) +
    _ * decode F x j (cutoffDifferential η.val a ⟨_,hxomega⟩) =
    _ * decode F x j (coefficient (D_U f).val a ⟨_,hxomega⟩) +
    decode F x j (cutoffDifferential η.val a ⟨_,hxomega⟩) * _
  ring

private theorem coordinateBall_graph_product
    (η : CompactMultiplier (U := U) (H := H))
    (M : ClosedGradientSpace A →L[ℂ] ClosedGradientSpace A)
    (hM : ∀ f : S_U F ζ hζ U R P H,
      M (KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization f) =
        KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization
          (scalarMultiply η.val f))
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3*d F)) (hB : InteriorBall a B)
    (j : Fin (3*d F)) (w : ClosedGradientSpace A) :
    KPContActualSectorBallRestriction.coordinateBall a B hB j (closedGradientCoordinate A (M w)) =
      mulBall B (multiplierCoordinate η a)
        (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
          (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn)
        (KPContActualSectorBallRestriction.coordinateBall a B hB j (closedGradientCoordinate A w)) +
      mulBall B (cutoffPartial F ζ hζ U R P H η a j)
        (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
          (cutoffPartial_cont F ζ hζ U R P H η a j))
        (KPContActualSectorBallRestriction.scalarBall a B hB (closedGradientEmbedding A w)) := by
  obtain ⟨fs,hfs⟩ := graph_tests_tendsto F ζ hζ U R P H μG hμG hR realization w
  let L := (KPContActualSectorBallRestriction.coordinateBall a B hB j).comp ((closedGradientCoordinate A).comp M)
  let N := (mulBall B (multiplierCoordinate η a)
    (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _ (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn)).comp
      ((KPContActualSectorBallRestriction.coordinateBall a B hB j).comp (closedGradientCoordinate A)) +
    (mulBall B (cutoffPartial F ζ hζ U R P H η a j)
      (memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
        (cutoffPartial_cont F ζ hζ U R P H η a j))).comp
        ((KPContActualSectorBallRestriction.scalarBall a B hB).comp (closedGradientEmbedding A))
  apply tendsto_nhds_unique ((L.continuous.tendsto w).comp hfs)
    (((N.continuous.tendsto w).comp hfs).congr' ?_)
  filter_upwards with n
  dsimp [L,N]
  rw [hM]
  exact (coordinateBall_product_test F ζ hζ U R P H μG hμG hR realization η a B hB j (fs n)).symm

private theorem ball_product_ae
    (η : CompactMultiplier (U := U) (H := H))
    (M : ClosedGradientSpace A →L[ℂ] ClosedGradientSpace A)
    (hM : ∀ f : S_U F ζ hζ U R P H,
      M (KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization f) =
        KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization
          (scalarMultiply η.val f))
    (w : ClosedGradientSpace A)
    (s t : BorelL2Sections F ζ hζ U R P H) (r z : SquareFiniteFamily (U := U) (H := H))
    (hs : sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A w) = mk F ζ hζ U R P H s)
    (ht : sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A (M w)) = mk F ζ hζ U R P H t)
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = closedGradientCoordinate A w)
    (hz : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H z = closedGradientCoordinate A (M w))
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3*d F)) (hB : InteriorBall a B) :
    ∀ᵐ x ∂volume.restrict B.carrier,
      scalarCoordinate t a x = multiplierCoordinate η a x * scalarCoordinate s a x ∧
      ∀ j, covariantCoordinate z.val a x j =
        multiplierCoordinate η a x * covariantCoordinate r.val a x j +
        scalarCoordinate s a x * cutoffPartial F ζ hζ U R P H η a j x := by
  have hb := memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
    (smooth_cutoff_flat F ζ hζ U R P H η a).continuousOn
  have hd := fun j => memLp_top_on_ball B _ (coordinateDomain_isOpen a) hB _
    (cutoffPartial_cont F ζ hζ U R P H η a j)
  have hscalar := mulBall_ae B (multiplierCoordinate η a) hb
    (KPContActualSectorBallRestriction.scalarBall a B hB (closedGradientEmbedding A w))
  rw [← scalarBall_graph_product F ζ hζ U R P H μG hμG hR realization η M hM] at hscalar
  have hcoord : ∀ j, ∀ᵐ x ∂volume.restrict B.carrier,
      covariantCoordinate z.val a x j = multiplierCoordinate η a x * covariantCoordinate r.val a x j +
        scalarCoordinate s a x * cutoffPartial F ζ hζ U R P H η a j x := by
    intro j
    have heq := coordinateBall_graph_product F ζ hζ U R P H μG hμG hR realization η M hM a B hB j w
    have hae := Lp.coeFn_add (mulBall B (multiplierCoordinate η a) hb
      (KPContActualSectorBallRestriction.coordinateBall a B hB j (closedGradientCoordinate A w)))
      (mulBall B (cutoffPartial F ζ hζ U R P H η a j) (hd j)
        (KPContActualSectorBallRestriction.scalarBall a B hB (closedGradientEmbedding A w)))
    rw [← heq] at hae
    filter_upwards [hae,
      mulBall_ae B (multiplierCoordinate η a) hb
        (KPContActualSectorBallRestriction.coordinateBall a B hB j (closedGradientCoordinate A w)),
      mulBall_ae B (cutoffPartial F ζ hζ U R P H η a j) (hd j)
        (KPContActualSectorBallRestriction.scalarBall a B hB (closedGradientEmbedding A w)),
      KPContActualSectorBallRestriction.coordinateBall_ae a B hB j _ z hz,
      KPContActualSectorBallRestriction.coordinateBall_ae a B hB j _ r hr,
      KPContActualSectorBallRestriction.scalarBall_ae a B hB _ s hs] with x h1 h2 h3 h4 h5 h6
    change _ = covariantCoordinate z.val a x j at h4
    change _ = covariantCoordinate r.val a x j at h5
    rw [← h4, h1]
    simp only [Pi.add_apply, h2,h3,h5,h6]
    change _ * _ + _ * scalarCoordinate s a x = _
    ring
  filter_upwards [hscalar, KPContActualSectorBallRestriction.scalarBall_ae a B hB _ s hs,
    KPContActualSectorBallRestriction.scalarBall_ae a B hB _ t ht, ae_all_iff.mpr hcoord] with x h1 h2 h3 h4
  refine ⟨?_,h4⟩
  change _ = scalarCoordinate s a x at h2
  change _ = scalarCoordinate t a x at h3
  simpa only [h2,h3] using h1

private theorem ae_of_interior_balls
    (a : ActualChart (U := U) (H := H)) (p : Space (3*d F) → Prop)
    (hp : ∀ B : LocalBall (3*d F), InteriorBall a B → ∀ᵐ x ∂volume.restrict B.carrier, p x) :
    ∀ᵐ x ∂volume.restrict (coordinateDomain a), p x := by
  let I := {B : LocalBall (3*d F) // InteriorBall a B}
  have hcover : (⋃ i : I, i.val.carrier) = coordinateDomain a := by
    ext x
    constructor
    · intro hx
      obtain ⟨B,hx⟩ := Set.mem_iUnion.mp hx
      exact B.property.2 (subset_closure hx)
    · intro hx
      obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp ((coordinateDomain_isOpen a).mem_nhds hx)
      have hn : 0 < 3*d F := by
        have hh := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
        have hd : 0 < d F := by simpa only [d, ← hh.2.1] using hh.2.2
        omega
      let B : LocalBall (3*d F) := ⟨hn, x, ε / 2, by positivity⟩
      have hB : InteriorBall a B := by
        refine ⟨isCompact_closedBall x (ε/2) |>.of_isClosed_subset isClosed_closure
          Metric.closure_ball_subset_closedBall, ?_⟩
        intro y hy
        apply hsub
        have hh : dist y x ≤ ε/2 := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hy)
        exact Metric.mem_ball.mpr (by linarith)
      exact Set.mem_iUnion.mpr ⟨⟨B,hB⟩, Metric.mem_ball_self B.radius_pos⟩
  obtain ⟨T,hTc,hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun i : I => i.val.carrier)
    (fun i => i.val.toOpens.isOpen)
  rw [← hcover, ← hT]
  exact (ae_restrict_biUnion_iff _ hTc _).mpr (fun i _ => hp i.val i.property)

private theorem decode_injective (x : Space (3*d F)) :
    Function.Injective (fun v : KPContCotangentActualGenuineTwistIsotropy.E F => fun j => decode F x j v) := by
  intro v w h
  apply PiLp.ext
  intro ik
  rcases ik with ⟨i,k⟩
  have hh := fun l : Fin 3 => congrFun h ((coefficientIndex (F := F)) (i,l))
  have h1 := hh 0
  have h2 := hh 1
  have h0 := hh 2
  simp only [decode, Equiv.symm_apply_apply] at h1 h2 h0
  have he : (Real.exp (-(baseReindex (F := F)).symm x (i,2)) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero _
  fin_cases k
  · exact h0
  · exact mul_left_cancel₀ he h1
  · exact mul_left_cancel₀ he h2

set_option maxHeartbeats 1000000 in
private theorem MultipliedData_of_lift
    (η : CompactMultiplier (U := U) (H := H))
    (M : ClosedGradientSpace A →L[ℂ] ClosedGradientSpace A)
    (hM : ∀ f : S_U F ζ hζ U R P H,
      M (KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization f) =
        KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization
          (scalarMultiply η.val f))
    (w : ClosedGradientSpace A)
    (s t : BorelL2Sections F ζ hζ U R P H) (r z : SquareFiniteFamily (U := U) (H := H))
    (hs : sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A w) = mk F ζ hζ U R P H s)
    (ht : sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A (M w)) = mk F ζ hζ U R P H t)
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = closedGradientCoordinate A w)
    (hz : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H z = closedGradientCoordinate A (M w)) :
    MultipliedData η s t r z := by
  intro a
  have hball := ae_of_interior_balls F ζ hζ U R P H a _
    (fun B hB => ball_product_ae F ζ hζ U R P H μG hμG hR realization η M hM w s t r z hs ht hr hz a B hB)
  have ha : ∀ᵐ x ∂measure a,
      scalarCoordinate t a x = multiplierCoordinate η a x * scalarCoordinate s a x ∧
      ∀ j, covariantCoordinate z.val a x j =
        multiplierCoordinate η a x * covariantCoordinate r.val a x j +
        scalarCoordinate s a x * cutoffPartial F ζ hζ U R P H η a j x := by
    change ∀ᵐ x ∂(volume.restrict (coordinateDomain a)).withDensity
      (fun x => ENNReal.ofReal (weight a x)), _
    exact (show (volume.restrict (coordinateDomain a)).withDensity
      (fun x => ENNReal.ofReal (weight a x)) ≪ volume.restrict (coordinateDomain a)
      from withDensity_absolutelyContinuous _ _).ae_le hball
  change ∀ᵐ x ∂KPChartL2.weightedMeasure (3*d F) (chart a) (weight a), _ at ha
  rw [← lifted_measure_transport (a := a)] at ha
  have hm : Measurable (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) := by
    apply Continuous.measurable
    unfold fromActual labeledAInv
    exact (baseReindex (F := F)).continuous.comp
      ((CotangentLogCoframe.A (d F)).symm.continuous.comp
        (continuous_pi (fun k => (continuous_apply ((placeEquiv F ζ hζ) k)).comp continuous_subtype_val)))
  have hp := ae_of_ae_map hm.aemeasurable ha
  have hpoint : ∀ (y : a.domain),
      (scalarCoordinate t a (fromActual (ζ := ζ) (hζ := hζ) y.val) =
        multiplierCoordinate η a (fromActual (ζ := ζ) (hζ := hζ) y.val) *
          scalarCoordinate s a (fromActual (ζ := ζ) (hζ := hζ) y.val) ∧
      ∀ j, covariantCoordinate z.val a (fromActual (ζ := ζ) (hζ := hζ) y.val) j =
        multiplierCoordinate η a (fromActual (ζ := ζ) (hζ := hζ) y.val) *
          covariantCoordinate r.val a (fromActual (ζ := ζ) (hζ := hζ) y.val) j +
        scalarCoordinate s a (fromActual (ζ := ζ) (hζ := hζ) y.val) *
          cutoffPartial F ζ hζ U R P H η a j (fromActual (ζ := ζ) (hζ := hζ) y.val)) →
      sectionFields t.val a (coordinates a y) = cutoffLift η.val a (coordinates a y) * sectionFields s.val a (coordinates a y) ∧
      localCoefficient a z.val y = cutoffLift η.val a (coordinates a y) • localCoefficient a r.val y +
        sectionFields s.val a (coordinates a y) • cutoffDifferential η.val a (coordinates a y) := by
    intro y h
    have hcoord : (coordinates a y).val = (baseReindex (F := F)).symm
      (fromActual (ζ := ζ) (hζ := hζ) y.val) := by simp [coordinates, fromActual]
    have hxomega : (baseReindex (F := F)).symm (fromActual (ζ := ζ) (hζ := hζ) y.val) ∈ omega a :=
      hcoord ▸ (coordinates a y).property
    have hx : fromActual (ζ := ζ) (hζ := hζ) y.val ∈ coordinateDomain a := hxomega
    have hc : (coordinates a y).val ∈ omega a := (coordinates a y).property
    constructor
    · simpa only [scalarCoordinate, multiplierCoordinate, liftExtension, ← hcoord, dif_pos hc] using h.1
    · apply decode_injective F (fromActual (ζ := ζ) (hζ := hζ) y.val)
      funext j
      dsimp only
      rw [decode_add_smul F]
      have hj := h.2 j
      rw [cutoffPartial_decode F ζ hζ U R P H η a j _ hx] at hj
      simpa only [covariantCoordinate, scalarCoordinate, multiplierCoordinate, liftExtension,
        ← hcoord, dif_pos hc, localCoefficient, decode] using hj
  have hh : ∀ᵐ y ∂a.liftedMeasure,
      sectionFields t.val a (coordinates a y) = cutoffLift η.val a (coordinates a y) * sectionFields s.val a (coordinates a y) ∧
      localCoefficient a z.val y = cutoffLift η.val a (coordinates a y) • localCoefficient a r.val y +
        sectionFields s.val a (coordinates a y) • cutoffDifferential η.val a (coordinates a y) := by
    filter_upwards [hp] with y hy
    exact hpoint y hy
  exact ⟨hh.mono (fun _ h => h.1), hh.mono (fun _ h => h.2)⟩

private theorem localized_coordinate_map_of_lift
    (η : CompactMultiplier (U := U) (H := H))
    (M : ClosedGradientSpace A →L[ℂ] ClosedGradientSpace A)
    (hM : ∀ f : S_U F ζ hζ U R P H,
      M (KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization f) =
        KPContActualFormCutoffClosedProduct.graphTestLift F ζ hζ U R P H μG hμG hR realization
          (scalarMultiply η.val f))
    (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) (hB : InteriorBall a B) :
    ∃ (Lη : ClosedGradientSpace A →L[ℂ] CoordinateH1 B) (C : ℝ),
      0 < C ∧ (∀ w, ‖Lη w‖ ≤ C * ‖w‖) ∧ ∀ (w : ClosedGradientSpace A)
      (s : BorelL2Sections F ζ hζ U R P H),
      sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A w) = mk F ζ hζ U R P H s →
      (fun x => (Lη w).val (zeroIndex (3 * d F)) x) =ᵐ[volume.restrict B.carrier]
        (fun x => multiplierCoordinate η a x * scalarCoordinate s a x) := by
  letI : NormedAddCommGroup (CoordinateH1 B) := Submodule.normedAddCommGroup (coordinateH1Submodule B)
  letI : NormedAddCommGroup (ClosedGradientSpace A) := Submodule.normedAddCommGroup (closedGradientGraph A)
  letI : NormedSpace ℂ (CoordinateH1 B) := Submodule.normedSpace (coordinateH1Submodule B)
  letI : NormedSpace ℂ (ClosedGradientSpace A) := Submodule.normedSpace (closedGradientGraph A)
  letI : IsBoundedSMul ℂ (CoordinateH1 B) := IsBoundedSMul.of_norm_smul_le
    (fun c x => norm_smul_le c (x : PiLp 2 (fun _ : MultiIndex (3*d F) 1 => BallL2 B)))
  letI : IsBoundedSMul ℂ (ClosedGradientSpace A) := IsBoundedSMul.of_norm_smul_le
    (fun c x => norm_smul_le c (x : WithLp 2
      (KPContSectorClosedLpSubspace.H F ζ hζ R U × KPContActualSectorCotangentL2.V F ζ hζ U R P H)))
  let L := (coordinateGraphMap F ζ hζ U R P H μG hμG hR realization a B hB).comp M
  refine ⟨L, ‖L‖ + 1, by positivity, fun w => ?_, ?_⟩
  · exact (L.le_opNorm w).trans (by nlinarith [norm_nonneg w])
  · intro w s hs
    change (fun x => ballDerivative a B hB (zeroIndex (3*d F))
      (closedGradientEmbedding A (M w), closedGradientCoordinate A (M w)) x) =ᵐ[_] _
    rw [ballDerivative_zero]
    rw [scalarBall_graph_product F ζ hζ U R P H μG hμG hR realization η M hM]
    filter_upwards [mulBall_ae B (multiplierCoordinate η a) _
      (KPContActualSectorBallRestriction.scalarBall a B hB (closedGradientEmbedding A w)),
      KPContActualSectorBallRestriction.scalarBall_ae a B hB _ s hs] with x h1 h2
    rw [h1,h2]
    rfl

structure Properties : Prop where
  weak_local : ∀ u : Q, ActualWeakH1Loc (H := H) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
  closed_gradient : ∀ u : Q,
    IsActualWeakGradient (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) ((A).closure u)
  form_integral : ∀ (u v : Q) (r s : SquareFiniteFamily (U := U) (H := H)),
    KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = (A).closure u →
    KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H s = (A).closure v →
    Integrable (pair r.val s.val) (KPContActualSectorCotangentL2.muU F ζ hζ U R P) ∧
    closedGradientForm A u v = ∫ x, pair r.val s.val x
      ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P
  energy_integral : ∀ (u : Q) (r : SquareFiniteFamily (U := U) (H := H)),
    KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = (A).closure u →
    (∀ i, Integrable (placeSquare r.val i) (KPContActualSectorCotangentL2.muU F ζ hζ U R P)) ∧
    closedGradientEnergy A u = ∑ i : Fin (d F), ∫ x, placeSquare r.val i x
      ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P

  multiplier : ∀ η : CompactMultiplier (U := U) (H := H),
    ∃ (Mη : ClosedGradientSpace A →L[ℂ] ClosedGradientSpace A) (C : ℝ),
      0 < C ∧ (∀ w, ‖Mη w‖ ≤ C * ‖w‖) ∧ ∀ w : ClosedGradientSpace A,
      ∃ (s t : BorelL2Sections F ζ hζ U R P H)
        (r z : SquareFiniteFamily (U := U) (H := H)),
        sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A w) = mk F ζ hζ U R P H s ∧
        sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A (Mη w)) = mk F ζ hζ U R P H t ∧
        KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = closedGradientCoordinate A w ∧
        KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H z = closedGradientCoordinate A (Mη w) ∧
        MultipliedData η s t r z

  localized_coordinate_map : ∀ (η : CompactMultiplier (U := U) (H := H))
      (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)), InteriorBall a B →
    ∃ (Lη : ClosedGradientSpace A →L[ℂ] CoordinateH1 B) (C : ℝ),
      0 < C ∧ (∀ w, ‖Lη w‖ ≤ C * ‖w‖) ∧ ∀ (w : ClosedGradientSpace A)
      (s : BorelL2Sections F ζ hζ U R P H),
      sectorLineIsometry F ζ hζ U R P H (closedGradientEmbedding A w) = mk F ζ hζ U R P H s →
      (fun x => (Lη w).val (zeroIndex (3 * d F)) x) =ᵐ[volume.restrict B.carrier]
        (fun x => multiplierCoordinate η a x * scalarCoordinate s a x)

end DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization

namespace DedekindZetaZeroFree

open KPContActualSectorFormWeakLocalization

set_option maxHeartbeats 1000000 in

theorem kp_cont_actual_sector_form_weak_localization
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorFormWeakLocalization.Properties F ζ hζ U R P H μG hμG hR realization := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    obtain ⟨s,r,hs,hr,hw⟩ := closedGradient_isActualWeak F ζ hζ U R P H μG hμG hR realization u
    exact ⟨s,r.val,hs,hw⟩
  · exact closedGradient_isActualWeak F ζ hζ U R P H μG hμG hR realization
  · intro u v r s hr hs
    refine ⟨KPContActualCotangentIntrinsicHilbertIntegral.integrable_pair r s, ?_⟩
    exact (kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization).inner_integral
      _ _ r s hr hs
  · intro u r hr
    refine ⟨place_square_integrable r, ?_⟩
    change ‖(KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H
      μG hμG hR realization).closure u‖ ^ 2 = _
    rw [(kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization).norm_integral _ r hr]
    rw [← integral_finsetSum _ (fun i _ => place_square_integrable r i)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (place_square_sum r.val x).symm))
  · intro η
    obtain ⟨B,D,hB,hD,hη,hdη⟩ := KPContActualSectorMultiplier.compactCutoff_bounds
      F ζ hζ U R P H η.val η.property
    obtain ⟨M⟩ := KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H η.val B hB hη
    obtain ⟨L,hL,hLt⟩ := KPContActualFormCutoffClosedProduct.exists_lift
      F ζ hζ U R P H μG hμG hR realization η.val M B D hB hD hη hdη
    let A := KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
    letI : NormedAddCommGroup (ClosedGradientSpace A) := Submodule.normedAddCommGroup (closedGradientGraph A)
    letI : NormedSpace ℂ (ClosedGradientSpace A) := Submodule.normedSpace (closedGradientGraph A)
    letI : IsBoundedSMul ℂ (ClosedGradientSpace A) := IsBoundedSMul.of_norm_smul_le
      (fun c x => norm_smul_le c (x : WithLp 2
        (KPContSectorClosedLpSubspace.H F ζ hζ R U × KPContActualSectorCotangentL2.V F ζ hζ U R P H)))
    refine ⟨L, ‖L‖ + 1, by positivity, fun w => (L.le_opNorm w).trans (by nlinarith [norm_nonneg w]), ?_⟩
    intro w
    obtain ⟨s,hs⟩ := Quotient.exists_rep (KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H
      (closedGradientEmbedding A w))
    obtain ⟨t,ht⟩ := Quotient.exists_rep (KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H
      (closedGradientEmbedding A (L w)))
    obtain ⟨r,hr⟩ := KPContActualSectorCotangentL2.ofFamily_surjective F ζ hζ U R P H (closedGradientCoordinate A w)
    obtain ⟨z,hz⟩ := KPContActualSectorCotangentL2.ofFamily_surjective F ζ hζ U R P H (closedGradientCoordinate A (L w))
    refine ⟨s,t,r,z,hs.symm,ht.symm,hr,hz,?_⟩
    exact MultipliedData_of_lift F ζ hζ U R P H μG hμG hR realization η L hLt w s t r z hs.symm ht.symm hr hz
  · intro η a B hB
    obtain ⟨C,D,hC,hD,hη,hdη⟩ := KPContActualSectorMultiplier.compactCutoff_bounds
      F ζ hζ U R P H η.val η.property
    obtain ⟨M⟩ := KPContActualSectorMultiplier.boundedSectorMultiplier F ζ hζ U R P H η.val C hC hη
    obtain ⟨L,hL,hLt⟩ := KPContActualFormCutoffClosedProduct.exists_lift
      F ζ hζ U R P H μG hμG hR realization η.val M C D hC hD hη hdη
    exact localized_coordinate_map_of_lift F ζ hζ U R P H μG hμG hR realization η L hLt a B hB

end DedekindZetaZeroFree

end
