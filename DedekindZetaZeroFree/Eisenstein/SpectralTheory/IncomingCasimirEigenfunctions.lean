module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SpectralCoordinateAndPoleOrders
public import DedekindZetaZeroFree.Geometry.HyperbolicActionMetricAndVolume
public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPIncomingCasimir

open scoped ContDiff

def nu (s : ℂ) : ℂ := (1 : ℂ) / 6 + s

def heightFactor (d : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((d : ℂ) * ((4 : ℂ) / 3 + 2 * s) * (t : ℂ))

def radialLaplacian (d : ℕ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  -((d : ℂ)⁻¹ * deriv (deriv w) t) + 2 * deriv w t

private theorem incoming_exp_hasDerivAt (c b : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (c * (u : ℂ)) * b)
      (c * (Complex.exp (c * (t : ℂ)) * b)) t := by
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one,
    mul_assoc, mul_comm, mul_left_comm] using
    (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).cexp.mul_const b)

theorem heightFactor_eigenfunction (d : ℕ) (hd : 0 < d) (s : ℂ) (b : ℂ) :
    ∀ t : ℝ,
      radialLaplacian d (fun u => heightFactor d s u * b) t =
        KPContinuation.spectralCoordinate (d : ℤ) s * (heightFactor d s t * b) := by
  let c : ℂ := (d : ℂ) * ((4 : ℂ) / 3 + 2 * s)
  have hfirst : deriv (fun u => heightFactor d s u * b) =
      fun t => c * (heightFactor d s t * b) := by
    funext t
    exact (incoming_exp_hasDerivAt c b t).deriv
  have hsecond (t : ℝ) :
      deriv (fun u => c * (heightFactor d s u * b)) t =
        c * (c * (heightFactor d s t * b)) :=
    ((incoming_exp_hasDerivAt c b t).const_mul c).deriv
  intro t
  unfold radialLaplacian
  rw [hfirst, hsecond]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp only [KPContinuation.spectralCoordinate, Int.cast_natCast]
  dsimp [c]
  field_simp
  ring

section RationalRealization

variable {G H A : Type*} [AddCommGroup H] [Module ℂ H]

def rationalIncoming (realize : ℂ → H →ₗ[ℂ] (G → ℂ))
    (cuspChart : A → ℝ → G) (a : A) (s : ℂ) : H →ₗ[ℂ] (ℝ → ℂ) where
  toFun f t := realize s f (cuspChart a t)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

def incomingCoefficient (realize : ℂ → H →ₗ[ℂ] (G → ℂ))
    (cuspChart : A → ℝ → G) (a : A) (s : ℂ) : H →ₗ[ℂ] ℂ where
  toFun f := realize s f (cuspChart a 0)
  map_add' := by intros; simp
  map_smul' := by intros; simp

end RationalRealization

end DedekindZetaZeroFree.KPIncomingCasimir

end
