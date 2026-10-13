module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Scales

noncomputable section

def xExponent : ℝ := 67 / 100

def yExponent : ℝ := 151 / 400

def smoothingExponent : ℝ := 33 / 100

def supportExponent : ℝ := 419 / 400

def reflectedExponent : ℝ := 287 / 800

def smallCutoffExponent : ℝ := 1 / 5

def largeCutoffExponent : ℝ := 3301 / 10000

def contourOffset : ℝ := 1 / 10000000

def rightLine : ℝ := 1 + contourOffset

def goodLine : ℝ := 8801 / 10000

def wLine : ℝ := 3 / 25

def zLine : ℝ := 2 / 5

def tailShift : ℝ := 50000

def kernelExponent (x y z : ℝ) : ℝ := xExponent / 2 + x - 1 + smoothingExponent * z + yExponent * (y - 1)

def spectralExponent (s : ℝ) : ℝ := s - 61 / 100

def mainExponent : ℝ := 39 / 100

def xScale (Z : ℝ) : ℝ := Z ^ xExponent

def yScale (Z : ℝ) : ℝ := Z ^ yExponent

theorem xScale_pos (Z : ℝ) (hZ : 0 < Z) : 0 < xScale Z := Real.rpow_pos_of_pos hZ _

theorem yScale_pos (Z : ℝ) (hZ : 0 < Z) : 0 < yScale Z := Real.rpow_pos_of_pos hZ _

theorem rightLine_eq : rightLine = 10000001 / 10000000 := by
  unfold rightLine contourOffset; norm_num

end

end DedekindZetaZeroFree.Quantitative.Scales
