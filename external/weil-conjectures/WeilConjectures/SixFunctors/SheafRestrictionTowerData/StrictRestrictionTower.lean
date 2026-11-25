/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower

/-! # Strict composites in a system of restriction functors

Source: Stacks Tag 03DA; blueprint DVR effectivity, composition of strict finite models.
(blueprint: lem-coef-strict-restriction-tower-composites).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
attribute [local instance 30000] SheafOfModules.instPreadditive
  Functor.preservesZeroMorphisms_of_additive
section RestrictionComposition
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  {R S T : Sheaf J RingCat.{r}}

/-- Canonical composition of scalar restriction, keeping the coefficient equality abstract.
Source: Stacks Tag 03DA; blueprint DVR effectivity, restriction comparison. -/
def normalizedDVRRestrictionComp (f : R ⟶ S) (g : S ⟶ T) (q : R ⟶ T)
    (e : f ≫ g = q) :
    SheafOfModules.restrictScalars.{w} g ⋙ SheafOfModules.restrictScalars.{w} f ≅
      SheafOfModules.restrictScalars.{w} q :=
  normalizedDVRRestrictionCompIso f g ≪≫
    eqToIso (congrArg (fun k ↦ SheafOfModules.restrictScalars.{w} k) e)

/-- Restriction composition remains associative on cochain complexes. -/
theorem normalizedDVRRestrictionComp_assoc_complex
    {R₀ R₁ R₂ R₃ : Sheaf J RingCat.{r}}
    (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) (h : R₂ ⟶ R₃)
    (fg : R₀ ⟶ R₂) (gh : R₁ ⟶ R₃) (fgh : R₀ ⟶ R₃)
    (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh)
    (e₃ : f ≫ gh = fgh) (e₄ : fg ≫ h = fgh)
    (K : CochainComplex (SheafOfModules.{w} R₃) ℤ) :
    ((SheafOfModules.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (normalizedDVRRestrictionComp g h gh e₂) (.up ℤ)).hom.app K) ≫
      (Functor.mapHomologicalComplexCompIso
        (normalizedDVRRestrictionComp f gh fgh e₃) (.up ℤ)).hom.app K =
    (Functor.mapHomologicalComplexCompIso
        (normalizedDVRRestrictionComp f g fg e₁) (.up ℤ)).hom.app
          (((SheafOfModules.restrictScalars h).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Functor.mapHomologicalComplexCompIso
        (normalizedDVRRestrictionComp fg h fgh e₄) (.up ℤ)).hom.app K := by
  cases e₁
  cases e₂
  cases e₃
  rfl

end RestrictionComposition

/-- Functor data for strict restriction composites. -/
structure StrictRestrictionData
    (B : ℕ → Type a) [∀ n, Category.{b} (B n)]
    (A : Type r) [Category.{w} A] where
  finite : ∀ {m n : ℕ}, n ≤ m → (B n ⥤ B m)
  completed : ∀ n : ℕ, B n ⥤ A
  finiteComp : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m),
    finite hmn ⋙ finite hkm ⟶ finite (le_trans hmn hkm)
  completedComp : ∀ {m n : ℕ} (h : n ≤ m),
    finite h ⋙ completed m ⟶ completed n
  coherence : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m) (K : B n),
    (completed k).map ((finiteComp hkm hmn).app K) ≫
      (completedComp (le_trans hmn hkm)).app K =
    (completedComp hkm).app ((finite hmn).obj K) ≫
      (completedComp hmn).app K

namespace StrictRestrictionData
variable {B : ℕ → Type a} [∀ n, Category.{b} (B n)]
  {A : Type r} [Category.{w} A] (data : StrictRestrictionData B A)

private theorem map_composite {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m)
    {K : B n} {M : B m} {N : B k}
    (f : N ⟶ (data.finite hkm).obj M)
    (g : M ⟶ (data.finite hmn).obj K) :
    (data.completed k).map
        (f ≫ (data.finite hkm).map g ≫ (data.finiteComp hkm hmn).app K) ≫
      (data.completedComp (le_trans hmn hkm)).app K =
    ((data.completed k).map f ≫ (data.completedComp hkm).app M) ≫
      ((data.completed m).map g ≫ (data.completedComp hmn).app K) := by
  have hn := (data.completedComp hkm).naturality g
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [data.coherence]
  rw [← Category.assoc ((data.completed k).map ((data.finite hkm).map g)), hn]
  simp only [Category.assoc]

variable (P : ∀ n, B n) (g : ∀ n, P (n + 1) ⟶ (data.finite n.le_succ).obj (P n))

/-- The recursively composed semilinear maps in the restriction diagram. -/
def finiteMap (n : ℕ) : ∀ k : ℕ, P (n + (k + 1)) ⟶
    (data.finite (Nat.le_add_right n (k + 1))).obj (P n)
  | 0 => g n
  | k + 1 => g (n + (k + 1)) ≫
      (data.finite (n + (k + 1)).le_succ).map (finiteMap n k) ≫
      (data.finiteComp (n + (k + 1)).le_succ
        (Nat.le_add_right n (k + 1))).app (P n)

/-- The successor equation of the finite composite, with functor data kept abstract. -/
theorem finiteMap_succ (n k : ℕ) :
    data.finiteMap P g n (k + 1) = g (n + (k + 1)) ≫
      (data.finite (n + (k + 1)).le_succ).map (data.finiteMap P g n k) ≫
      (data.finiteComp (n + (k + 1)).le_succ
        (Nat.le_add_right n (k + 1))).app (P n) := by
  rfl

variable [HasZeroMorphisms A] [HasZeroObject A]

/-- The completed representatives, with zero inserted at exponent zero. -/
def object : ℕ → A
  | 0 => 0
  | j + 1 => (data.completed j).obj (P j)

/-- The restricted successor maps of the completed representatives. -/
def step : ∀ j, data.object P (j + 1) ⟶ data.object P j
  | 0 => 0
  | j + 1 => (data.completed (j + 1)).map (g j) ≫
      (data.completedComp j.le_succ).app (P j)

/-- The actual inverse-sequence functor of the completed successor maps. -/
def tower : ℕᵒᵖ ⥤ A := Functor.ofOpSequence (data.step P g)

private theorem sequence_composite
    {A : Type*} [Category A] {Y : ℕ → A}
    (u : ∀ j : ℕ, Y (j + 1) ⟶ Y j) (n : ℕ)
    (a : ∀ k : ℕ, Y (n + (k + 1) + 1) ⟶ Y (n + 1))
    (h₀ : a 0 = u (n + 1))
    (hs : ∀ k : ℕ, a (k + 1) = u (n + (k + 1) + 1) ≫ a k) (k : ℕ) :
    (Functor.ofOpSequence u).map
      (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op = a k := by
  induction k with
  | zero =>
    simpa only [h₀] using (Functor.ofOpSequence_map_homOfLE_succ u (n + 1))
  | succ k ih =>
    have hh : (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 2)))).op =
        (homOfLE (n + (k + 1) + 1).le_succ).op ≫
          (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op := rfl
    rw [hh, CategoryTheory.Functor.map_comp, ih, hs]
    erw [Functor.ofOpSequence_map_homOfLE_succ]

/-- Completed restrictions of finite composites are the actual sequence maps. -/
theorem tower_map (n k : ℕ) :
    (data.tower P g).map
      (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op =
    (data.completed (n + (k + 1))).map (data.finiteMap P g n k) ≫
      (data.completedComp (Nat.le_add_right n (k + 1))).app (P n) := by
  apply sequence_composite (data.step P g) n
    (fun j ↦ (data.completed (n + (j + 1))).map (data.finiteMap P g n j) ≫
      (data.completedComp (Nat.le_add_right n (j + 1))).app (P n))
  · simp only [finiteMap, step]
  · intro j
    conv_lhs => rw [finiteMap]
    simp only [step]
    exact data.map_composite (n + (j + 1)).le_succ
      (Nat.le_add_right n (j + 1)) (g (n + (j + 1))) (data.finiteMap P g n j)

end StrictRestrictionData

variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}

/-- A coefficient tower together with compatible maps from a fixed coefficient sheaf.
The completed comparisons are certified canonical and stored explicitly so a strict
tower can share their actual terms. -/
structure SheafRestrictionTowerData
    (coefficient : ℕ → Sheaf J RingCat.{r}) (completed : Sheaf J RingCat.{r}) where
  quotient : ∀ {m n : ℕ}, n ≤ m → (coefficient m ⟶ coefficient n)
  quotient_comp : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m),
    quotient hkm ≫ quotient hmn = quotient (le_trans hmn hkm)
  projection : ∀ n : ℕ, completed ⟶ coefficient n
  projection_comp : ∀ {m n : ℕ} (h : n ≤ m),
    projection m ≫ quotient h = projection n
  completedComparison : ∀ {m n : ℕ} (h : n ≤ m),
    SheafOfModules.restrictScalars.{w} (quotient h) ⋙
      SheafOfModules.restrictScalars (projection m) ≅
        SheafOfModules.restrictScalars (projection n)
  completedComparison_eq : ∀ {m n : ℕ} (h : n ≤ m),
    completedComparison h = normalizedDVRRestrictionComp
      (projection m) (quotient h) (projection n) (projection_comp h)

namespace SheafRestrictionTowerData
variable {coefficient : ℕ → Sheaf J RingCat.{r}} {completed : Sheaf J RingCat.{r}}
  (syst : SheafRestrictionTowerData.{a, b, r, w} coefficient completed)

/-- Composition comparison at finite levels. -/
def finiteComp {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m) :
    SheafOfModules.restrictScalars.{w} (syst.quotient hmn) ⋙
      SheafOfModules.restrictScalars (syst.quotient hkm) ≅
        SheafOfModules.restrictScalars (syst.quotient (le_trans hmn hkm)) :=
  normalizedDVRRestrictionComp _ _ _ (syst.quotient_comp hkm hmn)

/-- Comparison between finite and completed restriction. -/
def completedComp {m n : ℕ} (h : n ≤ m) :
    SheafOfModules.restrictScalars.{w} (syst.quotient h) ⋙
      SheafOfModules.restrictScalars (syst.projection m) ≅
        SheafOfModules.restrictScalars (syst.projection n) :=
  syst.completedComparison h

/-- The coefficient restrictions, viewed as functors between complex categories. -/
def complexData : StrictRestrictionData
    (fun n ↦ CochainComplex (SheafOfModules.{w} (coefficient n)) ℤ)
    (CochainComplex (SheafOfModules.{w} completed) ℤ) where
  finite := fun h ↦ (SheafOfModules.restrictScalars (syst.quotient h)).mapHomologicalComplex
    (.up ℤ)
  completed := fun n ↦ (SheafOfModules.restrictScalars (syst.projection n)).mapHomologicalComplex
    (.up ℤ)
  finiteComp := fun hkm hmn ↦ (Functor.mapHomologicalComplexCompIso
    (syst.finiteComp hkm hmn) (.up ℤ)).hom
  completedComp := fun h ↦
    (Functor.mapHomologicalComplexCompIso (syst.completedComp h) (.up ℤ)).hom
  coherence := by
    intro k m n hkm hmn K
    simp only [completedComp, syst.completedComparison_eq]
    exact normalizedDVRRestrictionComp_assoc_complex
      (syst.projection k) (syst.quotient hkm) (syst.quotient hmn)
      (syst.projection m) (syst.quotient (le_trans hmn hkm)) (syst.projection n)
      (syst.projection_comp hkm) (syst.quotient_comp hkm hmn)
      (syst.projection_comp (le_trans hmn hkm)) (syst.projection_comp hmn) K

variable (P : ∀ j : ℕ, CochainComplex (SheafOfModules.{w} (coefficient j)) ℤ)
  (g : ∀ j : ℕ, P (j + 1) ⟶
    ((SheafOfModules.restrictScalars (syst.quotient j.le_succ)).mapHomologicalComplex
      (.up ℤ)).obj (P j))

/-- The finite semilinear composite of the successor maps. -/
def finiteMap (n k : ℕ) : P (n + (k + 1)) ⟶
    ((SheafOfModules.restrictScalars
      (syst.quotient (Nat.le_add_right n (k + 1)))).mapHomologicalComplex
        (.up ℤ)).obj (P n) :=
  syst.complexData.finiteMap P g n k

/-- The finite-composite successor equation without unfolding the complex functor data. -/
theorem finiteMap_succ (n k : ℕ) :
    syst.finiteMap P g n (k + 1) = g (n + (k + 1)) ≫
      ((SheafOfModules.restrictScalars (syst.quotient (n + (k + 1)).le_succ)).mapHomologicalComplex
        (.up ℤ)).map (syst.finiteMap P g n k) ≫
      (Functor.mapHomologicalComplexCompIso
        (syst.finiteComp (n + (k + 1)).le_succ (Nat.le_add_right n (k + 1)))
        (.up ℤ)).hom.app (P n) := by
  exact syst.complexData.finiteMap_succ P g n k

variable [HasZeroObject (SheafOfModules.{w} completed)]

/-- Completed representatives, with zero at level zero. -/
def complex : ℕ → CochainComplex (SheafOfModules.{w} completed) ℤ
  | 0 => 0
  | j + 1 => ((SheafOfModules.restrictScalars (syst.projection j)).mapHomologicalComplex
      (.up ℤ)).obj (P j)

/-- Completed successor maps. -/
def step : ∀ j : ℕ, syst.complex P (j + 1) ⟶ syst.complex P j
  | 0 => 0
  | j + 1 =>
    ((SheafOfModules.restrictScalars (syst.projection (j + 1))).mapHomologicalComplex
      (.up ℤ)).map (g j) ≫
    (Functor.mapHomologicalComplexCompIso (syst.completedComp j.le_succ)
      (.up ℤ)).hom.app (P j)

/-- The strict tower of the completed representatives. -/
def tower : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{w} completed) ℤ :=
  Functor.ofOpSequence (syst.step P g)

/-- Finite semilinear composites restrict to the actual strict tower maps.
Source: Stacks Tag 03DA; blueprint strict finite-model construction.
(blueprint: lem-coef-strict-restriction-tower-composites).

Proof: the finite composite starts with the given successor map. Naturality of the
restriction comparison and associativity of its identity maps on sections show
that completed restriction carries each recursive composite to the corresponding
composite of completed successor maps. Apply the abstract functor calculation,
which inducts on the number of successors using the sequence functor's map law. -/
theorem tower_map (n k : ℕ) :
    (syst.tower P g).map
      (homOfLE (Nat.succ_le_succ (Nat.le_add_right n (k + 1)))).op =
    ((SheafOfModules.restrictScalars (syst.projection (n + (k + 1)))).mapHomologicalComplex
       (.up ℤ)).map (syst.finiteMap P g n k) ≫
      (Functor.mapHomologicalComplexCompIso
        (syst.completedComp (Nat.le_add_right n (k + 1))) (.up ℤ)).hom.app (P n) := by
  exact syst.complexData.tower_map P g n k

end SheafRestrictionTowerData
end WeilConjectures
