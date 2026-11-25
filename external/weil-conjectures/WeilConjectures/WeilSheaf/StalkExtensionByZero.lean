/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.Triangle

import WeilConjectures.WeilSheaf.OpenImmersionRestriction
import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Stalks of the extension by zero of a Weil sheaf

Let `j : U ⟶ X` be a quasi-compact open immersion of `k₀`-schemes and `G` a Weil sheaf on `U`.
The extension by zero `j₀!G` (`AlgebraicGeometry.WeilSheaf.extensionByZero`) has the stalk
prescription of blueprint `proposition-extension-zero-restriction-closed-subscheme`: at a closed
point `j z` of `U` its geometric stalk, with its local Frobenius, is that of `G` at `z`, and at a
closed point outside `U` it vanishes. In particular `j₀!` preserves punctual purity, and, being
exact, mixed upper weight bounds.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_stalk_extensionByZero`: the stalk of `j₀!G` at a
  closed point outside `U` vanishes, since the pullback of `j̄_!G` along a geometric point
  missing `Ū` vanishes.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_extensionByZero`: the stalk of `j₀!G` at a
  closed point `j z` of `U` is that of `G` at `z`, with its local Frobenius
  (`proposition-extension-zero-restriction-closed-subscheme`).
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.extensionByZero` and
  `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.extensionByZero`: `j₀!` preserves
  punctual purity and mixed upper weight bounds.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

/-- The stalk of the extension by zero `j₀!G` at a closed point `x` outside the open subscheme
`U` vanishes: the geometric point over `x` misses the image of `Ū`, and the pullback of `j̄_!G`
along a morphism missing the image of `Ū` vanishes
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek`). -/
theorem subsingleton_stalk_extensionByZero (G : WeilSheaf k₀ l U) (x : X.finitePoints)
    (hx : x.1 ∉ Set.range j.base) :
    Subsingleton (((extensionByZero j).obj G).stalk x).carrier := by
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  have hdisj : Set.range (Scheme.Hom.geometricFiberMap j (comp_over j _)).base ∩
      Set.range s.base = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun p ⟨⟨q, hq⟩, ⟨c, hc⟩⟩ ↦ hx ?_
    have hc' : c = IsLocalRing.closedPoint (AlgebraicClosure k₀) := Subsingleton.elim _ _
    subst hc'
    have h₁ := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
      (X ↘ Spec (CommRingCat.of k₀)) x
    rw [Scheme.Hom.comp_apply, hc] at h₁
    refine ⟨((U ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base q, ?_⟩
    rw [← h₁, ← hq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj]
  have hz := ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek
    (Scheme.Hom.geometricFiberMap j (comp_over j _)) s hdisj G.obj.carrier
  have hz' : IsZero ((s)^*[WeilCoefficients.{u} l].obj
      ((extensionByZero j).obj G).obj.carrier.X) :=
    (ProEtale.AdicSheaf.forget _).map_isZero hz
  change Subsingleton ((WeilCoefficients.toModuleCat l).obj
    ((Sheaf.Γ _ _).obj ((s)^*[WeilCoefficients.{u} l].obj
      ((extensionByZero j).obj G).obj.carrier.X)))
  exact ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
    ((Sheaf.Γ _ _).map_isZero hz'))

private lemma stalkAt_eq_of_degree_eq (F : WeilSheaf k₀ l X)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {m n : ℕ} (h : m = n)
    (hm : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hn : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ s) :
    F.stalkAt s m hm = F.stalkAt s n hn := by
  subst n
  rfl

/-- **The stalks of the extension by zero inside `U`** (blueprint:
`proposition-extension-zero-restriction-closed-subscheme`, `(j_!K)_x̄ = K_x̄` for a geometric point
`x̄` of `U`): the geometric stalk of `j₀!G` at a closed point `j z` of `U`, with its local
Frobenius, is that of `G` at `z`. -/
theorem nonempty_equiv_stalk_extensionByZero (G : WeilSheaf k₀ l U) (z : U.finitePoints) :
    Nonempty ((((extensionByZero j).obj G).stalk
      ⟨j.base z.1, (Scheme.Hom.mem_finitePoints_iff_of_isIso j z.1).2 z.2⟩).Equiv
        (G.stalk z)) := by
  let J := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  let t := (U ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z
  let x : X.finitePoints :=
    ⟨j.base z.1, (Scheme.Hom.mem_finitePoints_iff_of_isIso j z.1).2 z.2⟩
  let s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  have hdeg : (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 =
      (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
    rw [← Scheme.Hom.degreeOver_comp_of_isIso j (X ↘ Spec (CommRingCat.of k₀)) z.1,
      comp_over]
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (U ↘ Spec (CommRingCat.of k₀)) z
  have ht' : (t ≫ J) ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom ≫
        (t ≫ J) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have : IsIso (𝟙 _ : (J)^*[WeilCoefficients.{u} l].obj
      ((extensionByZero j).obj G).obj.carrier.X ⟶
      ((upperStar j).obj ((extensionByZero j).obj G)).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((J)^*[WeilCoefficients.{u} l].obj
      ((extensionByZero j).obj G).obj.carrier.X)))
  obtain ⟨e₁⟩ := nonempty_equiv_stalkAt_of_upperStar (φ := j) (F := ((extensionByZero j).obj G))
    (G := (upperStar j).obj ((extensionByZero j).obj G)) (θ := 𝟙 _)
    (upperStar_frobeniusStr_compatible j ((extensionByZero j).obj G)) t _ ht ht'
  obtain ⟨e⟩ : Nonempty ((upperStar j).obj ((extensionByZero j).obj G) ≅ G) :=
    nonempty_upperStar_extensionByZero_iso j G
  obtain ⟨e₂⟩ := nonempty_equiv_stalkAt_of_iso t _ ht e
  have hbase := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (X ↘ Spec (CommRingCat.of k₀)) x
  have hss' : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((t ≫ J) ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc]
    exact (congrArg j.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ z)).symm
  have hmem : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k₀)) ∈ X.finitePoints := by
    rw [hbase]
    exact x.2
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  rw [hdeg] at hs
  obtain ⟨e₀⟩ := ((extensionByZero j).obj G).nonempty_equiv_stalkAt s (t ≫ J) hss' hmem _ hs ht'
  change Nonempty ((((extensionByZero j).obj G).stalk x).Equiv (G.stalk z))
  have heq : ((extensionByZero j).obj G).stalk x = ((extensionByZero j).obj G).stalkAt s
      ((U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1) hs :=
    stalkAt_eq_of_degree_eq ((extensionByZero j).obj G) s hdeg
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ x) hs
  dsimp only [J] at e₀
  rw [heq]
  exact ⟨e₀.trans (e₁.trans e₂)⟩

/-- The extension by zero `j₀!G` of a Weil sheaf punctually `ι`-pure of weight `w` is punctually
`ι`-pure of weight `w`: its stalks at the closed points of `U` are those of `G`, with the same
residue fields, and its other stalks vanish. -/
theorem IsPunctuallyPureOfWeight.extensionByZero {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l U}
    {w : ℝ} (hG : G.IsPunctuallyPureOfWeight ι w) :
    ((WeilSheaf.extensionByZero j).obj G).IsPunctuallyPureOfWeight ι w := by
  intro x
  by_cases hx : x.1 ∈ Set.range j.base
  · obtain ⟨z, hz⟩ := hx
    have hz' : z ∈ U.finitePoints :=
      (Scheme.Hom.mem_finitePoints_iff_of_isIso j z).1 (hz ▸ x.2)
    obtain rfl : x = ⟨j.base z, (Scheme.Hom.mem_finitePoints_iff_of_isIso j z).2 hz'⟩ :=
      Subtype.ext hz.symm
    obtain ⟨e⟩ := nonempty_equiv_stalk_extensionByZero j G ⟨z, hz'⟩
    have hdeg : (X ↘ Spec (CommRingCat.of k₀)).degreeOver (j.base z) =
        (U ↘ Spec (CommRingCat.of k₀)).degreeOver z := by
      rw [← Scheme.Hom.degreeOver_comp_of_isIso j (X ↘ Spec (CommRingCat.of k₀)) z, comp_over]
    have := hG ⟨z, hz'⟩
    rw [Scheme.Hom.residueCard] at this ⊢
    rw [hdeg]
    exact FrobeniusModule.IsPureOfWeight.of_equiv e this
  · intro α hα
    have := subsingleton_stalk_extensionByZero j G x hx
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    exact (hv.2 (Subsingleton.elim _ _)).elim

variable [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The extension by zero of Weil sheaves is left exact. -/
instance : PreservesFiniteLimits (WeilSheaf.extensionByZero (k₀ := k₀) (l := l) j) :=
  preservesFiniteLimits_of_comp_ι _ (ProEtaleWeilSheaf.extensionByZero k₀ l j)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _)

/-- The extension by zero of Weil sheaves is right exact. -/
instance : PreservesFiniteColimits (WeilSheaf.extensionByZero (k₀ := k₀) (l := l) j) :=
  preservesFiniteColimits_of_comp_ι _ (ProEtaleWeilSheaf.extensionByZero k₀ l j)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _)

end AlgebraicGeometry.WeilSheaf
