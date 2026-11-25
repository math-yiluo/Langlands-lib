/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.StrictlyHenselianNeighbourhood
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Boundary stalks of direct images as sections over a punctured strictly henselian neighbourhood

Let `j : U₀ ⟶ C₀` be a quasi-compact open immersion of `k₀`-schemes, `F` a Weil sheaf on `U₀` and
`x` a closed point of `C₀`, with geometric point `x̄ : Spec k̄ ⟶ C̄`. Let `h : Spec A ⟶ C̄` be a
weakly étale morphism from the spectrum of a strictly henselian local ring with a lift of `x̄`
through the closed point, for instance the strict localization of `C̄` at `x̄`. Then the germ map
identifies the sections of `F` over the pro-étale `Ū`-scheme `Spec A ×_C̄ Ū` with the stalk
`(j_* F)_x̄` (`AlgebraicGeometry.WeilSheaf.bijective_germ_stalk_directImage`).

For a boundary point `x` of a curve, `Spec A ×_C̄ Ū` is the spectrum of the fraction field of
the strict henselization, whose absolute Galois group is the inertia group at `x`: this is the
first step of blueprint `lemma-boundary-stalk--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The stalk of `j_* F` as sections over a strictly henselian neighbourhood.** Let
`h : Spec A ⟶ C̄` be weakly étale, `A` strictly henselian local, with a lift `t` of the geometric
point `x̄` of a closed point `x` through the closed point of `Spec A`. Then the germ map from the
sections of `F` over `Spec A ×_C̄ Ū` to the stalk `(j_* F)_x̄` is bijective.
(blueprint: `lemma-boundary-stalk--1`, first step) -/
theorem bijective_germ_stalk_directImage {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (x : C.finitePoints) {A : Type u} [CommRing A]
    [IsStrictlyHenselianLocalRing A]
    (h : Spec (.of A) ⟶ (C ↘ Spec (CommRingCat.of k₀)).geometricFiber) [WeaklyEtale h]
    (t : Scheme.ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤
      ((C ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)).obj
        (Scheme.ProEt.mk h))
    (ht : (t.left ≫ pullback.fst h _) (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      IsLocalRing.closedPoint A) :
    Function.Bijective (fun σ : ToType
        (((Scheme.Hom.geometricFiberMap j (comp_over j _))_*[WeilCoefficients.{u} l].obj
          F.obj.carrier.X).obj.obj (op (Scheme.ProEt.mk h))) ↦
      (germ (WeilCoefficients.{u} l) _
        ((Scheme.Hom.geometricFiberMap j (comp_over j _))_*[_].obj F.obj.carrier.X) t σ :
          (((directImage j).obj F).stalk x).carrier)) :=
  bijective_germ_of_weaklyEtale_of_isStrictlyHenselianLocalRing _ h
    ((Scheme.Hom.geometricFiberMap j (comp_over j _))_*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X) t ht

end AlgebraicGeometry.WeilSheaf
