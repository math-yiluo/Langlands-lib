/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityBoundedShriekUniversality
public import WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareInverse

/-! # Ambient coordinates of the cross-field compactification exchange -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (c : Compactification f.left) (c' : Compactification f'.left)
  {πZ : c'.Z ⟶ c.Z} (hi : IsPullback c'.i πX πZ c.i)
  (hg : IsPullback πZ c'.g c.g πY) [WeaklyEtale πZ] [WeaklyEtale πY]

/-- The inverse of the bounded compactification exchange in ambient coordinates. -/
lemma purityFieldCompactificationExchange_inv_app_hom
    (P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧) :
    ((purityFieldCompactificationExchange l f f' c c' hi hg).inv.app P).hom =
      (boundedConstructibleLowerShriekOfCompactificationCompatibility l c').hom.app
          ((boundedConstructibleUpperStarOfMap l πX).obj P) ≫
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c').map
        ((purityFieldPullbackCompatibility l (πY := πX)).hom.app P) ≫
      (purityFieldCompactificationAmbientExchange l f f' c c' hi hg).inv.app P.obj ≫
      (upperStar (Profinite.padicAlgClRingObj l) πY).leftDerivedFunctor.map
        ((boundedConstructibleLowerShriekOfCompactificationCompatibility l c).inv.app P) ≫
      (purityFieldPullbackCompatibility l (πY := πY)).inv.app
        ((boundedConstructibleLowerShriekOfCompactification l c).obj P) := by
  exact ObjectProperty.preimageIso_comparisonSquare_inv_app_hom
    (boundedConstructibleLowerShriekOfCompactificationCompatibility l c)
    (boundedConstructibleLowerShriekOfCompactificationCompatibility l c')
    (purityFieldPullbackCompatibility l (πY := πX))
    (purityFieldPullbackCompatibility l (πY := πY))
    (purityFieldCompactificationAmbientExchange l f f' c c' hi hg) P

variable {P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧}
  {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧}
  (ε : (boundedConstructibleLowerShriekOfCompactification l c).obj P ⟶ N)

/-- The ambient trace of the bounded base change is the base change of the ambient
trace, in the specified pullback coordinates. -/
lemma purityFieldCompactificationTrace_coordinates :
    (boundedConstructibleLowerShriekOfCompactificationCompatibility l c').inv.app
        ((boundedConstructibleUpperStarOfMap l πX).obj P) ≫
      ((purityFieldCompactificationExchange l f f' c c' hi hg).inv.app P).hom ≫
      ((boundedConstructibleUpperStarOfMap l πY).map ε).hom =
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c').map
      ((purityFieldPullbackCompatibility l (πY := πX)).hom.app P) ≫
      (purityFieldCompactificationAmbientExchange l f f' c c' hi hg).inv.app P.obj ≫
      (upperStar (Profinite.padicAlgClRingObj l) πY).leftDerivedFunctor.map
        ((boundedConstructibleLowerShriekOfCompactificationCompatibility l c).inv.app P ≫ ε.hom) ≫
      (purityFieldPullbackCompatibility l (πY := πY)).inv.app N := by
  have he := ObjectProperty.preimageIso_comparisonSquare_trace_coordinates
    (boundedConstructibleLowerShriekOfCompactificationCompatibility l c)
    (boundedConstructibleLowerShriekOfCompactificationCompatibility l c')
    (purityFieldPullbackCompatibility l (πY := πX))
    (purityFieldPullbackCompatibility l (πY := πY))
    (purityFieldCompactificationAmbientExchange l f f' c c' hi hg) ε
  exact he

end AlgebraicGeometry.ProEtale.CondensedRing
