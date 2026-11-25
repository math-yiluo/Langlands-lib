/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitSmoothSurface
public import WeilConjectures.AlgebraicGeometry.RegularDivisorRegularImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.TraceFormula.TransverseBoundary.Basic

/-!
# Transverse corners from regular divisors

The transverse boundary calculation (blueprint `lemma-cohomology-near-two-transverse-divisors`) is
proved for a `AlgebraicGeometry.Scheme.TransverseCorner`. This file builds such a corner from a
`k`-scheme `Z ⟶ Spec k` (an object of `Over (Spec k)`) which is an étale limit of smooth surfaces,
regular and locally noetherian, two regular divisors `X, Y` of `Z` meeting transversely at `z` whose
intersection has codimension two, and the open complements `Z - Y` and `Z - (X ∪ Y)`. It also
compares the two restriction maps `RΓ(X, K) ⟶ RΓ(X', f^* K)` built from the derived pullback
`Lf^*` and from the levelwise pullback `D(f^*)`.

## Main definitions and statements

- `AlgebraicGeometry.IsEtaleLimitOfSmoothSurfaces.scheme`: an étale limit of smooth surfaces in
  `Over (Spec k)` is one in the sense of `AlgebraicGeometry.Scheme.IsEtaleLimitOfSmoothSurfaces`.
- `AlgebraicGeometry.Scheme.TransverseCorner.ofRegularDivisors`: the transverse corner of two
  regular divisors meeting transversely.
- `AlgebraicGeometry.Etale.globalSectionsRestriction_eq_comp`: the restriction map along the
  levelwise pullback is the restriction map along the derived pullback, followed by the
  identification `Lf^* ≅ D(f^*)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- An étale limit of smooth surfaces in `Over (Spec k)` is an étale limit of smooth surfaces in
the sense of `AlgebraicGeometry.Scheme.IsEtaleLimitOfSmoothSurfaces`: the forgetful functor
`Over (Spec k) ⥤ Scheme` preserves cofiltered limits, which are connected. -/
theorem IsEtaleLimitOfSmoothSurfaces.scheme {Z : Over (Spec (.of k))}
    (h : IsEtaleLimitOfSmoothSurfaces Z) : Scheme.IsEtaleLimitOfSmoothSurfaces Z.hom := by
  obtain ⟨J, _, _, F, c, ⟨hc⟩, ⟨e⟩, hsm, hF⟩ := h
  have : IsConnected J := IsCofiltered.isConnected J
  refine ⟨J, inferInstance, inferInstance, F ⋙ Over.forget _, fun j ↦ (F.obj j).hom,
    (Over.forget _).mapCone c, isLimitOfPreserves (Over.forget _) hc, (Over.forget _).mapIso e,
    fun f ↦ Over.w (F.map f), fun j ↦ ?_, hsm, fun f ↦ ⟨(hF f).2, (hF f).1⟩⟩
  change (c.π.app j).left ≫ (F.obj j).hom = e.hom.left ≫ Z.hom
  rw [Over.w, Over.w]
  rfl

namespace Scheme.TransverseCorner

/-- **The transverse corner of two regular divisors** (blueprint
`lemma-cohomology-near-two-transverse-divisors`). Let `Z` be a regular, locally noetherian
`k`-scheme which is an étale limit of smooth surfaces, `X, Y` regular divisors of `Z` meeting
transversely at `z` (their scheme-theoretic intersection is the reduced point `z`) with intersection
of codimension two, and `Z - Y`, `Z - (X ∪ Y)` the open complements. This is a transverse corner
with `j : Z - Y ⟶ Z` and `i : Z - (X ∪ Y) ⟶ Z - Y` the inclusions. -/
@[simps]
noncomputable def ofRegularDivisors {Z : Over (Spec (.of k))}
    (hZ : AlgebraicGeometry.IsEtaleLimitOfSmoothSurfaces Z) [IsLocallyNoetherian Z.left]
    [IsRegular Z.left] {X Y : Scheme.{u}} {iX : X ⟶ Z.left} {iY : Y ⟶ Z.left}
    (hX : IsRegularDivisor iX) (hY : IsRegularDivisor iY) (z : Z.left)
    (hz : MeetTransverselyAt iX iY z) (hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX))
    {UY UXY : Z.left.Opens}
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY) :
    TransverseCorner k :=
  haveI := hX.isRegularImmersion
  haveI := hY.isRegularImmersion
  haveI := hX.2
  haveI := hY.2
  haveI := hz.isRegular_pullback
  { Z := Z.left
    aZ := Z.hom
    isEtaleLimitOfSmoothSurfaces := hZ.scheme
    X := X
    Y := Y
    iX := iX
    iY := iY
    isRegularImmersion_inter := hXY
    z := z
    range_inter := hz.range_inter_range
    U := UY
    j := UY.ι
    range_j := by rw [Scheme.Opens.range_ι, hUY]
    V := UXY
    i := Z.left.homOfLE hle
    range_i_j := by rw [Scheme.homOfLE_ι, Scheme.Opens.range_ι, hUXY] }

end Scheme.TransverseCorner

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The restriction map `RΓ(X, K) ⟶ RΓ(X', f^* K)` along the levelwise pullback `D(f^*)` is the
restriction map along the derived pullback `Lf^*`, followed by the comparison `Lf^* ≅ D(f^*)` of
the two left adjoints of `Rf_*`. -/
lemma globalSectionsRestriction_eq_comp {X X' : Scheme.{u}} (f : X' ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    globalSectionsRestriction f K = derivedGlobalSectionsRestriction Λ f K ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X').map
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).leftAdjointUniq
          (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)).hom.app K) := by
  rw [globalSectionsRestriction, derivedGlobalSectionsRestriction,
    ← Adjunction.unit_leftAdjointUniq_hom_app
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f), Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ f).hom.naturality _

/-- If the restriction map along the derived pullback vanishes, so does the restriction map
along the levelwise pullback. -/
lemma globalSectionsRestriction_eq_zero_of_derived {X X' : Scheme.{u}} (f : X' ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : derivedGlobalSectionsRestriction Λ f K = 0) : globalSectionsRestriction f K = 0 := by
  rw [globalSectionsRestriction_eq_comp, h, zero_comp]

end Etale

end AlgebraicGeometry
