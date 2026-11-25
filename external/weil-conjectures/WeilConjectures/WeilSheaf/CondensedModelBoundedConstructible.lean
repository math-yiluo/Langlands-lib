/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChangeCoherence
public import WeilConjectures.TraceFormula.WeilTrace

/-!
# Compactly supported direct images of bounded constructible complexes on the geometric fibres

Let `k` be a finite field and `f : X₀ ⟶ Y₀` a morphism of `k`-schemes with a compactification `c`.
`WeilConjectures.WeilSheaf.CondensedModelBaseChange` identifies the condensed Weil `Rf̄_!` of
the pulled-back Weil objects `p_X^* M` with `p_Y^* (Rf_!(c) M)`, conditionally on the Frobenius
compatibility `AlgebraicGeometry.ProEtale.CondensedRing.UpperStarWeilCompatible` of the pullback
comparisons. This file discharges that hypothesis and specializes the result to the bounded
constructible lower shriek of the trace chapter.

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarWeilCompatible`: the pullback comparison
  `φ^* ⋙ p_X^* ≅ p_Y^* ⋙ φ̄^*` is Frobenius compatible for every morphism `φ` of `k`-schemes,
  from `AlgebraicGeometry.ProEtale.CondensedRing.upperStarSquareComparison_inv_app_frobenius`.
- `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilRightDerivedLowerShriekIso'`: the
  unconditional `D(p_X^*) ⋙ Rf̄_! ≅ Rf_!(c) ⋙ D(p_Y^*)` on condensed Weil objects.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekGeometricFiberWeilIso`:
  for the bounded constructible lower shriek `Rf_!` of the trace chapter
  (`boundedConstructibleLowerShriek ℓ f`, for the compactification chosen by Nagata's theorem),
  `p_Y^* (Rf_! K) ≅ Rf̄_! (p_X^* K)` as condensed Weil objects, naturally in `K ∈ Dᵇc(X)`.
- `AlgebraicGeometry.ProEtale.CondensedRing.weilCompactSupportCohomologyGeometricFiberWeilIso`:
  the pullback to `Spec k̄` of the compactly supported cohomology `RΓ_c(X, K)`
  (`weilCompactSupportCohomology`) of a Weil object `K`, with its canonical Frobenius structure,
  is the condensed Weil `Rā_!` of the pullback of `K` to the geometric fibre.

## Implementation notes

The Frobenius compatibility is reduced to the abstract
`CategoryTheory.Endofunctor.IsoAlgebra.map_comp_mapOfNatIso_obj_mk_str_hom`, instantiated with
the underlying objects `p^* M` spelled out, so that neither the elaborator nor the kernel has to
identify the carriers of the pulled-back Weil objects inside the composite morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D}

/-- A morphism `c : x ⟶ L y` intertwines the structure isomorphisms of `mk x Φx` and of the
transport `mapOfNatIso e (mk y Φy)` as soon as `G c ≫ e_y ≫ L Φy = Φx ≫ c`. -/
lemma map_comp_mapOfNatIso_obj_mk_str_hom (e : L ⋙ G ≅ F ⋙ L) {x : D} (Φx : G.obj x ≅ x)
    {y : C} (Φy : F.obj y ≅ y) (c : x ⟶ L.obj y)
    (hc : G.map c ≫ e.hom.app y ≫ L.map Φy.hom = Φx.hom ≫ c) :
    G.map c ≫ ((mapOfNatIso e).obj (mk y Φy)).str.hom = (mk x Φx).str.hom ≫ c :=
  hc

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
  {t : Y₀ ⟶ Spec (.of k)}

variable (s) in
/-- The invariance isomorphism `p^* ⋙ (Fr_X⁻¹)_* ≅ p^*`, unfolded. -/
lemma geometricFiberProjLowerStarFrobeniusIso_eq :
    geometricFiberProjLowerStarFrobeniusIso Λ s =
      Functor.isoWhiskerLeft (s.geometricFiberProj)^*⟦Λ⟧
          (upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso).symm ≪≫
        (upperStarComp Λ s.geometricGaloisFrobenius.asIso.hom s.geometricFiberProj).symm ≪≫
        upperStarCongr Λ (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj s) :=
  rfl

section Exchange

variable (φ : X₀ ⟶ Y₀) (h : φ ≫ t = s)

/-- The exchange isomorphism of the pullback along `φ̄`, unfolded. -/
lemma upperStarGeometricFiberMapCompFrobeniusIso_eq :
    upperStarGeometricFiberMapCompFrobeniusIso Λ φ h =
      Endofunctor.IsoAlgebra.leftMateIso
        (upperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))
        (lowerStarComp Λ _ _ ≪≫
          lowerStarCongr Λ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
          (lowerStarComp Λ _ _).symm) :=
  rfl

omit [Finite k] in
/-- The comparison of the pullbacks around the base change square of `φ`, unfolded. -/
lemma geometricFiberUpperStarComparison_hom :
    (geometricFiberUpperStarComparison Λ φ h).hom =
      (upperStarSquareComparison Λ
        (Scheme.Hom.isPullback_geometricFiberMap φ h).flip.toCommSq).inv :=
  rfl

/-- **The pullback comparison is Frobenius compatible**: the hypothesis
`AlgebraicGeometry.ProEtale.CondensedRing.UpperStarWeilCompatible` holds for every morphism of
`k`-schemes, by `upperStarSquareComparison_inv_app_frobenius`. -/
theorem upperStarWeilCompatible : UpperStarWeilCompatible Λ φ h := fun N ↦ by
  refine Endofunctor.IsoAlgebra.map_comp_mapOfNatIso_obj_mk_str_hom
    (upperStarGeometricFiberMapCompFrobeniusIso Λ φ h)
    ((geometricFiberProjLowerStarFrobeniusIso Λ s).app ((φ)^*⟦Λ⟧.obj N))
    ((geometricFiberProjLowerStarFrobeniusIso Λ t).app N)
    ((geometricFiberUpperStarComparison Λ φ h).hom.app N) ?_
  rw [Iso.app_hom, Iso.app_hom, geometricFiberUpperStarComparison_hom,
    upperStarGeometricFiberMapCompFrobeniusIso_eq, geometricFiberProjLowerStarFrobeniusIso_eq,
    geometricFiberProjLowerStarFrobeniusIso_eq]
  exact upperStarSquareComparison_inv_app_frobenius Λ s.geometricFiberProj t.geometricFiberProj φ
    (Scheme.Hom.geometricFiberMap φ h) s.geometricGaloisFrobenius.asIso
    t.geometricGaloisFrobenius.asIso
    s.geometricGaloisFrobenius_hom_comp_geometricFiberProj
    t.geometricGaloisFrobenius_hom_comp_geometricFiberProj
    (Scheme.Hom.isPullback_geometricFiberMap φ h).flip.toCommSq
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm N

end Exchange

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
  {t : Y₀ ⟶ Spec (.of k)} {f : X₀ ⟶ Y₀}

/-- **The direct image with compact support of pulled-back Weil objects**: for a compactification
`c` of `f : X₀ ⟶ Y₀`, the condensed Weil `Rf̄_!` of the Weil objects `p_X^* M` with their canonical
Frobenius structure is `p_Y^* (Rf_! M)` with its canonical Frobenius structure:
`D(p_X^*) ⋙ Rf̄_! ≅ Rf_!(c) ⋙ D(p_Y^*)`. This is
`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilRightDerivedLowerShriekIso` with the
Frobenius compatibilities discharged by `upperStarWeilCompatible`. -/
noncomputable def geometricFiberWeilRightDerivedLowerShriekIso'
    (c : Compactification f) (h : f ≫ t = s) :
    (geometricFiberWeilLowerStar Λ s).mapDerivedCategory ⋙ weilRightDerivedLowerShriek Λ c h ≅
      Rf_!(c)⟦Λ⟧ ⋙ (geometricFiberWeilLowerStar Λ t).mapDerivedCategory :=
  geometricFiberWeilRightDerivedLowerShriekIso c h (upperStarWeilCompatible Λ _ _)
    (upperStarWeilCompatible Λ _ _)

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### Bounded constructible complexes -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The lower shriek `Rf_!^c` of bounded constructible complexes, for a compactification `c` of
`f.left`, commutes with the pullback to the geometric fibres, with Weil structures:
`ι ⋙ D(p_Y^*)` of `Rf_!^c K` is the condensed Weil `Rf̄_!` of `D(p_X^*) (ι K)`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationGeometricFiberWeilIso
    {f : X ⟶ Y} (c : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙ (boundedConstructible _).ι ⋙
        (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) Y.hom).mapDerivedCategory ≅
      (boundedConstructible _).ι ⋙
        (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) X.hom).mapDerivedCategory ⋙
          weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj ℓ) c (Over.w f) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c)
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (geometricFiberWeilRightDerivedLowerShriekIso' c (Over.w f)).symm

/-- **The compactly supported direct image of bounded constructible complexes commutes with the
pullback to the geometric fibres, with Weil structures**: for `K` bounded constructible on `X`,
`p_Y^* (Rf_! K) ≅ Rf̄_! (p_X^* K)` as condensed Weil objects, where `Rf_!` is
`boundedConstructibleLowerShriek ℓ f` (for the compactification chosen by Nagata's theorem) and
`Rf̄_!` is the condensed Weil lower shriek of its base change to the geometric fibres. -/
noncomputable def boundedConstructibleLowerShriekGeometricFiberWeilIso (f : X ⟶ Y) :
    boundedConstructibleLowerShriek ℓ f ⋙ (boundedConstructible _).ι ⋙
        (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) Y.hom).mapDerivedCategory ≅
      (boundedConstructible _).ι ⋙
        (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) X.hom).mapDerivedCategory ⋙
          weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj ℓ)
            (compactificationOverField f) (Over.w f) :=
  boundedConstructibleLowerShriekOfCompactificationGeometricFiberWeilIso ℓ
    (compactificationOverField f)

variable (e : X ≅ X)

/-- **Compactly supported cohomology and the geometric fibre**: for Weil objects `K` on `X` (for
any `e : X ≅ X`), the pullback to `Spec k̄` of the underlying complex of the compactly supported
cohomology `RΓ_c(X, K)` (`weilCompactSupportCohomology`), with its canonical Frobenius structure,
is the condensed Weil `Rā_!` of the pullback of `K` to the geometric fibre `X̄`, naturally in
`K`. -/
noncomputable def weilCompactSupportCohomologyGeometricFiberWeilIso :
    weilCompactSupportCohomology ℓ e ⋙ WeilBoundedConstructible.forget ℓ _ ⋙
        (boundedConstructible _).ι ⋙
          (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ)
            (point k).hom).mapDerivedCategory ≅
      WeilBoundedConstructible.forget ℓ e.hom ⋙ (boundedConstructible _).ι ⋙
        (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) X.hom).mapDerivedCategory ⋙
          weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj ℓ)
            (compactificationOverField (toPoint X)) (Over.w (toPoint X)) :=
  Functor.isoWhiskerLeft (WeilBoundedConstructible.forget ℓ e.hom)
    (boundedConstructibleLowerShriekGeometricFiberWeilIso ℓ (toPoint X))

/-- The components of `weilCompactSupportCohomologyGeometricFiberWeilIso`: for a Weil object `K`
on `X`, `p^* RΓ_c(X, K) ≅ Rā_! (p_X^* K)` as condensed Weil objects on `Spec k̄`. -/
lemma weilCompactSupportCohomologyGeometricFiberWeilIso_app
    (K : WeilBoundedConstructible ℓ e.hom) :
    (weilCompactSupportCohomologyGeometricFiberWeilIso ℓ e).app K =
      (boundedConstructibleLowerShriekGeometricFiberWeilIso ℓ (toPoint X)).app K.carrier :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
