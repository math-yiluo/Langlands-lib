/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# Finite-level coefficient change and the compactly supported direct image

Let `S` be a finite free algebra over a commutative ring `R`, for instance a finite extension of
finite coefficient rings `A_{E,n} → A_{E',n}` with `E'/E` unramified. Derived scalar extension
`N = - ⊗ᴸ_R S = L(S ⊗_R -) : D(X_proét, R) ⥤ D(X_proét, S)` commutes with the operations:

- with the derived pullbacks `Lf^*`
  (`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompUpperStarIso`,
  `AlgebraicGeometry.ProEtale.nonempty_leftDerivedUpperStar_comp_iso`), hence with geometric
  stalks, and Weil structures extend (`AlgebraicGeometry.ProEtale.extendScalarsWeilStructure`);
- with extension by zero along open immersions
  (`AlgebraicGeometry.ProEtale.mapDerivedCategoryOpenLowerShriekExtendScalarsIso`);
- with the derived direct images `Rg_*`
  (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarExtendScalarsIso`);
- hence with the compactly supported direct images `Rf_!`
  (`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationExtendScalarsIso`,
  `AlgebraicGeometry.ProEtale.nonempty_rightDerivedLowerShriek_comp_iso`).

These are the natural isomorphisms of blueprint `theorem-grothendieck-lefschetz-trace-formula--7`
and of the sketch `theorem-grothendieck-lefschetz-trace-formula--7`. Being natural, they intertwine
the images of every endomorphism, in particular of the Frobenius maps; by the scalar-extension law
of the categorical trace (`CategoryTheory.Functor.trace_eq_unitEndRingHom_trace`, blueprint
`proposition-properties-trace`, item (3)), the trace of the scalar extension of an endomorphism
of a compactly supported direct image is the image of its trace
(`AlgebraicGeometry.ProEtale.trace_rightDerivedLowerShriekOfCompactification_map_extendScalars`),
and similarly on derived pullbacks such as stalks
(`AlgebraicGeometry.ProEtale.trace_leftDerivedUpperStar_extendScalars`).

## Gaps with respect to the blueprint

- The coefficient map `ρ : A → B` is assumed finite free, so that `S ⊗_R -` is exact and its
  derived functor is computed levelwise. For a general `ρ` (such as `ℤ/ℓ² → ℤ/ℓ`) the derived
  scalar extension of pro-étale sheaves of modules is not available with its commutation
  isomorphisms.
- The derived scalar extension is not given a braided monoidal structure on the derived
  categories, and the derived categories `D(X_proét)` carry no chosen braiding; the trace law is
  therefore stated for a braided monoidal structure on `N` taken as an argument.
- The stability of `Dctf` under `N`, and the Frobenius operators of strict Weil complexes on the
  pro-étale site, are not formalised here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- The derived scalar extension is additive, being isomorphic to the levelwise one. -/
instance additive_leftDerivedSheafExtendScalars (X : Scheme.{u}) :
    (L(sheafExtendScalars (algebraMap R S) X)).Additive :=
  Functor.additive_of_iso
    (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorIsoMapDerivedCategory.symm

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--7`: derived scalar extension commutes
with extension by zero along an open immersion `j`, `L(S ⊗_R -) ∘ Dj_! ≅ Dj_! ∘ L(S ⊗_R -)`, both
functors being exact. -/
noncomputable def mapDerivedCategoryOpenLowerShriekExtendScalarsIso :
    D((j)_!open[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) X) ≅
      L(sheafExtendScalars (algebraMap R S) U) ⋙ D((j)_!open[ModuleCat.{u + 1} S]) :=
  Functor.isoWhiskerLeft _
      (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekCompSheafExtendScalarsIso j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight
      (sheafExtendScalars (algebraMap R S) U).leftDerivedFunctorIsoMapDerivedCategory.symm _

end OpenImmersion

variable [Module.Finite R S] [Module.Free R S] [Nontrivial R]

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--7`: derived scalar extension along a
finite free algebra commutes with the derived direct image, `L(S ⊗_R -) ∘ Rg_* ≅ Rg_* ∘ L(S ⊗_R -)`;
it is the base change map, the mate of the commutation with `Lg^*`, which is invertible by
`AlgebraicGeometry.ProEtale.isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app`. -/
noncomputable def rightDerivedLowerStarExtendScalarsIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    R((g)_*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Y) ≅
      L(sheafExtendScalars (algebraMap R S) Z) ⋙ R((g)_*[ModuleCat.{u + 1} S]) :=
  have (M : _) := isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app
    (R := R) (S := S) g M
  have : IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g).hom) :=
    NatIso.isIso_of_isIso_app _
  asIso (mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
    (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g).hom)

section UpperStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

omit [Module.Finite R S] [Module.Free R S] [Nontrivial R] in
/-- **Finite-level coefficient change commutes with `Lg^*`** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`): `(Lg^* L) ⊗ᴸ_R S ≅ Lg^*(L ⊗ᴸ_R S)`, the derived
commutation `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompUpperStarIso`. -/
theorem nonempty_leftDerivedUpperStar_comp_iso :
    Nonempty (L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Z) ≅
      L(sheafExtendScalars (algebraMap R S) Y) ⋙ L((g)^*[ModuleCat.{u + 1} S])) :=
  ⟨(leftDerivedSheafExtendScalarsCompUpperStarIso g).symm⟩

/-- The scalar extension of a Weil structure (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`): for an endomorphism `g` of `X` and
`φ : Lg^* K ≅ K` over `R`, the structure `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S ≅ K ⊗ᴸ_R S` over `S`. -/
noncomputable def extendScalarsWeilStructure (g : Y ⟶ Y)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R))}
    (φ : (L((g)^*[ModuleCat.{u + 1} R])).obj K ≅ K) :
    (L((g)^*[ModuleCat.{u + 1} S])).obj ((L(sheafExtendScalars (algebraMap R S) Y)).obj K) ≅
      (L(sheafExtendScalars (algebraMap R S) Y)).obj K :=
  (leftDerivedSheafExtendScalarsCompUpperStarIso g).app K ≪≫
    (L(sheafExtendScalars (algebraMap R S) Y)).mapIso φ

omit [Module.Finite R S] [Module.Free R S] [Nontrivial R] in
/-- **Scalar-extension law for the traces on derived pullbacks**, for instance on geometric
stalks (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`): an endomorphism `w` of
`Lg^* K` and its transport `w'` to `Lg^*(K ⊗ᴸ_R S)` along the commutation of `Lg^*` with the scalar
extension `N` (for instance a local Frobenius `F_{y,m}` and its scalar extension) satisfy
`tr(w') = ρ_N(tr w)`. The braidings and the braided monoidal structure of `N` are arguments. -/
theorem trace_leftDerivedUpperStar_extendScalars
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)))]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S)))]
    [(L(sheafExtendScalars (algebraMap R S) Z)).Braided]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    (w : (L((g)^*[ModuleCat.{u + 1} R])).obj K ⟶ (L((g)^*[ModuleCat.{u + 1} R])).obj K)
    [HasRightDual ((L((g)^*[ModuleCat.{u + 1} R])).obj K)]
    [HasRightDual ((L(sheafExtendScalars (algebraMap R S) Z)).obj
      ((L((g)^*[ModuleCat.{u + 1} R])).obj K))]
    [HasRightDual ((L((g)^*[ModuleCat.{u + 1} S])).obj
      ((L(sheafExtendScalars (algebraMap R S) Y)).obj K))] :
    trace (X := (L((g)^*[ModuleCat.{u + 1} S])).obj
        ((L(sheafExtendScalars (algebraMap R S) Y)).obj K))
      ((leftDerivedSheafExtendScalarsCompUpperStarIso g).hom.app K ≫
        (L(sheafExtendScalars (algebraMap R S) Z)).map w ≫
          (leftDerivedSheafExtendScalarsCompUpperStarIso g).inv.app K) =
      ((L(sheafExtendScalars (algebraMap R S) Z)).unitEndRingHom (.of (trace w))).asHom :=
  Functor.trace_eq_unitEndRingHom_trace (L(sheafExtendScalars (algebraMap R S) Z))
    (X' := (L((g)^*[ModuleCat.{u + 1} S])).obj ((L(sheafExtendScalars (algebraMap R S) Y)).obj K))
    w _ ((leftDerivedSheafExtendScalarsCompUpperStarIso g).app K).symm (by simp)

end UpperStar

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--7`: derived scalar extension along a
finite free algebra commutes with the compactly supported direct image attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)`, `(Rf_! K) ⊗ᴸ_R S ≅ Rf_!(K ⊗ᴸ_R S)`: it commutes with
`Di_!` and with `Rg_*`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationExtendScalarsIso
    (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} R] ⋙ L(sheafExtendScalars (algebraMap R S) Y) ≅
      L(sheafExtendScalars (algebraMap R S) X) ⋙ Rf_!(c)[ModuleCat.{u + 1} S] :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarExtendScalarsIso c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryOpenLowerShriekExtendScalarsIso c.i) _ ≪≫
    Functor.associator _ _ _

variable (f) in
/-- **Finite-level coefficient change commutes with `Rf_!`** (sketch
`theorem-grothendieck-lefschetz-trace-formula--7`, blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`): for a finite free algebra `S` over `R` and a
compactifiable morphism `f`, there is a natural isomorphism `(Rf_! K) ⊗ᴸ_R S ≅ Rf_!(K ⊗ᴸ_R S)`. -/
theorem nonempty_rightDerivedLowerShriek_comp_iso [HasCompactification f] :
    Nonempty (R(f)_![ModuleCat.{u + 1} R] ⋙ L(sheafExtendScalars (algebraMap R S) Y) ≅
      L(sheafExtendScalars (algebraMap R S) X) ⋙ R(f)_![ModuleCat.{u + 1} S]) :=
  ⟨rightDerivedLowerShriekOfCompactificationExtendScalarsIso _⟩

/-- **Scalar-extension law for the traces of compactly supported direct images** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`, through item (3) of
`proposition-properties-trace`): for an endomorphism `v` of `K ∈ D(X_proét, R)`, for instance a
Frobenius map, the trace of `Rf_!(v ⊗ᴸ_R S)` is the image of the trace of `Rf_! v` under the map
`ρ_N : End(Λ_Y) → End(S_Y)` induced by the derived scalar extension `N`. The braidings of the
derived categories and the braided monoidal structure of `N` are arguments (see the module
docstring). -/
theorem trace_rightDerivedLowerShriekOfCompactification_map_extendScalars
    (c : Compactification f)
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} S)))]
    [(L(sheafExtendScalars (algebraMap R S) Y)).Braided]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) (v : K ⟶ K)
    [HasRightDual ((Rf_!(c)[ModuleCat.{u + 1} R]).obj K)]
    [HasRightDual ((L(sheafExtendScalars (algebraMap R S) Y)).obj
      ((Rf_!(c)[ModuleCat.{u + 1} R]).obj K))]
    [HasRightDual ((Rf_!(c)[ModuleCat.{u + 1} S]).obj
      ((L(sheafExtendScalars (algebraMap R S) X)).obj K))] :
    trace ((Rf_!(c)[ModuleCat.{u + 1} S]).map ((L(sheafExtendScalars (algebraMap R S) X)).map v)) =
      ((L(sheafExtendScalars (algebraMap R S) Y)).unitEndRingHom
        (.of (trace ((Rf_!(c)[ModuleCat.{u + 1} R]).map v)))).asHom :=
  Functor.trace_eq_unitEndRingHom_trace (L(sheafExtendScalars (algebraMap R S) Y))
    (X' := (Rf_!(c)[ModuleCat.{u + 1} S]).obj ((L(sheafExtendScalars (algebraMap R S) X)).obj K))
    _ _
    ((rightDerivedLowerShriekOfCompactificationExtendScalarsIso c).app K)
    ((rightDerivedLowerShriekOfCompactificationExtendScalarsIso c).hom.naturality v)

end AlgebraicGeometry.ProEtale
